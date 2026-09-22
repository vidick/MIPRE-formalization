/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.Introspection.CompleteMeasurements

/-! # The actual QLD Pauli answers pass the introspection anchor tests -/

noncomputable section
namespace MIPRE.Introspection.Complete
open Matrix Finset Classical
set_option linter.unusedSectionVars false

variable {F A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] {m d ℓ : ℕ} [NeZero m]
  (L : Bool → CL.CLFun F (Fin m → Bool) ℓ)
  (D : Seed F m → Seed F m → A → A → Bool)
  (R : SyncStrategy (Honest.sourceGame L D).doubled)

def seedAnswer : Answer F A m d → ParsedAnswer (Seed F m) A (Seed F m)
  | .pauli a => .pauli (project a)
  | .pair y a => .pair y a
  | .read y yp a => .read y yp a
  | .hide y yp x => .hide y yp x

theorem auxOp_seedAnswer (hL : ∀ w, (L w).SupportedOn univ)
    (q : Honest.AuxQuestion ℓ) (a : Answer F A m d) :
    Honest.auxOp L D R hL q a = Honest.auxOp L D R hL q (seedAnswer a) := by
  rcases q with ⟨q,w⟩
  cases q <;> cases a <;> rfl

theorem pauliOp_zero_or_seed (hm : m ∣ Fintype.card F) (W : QLD.Bas)
    (a : Answer F A m d) :
    pauliOp L D R hm (.pauli W) a = 0 ∨ ∃ x, a = .pauli (.pauliAns x) := by
  cases a with
  | pauli a =>
    cases a with
    | pauliAns x => exact Or.inr ⟨x,rfl⟩
    | val x | apoly x | dpoly x | bit x | bitPair x | bitTriple x =>
      exact Or.inl (pauliOp_wrong L D R hm W _ rfl)
  | pair y a | read y yp a | hide y yp x => exact Or.inl rfl

theorem anchor_check (p : QLD.Ty) (q : Honest.AuxQuestion ℓ)
    (DP : QLD.Ty → QLD.Ty → QLD.Answer F m d → QLD.Answer F m d → Bool)
    (x : Seed F m) (b : Answer F A m d) :
    TypedPredicate.check L (.pauli .X) (.pauli .Z) project D DP
      (.inl p) (.inr q) (.pauli (.pauliAns x)) b =
    TypedPredicate.check L (.pauli .X) (.pauli .Z) id D (fun _ _ _ _ => true)
      (.inl p) (.inr q) (.pauli x) (seedAnswer b) := by
  rcases q with ⟨q,w⟩
  cases q <;> cases b <;>
    simp [TypedPredicate.check, TypedPredicate.fits, TypedPredicate.directed,
      seedAnswer, project] <;> congr 1
  by_cases hp : p = .pauli .Z <;> simp [hp]

theorem anchor_check_swap (p : QLD.Ty) (q : Honest.AuxQuestion ℓ)
    (DP : QLD.Ty → QLD.Ty → QLD.Answer F m d → QLD.Answer F m d → Bool)
    (a b : Answer F A m d) :
    TypedPredicate.check L (.pauli .X) (.pauli .Z) project D DP (.inl p) (.inr q) a b =
    TypedPredicate.check L (.pauli .X) (.pauli .Z) project D DP (.inr q) (.inl p) b a := by
  simp [TypedPredicate.check, Bool.and_comm, Bool.and_left_comm]

theorem anchor_X_commute (hm : m ∣ Fintype.card F)
    (hL : ∀ w, (L w).SupportedOn univ) (w : Bool) (k : Fin ℓ) (hk : k.val = 0)
    (a b : Answer F A m d) :
    Commute (pauliOp L D R hm (.pauli .X) a) (auxOp L D R hL (.hide k,w) b) := by
  rcases pauliOp_zero_or_seed L D R hm .X a with ha | ⟨x,rfl⟩
  · rw [ha]; exact Commute.zero_left _
  rw [pauliOp_X, auxOp, auxOp_seedAnswer]
  have hc := Honest.parsedPauliX_hide_commute L D R w (hL w)
    (.pauli x) (seedAnswer b)
  change Commute (aOp (HB := Fin 2) (Honest.pauliXOp L D R x))
    (aOp (HB := Fin 2) (Honest.parsedHideOp L D R w k.val (hL w) (seedAnswer b)))
  rw [hk]
  change _ * _ = _ * _
  rw [← aOp_mul, ← aOp_mul]
  exact congrArg (aOp (HB := Fin 2)) hc.eq

theorem anchor_Z_commute (hm : m ∣ Fintype.card F)
    (hL : ∀ w, (L w).SupportedOn univ) (w : Bool) (a b : Answer F A m d) :
    Commute (pauliOp L D R hm (.pauli .Z) a) (auxOp L D R hL (.sample,w) b) := by
  rcases pauliOp_zero_or_seed L D R hm .Z a with ha | ⟨x,rfl⟩
  · rw [ha]; exact Commute.zero_left _
  rw [pauliOp_Z, auxOp, auxOp_seedAnswer]
  have hc := Honest.parsedPauliZ_sample_commute L D R w (.pauli x) (seedAnswer b)
  change _ * _ = _ * _
  rw [← aOp_mul, ← aOp_mul]
  exact congrArg (aOp (HB := Fin 2)) hc.eq

theorem anchor_X_reject (hm : m ∣ Fintype.card F)
    (hL : ∀ w, (L w).SupportedOn univ) (w : Bool) (k : Fin ℓ) (hk : k.val = 0)
    (DP : QLD.Ty → QLD.Ty → QLD.Answer F m d → QLD.Answer F m d → Bool)
    (a b : Answer F A m d)
    (hr : TypedPredicate.check L (.pauli .X) (.pauli .Z) project D DP
      (.inl (.pauli .X)) (.inr (.hide k,w)) a b = false) :
    pauliOp L D R hm (.pauli .X) a * auxOp L D R hL (.hide k,w) b = 0 := by
  rcases pauliOp_zero_or_seed L D R hm .X a with ha | ⟨x,rfl⟩
  · rw [ha, zero_mul]
  rw [anchor_check] at hr
  have hz := Honest.parsedPauliX_hide_reject_zero L D R (.pauli .X : QLD.Ty)
    (.pauli .Z) (fun _ _ _ _ => true) w k hk (hL w) (.pauli x) (seedAnswer b) hr
  rw [pauliOp_X, auxOp, auxOp_seedAnswer, ← aOp_mul]
  change aOp (HB := Fin 2) (Honest.pauliXOp L D R x *
    Honest.parsedHideOp L D R w k.val (hL w) (seedAnswer b)) = 0
  rw [hk]
  exact (congrArg (aOp (HB := Fin 2)) hz).trans aOp_zero

theorem anchor_Z_reject (hm : m ∣ Fintype.card F)
    (hL : ∀ w, (L w).SupportedOn univ) (w : Bool)
    (DP : QLD.Ty → QLD.Ty → QLD.Answer F m d → QLD.Answer F m d → Bool)
    (a b : Answer F A m d)
    (hr : TypedPredicate.check L (.pauli .X) (.pauli .Z) project D DP
      (.inl (.pauli .Z)) (.inr (.sample,w)) a b = false) :
    pauliOp L D R hm (.pauli .Z) a * auxOp L D R hL (.sample,w) b = 0 := by
  rcases pauliOp_zero_or_seed L D R hm .Z a with ha | ⟨x,rfl⟩
  · rw [ha, zero_mul]
  rw [anchor_check] at hr
  have hz := Honest.parsedPauliZ_sample_reject_zero L D R (.pauli .X : QLD.Ty)
    (.pauli .Z) (fun _ _ _ _ => true) w (.pauli x) (seedAnswer b) hr
  rw [pauliOp_Z, auxOp, auxOp_seedAnswer, ← aOp_mul]
  exact (congrArg (aOp (HB := Fin 2)) hz).trans aOp_zero

end MIPRE.Introspection.Complete
end

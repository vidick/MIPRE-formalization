/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.Introspection.BinaryMeasurements

/-! # The actual QLD Pauli answers pass the introspection anchor tests -/

noncomputable section
namespace MIPRE.Introspection.BinaryComplete
open Matrix Finset Classical
set_option linter.unusedSectionVars false

variable {F A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] {m d ℓ t : ℕ} [NeZero m]
  (β : Module.Basis (Fin t) (ZMod 2) F)
  (L : Bool → CL.CLFun (ZMod 2) (Coord m t) ℓ)
  (D : Seed m t → Seed m t → A → A → Bool)
  (R : SyncStrategy (Honest.sourceGame L D).doubled)

def seedAnswer : Answer F A m t d → ParsedAnswer (Seed m t) A (Seed m t)
  | .pauli a => .pauli (project β a)
  | .pair y a => .pair y a
  | .read y yp a => .read y yp a
  | .hide y yp x => .hide y yp x

theorem auxOp_seedAnswer (hL : ∀ w, (L w).SupportedOn univ)
    (q : Honest.AuxQuestion ℓ) (a : Answer F A m t d) :
    Honest.auxOp L D R hL q a = Honest.auxOp L D R hL q (seedAnswer β a) := by
  rcases q with ⟨q,w⟩
  cases q <;> cases a <;> rfl

theorem pauliOp_zero_or_seed (hm : m ∣ Fintype.card F) (W : QLD.Bas)
    (a : Answer F A m t d) :
    pauliOp β L D R hm (.pauli W) a = 0 ∨ ∃ x, a = .pauli (.pauliAns x) := by
  cases a with
  | pauli a =>
    cases a with
    | pauliAns x => exact Or.inr ⟨x,rfl⟩
    | val x | apoly x | dpoly x | bit x | bitPair x | bitTriple x =>
      exact Or.inl (pauliOp_wrong β L D R hm W _ rfl)
  | pair y a | read y yp a | hide y yp x => exact Or.inl rfl

theorem anchor_check (p : QLD.Ty) (q : Honest.AuxQuestion ℓ)
    (DP : QLD.Ty → QLD.Ty → QLD.Answer F m d → QLD.Answer F m d → Bool)
    (x : QLD.Honest.Register F m) (b : Answer F A m t d) :
    TypedPredicate.check L (.pauli .X) (.pauli .Z) (project β) D DP
      (.inl p) (.inr q) (.pauli (.pauliAns x)) b =
    TypedPredicate.check L (.pauli .X) (.pauli .Z) id D (fun _ _ _ _ => true)
      (.inl p) (.inr q) (.pauli (Weyl.binEquiv β x)) (seedAnswer β b) := by
  rcases q with ⟨q,w⟩
  cases q <;> cases b <;>
    simp [TypedPredicate.check, TypedPredicate.fits, TypedPredicate.directed,
      seedAnswer, project] <;> congr 1
  by_cases hp : p = .pauli .Z <;> simp [hp]

theorem anchor_check_swap (p : QLD.Ty) (q : Honest.AuxQuestion ℓ)
    (DP : QLD.Ty → QLD.Ty → QLD.Answer F m d → QLD.Answer F m d → Bool)
    (a b : Answer F A m t d) :
    TypedPredicate.check L (.pauli .X) (.pauli .Z) (project β) D DP (.inl p) (.inr q) a b =
    TypedPredicate.check L (.pauli .X) (.pauli .Z) (project β) D DP (.inr q) (.inl p) b a := by
  simp [TypedPredicate.check, Bool.and_comm, Bool.and_left_comm]

theorem anchor_X_commute (hβ : LowDegree.IsSelfDualBasis β) (hm : m ∣ Fintype.card F)
    (hL : ∀ w, (L w).SupportedOn univ) (w : Bool) (k : Fin ℓ) (hk : k.val = 0)
    (a b : Answer F A m t d) :
    Commute (pauliOp β L D R hm (.pauli .X) a) (auxOp L D R hL (.hide k,w) b) := by
  rcases pauliOp_zero_or_seed β L D R hm .X a with ha | ⟨x,rfl⟩
  · rw [ha]; exact Commute.zero_left _
  rw [pauliOp_X _ _ _ _ hβ, auxOp, auxOp_seedAnswer β]
  have hc := Honest.parsedPauliX_hide_commute L D R w (hL w)
    (.pauli (Weyl.binEquiv β x)) (seedAnswer β b)
  change Commute (aOp (HB := Fin 2) (Honest.pauliXOp L D R (Weyl.binEquiv β x)))
    (aOp (HB := Fin 2) (Honest.parsedHideOp L D R w k.val (hL w) (seedAnswer β b)))
  rw [hk]
  change _ * _ = _ * _
  rw [← aOp_mul, ← aOp_mul]
  exact congrArg (aOp (HB := Fin 2)) hc.eq

theorem anchor_Z_commute (hβ : LowDegree.IsSelfDualBasis β) (hm : m ∣ Fintype.card F)
    (hL : ∀ w, (L w).SupportedOn univ) (w : Bool) (a b : Answer F A m t d) :
    Commute (pauliOp β L D R hm (.pauli .Z) a) (auxOp L D R hL (.sample,w) b) := by
  rcases pauliOp_zero_or_seed β L D R hm .Z a with ha | ⟨x,rfl⟩
  · rw [ha]; exact Commute.zero_left _
  rw [pauliOp_Z _ _ _ _ hβ, auxOp, auxOp_seedAnswer β]
  have hc := Honest.parsedPauliZ_sample_commute L D R w (.pauli (Weyl.binEquiv β x)) (seedAnswer β b)
  change _ * _ = _ * _
  rw [← aOp_mul, ← aOp_mul]
  exact congrArg (aOp (HB := Fin 2)) hc.eq

theorem anchor_X_reject (hβ : LowDegree.IsSelfDualBasis β) (hm : m ∣ Fintype.card F)
    (hL : ∀ w, (L w).SupportedOn univ) (w : Bool) (k : Fin ℓ) (hk : k.val = 0)
    (DP : QLD.Ty → QLD.Ty → QLD.Answer F m d → QLD.Answer F m d → Bool)
    (a b : Answer F A m t d)
    (hr : TypedPredicate.check L (.pauli .X) (.pauli .Z) (project β) D DP
      (.inl (.pauli .X)) (.inr (.hide k,w)) a b = false) :
    pauliOp β L D R hm (.pauli .X) a * auxOp L D R hL (.hide k,w) b = 0 := by
  rcases pauliOp_zero_or_seed β L D R hm .X a with ha | ⟨x,rfl⟩
  · rw [ha, zero_mul]
  rw [anchor_check] at hr
  have hz := Honest.parsedPauliX_hide_reject_zero L D R (.pauli .X : QLD.Ty)
    (.pauli .Z) (fun _ _ _ _ => true) w k hk (hL w) (.pauli (Weyl.binEquiv β x)) (seedAnswer β b) hr
  rw [pauliOp_X _ _ _ _ hβ, auxOp, auxOp_seedAnswer β, ← aOp_mul]
  change aOp (HB := Fin 2) (Honest.pauliXOp L D R (Weyl.binEquiv β x) *
    Honest.parsedHideOp L D R w k.val (hL w) (seedAnswer β b)) = 0
  rw [hk]
  exact (congrArg (aOp (HB := Fin 2)) hz).trans aOp_zero

theorem anchor_Z_reject (hβ : LowDegree.IsSelfDualBasis β) (hm : m ∣ Fintype.card F)
    (hL : ∀ w, (L w).SupportedOn univ) (w : Bool)
    (DP : QLD.Ty → QLD.Ty → QLD.Answer F m d → QLD.Answer F m d → Bool)
    (a b : Answer F A m t d)
    (hr : TypedPredicate.check L (.pauli .X) (.pauli .Z) (project β) D DP
      (.inl (.pauli .Z)) (.inr (.sample,w)) a b = false) :
    pauliOp β L D R hm (.pauli .Z) a * auxOp L D R hL (.sample,w) b = 0 := by
  rcases pauliOp_zero_or_seed β L D R hm .Z a with ha | ⟨x,rfl⟩
  · rw [ha, zero_mul]
  rw [anchor_check] at hr
  have hz := Honest.parsedPauliZ_sample_reject_zero L D R (.pauli .X : QLD.Ty)
    (.pauli .Z) (fun _ _ _ _ => true) w (.pauli (Weyl.binEquiv β x)) (seedAnswer β b) hr
  rw [pauliOp_Z _ _ _ _ hβ, auxOp, auxOp_seedAnswer β, ← aOp_mul]
  exact (congrArg (aOp (HB := Fin 2)) hz).trans aOp_zero

end MIPRE.Introspection.BinaryComplete
end

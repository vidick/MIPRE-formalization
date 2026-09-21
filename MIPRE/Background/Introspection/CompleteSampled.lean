/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.Introspection.CompleteAnchors
import MIPRE.Background.Introspection.HonestPauliGame

/-! # Every edge of the full introspection graph has perfect honest play -/

noncomputable section
namespace MIPRE.Introspection.Complete
open Matrix Finset Classical
set_option linter.unusedSectionVars false

variable {F A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] {m d ℓ : ℕ} [NeZero m]
  (L : Bool → CL.CLFun F (Fin m → Bool) ℓ)
  (D : Seed F m → Seed F m → A → A → Bool)
  (R : SyncStrategy (Honest.sourceGame L D).doubled)

def sampleOp (hm : m ∣ Fintype.card F) (hL : ∀ w, (L w).SupportedOn univ)
    (c : QLD.Content F m) : QuestionType QLD.Ty ℓ → Answer F A m d →
      Matrix (Space L D R) (Space L D R) ℂ
  | .inl p => pauliOp L D R hm (c.question hm p)
  | .inr q => auxOp L D R hL q

def sampleCheck (hm : m ∣ Fintype.card F) (c : QLD.Content F m) :=
  TypedPredicate.check L (.pauli .X : QLD.Ty) (.pauli .Z) project D
    (fun p q => QLD.accepts hm (c.question hm p) (c.question hm q) (d := d))

private theorem pauli_adj (p q : QLD.Ty)
    (h : TypeGraph.Adj (ℓ := ℓ) QLD.adj (.pauli .X) (.pauli .Z) (.inl p) (.inl q)) :
    QLD.adj p q = true := by
  change TypeGraph.adj QLD.adj (.pauli .X) (.pauli .Z) (.inl p) (.inl q) = true at h
  rwa [TypeGraph.adj_pauli QLD.adj _ _ QLD.adj_symm QLD.adj_self] at h

theorem pauli_pair_commute (hm : m ∣ Fintype.card F) (c : QLD.Content F m)
    (p q : QLD.Ty) (h : QLD.adj p q = true) (a b : Answer F A m d) :
    Commute (pauliOp L D R hm (c.question hm p) a)
      (pauliOp L D R hm (c.question hm q) b) := by
  cases a <;> cases b <;>
    simp only [pauliOp, Honest.parsedPauliOp, Commute.zero_left, Commute.zero_right]
  change _ * _ = _ * _
  rw [← pauliLift_mul, ← pauliLift_mul]
  exact congrArg (pauliLift L D R) (QLD.Honest.answerOp_sampled_commute hm c p q h _ _).eq

theorem pauli_pair_reject (hm : m ∣ Fintype.card F) (hd : 1 ≤ d) (c : QLD.Content F m)
    (p q : QLD.Ty) (h : QLD.adj p q = true) (a b : Answer F A m d)
    (hr : sampleCheck L D hm c (.inl p) (.inl q) a b = false) :
    pauliOp L D R hm (c.question hm p) a * pauliOp L D R hm (c.question hm q) b = 0 := by
  cases a <;> cases b <;> simp only [pauliOp, Honest.parsedPauliOp, zero_mul, mul_zero]
  rename_i a b
  rw [← pauliLift_mul]
  apply (congrArg (pauliLift L D R) ?_).trans (pauliLift_zero L D R)
  by_cases ht : p = q
  · subst q
    by_cases hab : a = b
    · subst b
      apply QLD.Honest.answerOp_sampled_reject hm hd c p p h a a
      simpa [sampleCheck, TypedPredicate.check, TypedPredicate.fits, TypedPredicate.directed] using hr
    · exact (QLD.Honest.answerOp_isPVM hm _).orthogonal hab
  · apply QLD.Honest.answerOp_sampled_reject hm hd c p q h a b
    simpa [sampleCheck, TypedPredicate.check, TypedPredicate.fits, TypedPredicate.directed, ht] using hr

theorem sampleOp_commute (hm : m ∣ Fintype.card F) (hL : ∀ w, (L w).SupportedOn univ)
    (hR : R.IsPCC) (c : QLD.Content F m) (p q : QuestionType QLD.Ty ℓ)
    (h : TypeGraph.Adj QLD.adj (.pauli .X) (.pauli .Z) p q) (a b : Answer F A m d) :
    Commute (sampleOp L D R hm hL c p a) (sampleOp L D R hm hL c q b) := by
  cases p with
  | inl p =>
    cases q with
    | inl q => exact pauli_pair_commute L D R hm c p q (pauli_adj p q h) a b
    | inr q =>
      obtain ⟨q,w⟩ := q
      rcases (TypeGraph.adj_pauli_aux_iff QLD.adj (.pauli .X) (.pauli .Z) p q w).mp h with
        ⟨rfl,k,rfl,hk⟩ | ⟨rfl,rfl⟩
      · exact anchor_X_commute L D R hm hL w k hk a b
      · exact anchor_Z_commute L D R hm hL w a b
  | inr p =>
    cases q with
    | inl q =>
      have hs := TypeGraph.symmetric QLD.adj (.pauli .X) (.pauli .Z) _ _ h
      obtain ⟨p,w⟩ := p
      rcases (TypeGraph.adj_pauli_aux_iff QLD.adj (.pauli .X) (.pauli .Z) q p w).mp hs with
        ⟨rfl,k,rfl,hk⟩ | ⟨rfl,rfl⟩
      · exact (anchor_X_commute L D R hm hL w k hk b a).symm
      · exact (anchor_Z_commute L D R hm hL w b a).symm
    | inr q =>
      change _ * _ = _ * _
      simp only [sampleOp, auxOp, ← aOp_mul]
      exact congrArg (aOp (HB := Fin 2))
        (Honest.auxOp_commute L D R hL hR QLD.adj (.pauli .X) (.pauli .Z) p q h a b).eq

theorem sampleOp_reject (hm : m ∣ Fintype.card F) (hd : 1 ≤ d)
    (hL : ∀ w, (L w).SupportedOn univ) (hR : R.IsPCC) (hval : R.value = 1)
    (c : QLD.Content F m) (p q : QuestionType QLD.Ty ℓ)
    (h : TypeGraph.Adj QLD.adj (.pauli .X) (.pauli .Z) p q) (a b : Answer F A m d)
    (hr : sampleCheck L D hm c p q a b = false) :
    sampleOp L D R hm hL c p a * sampleOp L D R hm hL c q b = 0 := by
  cases p with
  | inl p =>
    cases q with
    | inl q => exact pauli_pair_reject L D R hm hd c p q (pauli_adj p q h) a b hr
    | inr q =>
      obtain ⟨q,w⟩ := q
      rcases (TypeGraph.adj_pauli_aux_iff QLD.adj (.pauli .X) (.pauli .Z) p q w).mp h with
        ⟨rfl,k,rfl,hk⟩ | ⟨rfl,rfl⟩
      · exact anchor_X_reject L D R hm hL w k hk _ a b hr
      · exact anchor_Z_reject L D R hm hL w _ a b hr
  | inr p =>
    cases q with
    | inl q =>
      rw [(sampleOp_commute L D R hm hL hR c _ _ h a b).eq]
      have hr' : sampleCheck L D hm c (.inl q) (.inr p) b a = false := by
        change TypedPredicate.check _ _ _ _ _ _ _ _ _ _ = false
        rwa [anchor_check_swap]
      have hs := TypeGraph.symmetric QLD.adj (.pauli .X) (.pauli .Z) _ _ h
      obtain ⟨p,w⟩ := p
      rcases (TypeGraph.adj_pauli_aux_iff QLD.adj (.pauli .X) (.pauli .Z) q p w).mp hs with
        ⟨rfl,k,rfl,hk⟩ | ⟨rfl,rfl⟩
      · exact anchor_X_reject L D R hm hL w k hk _ b a hr'
      · exact anchor_Z_reject L D R hm hL w _ b a hr'
    | inr q =>
      simp only [sampleOp, auxOp, ← aOp_mul]
      exact (congrArg (aOp (HB := Fin 2))
        (Honest.auxOp_reject_zero L D R hL hR hval QLD.adj (.pauli .X) (.pauli .Z)
          project _ p q h a b hr)).trans aOp_zero

end MIPRE.Introspection.Complete
end

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AuxiliaryQuotientReindex
import MIPRE.Foundations.Introspection.TypedQuotientGame
import MIPRE.Foundations.Introspection.PrefixGuardGame

/-! # Exact game and PCC transport of quotient answers between coordinate types -/

noncomputable section
namespace MIPRE.Introspection.AuxiliaryQuotient
open Finset CL CLChecks Classical
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency true
variable {F ι κ A PA PT Q : Type*} [Field F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {ℓ : ℕ}

theorem prefix_attained_reindex (e : ι ≃ κ) (P : CLFun F ι ℓ) (k : ℕ) (y : ι → F) :
    (∃ x, ((P.reindex e).truncate k).eval x =
      (P.reindex e).outputPrefix k (reindexEquiv e y)) ↔
      ∃ x, (P.truncate k).eval x = P.outputPrefix k y := by
  rw [CLFun.truncate_reindex, outputPrefix_reindex]
  constructor
  · rintro ⟨x,hx⟩
    refine ⟨(reindexEquiv e).symm x, ?_⟩
    rw [CLFun.eval_reindex'] at hx
    exact (reindexEquiv e).injective hx
  · rintro ⟨x,hx⟩
    exact ⟨reindexEquiv e x, by rw [CLFun.eval_reindex, hx]⟩

theorem prefixGuard_reindex (e : ι ≃ κ) (L : Bool → CLFun F ι ℓ)
    (t : QuestionType PT ℓ) (a : ParsedAnswer (ι → F) A PA) :
    PrefixGuard.holds (fun w => (L w).reindex e) t (answerEquiv e a) ↔
      PrefixGuard.holds L t a := by
  rcases t with p | ⟨t,w⟩
  · cases a <;> rfl
  · cases t <;> cases a <;> try rfl
    all_goals exact prefix_attained_reindex e _ _ _

variable [Fintype F] [DecidableEq F] [Fintype A] [Fintype PA]
  [Fintype PT] [DecidableEq PT] [Fintype Q] [DecidableEq Q]
  (e : ι ≃ κ) (E : PT → PT → Bool) (X Z : PT)
  (P : PT → CLFun (ZMod 2) Q 3) (L : Bool → CLFun F ι ℓ)
  (project : PA → ι → F) (D : (ι → F) → (ι → F) → A → A → Bool)
  (DP : PT → PT → (Q → ZMod 2) → (Q → ZMod 2) → PA → PA → Bool)

abbrev reindexedGame := game E X Z P (fun w => (L w).reindex e)
  (fun a => reindexEquiv e (project a))
  (fun x y => D ((reindexEquiv e).symm x) ((reindexEquiv e).symm y)) DP

theorem reindexedGame_D (q r : CL.Detyping.Question (QuestionType PT ℓ) Q)
    (a b : ParsedAnswer (ι → F) A PA) :
    (reindexedGame e E X Z P L project D DP).D q r (answerEquiv e a) (answerEquiv e b) =
      (game E X Z P L project D DP).D q r a b :=
  check_reindex e L X Z project D _ _ _ _ _

/-- Return to the original coordinate type by an exact answer relabeling. -/
abbrev originalStrategy (S : TensorProductStrategy (reindexedGame e E X Z P L project D DP)) :
    TensorProductStrategy (game E X Z P L project D DP) :=
  S.relabel _ (Equiv.refl _) (Equiv.refl _) (answerEquiv e) (answerEquiv e)

theorem originalStrategy_value
    (S : TensorProductStrategy (reindexedGame e E X Z P L project D DP)) :
    (originalStrategy e E X Z P L project D DP S).value = S.value := by
  apply S.value_relabel _ (Equiv.refl _) (Equiv.refl _) (answerEquiv e) (answerEquiv e) (fun _ _ => rfl)
  intro q r a b
  exact (reindexedGame_D e E X Z P L project D DP q r a b).symm

theorem reindexedGame_quantumValue :
    quantumValue (reindexedGame e E X Z P L project D DP) =
      quantumValue (game E X Z P L project D DP) := by
  symm
  apply quantumValue_eq_of_equiv _ _ (Equiv.refl _) (Equiv.refl _) (answerEquiv e) (answerEquiv e)
    (fun _ _ => rfl)
  intro q r a b
  exact (reindexedGame_D e E X Z P L project D DP q r a b).symm

abbrev reindexedStrategy (S : TensorProductStrategy (game E X Z P L project D DP)) :
    TensorProductStrategy (reindexedGame e E X Z P L project D DP) :=
  S.relabel _ (Equiv.refl _) (Equiv.refl _) (answerEquiv e).symm (answerEquiv e).symm

theorem reindexedStrategy_value
    (S : TensorProductStrategy (game E X Z P L project D DP)) :
    (reindexedStrategy e E X Z P L project D DP S).value = S.value := by
  apply S.value_relabel _ (Equiv.refl _) (Equiv.refl _) (answerEquiv e).symm (answerEquiv e).symm
    (fun _ _ => rfl)
  intro q r a b
  obtain ⟨a,rfl⟩ := (answerEquiv (F := F) (A := A) (PA := PA) e).surjective a
  obtain ⟨b,rfl⟩ := (answerEquiv (F := F) (A := A) (PA := PA) e).surjective b
  simpa only [Equiv.refl_apply, Equiv.symm_apply_apply] using
    reindexedGame_D e E X Z P L project D DP q r a b

variable [DecidableEq A] [DecidableEq PA]

abbrev originalPCC (S : SyncStrategy (reindexedGame e E X Z P L project D DP).doubled) :
    SyncStrategy (game E X Z P L project D DP).doubled :=
  S.relabel _ (Equiv.refl _) (answerEquiv e)

theorem originalPCC_isPCC
    (S : SyncStrategy (reindexedGame e E X Z P L project D DP).doubled) (hS : S.IsPCC) :
    (originalPCC e E X Z P L project D DP S).IsPCC :=
  SyncStrategy.isPCC_relabel hS _ _ _ (fun _ _ => rfl)

theorem originalPCC_value
    (S : SyncStrategy (reindexedGame e E X Z P L project D DP).doubled) :
    (originalPCC e E X Z P L project D DP S).value = S.value := by
  apply S.value_relabel _ (Equiv.refl _) (answerEquiv e) (fun _ _ => rfl)
  intro q r a b
  simp only [Game.doubled_D, Equiv.refl_apply, reindexedGame_D]

@[simp] theorem originalPCC_dimension
    (S : SyncStrategy (reindexedGame e E X Z P L project D DP).doubled) :
    (originalPCC e E X Z P L project D DP S).d = S.d := rfl

theorem originalPCC_prefixGuard
    (S : SyncStrategy (reindexedGame e E X Z P L project D DP).doubled)
    (hS : ∀ q a, S.P.M q a ≠ 0 →
      PrefixGuard.holds (fun w => (L w).reindex e) q.2.1 a)
    (q : Bool × CL.Detyping.Question (QuestionType PT ℓ) Q)
    (a : ParsedAnswer (ι → F) A PA)
    (ha : (originalPCC e E X Z P L project D DP S).P.M q a ≠ 0) :
    PrefixGuard.holds L q.2.1 a :=
  (prefixGuard_reindex e L q.2.1 a).mp (hS q (answerEquiv e a) ha)

/-- Carry the same honest operators to the concrete coordinate numbering. -/
abbrev reindexedPCC (S : SyncStrategy (game E X Z P L project D DP).doubled) :
    SyncStrategy (reindexedGame e E X Z P L project D DP).doubled :=
  S.relabel _ (Equiv.refl _) (answerEquiv e).symm

theorem reindexedPCC_isPCC (S : SyncStrategy (game E X Z P L project D DP).doubled)
    (hS : S.IsPCC) : (reindexedPCC e E X Z P L project D DP S).IsPCC :=
  SyncStrategy.isPCC_relabel hS _ _ _ (fun _ _ => rfl)

theorem reindexedPCC_value (S : SyncStrategy (game E X Z P L project D DP).doubled) :
    (reindexedPCC e E X Z P L project D DP S).value = S.value := by
  apply S.value_relabel _ (Equiv.refl _) (answerEquiv e).symm (fun _ _ => rfl)
  intro q r a b
  obtain ⟨a,rfl⟩ := (answerEquiv (F := F) (A := A) (PA := PA) e).surjective a
  obtain ⟨b,rfl⟩ := (answerEquiv (F := F) (A := A) (PA := PA) e).surjective b
  simp only [Game.doubled_D, Equiv.refl_apply, Equiv.symm_apply_apply, reindexedGame_D]

@[simp] theorem reindexedPCC_dimension
    (S : SyncStrategy (game E X Z P L project D DP).doubled) :
    (reindexedPCC e E X Z P L project D DP S).d = S.d := rfl

set_option backward.isDefEq.respectTransparency false in
theorem reindexedPCC_prefixGuard (S : SyncStrategy (game E X Z P L project D DP).doubled)
    (hS : ∀ q a, S.P.M q a ≠ 0 → PrefixGuard.holds L q.2.1 a)
    (q : Bool × CL.Detyping.Question (QuestionType PT ℓ) Q)
    (a : ParsedAnswer (κ → F) A PA)
    (ha : (reindexedPCC e E X Z P L project D DP S).P.M q a ≠ 0) :
    PrefixGuard.holds (fun w => (L w).reindex e) q.2.1 a := by
  obtain ⟨a,rfl⟩ := (answerEquiv (F := F) (A := A) (PA := PA) e).surjective a
  apply (prefixGuard_reindex e L q.2.1 a).mpr
  apply hS q a
  simpa only [reindexedPCC, SyncStrategy.relabel_P_M, Equiv.refl_apply,
    Equiv.symm_apply_apply, SyncStrategy.relabel_d] using ha

end MIPRE.Introspection.AuxiliaryQuotient
end

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AnswerRefinement
import MIPRE.Foundations.Introspection.AdaptivePrefixAdvance
import MIPRE.Foundations.Introspection.AdaptivePrefixReplacement

/-! # Refining actual Introspect answers for the adaptive stage

The stage coordinate is read from a valid full answer. A malformed answer is
retained as `none`, with coordinate zero; its operator is never discarded.
The second component retains the full old answer as a fixed tail alphabet.
-/

noncomputable section
namespace MIPRE.Introspection
open Finset Matrix Classical Weyl
set_option linter.unusedSectionVars false

variable {ι F H K A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype A] [DecidableEq A] {ℓ : ℕ}

/-- Select the current coordinate, retaining malformed answers separately in
the tail rather than postulating that their operator vanishes. -/
def stageAnswerCoordinate (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F) :
    Option ((ι → F) × A) → (Fin (Fintype.card (P.factorOfPrefix k y)) → F)
  | none => 0
  | some a => coordinateRestrict (P.factorOfPrefix k y) a.1

def stageAnswerRefinement (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F)
    (M : Option ((ι → F) × A) → Matrix ((stageRemaining P k y → F) × H)
      ((stageRemaining P k y → F) × H) ℂ) :=
  graphRefinement M (stageAnswerCoordinate P k y)

def stageAnswerRefinementPOVM (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F)
    (M : POVM (Option ((ι → F) × A)) ((stageRemaining P k y → F) × H)) :=
  graphRefinementPOVM M (stageAnswerCoordinate P k y)

theorem stageAnswerRefinement_none (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F)
    (M : Option ((ι → F) × A) → Matrix ((stageRemaining P k y → F) × H) _ ℂ)
    (z : Fin (Fintype.card (P.factorOfPrefix k y)) → F) :
    stageAnswerRefinement P k y M (z, none) = if z = 0 then M none else 0 := rfl

theorem stageAnswerRefinement_some (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F)
    (M : Option ((ι → F) × A) → Matrix ((stageRemaining P k y → F) × H) _ ℂ)
    (z : Fin (Fintype.card (P.factorOfPrefix k y)) → F) (x : ι → F) (a : A) :
    stageAnswerRefinement P k y M (z, some (x, a)) =
      if z = coordinateRestrict (P.factorOfPrefix k y) x then M (some (x, a)) else 0 := rfl

theorem stageAnswerRefinementPOVM_mats (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F)
    (M : POVM (Option ((ι → F) × A)) ((stageRemaining P k y → F) × H)) (p) :
    ((stageAnswerRefinementPOVM P k y M).mats p).val =
      stageAnswerRefinement P k y (fun a => (M.mats a).val) p :=
  graphRefinementPOVM_mats _ _ _

theorem stageAnswerRefinementPOVM_recover (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F)
    (M : POVM (Option ((ι → F) × A)) ((stageRemaining P k y → F) × H)) :
    (stageAnswerRefinementPOVM P k y M).map Prod.snd = M :=
  graphRefinementPOVM_recover _ _

theorem stageAnswerRefinementPOVM_isPVM (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F)
    (M : POVM (Option ((ι → F) × A)) ((stageRemaining P k y → F) × H))
    (hM : IsPVM (fun a => (M.mats a).val)) :
    IsPVM (fun p => ((stageAnswerRefinementPOVM P k y M).mats p).val) :=
  graphRefinementPOVM_isPVM _ _ hM

/-- Both the Z and dual-X local commutator budgets pass to the actual stage
alphabet exactly, including the malformed outcome. -/
theorem stageAnswerRefinement_commutator (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ) (ξ : H × K → ℂ)
    (M : (y : ι → F) → Option ((ι → F) × A) →
      Matrix ((stageRemaining P k y → F) × H) _ ℂ)
    (w : (y : ι → F) → (Fin (Fintype.card (P.factorOfPrefix k y)) → F) →
      Matrix (Fin (Fintype.card (P.factorOfPrefix k y)) → F) _ ℂ)
    (L : (y : ι → F) → (Fin (Fintype.card (P.factorOfPrefix k y)) → F) →ₗ[F]
      (Fin (Fintype.card (P.factorOfPrefix k y)) → F)) :
    prefixStageCommutatorError P hP k ξ (fun y => stageAnswerRefinement P k y (M y)) w L =
      ∑ y, prefixWeight P k y * ∑ a, ∑ z,
        stateSqNorm (registerState (stageRemaining P k y → F) ξ)
          (M y a * registerReadout (stageSplit P hP k y) (w y) (L y) z -
            registerReadout (stageSplit P hP k y) (w y) (L y) z * M y a) := by
  rw [prefixStageCommutatorError_eq]
  simp only [ambientCommutatorError_eq, registerCommutatorError]
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  exact graphRefinement_commutator_sum _ _ _ _

/-- Forgetting the added coordinate recovers the exact old ambient family,
with no support premise and with every malformed-answer block retained. -/
theorem stageAnswerRefinement_reassemble (P : CL.CLFun F ι ℓ) (k : ℕ)
    (M : (y : ι → F) → Option ((ι → F) × A) →
      Matrix ((stageRemaining P k y → F) × H) _ ℂ) (a : Option ((ι → F) × A)) :
    fibSum (fun p : AdaptiveStageAnswer P k (Option ((ι → F) × A)) =>
      prefixResidualOp P k p.1 (stageAnswerRefinement P k p.1 (M p.1) p.2))
      (fun p => p.2.2) a = ∑ y, prefixResidualOp P k y (M y a) := by
  simp only [fibSum, Finset.sum_filter, Fintype.sum_sigma, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y _
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← prefixResidualOp_sum]
  congr 1
  exact graphRefinement_sum_coordinate _ _ _

end MIPRE.Introspection
end

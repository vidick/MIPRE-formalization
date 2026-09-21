/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AdaptiveResidual
import MIPRE.Foundations.Introspection.PrefixConditioning
import MIPRE.Foundations.Introspection.AmbientMixing

/-! # Mixing on the actual adaptive continuation

The prefix law, next linear map, and remaining coordinates are computed from
the CL presentation. Full-carrier errors of prefix-conditioned operators
give the weighted hypotheses of mixing exactly. The constructed residual
POVM acts on the complement of the next prefix, with the original ancilla.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Weyl Classical
open scoped Kronecker
set_option linter.unusedSectionVars false

variable {ι F H K A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype A] [DecidableEq A] {ℓ : ℕ}

/-- The unvisited coordinates at an actual claimed prefix. -/
abbrev stageRemaining (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F) : Finset ι :=
  (CLChecks.prefixRegister P k y)ᶜ

theorem stageFactor_subset_remaining (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ) (y : ι → F) :
    P.factorOfPrefix k y ⊆ stageRemaining P k y := by
  simpa only [stageRemaining, Finset.compl_eq_univ_sdiff] using
    CLChecks.stageFactor_subset_residual hP k y

/-- The output support of mixing is precisely the next unvisited register. -/
theorem stageRemaining_step (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F) :
    stageRemaining P k y \ P.factorOfPrefix k y = stageRemaining P (k + 1) y := by
  simpa only [stageRemaining, Finset.compl_eq_univ_sdiff] using
    CLChecks.residualRegister_step P univ k y

/-- Split the actual remaining register into its next factor and its continuation. -/
def stageSplit (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ) (k : ℕ) (y : ι → F) :
    (stageRemaining P k y → F) ≃ (Fin (Fintype.card (P.factorOfPrefix k y)) → F) ×
      ((↥(stageRemaining P k y \ P.factorOfPrefix k y)) → F) :=
  coordinateSplit _ _ (stageFactor_subset_remaining P hP k y)

/-- Full-carrier marginal error, retaining its actual adaptive prefix projector. -/
def prefixStageMarginalError (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (ξ : H × K → ℂ)
    (M : (y : ι → F) → (Fin (Fintype.card (P.factorOfPrefix k y)) → F) × A →
      Matrix ((stageRemaining P k y → F) × H) ((stageRemaining P k y → F) × H) ℂ) : ℝ :=
  ∑ y, ∑ z, stateSqNorm (registerState (ι → F) ξ)
    (prefixResidualOp P k y (∑ a, M y (z, a)) -
      prefixResidualOp P k y (registerReadout (stageSplit P hP k y)
        wZ (coordinateLinear (CLChecks.stageLinear P k y)) z))

/-- Full-carrier commutation error with the actual prefix left in place. -/
def prefixStageCommutatorError (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (ξ : H × K → ℂ)
    (M : (y : ι → F) → (Fin (Fintype.card (P.factorOfPrefix k y)) → F) × A →
      Matrix ((stageRemaining P k y → F) × H) ((stageRemaining P k y → F) × H) ℂ)
    (w : (y : ι → F) → (Fin (Fintype.card (P.factorOfPrefix k y)) → F) →
      Matrix (Fin (Fintype.card (P.factorOfPrefix k y)) → F)
        (Fin (Fintype.card (P.factorOfPrefix k y)) → F) ℂ)
    (L : (y : ι → F) → (Fin (Fintype.card (P.factorOfPrefix k y)) → F) →ₗ[F]
      (Fin (Fintype.card (P.factorOfPrefix k y)) → F)) : ℝ :=
  ∑ y, ∑ p, ∑ z, stateSqNorm (registerState (ι → F) ξ)
    (prefixResidualOp P k y (M y p) *
        prefixResidualOp P k y (registerReadout (stageSplit P hP k y) (w y) (L y) z) -
      prefixResidualOp P k y (registerReadout (stageSplit P hP k y) (w y) (L y) z) *
        prefixResidualOp P k y (M y p))

theorem prefixStageMarginalError_eq (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (ξ : H × K → ℂ)
    (M : (y : ι → F) → (Fin (Fintype.card (P.factorOfPrefix k y)) → F) × A →
      Matrix ((stageRemaining P k y → F) × H) _ ℂ) :
    prefixStageMarginalError P hP k ξ M = ∑ y, prefixWeight P k y *
      ambientMarginalError (P.factorOfPrefix k y) (stageRemaining P k y)
        (stageFactor_subset_remaining P hP k y) (CLChecks.stageLinear P k y) ξ (M y) := by
  simp only [prefixStageMarginalError, prefixResidual_distance P hP,
    ambientMarginalError_eq, registerMarginalError, stageSplit, Finset.mul_sum]

theorem prefixStageCommutatorError_eq (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (ξ : H × K → ℂ)
    (M : (y : ι → F) → (Fin (Fintype.card (P.factorOfPrefix k y)) → F) × A →
      Matrix ((stageRemaining P k y → F) × H) _ ℂ)
    (w : (y : ι → F) → (Fin (Fintype.card (P.factorOfPrefix k y)) → F) →
      Matrix (Fin (Fintype.card (P.factorOfPrefix k y)) → F) _ ℂ)
    (L : (y : ι → F) → (Fin (Fintype.card (P.factorOfPrefix k y)) → F) →ₗ[F]
      (Fin (Fintype.card (P.factorOfPrefix k y)) → F)) :
    prefixStageCommutatorError P hP k ξ M w L = ∑ y, prefixWeight P k y *
      ambientCommutatorError (P.factorOfPrefix k y) (stageRemaining P k y)
        (stageFactor_subset_remaining P hP k y) ξ (M y) (w y) (L y) := by
  simp only [prefixStageCommutatorError, prefixResidual_commutator P hP,
    ambientCommutatorError_eq, registerCommutatorError, stageSplit, Finset.mul_sum]

/-- **One adaptive extraction step.** The three errors are measured on the
original EPR-plus-auxiliary state. The theorem constructs the next residual
POVMs on the actual next unvisited coordinates; no prefix distribution,
support identification, or product-form conclusion is an input. -/
theorem exists_adaptive_prefix_mixing (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (ξ : H × K → ℂ) (hξ : ‖evec ξ‖ = 1)
    (M : (y : ι → F) → POVM ((Fin (Fintype.card (P.factorOfPrefix k y)) → F) × A)
      ((stageRemaining P k y → F) × H))
    (hM : ∀ y, IsPVM (fun p => ((M y).mats p).val))
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hmarg : prefixStageMarginalError P hP k ξ (fun y p => ((M y).mats p).val) ≤ ε)
    (hZ : prefixStageCommutatorError P hP k ξ (fun y p => ((M y).mats p).val)
      (fun _ => wZ) (fun _ => LinearMap.id) ≤ ε)
    (hX : prefixStageCommutatorError P hP k ξ (fun y p => ((M y).mats p).val)
      (fun _ => wX) (fun y => CL.lperp (coordinateLinear (CLChecks.stageLinear P k y))) ≤ ε) :
    ∃ Q : (y : ι → F) → (Fin (Fintype.card (P.factorOfPrefix k y)) → F) →
      POVM A ((↥(stageRemaining P k y \ P.factorOfPrefix k y) → F) × H),
      (∑ y, ∑ p : (Fin (Fintype.card (P.factorOfPrefix k y)) → F) × A,
        stateSqNorm (registerState (ι → F) ξ)
          (prefixResidualOp P k y ((M y).mats p).val -
            prefixResidualOp P k y (registerOp (registerParty (stageSplit P hP k y) H)
              (synOf wZ (coordinateLinear (CLChecks.stageLinear P k y)) p.1 ⊗ₖ
                ((Q y p.1).mats p.2).val)))) ≤ 56 * Real.sqrt ε := by
  rw [prefixStageMarginalError_eq] at hmarg
  rw [prefixStageCommutatorError_eq] at hZ hX
  obtain ⟨Q, hQ⟩ := exists_ambient_pauli_mixing (prefixWeight P k)
    (prefixWeight_nonneg P k) (sum_prefixWeight P k)
    (P.factorOfPrefix k) (stageRemaining P k) (stageFactor_subset_remaining P hP k)
    (CLChecks.stageLinear P k) ξ hξ M hM hε0 hε1 hmarg hZ hX
  refine ⟨Q, ?_⟩
  simpa only [prefixResidual_distance P hP, ← Finset.mul_sum, ambientOperator,
    ← registerExtend_sub, stateSqNorm_registerExtend, stageSplit] using hQ

end MIPRE.Introspection

end

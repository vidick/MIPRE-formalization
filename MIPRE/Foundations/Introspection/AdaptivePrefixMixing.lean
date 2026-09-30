/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.AdaptiveResidual
public import MIPRE.Foundations.Introspection.PrefixConditioning
public import MIPRE.Foundations.Introspection.AmbientMixing

@[expose] public section

/-! # Mixing on the actual adaptive continuation

The prefix law, next linear map, and remaining coordinates are computed from
the CL presentation. Full-carrier errors of prefix-conditioned operators
give the weighted hypotheses of mixing exactly. The constructed residual
POVM acts on the complement of the next prefix, with the original ancilla.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the full-carrier errors are
measured in the register model `Ξ.reg (ι → F)`, and a residual operator at the prefix `y` is a
block matrix over the unvisited register `stageRemaining P k y → F` with entries in the first
player's algebra, whose error is measured in the residual model
`Ξ.reg (stageRemaining P k y → F)`. Ambient mixing is applied to the one model `Ξ` with this
prefix-dependent family of registers, weighted by the prefix law. The constructed POVMs are block
matrices over the next unvisited register, entering along the split as
`regSplitHom (stageSplit P hP k y) (smulKron _ _)`.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Weyl Classical
set_option linter.unusedSectionVars false

variable {ι F A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype A] [DecidableEq A] {ℓ : ℕ}
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [StarModule ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [StarModule ℂ ℬ]

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
    (k : ℕ) (Ξ : BipartiteModel 𝒞 𝒜 ℬ)
    (M : (y : ι → F) → (Fin (Fintype.card (P.factorOfPrefix k y)) → F) × A →
      Matrix (stageRemaining P k y → F) (stageRemaining P k y → F) 𝒜) : ℝ :=
  ∑ y, ∑ z, (Ξ.reg (ι → F)).stateSqNorm
    (prefixResidualOp P k y (∑ a, M y (z, a)) -
      prefixResidualOp P k y (registerReadout (stageSplit P hP k y)
        wZ (coordinateLinear (CLChecks.stageLinear P k y)) z))

/-- Full-carrier commutation error with the actual prefix left in place. -/
def prefixStageCommutatorError (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (Ξ : BipartiteModel 𝒞 𝒜 ℬ)
    (M : (y : ι → F) → (Fin (Fintype.card (P.factorOfPrefix k y)) → F) × A →
      Matrix (stageRemaining P k y → F) (stageRemaining P k y → F) 𝒜)
    (w : (y : ι → F) → (Fin (Fintype.card (P.factorOfPrefix k y)) → F) →
      Matrix (Fin (Fintype.card (P.factorOfPrefix k y)) → F)
        (Fin (Fintype.card (P.factorOfPrefix k y)) → F) ℂ)
    (L : (y : ι → F) → (Fin (Fintype.card (P.factorOfPrefix k y)) → F) →ₗ[F]
      (Fin (Fintype.card (P.factorOfPrefix k y)) → F)) : ℝ :=
  ∑ y, ∑ p, ∑ z, (Ξ.reg (ι → F)).stateSqNorm
    (prefixResidualOp P k y (M y p) *
        prefixResidualOp P k y (registerReadout (stageSplit P hP k y) (w y) (L y) z) -
      prefixResidualOp P k y (registerReadout (stageSplit P hP k y) (w y) (L y) z) *
        prefixResidualOp P k y (M y p))

theorem prefixStageMarginalError_eq (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (Ξ : BipartiteModel 𝒞 𝒜 ℬ)
    (M : (y : ι → F) → (Fin (Fintype.card (P.factorOfPrefix k y)) → F) × A →
      Matrix (stageRemaining P k y → F) _ 𝒜) :
    prefixStageMarginalError P hP k Ξ M = ∑ y, prefixWeight P k y *
      ambientMarginalError (P.factorOfPrefix k y) (stageRemaining P k y)
        (stageFactor_subset_remaining P hP k y) (CLChecks.stageLinear P k y) Ξ (M y) := by
  simp only [prefixStageMarginalError, prefixResidual_distance Ξ P hP,
    ambientMarginalError_eq, registerMarginalError, stageSplit, Finset.mul_sum]

theorem prefixStageCommutatorError_eq (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (Ξ : BipartiteModel 𝒞 𝒜 ℬ)
    (M : (y : ι → F) → (Fin (Fintype.card (P.factorOfPrefix k y)) → F) × A →
      Matrix (stageRemaining P k y → F) _ 𝒜)
    (w : (y : ι → F) → (Fin (Fintype.card (P.factorOfPrefix k y)) → F) →
      Matrix (Fin (Fintype.card (P.factorOfPrefix k y)) → F) _ ℂ)
    (L : (y : ι → F) → (Fin (Fintype.card (P.factorOfPrefix k y)) → F) →ₗ[F]
      (Fin (Fintype.card (P.factorOfPrefix k y)) → F)) :
    prefixStageCommutatorError P hP k Ξ M w L = ∑ y, prefixWeight P k y *
      ambientCommutatorError (P.factorOfPrefix k y) (stageRemaining P k y)
        (stageFactor_subset_remaining P hP k y) Ξ (M y) (w y) (L y) := by
  simp only [prefixStageCommutatorError, prefixResidual_commutator Ξ P hP,
    ambientCommutatorError_eq, registerCommutatorError, stageSplit, Finset.mul_sum]

/-- **One adaptive extraction step.** The three errors are measured on the
original EPR-plus-auxiliary state. The theorem constructs the next residual
POVMs on the actual next unvisited coordinates; no prefix distribution,
support identification, or product-form conclusion is an input. -/
theorem exists_adaptive_prefix_mixing [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarProper 𝒜]
    (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (Ξ : BipartiteModel 𝒞 𝒜 ℬ) (hΞ : ‖Ξ.ψ‖ = 1)
    (M : (y : ι → F) → POVMIn ((Fin (Fintype.card (P.factorOfPrefix k y)) → F) × A)
      (Matrix (stageRemaining P k y → F) (stageRemaining P k y → F) 𝒜))
    (hM : ∀ y, IsPVMIn (M y).op)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hmarg : prefixStageMarginalError P hP k Ξ (fun y => (M y).op) ≤ ε)
    (hZ : prefixStageCommutatorError P hP k Ξ (fun y => (M y).op)
      (fun _ => wZ) (fun _ => LinearMap.id) ≤ ε)
    (hX : prefixStageCommutatorError P hP k Ξ (fun y => (M y).op)
      (fun _ => wX) (fun y => CL.lperp (coordinateLinear (CLChecks.stageLinear P k y))) ≤ ε) :
    ∃ Q : (y : ι → F) → (Fin (Fintype.card (P.factorOfPrefix k y)) → F) →
      POVMIn A (Matrix (↥(stageRemaining P k y \ P.factorOfPrefix k y) → F)
        (↥(stageRemaining P k y \ P.factorOfPrefix k y) → F) 𝒜),
      (∑ y, ∑ p : (Fin (Fintype.card (P.factorOfPrefix k y)) → F) × A,
        (Ξ.reg (ι → F)).stateSqNorm
          (prefixResidualOp P k y ((M y).op p) -
            prefixResidualOp P k y (regSplitHom (stageSplit P hP k y)
              (smulKron ((Q y p.1).op p.2)
                (synOf wZ (coordinateLinear (CLChecks.stageLinear P k y)) p.1))))) ≤
        56 * Real.sqrt ε := by
  rw [prefixStageMarginalError_eq] at hmarg
  rw [prefixStageCommutatorError_eq] at hZ hX
  obtain ⟨Q, hQ⟩ := exists_ambient_pauli_mixing (prefixWeight P k)
    (prefixWeight_nonneg P k) (sum_prefixWeight P k)
    (P.factorOfPrefix k) (stageRemaining P k) (stageFactor_subset_remaining P hP k)
    (CLChecks.stageLinear P k) Ξ hΞ M hM hε0 hε1 hmarg hZ hX
  refine ⟨Q, ?_⟩
  simpa only [prefixResidual_distance Ξ P hP, ← Finset.mul_sum, ambientOperator,
    ← map_sub, stateSqNorm_ambientOperator, stageSplit] using hQ

end MIPRE.Introspection

end

end

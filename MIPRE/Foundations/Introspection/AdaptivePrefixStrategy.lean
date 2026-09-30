/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.AdaptivePrefixReplacement

@[expose] public section

/-! # A legal strategy after one adaptive product-form step

Mixing, one fixed residual ancilla, orthogonal prefix reassembly, and actual
question replacement are composed here. The output is a concrete
`TensorProductStrategy`; its state preserves the original EPR register and
all questions except the selected one retain their old measurements.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the output is a projective
strategy of the register model of the auxiliary model extended by the ancilla,
`(Ξ.expandA t₀).reg (ι → F)` (`registeredReplacementStrategy`).
-/

noncomputable section
namespace MIPRE.Introspection

open Finset Matrix Weyl Classical
set_option linter.unusedSectionVars false

variable {ι F A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype A] [DecidableEq A] {ℓ : ℕ}
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [StarModule ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜]
  [StarOrderedRing 𝒜] [StarProper 𝒜]
variable {T : Type*} [Fintype T] [DecidableEq T]

/-- Returning from the extension ordering reveals exactly the prefix and
new Z-factor measurement constructed on the new auxiliary space. -/
theorem adaptiveReplacementPOVM_reindex (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (D : AdaptiveDilationFamily P k 𝒜 T A) (hD : ∀ y z, IsPVMIn (D y z)) :
    (adaptiveReplacementPOVM P hP k D hD).pushforward BipartiteModel.layerSwap
        BipartiteModel.layerSwap_one =
      (adaptiveReplacementJointOp_isPVM P hP k D hD).toPOVMIn :=
  POVMIn.ext' fun p => layerSwap_layerSwap _

variable [PartialOrder ℬ] [StarOrderedRing ℬ] [StarModule ℂ ℬ] [StarProper ℬ]
  (Ξ : BipartiteModel 𝒞 𝒜 ℬ)
variable {X Y Ans B : Type*} [Fintype X] [DecidableEq X] [Fintype Y]
  [Fintype Ans] [DecidableEq Ans] [Fintype B] [DecidableEq B]

/-- The actual next strategy, including all unchanged questions. -/
def adaptiveReplacementStrategy (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ) (k : ℕ)
    (G : Game X Y Ans B) (hΞ : ‖Ξ.ψ‖ = 1) (t₀ : T)
    (MA : X → POVMIn Ans (Matrix (ι → F) (ι → F) 𝒜))
    (MB : Y → POVMIn B (Matrix (ι → F) (ι → F) ℬ)) (q : X)
    (f : AdaptiveStageAnswer P k A → Ans)
    (hMA : ∀ x, IsPVMIn (MA x).op) (hMB : ∀ y, IsPVMIn (MB y).op)
    (D : AdaptiveDilationFamily P k 𝒜 T A) (hD : ∀ y z, IsPVMIn (D y z)) :
    ((Ξ.expandA t₀).reg (ι → F)).ProjStrat G :=
  registeredReplacementStrategy Ξ G hΞ t₀ MA MB q
    ((adaptiveReplacementPOVM P hP k D hD).map f) hMA hMB
    (POVMIn.isPVMIn_map (adaptiveReplacementPOVM_isPVM P hP k D hD) f)

/-- **One complete adaptive replacement step.** The hypotheses are the three
full-carrier mixing errors and the old selected measurement's explicit
prefix form. The residual projectors and resulting legal strategy are
constructed, with a dimension-independent game-value bound. -/
theorem exists_adaptive_replacement_strategy (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ)
    (G : Game X Y Ans B) (hΞ : ‖Ξ.ψ‖ = 1) (a₀ : A)
    (MA : X → POVMIn Ans (Matrix (ι → F) (ι → F) 𝒜))
    (MB : Y → POVMIn B (Matrix (ι → F) (ι → F) ℬ)) (q : X)
    (M : (y : ι → F) → POVMIn ((Fin (Fintype.card (P.factorOfPrefix k y)) → F) × A)
      (Matrix (stageRemaining P k y → F) (stageRemaining P k y → F) 𝒜))
    (hM : ∀ y, IsPVMIn (M y).op)
    (f : AdaptiveStageAnswer P k A → Ans)
    (hMA : ∀ x, IsPVMIn (MA x).op) (hMB : ∀ y, IsPVMIn (MB y).op)
    (hselected : MA q = (adaptiveOldJointPOVM P hP k M).map f)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hmarg : prefixStageMarginalError P hP k Ξ (fun y => (M y).op) ≤ ε)
    (hZ : prefixStageCommutatorError P hP k Ξ (fun y => (M y).op)
      (fun _ => wZ) (fun _ => LinearMap.id) ≤ ε)
    (hX : prefixStageCommutatorError P hP k Ξ (fun y => (M y).op)
      (fun _ => wX) (fun y => CL.lperp (coordinateLinear (CLChecks.stageLinear P k y))) ≤ ε) :
    ∃ (K : ℕ) (D : AdaptiveDilationFamily P k 𝒜 (DilationAncilla A K) A)
      (hD : ∀ y z, IsPVMIn (D y z)),
      (∑ p, ((Ξ.reg (ι → F)).expandA (Sum.inl (a₀, 0) : DilationAncilla A K)).stateSqNorm
        ((diagonal fun _ => (adaptiveOldJointPOVM P hP k M).op p) -
          (adaptiveReplacementPOVM P hP k D hD).op p)) ≤
        2*Real.sqrt (56*Real.sqrt ε) ∧
      |(Ξ.reg (ι → F)).povmValue G MA MB -
        (adaptiveReplacementStrategy Ξ P hP k G hΞ (Sum.inl (a₀, 0)) MA MB q f hMA hMB
          D hD).value| ≤
        2*Real.sqrt (2*Real.sqrt (56*Real.sqrt ε)) := by
  obtain ⟨K, D, hD, hd⟩ := exists_adaptive_prefix_dilation Ξ P hP k hΞ a₀ M hM hε0 hε1
    hmarg hZ hX
  have hglobal := adaptiveReplacement_distance Ξ P hP k (Sum.inl (a₀, 0)) M D hD hd
  refine ⟨K, D, hD, hglobal, ?_⟩
  exact registeredReplacementStrategy_value_loss Ξ G hΞ (Sum.inl (a₀, 0)) MA MB q
    (adaptiveOldJointPOVM P hP k M) (adaptiveReplacementPOVM P hP k D hD) f hMA hMB
    hselected (adaptiveOldJointPOVM_isPVM P hP k M hM)
    (adaptiveReplacementPOVM_isPVM P hP k D hD) hglobal

end MIPRE.Introspection
end

end

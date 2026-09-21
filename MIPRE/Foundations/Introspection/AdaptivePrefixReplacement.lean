/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AdaptivePrefixMixing
import MIPRE.Foundations.Introspection.AdaptivePrefixMeasurement
import MIPRE.Foundations.Introspection.AdaptivePrefixExtension
import MIPRE.Foundations.Introspection.AdaptiveDilationTransport

/-! # Actual adaptive residual projectors after mixing

Every conditioned prefix uses its actual remaining coordinates. Naimark
produces projective residual measurements with the single ancilla alphabet
`A` and fixed state `a₀`. The original prefix and the next Z readout remain
explicit tensor factors, and the error is averaged with the actual CL law.
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

/-- Joint outcomes retain the actual prefix and the next factor's outcome. -/
abbrev AdaptiveStageAnswer (P : CL.CLFun F ι ℓ) (k : ℕ) (A : Type*) :=
  (y : ι → F) × ((Fin (Fintype.card (P.factorOfPrefix k y)) → F) × A)

abbrev AdaptiveDilationFamily (P : CL.CLFun F ι ℓ) (k : ℕ) (H A : Type*) :=
  (y : ι → F) → (Fin (Fintype.card (P.factorOfPrefix k y)) → F) → A →
    Matrix (((↥(stageRemaining P k y \ P.factorOfPrefix k y) → F) × H) × A)
      (((↥(stageRemaining P k y \ P.factorOfPrefix k y) → F) × H) × A) ℂ

/-- The actual old joint PVM, with dependent local outcome spaces. -/
def adaptiveOldJointPOVM (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ) (k : ℕ)
    (M : (y : ι → F) → POVM ((Fin (Fintype.card (P.factorOfPrefix k y)) → F) × A)
      ((stageRemaining P k y → F) × H))
    (hM : ∀ y, IsPVM (fun p => ((M y).mats p).val)) :
    POVM (AdaptiveStageAnswer P k A) ((ι → F) × H) :=
  (prefixResidual_isPVM P hP k (fun y p => ((M y).mats p).val) hM).toPOVM

theorem adaptiveOldJointPOVM_isPVM (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ) (k : ℕ)
    (M : (y : ι → F) → POVM ((Fin (Fintype.card (P.factorOfPrefix k y)) → F) × A)
      ((stageRemaining P k y → F) × H))
    (hM : ∀ y, IsPVM (fun p => ((M y).mats p).val)) :
    IsPVM (fun p => ((adaptiveOldJointPOVM P hP k M hM).mats p).val) :=
  prefixResidual_isPVM P hP k (fun y p => ((M y).mats p).val) hM

/-- The next joint PVM on one ambient register, retaining both the old
prefix and the new Z factor explicitly. -/
def adaptiveReplacementJointOp (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (D : AdaptiveDilationFamily P k H A) (p : AdaptiveStageAnswer P k A) :
    Matrix ((ι → F) × (H × A)) ((ι → F) × (H × A)) ℂ :=
  prefixResidualOp P k p.1 (reassociatedConditionalDilation (stageSplit P hP k p.1)
    (synOf wZ (coordinateLinear (CLChecks.stageLinear P k p.1))) (D p.1) p.2)

set_option maxHeartbeats 800000 in
theorem adaptiveReplacementJointOp_isPVM (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (D : AdaptiveDilationFamily P k H A) (hD : ∀ y z, IsPVM (D y z)) :
    IsPVM (adaptiveReplacementJointOp P hP k D) :=
  prefixResidual_isPVM P hP k
    (fun y => reassociatedConditionalDilation (stageSplit P hP k y)
      (synOf wZ (coordinateLinear (CLChecks.stageLinear P k y))) (D y))
    (fun y => reassociatedConditionalDilation_isPVM (stageSplit P hP k y)
      (synOf wZ (coordinateLinear (CLChecks.stageLinear P k y)))
      (isPVM_synOf isWeylFamily_wZ _) (D y) (hD y))

/-- The same actual joint PVM, in the extension ordering used by the
replacement-strategy constructor. -/
def adaptiveReplacementPOVM (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (D : AdaptiveDilationFamily P k H A) (hD : ∀ y z, IsPVM (D y z)) :
    POVM (AdaptiveStageAnswer P k A) (((ι → F) × H) × A) :=
  (registerOp_isPVM (Equiv.prodAssoc (ι → F) H A)
    (adaptiveReplacementJointOp_isPVM P hP k D hD)).toPOVM

theorem adaptiveReplacementPOVM_isPVM (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (D : AdaptiveDilationFamily P k H A) (hD : ∀ y z, IsPVM (D y z)) :
    IsPVM (fun p => ((adaptiveReplacementPOVM P hP k D hD).mats p).val) :=
  registerOp_isPVM (Equiv.prodAssoc (ι → F) H A)
    (adaptiveReplacementJointOp_isPVM P hP k D hD)

/-- The local weighted dilation error is the squared error of the actual
global replacement PVM. No number-of-prefixes loss is introduced. -/
theorem adaptiveReplacement_distance (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (ξ : H × K → ℂ) (a₀ : A)
    (M : (y : ι → F) → POVM ((Fin (Fintype.card (P.factorOfPrefix k y)) → F) × A)
      ((stageRemaining P k y → F) × H))
    (hM : ∀ y, IsPVM (fun p => ((M y).mats p).val))
    (D : AdaptiveDilationFamily P k H A) (hD : ∀ y z, IsPVM (D y z)) {δ : ℝ}
    (hd : (∑ y, prefixWeight P k y * ∑ p,
      stateSqNorm (extVecA (registerState (stageRemaining P k y → F) ξ) a₀)
        (aOp ((M y).mats p).val - transportedConditionalDilation (stageSplit P hP k y)
          (synOf wZ (coordinateLinear (CLChecks.stageLinear P k y))) (D y) p)) ≤ δ) :
    (∑ p, stateSqNorm (extVecA (registerState (ι → F) ξ) a₀)
      (aOp ((adaptiveOldJointPOVM P hP k M hM).mats p).val -
        ((adaptiveReplacementPOVM P hP k D hD).mats p).val)) ≤ δ := by
  change (∑ p : AdaptiveStageAnswer P k A,
    stateSqNorm (extVecA (registerState (ι → F) ξ) a₀)
      (aOp (prefixResidualOp P k p.1 ((M p.1).mats p.2).val) -
        registerOp (Equiv.prodAssoc (ι → F) H A) (adaptiveReplacementJointOp P hP k D p))) ≤ δ
  have he (y : ι → F) (p : (Fin (Fintype.card (P.factorOfPrefix k y)) → F) × A) :
      stateSqNorm (extVecA (registerState (ι → F) ξ) a₀)
        (aOp (prefixResidualOp P k y ((M y).mats p).val) -
          registerOp (Equiv.prodAssoc (ι → F) H A)
            (adaptiveReplacementJointOp P hP k D ⟨y,p⟩)) =
      prefixWeight P k y * stateSqNorm
        (extVecA (registerState (stageRemaining P k y → F) ξ) a₀)
        (aOp ((M y).mats p).val - transportedConditionalDilation (stageSplit P hP k y)
          (synOf wZ (coordinateLinear (CLChecks.stageLinear P k y))) (D y) p) := by
    rw [← stateSqNorm_reassociated_extVecA ξ a₀, registerOp_sub, registerOp_inv,
      ← prefixResidualOp_extend P k y ((M y).mats p).val]
    change stateSqNorm (registerState (ι → F) (extVecA ξ a₀))
      (prefixResidualOp P k y _ - prefixResidualOp P k y _) = _
    rw [prefixResidual_distance P hP, reassociatedConditionalDilation,
      ← registerOp_sub, stateSqNorm_reassociated_extVecA]
  rw [Fintype.sum_sigma]
  simp_rw [he]
  simpa only [Finset.mul_sum] using hd

/-- The one shared answer ancilla suffices although the remaining coordinate
space and the next factor dimension depend on the prefix. -/
theorem exists_adaptive_prefix_dilation (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (ξ : H × K → ℂ) (hξ : ‖evec ξ‖ = 1) (a₀ : A)
    (M : (y : ι → F) → POVM ((Fin (Fintype.card (P.factorOfPrefix k y)) → F) × A)
      ((stageRemaining P k y → F) × H))
    (hM : ∀ y, IsPVM (fun p => ((M y).mats p).val))
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hmarg : prefixStageMarginalError P hP k ξ (fun y p => ((M y).mats p).val) ≤ ε)
    (hZ : prefixStageCommutatorError P hP k ξ (fun y p => ((M y).mats p).val)
      (fun _ => wZ) (fun _ => LinearMap.id) ≤ ε)
    (hX : prefixStageCommutatorError P hP k ξ (fun y p => ((M y).mats p).val)
      (fun _ => wX) (fun y => CL.lperp (coordinateLinear (CLChecks.stageLinear P k y))) ≤ ε) :
    ∃ D : (y : ι → F) → (Fin (Fintype.card (P.factorOfPrefix k y)) → F) →
      A → Matrix (((↥(stageRemaining P k y \ P.factorOfPrefix k y) → F) × H) × A)
        (((↥(stageRemaining P k y \ P.factorOfPrefix k y) → F) × H) × A) ℂ,
      (∀ y z, IsPVM (D y z)) ∧
      (∑ y, prefixWeight P k y * ∑ p,
        stateSqNorm (extVecA (registerState (stageRemaining P k y → F) ξ) a₀)
          (aOp ((M y).mats p).val - transportedConditionalDilation (stageSplit P hP k y)
            (synOf wZ (coordinateLinear (CLChecks.stageLinear P k y))) (D y) p)) ≤
        2*Real.sqrt (56*Real.sqrt ε) := by
  obtain ⟨Q, hQ⟩ := exists_adaptive_prefix_mixing P hP k ξ hξ M hM hε0 hε1 hmarg hZ hX
  have hlocal y : ∃ D : (Fin (Fintype.card (P.factorOfPrefix k y)) → F) → A →
      Matrix (((↥(stageRemaining P k y \ P.factorOfPrefix k y) → F) × H) × A)
        (((↥(stageRemaining P k y \ P.factorOfPrefix k y) → F) × H) × A) ℂ,
      (∀ z, IsPVM (D z)) ∧
      (∀ z a, (ancillaEmbed ((↥(stageRemaining P k y \ P.factorOfPrefix k y) → F) × H) a₀)ᴴ *
        (D z a * ancillaEmbed ((↥(stageRemaining P k y \ P.factorOfPrefix k y) → F) × H) a₀) =
          ((Q y z).mats a).val) := by
    obtain ⟨D, hsa, hid, hsum, hk⟩ := exists_projective_dilation a₀
      (E := fun z a => ((Q y z).mats a).val)
      (fun z a => (Q y z).posSemidef a) (fun z => (Q y z).sum_val)
    refine ⟨D, fun z => ⟨?_, hid z, hsum z⟩, hk⟩
    intro a
    rw [← Matrix.star_eq_conjTranspose]
    exact hsa z a
  choose D hD hk using hlocal
  refine ⟨D, hD, ?_⟩
  let err y := ∑ p, stateSqNorm (registerState (stageRemaining P k y → F) ξ)
    (((M y).mats p).val - registerOp (registerParty (stageSplit P hP k y) H)
      (synOf wZ (coordinateLinear (CLChecks.stageLinear P k y)) p.1 ⊗ₖ
        ((Q y p.1).mats p.2).val))
  have herr y : 0 ≤ err y := Finset.sum_nonneg fun _ _ => stateSqNorm_nonneg _ _
  have havg : ∑ y, prefixWeight P k y * err y ≤ 56*Real.sqrt ε := by
    simpa only [prefixResidual_distance P hP, Finset.mul_sum, err] using hQ
  have hpoint y := dilated_pvm_distance (registerState (stageRemaining P k y → F) ξ)
    (registerState_norm ξ hξ) a₀ (fun p => ((M y).mats p).val)
    (fun p => registerOp (registerParty (stageSplit P hP k y) H)
      (synOf wZ (coordinateLinear (CLChecks.stageLinear P k y)) p.1 ⊗ₖ
        ((Q y p.1).mats p.2).val))
    (transportedConditionalDilation (stageSplit P hP k y)
      (synOf wZ (coordinateLinear (CLChecks.stageLinear P k y))) (D y))
    (hM y) (transportedConditionalDilation_isPVM _ _ (isPVM_synOf isWeylFamily_wZ _) _ (hD y))
    (transportedConditionalDilation_compress _ a₀ _ _ (Q y) (hk y)) (δ := err y) le_rfl
  calc
    _ ≤ ∑ y, prefixWeight P k y * (2*Real.sqrt (err y)) :=
      Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hpoint y) (prefixWeight_nonneg P k y)
    _ = 2*∑ y, prefixWeight P k y * Real.sqrt (err y) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ ≤ 2*Real.sqrt (56*Real.sqrt ε) := mul_le_mul_of_nonneg_left
      ((sum_weighted_sqrt_le (prefixWeight P k) err (prefixWeight_nonneg P k)
        (sum_prefixWeight P k) herr).trans (Real.sqrt_le_sqrt havg)) (by norm_num)

end MIPRE.Introspection
end

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.Introspection.PauliRestriction
import MIPRE.Background.Introspection.BinaryMeasurements
import MIPRE.Foundations.Introspection.ValidPauliSoundness

/-! # Source-game soundness from the restricted QLD strategy

The extraction inputs refer to the actual restricted QLD strategy, with scalar
completion of malformed answers. The full-register answers retain their original
operators, so the checked finite-game soundness theorem applies without a
malformed-mass hypothesis. Extraction existence remains an external input.

The isometry codomains and ideal projectors here use binary coordinates under
`Weyl.binEquiv b`. Thus the witness interface explicitly records the coordinate
convention expected after the field-to-binary Pauli equivalence.
-/

noncomputable section
namespace MIPRE.Introspection.RestrictedSoundness
open Matrix Finset Classical BinaryComplete
set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] {m t d ℓ : ℕ} [NeZero m]
  {A H K : Type} [Fintype A] [Nonempty A]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

/-- Interpret a full binary register answer as the genuine QLD Pauli answer. -/
def validAnswer (b : Module.Basis (Fin t) (ZMod 2) F) (x : Seed m t) : QLD.Answer F m d :=
  .pauliAns ((Weyl.binEquiv b).symm x)

theorem project_validAnswer (b : Module.Basis (Fin t) (ZMod 2) F) (x : Seed m t) :
    BinaryComplete.project b (validAnswer (d := d) b x) = x :=
  (Weyl.binEquiv b).apply_symm_apply x

/-- Local isometries and the three quantitative extraction estimates for an
actual QLD strategy, with the extracted register in binary coordinates. -/
structure Extraction (hm : m ∣ Fintype.card F)
    (b : Module.Basis (Fin t) (ZMod 2) F)
    (R : TensorProductStrategy (QLD.qldGame (d := d) hm)) (δ : ℝ) where
  dA : ℕ
  dB : ℕ
  ξ : Fin dA × Fin dB → ℂ
  ξ_unit : star ξ ⬝ᵥ ξ = 1
  VA : Matrix (Seed m t × Fin dA) (Fin R.dA) ℂ
  VB : Matrix (Seed m t × Fin dB) (Fin R.dB) ℂ
  VA_isometry : VAᴴ * VA = 1
  VB_isometry : VBᴴ * VB = 1
  state_error : ‖evec (isometricState VA VB R.ψ - registerState (Seed m t) ξ)‖ ≤ δ
  X_error : ∑ x : Seed m t, snorm (registerState (Seed m t) ξ) (aOp
    (isometricImage VA (R.PA.M (.pauli .X) (validAnswer b x)) -
      (aOp (Honest.pauliXReadout (some x)) : Matrix (Seed m t × Fin dA) _ ℂ))) ^ 2 ≤ δ
  Z_error : ∑ z : Seed m t, snorm (registerState (Seed m t) ξ) (bOp
    (isometricImage VB (R.PB.M (.pauli .Z) (validAnswer b z)) -
      (aOp (readout (some : Seed m t → Option (Seed m t)) (some z)) :
        Matrix (Seed m t × Fin dB) _ ℂ))) ^ 2 ≤ δ

variable (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
  (L : Bool → CL.CLFun (ZMod 2) (Coord m t) ℓ)
  (D : Seed m t → Seed m t → A → A → Bool)
  (S : TensorProductStrategy
    (PauliRestriction.fullGame hm b L (BinaryComplete.project (d := d) b) D))

/-- The extraction theorem is applied to this precise QLD strategy. -/
abbrev restriction := PauliRestriction.strategy hm b L (BinaryComplete.project b) D S
  (.val 0) (.val 0)

set_option backward.isDefEq.respectTransparency false in
/-- Concrete valid-answer extraction estimates imply source-game soundness.
The common error is the maximum of full-game failure and extraction error. -/
theorem quantumValue_ge_of_extraction
    (hL : ∀ w, (L w).ExactlyOn univ)
    (ξ : H × K → ℂ) (hξ : star ξ ⬝ᵥ ξ = 1)
    (VA : Matrix (Seed m t × H) (Fin S.dA) ℂ)
    (VB : Matrix (Seed m t × K) (Fin S.dB) ℂ)
    (hVA : VAᴴ * VA = 1) (hVB : VBᴴ * VB = 1)
    {ε δ : ℝ} (hδ : 0 ≤ δ) (hfail : 1 - S.value ≤ ε)
    (hstate : ‖evec (isometricState VA VB (restriction hm b L D S).ψ -
      registerState (Seed m t) ξ)‖ ≤ δ)
    (hX : ∑ x : Seed m t, snorm (registerState (Seed m t) ξ) (aOp
      (isometricImage VA ((restriction hm b L D S).PA.M (.pauli .X) (validAnswer b x)) -
        (aOp (Honest.pauliXReadout (some x)) : Matrix (Seed m t × H) _ ℂ))) ^ 2 ≤ δ)
    (hZ : ∑ z : Seed m t, snorm (registerState (Seed m t) ξ) (bOp
      (isometricImage VB ((restriction hm b L D S).PB.M (.pauli .Z) (validAnswer b z)) -
        (aOp (readout (some : Seed m t → Option (Seed m t)) (some z)) :
          Matrix (Seed m t × K) _ ℂ))) ^ 2 ≤ δ) :
    1 - validSoundnessCoefficient ℓ
      (TypeGraph.edges QLD.adj (.pauli .X) (.pauli .Z) ℓ).card *
      iteratedRoot (6 * ℓ + 2) (max ε δ) ≤ quantumValue (Honest.sourceGame L D) := by
  apply TypedEstimates.quantumValue_ge_of_valid_isometric_images
    QLD.adj (.pauli .X) (.pauli .Z) (QLD.PauliCL.binaryPresentation hm b) L hL
    (BinaryComplete.project b) (validAnswer b) (project_validAnswer b)
    D (PauliRestriction.pauliCheck hm b) (Honest.sourceGame L D)
    (by
      intro x y
      change SampledGame.dist _ _ x y = _
      rw [SampledGame.dist_eq_card]
      unfold CL.clDist
      congr 2
      apply congrArg Finset.card
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]) rfl ξ hξ S.ψ
    (norm_evec_eq_one_of_unit S.ψ_unit)
    VA VB hVA hVB S.PA.toPOVM S.PB.toPOVM
    (fun q => ⟨S.PA.selfAdjoint q, S.PA.projective q, S.PA.normalized q⟩)
    (fun q => ⟨S.PB.selfAdjoint q, S.PB.projective q, S.PB.normalized q⟩)
    0 0 (QLD.PauliCL.binaryPresentation_pauli_eval hm b .X)
    (QLD.PauliCL.binaryPresentation_pauli_eval hm b .Z)
    (hδ.trans (le_max_right ε δ)) (hstate.trans (le_max_right ε δ))
  · change 1 - povmValue _ S.ψ S.PA.toPOVM S.PB.toPOVM ≤ max ε δ
    rw [← TensorProductStrategy.value_eq_povmValue]
    exact hfail.trans (le_max_left ε δ)
  · have hh := hX.trans (le_max_right ε δ)
    simpa only [restriction, validAnswer, PauliRestriction.strategy_pauliAns_A,
      ProjectiveMeasurement.toPOVM] using hh
  · have hh := hZ.trans (le_max_right ε δ)
    simpa only [restriction, validAnswer, PauliRestriction.strategy_pauliAns_B,
      ProjectiveMeasurement.toPOVM] using hh

/-- An external QLD extraction theorem is invoked with the proved failure
bound of the actual restriction; introspection then supplies source success. -/
theorem quantumValue_ge_of_qld_extraction
    (hL : ∀ w, (L w).ExactlyOn univ) {ε δ : ℝ}
    (hδ : 0 ≤ δ) (hfail : 1 - S.value ≤ ε)
    (extract : ∀ R : TensorProductStrategy (QLD.qldGame (d := d) hm),
      1 - R.value ≤
        (TypeGraph.edges QLD.adj (.pauli .X) (.pauli .Z) ℓ).card * ε →
      Nonempty (Extraction hm b R δ)) :
    1 - validSoundnessCoefficient ℓ
      (TypeGraph.edges QLD.adj (.pauli .X) (.pauli .Z) ℓ).card *
      iteratedRoot (6 * ℓ + 2) (max ε δ) ≤ quantumValue (Honest.sourceGame L D) := by
  obtain ⟨w⟩ := extract (restriction hm b L D S)
    (PauliRestriction.strategy_failure_le hm b L (BinaryComplete.project b) D S
      (.val 0) (.val 0) hfail)
  exact quantumValue_ge_of_extraction hm b L D S hL w.ξ w.ξ_unit w.VA w.VB
    w.VA_isometry w.VB_isometry hδ hfail w.state_error w.X_error w.Z_error

end MIPRE.Introspection.RestrictedSoundness
end

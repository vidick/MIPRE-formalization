/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.ValidOutcomeError
import MIPRE.Foundations.Introspection.IsometricSoundness

/-! # Finite introspection soundness from valid-answer Pauli extraction

This is the extraction interface used in the paper: an unsquared state
distance and measurement errors summed only over valid full-register
answers. Every other raw answer, and the isometric image complement, is
accounted for by the proof. The local isometries and their estimates are
inputs; existence of those data is the separate Pauli soundness theorem.
-/

noncomputable section
namespace MIPRE.Introspection
open Finset Matrix Classical
set_option linter.unusedSectionVars false

def validSoundnessCoefficient (r : ℕ) (edges : ℝ) : ℝ :=
  6 * extractedSoundnessCoefficient r edges

theorem validSoundnessCoefficient_one_le (r : ℕ) {edges : ℝ} (he : 0 ≤ edges) :
    1 ≤ validSoundnessCoefficient r edges := by
  have h := extractedSoundnessCoefficient_one_le r he
  unfold validSoundnessCoefficient
  linarith

/-- The valid-answer interface retains the paper's two-term power profile,
with constants uniform in the source and register dimensions. -/
theorem exists_validSoundness_errorProfile (r : ℕ) {edges a b : ℝ}
    (hE : 0 ≤ edges) (ha : 0 ≤ a) (hb0 : 0 < b) (hb1 : b ≤ 1) :
    ∃ a' b' : ℝ, 1 ≤ a' ∧ 0 < b' ∧ b' ≤ 1 ∧
      ∀ x ε : ℝ, 1 ≤ x → 0 ≤ ε →
        validSoundnessCoefficient r edges *
          iteratedRoot (6 * r + 2) (errorProfile a b x ε) ≤ errorProfile a' b' x ε := by
  refine ⟨powerCoefficient (validSoundnessCoefficient r edges) a (rootExponent (6 * r + 2)),
    b * rootExponent (6 * r + 2), one_le_powerCoefficient _ _ _,
    (power_exponent_bounds hb0 hb1 (rootExponent_pos _) (rootExponent_le_one _)).1,
    (power_exponent_bounds hb0 hb1 (rootExponent_pos _) (rootExponent_le_one _)).2, ?_⟩
  intro x ε hx hε
  exact errorProfile_iteratedRoot (6 * r + 2)
    (by linarith [validSoundnessCoefficient_one_le r hE]) ha hx hε

namespace TypedEstimates
universe u
variable {F ι A H K : Type u} {H₀ K₀ PauliType PauliAnswer κ : Type*}
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype A] [Nonempty A]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype H₀] [DecidableEq H₀] [Fintype K₀] [DecidableEq K₀]
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Fintype κ] [DecidableEq κ] {ℓ : ℕ}

set_option backward.isDefEq.respectTransparency false in
/-- Complete finite-game soundness from the valid-answer, unsquared-distance
form of Pauli extraction. No zero-malformed-mass assumption is required. -/
theorem quantumValue_ge_of_valid_isometric_images
    (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
    (hL : ∀ w, (L w).ExactlyOn univ)
    (projectPauli : PauliAnswer → ι → F)
    (validPauli : (ι → F) → PauliAnswer)
    (hvalid : ∀ x, projectPauli (validPauli x) = x)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
      PauliAnswer → PauliAnswer → Bool)
    (G : Game (ι → F) (ι → F) A A)
    (hμ : ∀ x y, G.μ x y = CL.clDist (L false).eval (L true).eval x y)
    (hD : G.D = D) (ξ : H × K → ℂ) (hξ : star ξ ⬝ᵥ ξ = 1)
    (ψ : H₀ × K₀ → ℂ) (hψ : ‖evec ψ‖ = 1)
    (VA : Matrix ((ι → F) × H) H₀ ℂ) (VB : Matrix ((ι → F) × K) K₀ ℂ)
    (hVA : VAᴴ * VA = 1) (hVB : VBᴴ * VB = 1)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) H₀)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) K₀)
    (hMA : ∀ q, IsPVM (fun a => ((MA q).mats a).val))
    (hMB : ∀ q, IsPVM (fun a => ((MB q).mats a).val))
    (qX qZ : κ → ZMod 2)
    (hqX : ∀ z, (P X).eval z = qX) (hqZ : ∀ z, (P Z).eval z = qZ)
    {t : ℝ} (ht : 0 ≤ t)
    (hstate : ‖evec (isometricState VA VB ψ - registerState (ι → F) ξ)‖ ≤ t)
    (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP) ψ MA MB ≤ t)
    (hX : ∑ x, snorm (registerState (ι → F) ξ) (aOp
      (isometricImage VA ((MA (QuestionType.pauli X, qX)).mats (.pauli (validPauli x))).val -
        (aOp (Honest.pauliXReadout (some x)) : Matrix ((ι → F) × H) _ ℂ))) ^ 2 ≤ t)
    (hZ : ∑ z, snorm (registerState (ι → F) ξ) (bOp
      (isometricImage VB ((MB (QuestionType.pauli Z, qZ)).mats (.pauli (validPauli z))).val -
        (aOp (readout (some : (ι → F) → Option (ι → F)) (some z)) :
          Matrix ((ι → F) × K) _ ℂ))) ^ 2 ≤ t) :
    1 - validSoundnessCoefficient ℓ (TypeGraph.edges E X Z ℓ).card *
      iteratedRoot (6 * ℓ + 2) t ≤ quantumValue G := by
  have hE : (0 : ℝ) ≤ (TypeGraph.edges E X Z ℓ).card := Nat.cast_nonneg _
  by_cases ht1 : t ≤ 1
  · have hnφ := registerState_norm (I := ι → F) ξ (norm_evec_eq_one_of_unit hξ)
    have hv (x : ι → F) : pauliProjection projectPauli
        (ParsedAnswer.pauli (A := A) (validPauli x)) = some x := by
      simp only [pauliProjection, hvalid]
    have hx := isometric_valid_outcome_alice_error_le VA hVA _ hnφ
      (MA (QuestionType.pauli X, qX)) (pauliProjection projectPauli)
      (fun x => .pauli (validPauli x)) hv (fun x => aOp (Honest.pauliXReadout x))
      Honest.pauliXReadout_isPVM.aOp (by rw [Honest.pauliXReadout_none, aOp_zero]) hX
    have hz := isometric_valid_outcome_bob_error_le VB hVB _ hnφ
      (MB (QuestionType.pauli Z, qZ)) (pauliProjection projectPauli)
      (fun x => .pauli (validPauli x)) hv (fun z => aOp (readout (some : (ι → F) → Option (ι → F)) z))
      (readout_isPVM some).aOp (by simp [readout, aOp_zero]) hZ
    have hs := Real.sqrt_nonneg t
    have htr : t ≤ Real.sqrt t := by
      simpa only [iteratedRoot] using self_le_iteratedRoot 1 ht ht1
    have hstate' : ‖evec (isometricState VA VB ψ - registerState (ι → F) ξ)‖ ^ 2 ≤
        6 * Real.sqrt t := by
      nlinarith [norm_nonneg (evec (isometricState VA VB ψ - registerState (ι → F) ξ)),
        mul_nonneg ht (sub_nonneg.mpr ht1)]
    have hout := quantumValue_ge_of_isometric_images E X Z P L hL projectPauli D DP
      G hμ hD ξ hξ ψ hψ VA VB hVA hVB MA MB hMA hMB qX qZ hqX hqZ
      (show 0 ≤ 6 * Real.sqrt t by positivity) hstate' (hfail.trans (by linarith))
      (by simpa only [stateSqNorm, stateNorm, norm_stateVec_eq_snorm] using
        hx.trans (show 2 * t + 4 * Real.sqrt t ≤ 6 * Real.sqrt t by linarith))
      (hz.trans (by linarith))
    have hr := iteratedRoot_scale_le (6 * ℓ + 1) (c := 6) (t := Real.sqrt t) (by norm_num)
    have he : iteratedRoot (6 * ℓ + 1) (Real.sqrt t) = iteratedRoot (6 * ℓ + 2) t := by
      simpa only [Nat.add_assoc, iteratedRoot] using
        (iteratedRoot_add (6 * ℓ + 1) 1 t).symm
    rw [he] at hr
    have hc := extractedSoundnessCoefficient_one_le ℓ hE
    unfold validSoundnessCoefficient
    nlinarith
  · have hc := validSoundnessCoefficient_one_le ℓ hE
    have hr : 1 ≤ iteratedRoot (6 * ℓ + 2) t := by
      simpa only [iteratedRoot_one] using iteratedRoot_mono (6 * ℓ + 2) (le_of_not_ge ht1)
    have hp : 1 ≤ validSoundnessCoefficient ℓ (TypeGraph.edges E X Z ℓ).card *
        iteratedRoot (6 * ℓ + 2) t := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr hr)]
    exact (by linarith : 1 - validSoundnessCoefficient ℓ
      (TypeGraph.edges E X Z ℓ).card * iteratedRoot (6 * ℓ + 2) t ≤ 0).trans
      (quantumValue_nonneg G)

end TypedEstimates
end MIPRE.Introspection
end

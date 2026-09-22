/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.PrimitiveSoundness
import MIPRE.Foundations.Introspection.PVMStateTransfer
import MIPRE.Foundations.Introspection.StateStability

/-! # Soundness before replacing the extracted state

The primitive measurement guarantees may hold on the actual extracted
state, which is only approximately an EPR register tensored with an
auxiliary state. Both the game value and the two complete Pauli families
are transferred here, with no answer-cardinality factor. The resulting
original-game bound has one additional square root and covers all errors.
-/

noncomputable section
namespace MIPRE.Introspection
open Finset Matrix Classical
set_option linter.unusedSectionVars false

/-- The coefficient after transferring the extracted state and measurements. -/
def extractedSoundnessCoefficient (r : ℕ) (edges : ℝ) : ℝ :=
  20 * primitiveSoundnessCoefficient r edges

theorem extractedSoundnessCoefficient_one_le (r : ℕ) {edges : ℝ} (hE : 0 ≤ edges) :
    1 ≤ extractedSoundnessCoefficient r edges := by
  unfold extractedSoundnessCoefficient
  linarith [primitiveSoundnessCoefficient_one_le r hE]

/-- One additional square root pays for the initial state transfer. -/
theorem extractedSoundness_power_bound (r : ℕ) {edges t : ℝ} (hE : 0 ≤ edges) :
    primitiveSoundnessCoefficient r edges * iteratedRoot (6 * r) (20 * Real.sqrt t) ≤
      extractedSoundnessCoefficient r edges * iteratedRoot (6 * r + 1) t := by
  have h := iteratedRoot_scale_le (6 * r) (t := Real.sqrt t) (by norm_num : (1 : ℝ) ≤ 20)
  have hC := primitiveSoundnessCoefficient_one_le r hE
  have hmul := mul_le_mul_of_nonneg_left h (by linarith : 0 ≤ primitiveSoundnessCoefficient r edges)
  rw [iteratedRoot_add]
  change _ ≤ extractedSoundnessCoefficient r edges * iteratedRoot (6 * r) (Real.sqrt t)
  exact hmul.trans_eq (by unfold extractedSoundnessCoefficient; ring)

/-- Uniform constants for the profile after state transfer and both inductions. -/
theorem exists_extractedSoundness_errorProfile (r : ℕ) {edges a b : ℝ}
    (hE : 0 ≤ edges) (ha : 0 ≤ a) (hb0 : 0 < b) (hb1 : b ≤ 1) :
    ∃ a' b' : ℝ, 1 ≤ a' ∧ 0 < b' ∧ b' ≤ 1 ∧
      ∀ x ε : ℝ, 1 ≤ x → 0 ≤ ε →
        extractedSoundnessCoefficient r edges *
          iteratedRoot (6 * r + 1) (errorProfile a b x ε) ≤ errorProfile a' b' x ε := by
  refine ⟨powerCoefficient (extractedSoundnessCoefficient r edges) a (rootExponent (6 * r + 1)),
    b * rootExponent (6 * r + 1), one_le_powerCoefficient _ _ _,
    (power_exponent_bounds hb0 hb1 (rootExponent_pos _) (rootExponent_le_one _)).1,
    (power_exponent_bounds hb0 hb1 (rootExponent_pos _) (rootExponent_le_one _)).2, ?_⟩
  intro x ε hx hε
  exact errorProfile_iteratedRoot (6 * r + 1)
    (by linarith [extractedSoundnessCoefficient_one_le r hE]) ha hx hε

namespace TypedEstimates
universe u
variable {F ι A H K : Type u} {PauliType PauliAnswer κ : Type*}
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype A] [Nonempty A]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Fintype κ] [DecidableEq κ] {ℓ : ℕ}

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- Original-game soundness from an actual extracted state and its primitive
X/Z guarantees. The ideal register-state estimates are conclusions of this
proof, rather than hypotheses on the output of QLD extraction. -/
theorem quantumValue_ge_of_extracted_state
    (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
    (hL : ∀ w, (L w).ExactlyOn univ)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
      PauliAnswer → PauliAnswer → Bool)
    (G : Game (ι → F) (ι → F) A A)
    (hμ : ∀ x y, G.μ x y = CL.clDist (L false).eval (L true).eval x y)
    (hD : G.D = D) (ξ : H × K → ℂ) (hξ : star ξ ⬝ᵥ ξ = 1)
    (ψ : ((ι → F) × H) × ((ι → F) × K) → ℂ) (hψ : ‖evec ψ‖ = 1)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H))
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × K))
    (hMA : ∀ q, IsPVM (fun a => ((MA q).mats a).val))
    (hMB : ∀ q, IsPVM (fun a => ((MB q).mats a).val))
    (qX qZ : κ → ZMod 2)
    (hqX : ∀ z, (P X).eval z = qX) (hqZ : ∀ z, (P Z).eval z = qZ)
    {t : ℝ} (ht : 0 ≤ t)
    (hstate : ‖evec (ψ - registerState (ι → F) ξ)‖ ^ 2 ≤ t)
    (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP) ψ MA MB ≤ t)
    (hX : ∑ x, stateSqNorm ψ
      ((((MA (QuestionType.pauli X, qX)).map (pauliProjection projectPauli)).mats x).val -
        (aOp (Honest.pauliXReadout x) : Matrix ((ι → F) × H) _ ℂ)) ≤ t)
    (hZ : ∑ z, snorm ψ (bOp
      ((((MB (QuestionType.pauli Z, qZ)).map (pauliProjection projectPauli)).mats z).val -
        (aOp (readout (some : (ι → F) → Option (ι → F)) z) :
          Matrix ((ι → F) × K) _ ℂ))) ^ 2 ≤ t) :
    1 - extractedSoundnessCoefficient ℓ (TypeGraph.edges E X Z ℓ).card *
      iteratedRoot (6 * ℓ + 1) t ≤ quantumValue G := by
  have hE : (0 : ℝ) ≤ (TypeGraph.edges E X Z ℓ).card := Nat.cast_nonneg _
  have hC := extractedSoundnessCoefficient_one_le ℓ hE
  by_cases ht1 : t ≤ 1
  · have hs := Real.sqrt_nonneg t
    have htr : t ≤ Real.sqrt t := by
      simpa only [iteratedRoot] using self_le_iteratedRoot 1 ht ht1
    have hφ := registerState_norm (I := ι → F) ξ (norm_evec_eq_one_of_unit hξ)
    have hf := povmValue_failure_transfer (parsedGame E X Z P L projectPauli D DP)
      ψ (registerState (ι → F) ξ) hψ hφ MA MB hMA hMB hfail hstate
    have hx := sum_stateSqNorm_state_transfer_le ψ (registerState (ι → F) ξ)
      (isPVM_povm_map _ (hMA _) (pauliProjection projectPauli))
      (Honest.pauliXReadout_isPVM (F := F) (ι := ι)).aOp hX hstate
    have hz := sum_bob_snorm_state_transfer_le ψ (registerState (ι → F) ξ)
      (isPVM_povm_map _ (hMB _) (pauliProjection projectPauli))
      (readout_isPVM (some : (ι → F) → Option (ι → F))).aOp hZ hstate
    have hv := quantumValue_ge_of_primitive_pauli E X Z P L hL projectPauli D DP
      G hμ hD ξ hξ MA MB hMA hMB qX qZ hqX hqZ
      (show 0 ≤ 20 * Real.sqrt t by positivity)
      (hf.trans (by linarith)) (hx.trans (by linarith)) (hz.trans (by linarith))
    have hp := extractedSoundness_power_bound ℓ (t := t) hE
    linarith
  · have hroot : 1 ≤ iteratedRoot (6 * ℓ + 1) t := by
      simpa only [iteratedRoot_one] using iteratedRoot_mono (6 * ℓ + 1) (le_of_not_ge ht1)
    have hp : 1 ≤ extractedSoundnessCoefficient ℓ (TypeGraph.edges E X Z ℓ).card *
        iteratedRoot (6 * ℓ + 1) t := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hC) (sub_nonneg.mpr hroot)]
    exact (by linarith : 1 - extractedSoundnessCoefficient ℓ
      (TypeGraph.edges E X Z ℓ).card * iteratedRoot (6 * ℓ + 1) t ≤ 0).trans
      (quantumValue_nonneg G)

end TypedEstimates
end MIPRE.Introspection
end

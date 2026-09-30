/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.PrimitiveSoundness
public import MIPRE.Foundations.Introspection.PVMStateTransfer
public import MIPRE.Foundations.Introspection.StateStability

@[expose] public section

/-! # Soundness before replacing the extracted state

The primitive measurement guarantees may hold on the actual extracted
state, which is only approximately an EPR register tensored with an
auxiliary state. Both the game value and the two complete Pauli families
are transferred here, with no answer-cardinality factor. The resulting
original-game bound has one additional square root and covers all errors.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the extracted state is a unit
vector `φ` of the register model `Ξ.reg (ι → F)`, near its state, and the strategy and its
guarantees live in the register model with that state (`BipartiteModel.withState`).
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
universe u v
variable {F ι A : Type} {PauliType PauliAnswer κ : Type*}
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype A] [Nonempty A]
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Fintype κ] [DecidableEq κ] {ℓ : ℕ}
variable {𝒞 𝒜 ℬ : Type u} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [StarModule ℂ 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarProper 𝒜]
  [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [StarModule ℂ ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]
  [StarProper ℬ]

set_option maxHeartbeats 800000 in
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
    (ω : ValueModel) (G : Game (ι → F) (ι → F) A A)
    (hμ : ∀ x y, G.μ x y = CL.clDist (L false).eval (L true).eval x y)
    (hD : G.D = D) (Ξ : BipartiteModel.{v} 𝒞 𝒜 ℬ) (hΞ : ‖Ξ.ψ‖ = 1)
    (hω : ω.DominatesPOVM Ξ) (φ : (Ξ.reg (ι → F)).H) (hφ : ‖φ‖ = 1)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) 𝒜))
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) ℬ))
    (hMA : ∀ q, IsPVMIn (MA q).op) (hMB : ∀ q, IsPVMIn (MB q).op)
    (qX qZ : κ → ZMod 2)
    (hqX : ∀ z, (P X).eval z = qX) (hqZ : ∀ z, (P Z).eval z = qZ)
    {t : ℝ} (ht : 0 ≤ t)
    (hstate : ‖φ - (Ξ.reg (ι → F)).ψ‖ ^ 2 ≤ t)
    (hfail : 1 - ((Ξ.reg (ι → F)).withState φ).povmValue
      (parsedGame E X Z P L projectPauli D DP) MA MB ≤ t)
    (hX : ∑ x, ((Ξ.reg (ι → F)).withState φ).stateSqNorm
      (((MA (QuestionType.pauli X, qX)).map (pauliProjection projectPauli)).op x -
        smulKron 1 (Honest.pauliXReadout x)) ≤ t)
    (hZ : ∑ z, ((Ξ.reg (ι → F)).withState φ).swap.stateSqNorm
      (((MB (QuestionType.pauli Z, qZ)).map (pauliProjection projectPauli)).op z -
        smulKron 1 (readout (some : (ι → F) → Option (ι → F)) z)) ≤ t) :
    1 - extractedSoundnessCoefficient ℓ (TypeGraph.edges E X Z ℓ).card *
      iteratedRoot (6 * ℓ + 1) t ≤ ω.val G := by
  have hE : (0 : ℝ) ≤ (TypeGraph.edges E X Z ℓ).card := Nat.cast_nonneg _
  have hC := extractedSoundnessCoefficient_one_le ℓ hE
  by_cases ht1 : t ≤ 1
  · have hs := Real.sqrt_nonneg t
    have htr : t ≤ Real.sqrt t := by
      simpa only [iteratedRoot] using self_le_iteratedRoot 1 ht ht1
    let Ψ := (Ξ.reg (ι → F)).withState φ
    have hreg : ‖(Ξ.reg (ι → F)).ψ‖ = 1 := by rw [BipartiteModel.norm_reg_ψ, hΞ]
    have hf := povmValue_failure_transfer Ψ (parsedGame E X Z P L projectPauli D DP)
      (Ξ.reg (ι → F)).ψ hφ hreg MA MB hMA hMB hfail hstate
    have hx := sum_stateSqNorm_state_transfer_le Ψ (Ξ.reg (ι → F)).ψ
      (POVMIn.isPVMIn_map (hMA (QuestionType.pauli X, qX)) (pauliProjection projectPauli))
      (Honest.pauliXReadout_isPVM (F := F) (ι := ι)).toIn.smulKron_one hX hstate
    have hz := sum_bob_snorm_state_transfer_le Ψ (Ξ.reg (ι → F)).ψ
      (POVMIn.isPVMIn_map (hMB (QuestionType.pauli Z, qZ)) (pauliProjection projectPauli))
      (readout_isPVM (some : (ι → F) → Option (ι → F))).toIn.smulKron_one hZ hstate
    have hv := quantumValue_ge_of_primitive_pauli E X Z P L hL projectPauli D DP
      ω G hμ hD Ξ hΞ hω MA MB hMA hMB qX qZ hqX hqZ
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
      (TypeGraph.edges E X Z ℓ).card * iteratedRoot (6 * ℓ + 1) t ≤ 0).trans (ω.nonneg G)

end TypedEstimates
end MIPRE.Introspection
end

end

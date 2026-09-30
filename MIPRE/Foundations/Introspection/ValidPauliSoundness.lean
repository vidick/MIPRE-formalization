/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.ValidOutcomeError
public import MIPRE.Foundations.Introspection.IsometricSoundness

@[expose] public section

/-! # Finite introspection soundness from valid-answer Pauli extraction

This is the extraction interface used in the paper: an unsquared state
distance and measurement errors summed only over valid full-register
answers. Every other raw answer, and the isometric image complement, is
accounted for by the proof. The local isometries and their estimates are
inputs; existence of those data is the separate Pauli soundness theorem.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the strategy lives in any model
`M`, the local isometries are one local isometry of models into the register model `Ξ.reg (ι → F)`
of a normalized auxiliary model `Ξ`, and the value is that of any value model dominating the POVM
strategies of `Ξ`. This is the shape of the conclusion of the Pauli basis test in a model
(`QLD.Extraction`).
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
variable {𝒞₀ 𝒜₀ ℬ₀ : Type*} [Ring 𝒞₀] [StarRing 𝒞₀] [Algebra ℂ 𝒞₀] [Ring 𝒜₀] [StarRing 𝒜₀]
  [Algebra ℂ 𝒜₀] [Ring ℬ₀] [StarRing ℬ₀] [Algebra ℂ ℬ₀] [PartialOrder 𝒜₀] [StarOrderedRing 𝒜₀]
  [PartialOrder ℬ₀] [StarOrderedRing ℬ₀]

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
    (ω : ValueModel) (G : Game (ι → F) (ι → F) A A)
    (hμ : ∀ x y, G.μ x y = CL.clDist (L false).eval (L true).eval x y)
    (hD : G.D = D) (Ξ : BipartiteModel.{v} 𝒞 𝒜 ℬ) (hΞ : ‖Ξ.ψ‖ = 1)
    (hω : ω.DominatesPOVM Ξ) (M : BipartiteModel 𝒞₀ 𝒜₀ ℬ₀) (hM : ‖M.ψ‖ = 1)
    (Φ : BipartiteModel.LocalIsometry M (Ξ.reg (ι → F)))
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) 𝒜₀)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) ℬ₀)
    (hMA : ∀ q, IsPVMIn (MA q).op) (hMB : ∀ q, IsPVMIn (MB q).op)
    (qX qZ : κ → ZMod 2)
    (hqX : ∀ z, (P X).eval z = qX) (hqZ : ∀ z, (P Z).eval z = qZ)
    {t : ℝ} (ht : 0 ≤ t)
    (hstate : ‖Φ.W M.ψ - (Ξ.reg (ι → F)).ψ‖ ≤ t)
    (hfail : 1 - M.povmValue (parsedGame E X Z P L projectPauli D DP) MA MB ≤ t)
    (hX : ∑ x, (Ξ.reg (ι → F)).stateSqNorm
      (Φ.ΦA ((MA (QuestionType.pauli X, qX)).op (.pauli (validPauli x))) -
        smulKron 1 (Honest.pauliXReadout (some x))) ≤ t)
    (hZ : ∑ z, (Ξ.reg (ι → F)).swap.stateSqNorm
      (Φ.ΦB ((MB (QuestionType.pauli Z, qZ)).op (.pauli (validPauli z))) -
        smulKron 1 (readout (some : (ι → F) → Option (ι → F)) (some z))) ≤ t) :
    1 - validSoundnessCoefficient ℓ (TypeGraph.edges E X Z ℓ).card *
      iteratedRoot (6 * ℓ + 2) t ≤ ω.val G := by
  have hE : (0 : ℝ) ≤ (TypeGraph.edges E X Z ℓ).card := Nat.cast_nonneg _
  by_cases ht1 : t ≤ 1
  · have hreg : ‖(Ξ.reg (ι → F)).ψ‖ = 1 := by rw [BipartiteModel.norm_reg_ψ, hΞ]
    have hv (x : ι → F) : pauliProjection projectPauli
        (ParsedAnswer.pauli (A := A) (validPauli x)) = some x := by
      simp only [pauliProjection, hvalid]
    have hx := isometric_valid_outcome_alice_error_le Φ hreg
      (MA (QuestionType.pauli X, qX)) (pauliProjection projectPauli)
      (fun x => .pauli (validPauli x)) hv (fun x => smulKron 1 (Honest.pauliXReadout x))
      (Honest.pauliXReadout_isPVM (F := F) (ι := ι)).toIn.smulKron_one
      (by rw [Honest.pauliXReadout_none, smulKron_zero_right]) hX
    have hz := isometric_valid_outcome_bob_error_le Φ hreg
      (MB (QuestionType.pauli Z, qZ)) (pauliProjection projectPauli)
      (fun x => .pauli (validPauli x)) hv
      (fun z => smulKron 1 (readout (some : (ι → F) → Option (ι → F)) z))
      (readout_isPVM (some : (ι → F) → Option (ι → F))).toIn.smulKron_one
      (by simp [readout, smulKron_zero_right]) hZ
    have hs := Real.sqrt_nonneg t
    have htr : t ≤ Real.sqrt t := by
      simpa only [iteratedRoot] using self_le_iteratedRoot 1 ht ht1
    have hstate' : ‖Φ.W M.ψ - (Ξ.reg (ι → F)).ψ‖ ^ 2 ≤ 6 * Real.sqrt t := by
      nlinarith [norm_nonneg (Φ.W M.ψ - (Ξ.reg (ι → F)).ψ), mul_nonneg ht (sub_nonneg.mpr ht1)]
    have hout := quantumValue_ge_of_isometric_images E X Z P L hL projectPauli D DP
      ω G hμ hD Ξ hΞ hω M hM Φ MA MB hMA hMB qX qZ hqX hqZ
      (show 0 ≤ 6 * Real.sqrt t by positivity) hstate' (hfail.trans (by linarith))
      (hx.trans (show 2 * t + 4 * Real.sqrt t ≤ 6 * Real.sqrt t by linarith))
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
      (TypeGraph.edges E X Z ℓ).card * iteratedRoot (6 * ℓ + 2) t ≤ 0).trans (ω.nonneg G)

end TypedEstimates
end MIPRE.Introspection
end

end

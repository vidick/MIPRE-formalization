/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.IsometricCompletionError
import MIPRE.Foundations.Introspection.ExtractedStateSoundness

/-! # Introspection soundness from local-isometry image estimates

This assembles the actual transported strategy and its image-complement
completion. Primitive estimates can be stated on the ideal register state,
as in Pauli extraction, for the image effects of the original measurements.
No future normalized measurement or transported game-success assumption is
required. The full projected answer alphabet includes malformed outcomes.
-/

noncomputable section
namespace MIPRE.Introspection.TypedEstimates
open Finset Matrix Classical
set_option linter.unusedSectionVars false
universe u
variable {F ι A H K : Type u} {H₀ K₀ PauliType PauliAnswer κ : Type*}
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype A] [Nonempty A]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype H₀] [DecidableEq H₀] [Fintype K₀] [DecidableEq K₀]
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Fintype κ] [DecidableEq κ] {ℓ : ℕ}

set_option backward.isDefEq.respectTransparency false in
/-- The complete finite-game soundness argument with the original strategy
and actual local isometries. Primitive image estimates and the state bound
are the only extraction inputs; all subsequent strategies are constructed. -/
theorem quantumValue_ge_of_isometric_images
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
    (hstate : ‖evec (isometricState VA VB ψ - registerState (ι → F) ξ)‖ ^ 2 ≤ t)
    (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP) ψ MA MB ≤ t)
    (hX : ∑ x, stateSqNorm (registerState (ι → F) ξ)
      (isometricImage VA
        ((((MA (QuestionType.pauli X, qX)).map (pauliProjection projectPauli)).mats x).val) -
        (aOp (Honest.pauliXReadout x) : Matrix ((ι → F) × H) _ ℂ)) ≤ t)
    (hZ : ∑ z, snorm (registerState (ι → F) ξ) (bOp
      (isometricImage VB
        ((((MB (QuestionType.pauli Z, qZ)).map (pauliProjection projectPauli)).mats z).val) -
        (aOp (readout (some : (ι → F) → Option (ι → F)) z) :
          Matrix ((ι → F) × K) _ ℂ))) ^ 2 ≤ t) :
    1 - extractedSoundnessCoefficient ℓ (TypeGraph.edges E X Z ℓ).card *
      iteratedRoot (6 * ℓ + 1) t ≤ quantumValue G := by
  have hE : (0 : ℝ) ≤ (TypeGraph.edges E X Z ℓ).card := Nat.cast_nonneg _
  have hC := extractedSoundnessCoefficient_one_le ℓ hE
  by_cases ht1 : t ≤ 1
  · let a₀ : ParsedAnswer (ι → F) A PauliAnswer := .pair 0 (Classical.choice inferInstance)
    let NA := fun q => isometricPOVM VA hVA a₀ (MA q) (hMA q)
    let NB := fun q => isometricPOVM VB hVB a₀ (MB q) (hMB q)
    have hNA q : IsPVM (fun a => ((NA q).mats a).val) := isometricPOVM_isPVM _ _ _ _ _
    have hNB q : IsPVM (fun a => ((NB q).mats a).val) := isometricPOVM_isPVM _ _ _ _ _
    have hnψ : ‖evec (isometricState VA VB ψ)‖ = 1 := by
      rw [isometricState_norm VA VB hVA hVB, hψ]
    have hnφ := registerState_norm (I := ι → F) ξ (norm_evec_eq_one_of_unit hξ)
    have hfi : 1 - povmValue (parsedGame E X Z P L projectPauli D DP)
        (isometricState VA VB ψ) NA NB ≤ t := by
      rw [show povmValue (parsedGame E X Z P L projectPauli D DP)
        (isometricState VA VB ψ) NA NB =
        povmValue (parsedGame E X Z P L projectPauli D DP) ψ MA MB from
        povmValue_isometricState _ VA VB hVA hVB ψ a₀ a₀ MA MB hMA hMB]
      exact hfail
    have hf := povmValue_failure_transfer (parsedGame E X Z P L projectPauli D DP)
      (isometricState VA VB ψ) (registerState (ι → F) ξ) hnψ hnφ NA NB hNA hNB hfi hstate
    have hx := isometricEffect_alice_error_le VA VB hVA ψ (registerState (ι → F) ξ)
      (pauliProjection projectPauli a₀)
      (fun x => (((MA (QuestionType.pauli X, qX)).map (pauliProjection projectPauli)).mats x).val)
      (fun x => aOp (Honest.pauliXReadout x))
      (by simpa only [stateSqNorm, stateNorm, norm_stateVec_eq_snorm] using hX) hstate
    have hz := isometricEffect_bob_error_le VA VB hVB ψ (registerState (ι → F) ξ)
      (pauliProjection projectPauli a₀)
      (fun z => (((MB (QuestionType.pauli Z, qZ)).map (pauliProjection projectPauli)).mats z).val)
      (fun z => aOp (readout (some : (ι → F) → Option (ι → F)) z)) hZ hstate
    have hdec : (fun a b : Option (ι → F) => Classical.propDecidable (a = b)) =
        (inferInstance : DecidableEq (Option (ι → F))) := Subsingleton.elim _ _
    have heA (x : Option (ι → F)) :
        (((NA (QuestionType.pauli X, qX)).map (pauliProjection projectPauli)).mats x).val =
          isometricEffect VA (pauliProjection projectPauli a₀)
            (fun x => (((MA (QuestionType.pauli X, qX)).map
              (pauliProjection projectPauli)).mats x).val) x := by
      have he := isometricPOVM_map_mats_eq VA hVA a₀ (MA (QuestionType.pauli X, qX))
        (hMA (QuestionType.pauli X, qX)) (pauliProjection projectPauli) x
      rw [hdec] at he
      exact he
    have heB (z : Option (ι → F)) :
        (((NB (QuestionType.pauli Z, qZ)).map (pauliProjection projectPauli)).mats z).val =
          isometricEffect VB (pauliProjection projectPauli a₀)
            (fun z => (((MB (QuestionType.pauli Z, qZ)).map
              (pauliProjection projectPauli)).mats z).val) z := by
      have he := isometricPOVM_map_mats_eq VB hVB a₀ (MB (QuestionType.pauli Z, qZ))
        (hMB (QuestionType.pauli Z, qZ)) (pauliProjection projectPauli) z
      rw [hdec] at he
      exact he
    have hx' : ∑ x, stateSqNorm (registerState (ι → F) ξ)
        ((((NA (QuestionType.pauli X, qX)).map (pauliProjection projectPauli)).mats x).val -
          (aOp (Honest.pauliXReadout x) : Matrix ((ι → F) × H) _ ℂ)) ≤ 4 * t := by
      simp_rw [heA]
      simpa only [stateSqNorm, stateNorm,
        norm_stateVec_eq_snorm, show 2 * t + 2 * t = 4 * t by ring] using hx
    have hz' : introBobZError projectPauli Z qZ ξ NB ≤ 4 * t := by
      unfold introBobZError
      simp_rw [heB]
      simpa only [show 2 * t + 2 * t = 4 * t by ring] using hz
    have hs := Real.sqrt_nonneg t
    have htr : t ≤ Real.sqrt t := by
      simpa only [iteratedRoot] using self_le_iteratedRoot 1 ht ht1
    have hv := quantumValue_ge_of_primitive_pauli E X Z P L hL projectPauli D DP
      G hμ hD ξ hξ NA NB hNA hNB qX qZ hqX hqZ
      (show 0 ≤ 20 * Real.sqrt t by positivity)
      (hf.trans (by linarith)) (hx'.trans (by linarith)) (hz'.trans (by linarith))
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

end MIPRE.Introspection.TypedEstimates
end

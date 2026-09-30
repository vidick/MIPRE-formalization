/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.IsometricCompletionError
public import MIPRE.Foundations.Introspection.ExtractedStateSoundness

@[expose] public section

/-! # Introspection soundness from local-isometry image estimates

This assembles the actual transported strategy and its image-complement
completion. Primitive estimates can be stated on the ideal register state,
as in Pauli extraction, for the image effects of the original measurements.
No future normalized measurement or transported game-success assumption is
required. The full projected answer alphabet includes malformed outcomes.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the original strategy lives in
any model `M`, and the local isometries are one local isometry of models `Φ` from `M` into the
register model `Ξ.reg (ι → F)`. Its homomorphisms are not unital, so the transported measurements
are completed by the image complement (`LocalIsometry.transportA`), whose mass the state distance
controls (`IsometricCompletionError`).
-/

noncomputable section
namespace MIPRE.Introspection.TypedEstimates
open Finset Matrix Classical
set_option linter.unusedSectionVars false
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

/-- The complete finite-game soundness argument with the original strategy
and an actual local isometry. Primitive image estimates and the state bound
are the only extraction inputs; all subsequent strategies are constructed. -/
theorem quantumValue_ge_of_isometric_images
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
    (hstate : ‖Φ.W M.ψ - (Ξ.reg (ι → F)).ψ‖ ^ 2 ≤ t)
    (hfail : 1 - M.povmValue (parsedGame E X Z P L projectPauli D DP) MA MB ≤ t)
    (hX : ∑ x, (Ξ.reg (ι → F)).stateSqNorm
      (Φ.ΦA (((MA (QuestionType.pauli X, qX)).map (pauliProjection projectPauli)).op x) -
        smulKron 1 (Honest.pauliXReadout x)) ≤ t)
    (hZ : ∑ z, (Ξ.reg (ι → F)).swap.stateSqNorm
      (Φ.ΦB (((MB (QuestionType.pauli Z, qZ)).map (pauliProjection projectPauli)).op z) -
        smulKron 1 (readout (some : (ι → F) → Option (ι → F)) z)) ≤ t) :
    1 - extractedSoundnessCoefficient ℓ (TypeGraph.edges E X Z ℓ).card *
      iteratedRoot (6 * ℓ + 1) t ≤ ω.val G := by
  have hE : (0 : ℝ) ≤ (TypeGraph.edges E X Z ℓ).card := Nat.cast_nonneg _
  have hC := extractedSoundnessCoefficient_one_le ℓ hE
  by_cases ht1 : t ≤ 1
  · let a₀ : ParsedAnswer (ι → F) A PauliAnswer := .pair 0 (Classical.choice inferInstance)
    let NA := fun q => Φ.transportA a₀ (MA q) (hMA q)
    let NB := fun q => Φ.transportB a₀ (MB q) (hMB q)
    have hNA q : IsPVMIn (NA q).op := Φ.isPVMIn_transportA a₀ (MA q) (hMA q)
    have hNB q : IsPVMIn (NB q).op := Φ.isPVMIn_transportB a₀ (MB q) (hMB q)
    have hnψ : ‖Φ.W M.ψ‖ = 1 := by rw [Φ.norm_W_ψ, hM]
    have hreg : ‖(Ξ.reg (ι → F)).ψ‖ = 1 := by rw [BipartiteModel.norm_reg_ψ, hΞ]
    have hfi : 1 - ((Ξ.reg (ι → F)).withState (Φ.W M.ψ)).povmValue
        (parsedGame E X Z P L projectPauli D DP) NA NB ≤ t := by
      rw [Φ.povmValue_transport (parsedGame E X Z P L projectPauli D DP) a₀ a₀ MA MB hMA hMB]
      exact hfail
    have hf := povmValue_failure_transfer ((Ξ.reg (ι → F)).withState (Φ.W M.ψ))
      (parsedGame E X Z P L projectPauli D DP) (Ξ.reg (ι → F)).ψ hnψ hreg NA NB hNA hNB hfi
      hstate
    have hx := isometricEffect_alice_error_le Φ (pauliProjection projectPauli a₀)
      (fun x => ((MA (QuestionType.pauli X, qX)).map (pauliProjection projectPauli)).op x)
      (fun x => smulKron 1 (Honest.pauliXReadout x)) hX hstate
    have hz := isometricEffect_bob_error_le Φ (pauliProjection projectPauli a₀)
      (fun z => ((MB (QuestionType.pauli Z, qZ)).map (pauliProjection projectPauli)).op z)
      (fun z => smulKron 1 (readout (some : (ι → F) → Option (ι → F)) z)) hZ hstate
    have heA (x : Option (ι → F)) :
        ((NA (QuestionType.pauli X, qX)).map (pauliProjection projectPauli)).op x =
          Φ.transportOpA (pauliProjection projectPauli a₀)
            ((MA (QuestionType.pauli X, qX)).map (pauliProjection projectPauli)).op x :=
      transportA_map_op Φ a₀ _ (hMA _) _ x
    have heB (z : Option (ι → F)) :
        ((NB (QuestionType.pauli Z, qZ)).map (pauliProjection projectPauli)).op z =
          Φ.swap.transportOpA (pauliProjection projectPauli a₀)
            ((MB (QuestionType.pauli Z, qZ)).map (pauliProjection projectPauli)).op z :=
      transportA_map_op Φ.swap a₀ _ (hMB _) _ z
    have hx' : ∑ x, (Ξ.reg (ι → F)).stateSqNorm
        (((NA (QuestionType.pauli X, qX)).map (pauliProjection projectPauli)).op x -
          smulKron 1 (Honest.pauliXReadout x)) ≤ 4 * t := by
      simp_rw [heA]
      exact hx.trans_eq (by ring)
    have hz' : introBobZError projectPauli Z qZ Ξ NB ≤ 4 * t := by
      unfold introBobZError
      simp_rw [heB]
      exact hz.trans_eq (by ring)
    have hs := Real.sqrt_nonneg t
    have htr : t ≤ Real.sqrt t := by
      simpa only [iteratedRoot] using self_le_iteratedRoot 1 ht ht1
    have hv := quantumValue_ge_of_primitive_pauli E X Z P L hL projectPauli D DP
      ω G hμ hD Ξ hΞ hω NA NB hNA hNB qX qZ hqX hqZ
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
      (TypeGraph.edges E X Z ℓ).card * iteratedRoot (6 * ℓ + 1) t ≤ 0).trans (ω.nonneg G)

end MIPRE.Introspection.TypedEstimates
end

end

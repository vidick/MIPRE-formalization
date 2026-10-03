/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Background.Introspection.NumberedSoundness
public import MIPRE.Background.Introspection.CanonicalDecodedStrategy

@[expose] public section

/-! # Soundness of the actual compiled introspection verifier

The compiled strategy is restricted through finite detyping, decoded to the
canonical quotient game, and passed to the proved QLD theorem. Coordinate
padding is removed and the fixed detyping factor is absorbed into the uniform
error profile. The answer budget may be any budget above the enforced cutoff.

Stated in a value model (Phase 4 of `planning/mipco-track.md`): a raw strategy is a projective
strategy of a model in which the Pauli basis test is sound (`QLD.SoundIn ω M`), and the output's
value is that of any value model approached by such strategies (`QLD.ApproxSoundIn ω`) and by the
projective strategies of the models it dominates (`ValueModel.ProjApprox`, for the padding). Both
hold for `val*` (`QLD.approxSoundIn_tensor`, `ValueModel.tensor_projApprox`) and, when the test
is sound in every commuting-operator model, for `ω_co`.
-/

noncomputable section
namespace MIPRE.Introspection.CompiledSoundness
open CL Cost SourceCompiler PauliSamplerParameters RestrictedSoundness DecisionCompiler
set_option linter.unusedSectionVars false

def sourceCoefficient (c : ℕ) : ℝ :=
  profileCoefficient 7 (PauliErrorParameters.profileCoefficient qldCoefficient c) qldExponent

def exponent : ℝ := qldExponent * rootExponent (6 * 7 + 2)

def coefficient (c : ℕ) : ℝ :=
  powerCoefficient (max 1 (detypingLoss ^ exponent)) (sourceCoefficient c) 1

theorem sourceCoefficient_one_le (c : ℕ) : 1 ≤ sourceCoefficient c :=
  profileCoefficient_one_le _ _ _

theorem coefficient_one_le (c : ℕ) : 1 ≤ coefficient c := one_le_powerCoefficient _ _ _

theorem exponent_pos : 0 < exponent := mul_pos qldExponent_pos (rootExponent_pos _)

theorem exponent_le_one : exponent ≤ 1 :=
  (power_exponent_bounds qldExponent_pos qldExponent_lt_one.le
    (rootExponent_pos _) (rootExponent_le_one _)).2

theorem scale_error {x ε : ℝ} (c : ℕ) (hx : 1 ≤ x) (hε : 0 ≤ ε) :
    errorProfile (sourceCoefficient c) exponent x (detypingLoss * ε) ≤
      errorProfile (coefficient c) exponent x ε := by
  have h := errorProfile_scaled_power (C := 1) (a := sourceCoefficient c)
    (b := exponent) (c := detypingLoss) (r := 1) (x := x) (ε := ε)
    (by norm_num) (by linarith [sourceCoefficient_one_le c]) detypingLoss_nonneg
    (by norm_num) le_rfl hx hε
  simpa only [coefficient, Real.rpow_one, one_mul, mul_one] using h

local instance power_neZero (c lam n : ℕ) : NeZero (registerPower c lam n) :=
  ⟨Nat.ne_of_gt (registerPower_pos c lam n)⟩

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ]

/-- A raw typed strategy, in a model where the Pauli basis test is sound, already gives the
original verifier's source value, in every value model approached by projective strategies. -/
theorem source_value_ge_of_raw (ω : ValueModel) (hω : ω.ProjApprox) (c : ℕ) (hc : 2 ≤ c)
    (he : Even c) (hcb : 2 * qldCoefficient + 2 ≤ (c : ℝ) * qldExponent)
    (U : ClockedUniversalMachine) {lam n : ℕ}
    (V : Verifier 7) (hV : V.IsBounded lam) (hn : 1 ≤ n) {M : BipartiteModel 𝒞 𝒜 ℬ}
    (hQ : QLD.SoundIn ω M)
    (S : M.ProjStrat (rawGame c (by omega) he U (V.sampler.prog,V.decider.prog) lam n))
    {ε : ℝ} (hε : 0 ≤ ε) (hS : 1 - S.value ≤ ε) :
    1 - errorProfile (sourceCoefficient c) exponent (lam * n) ε ≤
      V.val ω (2^n) ((2^n)^lam) := by
  have hc1 : 1 ≤ c := by omega
  have hx : 2 ≤ lam * n := calc
    2 ≤ lam := hV.two_le
    _ ≤ lam * n := by simpa using Nat.mul_le_mul_left lam hn
  let hs := VerifierSource.dimension_le_registerBits hc V hV hn
  let R := CanonicalDecoded.strategy c hc1 he U lam n V hs S
  have hL : ∀ w, (AuxiliaryDecision.padded V hs w).ExactlyOn Finset.univ :=
    SourcePadding.depthFamily_exactlyOn (AuxiliaryProgram.firstEmbedding hs)
      (SourcePadding.Program.sourceFamily V n) (by decide) (fun _ => V.sampler.cl_exactlyOn _ _)
  have hv := NumberedSoundness.canonical_quantumValue_ge c lam n hc hcb hx
    (CanonicalGame.field c lam n).card_carrier (CanonicalGame.divides c hc1 lam n)
    (CanonicalGame.basis c he lam n) (SAT.shoupSelfDualNormalBasis_selfDual _ _ _)
    (CanonicalGame.numbering c lam n) (AuxiliaryDecision.padded V hs)
    (VerifierSource.paddedPredicate V hs ((2^n)^lam)) hL
    (CanonicalGame.selector c hc1 lam n) (CanonicalGame.permutation c lam n)
    (CanonicalGame.selector_eq c hc1 lam n) hQ R
    (CanonicalDecoded.supported_A c hc1 he U lam n V hs S)
    (CanonicalDecoded.supported_B c hc1 he U lam n V hs S) hε
    (CanonicalDecoded.failure_le c hc1 he U V hV hn hc hs S hS)
  exact hv.trans (VerifierSource.padded_quantumValue_le V hs hω)

/-- Soundness in exactly the ambient verifier-value form used by the pipeline, in every value
model approached by projective strategies of models where the Pauli basis test is sound. -/
theorem output_soundness (ω : ValueModel) (hω : ω.ProjApprox) (hA : QLD.ApproxSoundIn ω)
    (c : ℕ) (hc : 2 ≤ c) (he : Even c)
    (hcb : 2 * qldCoefficient + 2 ≤ (c : ℝ) * qldExponent)
    (U : ClockedUniversalMachine) (V : Verifier 7) (lam n B : ℕ) (ε : ℝ)
    (hV : V.IsBounded lam) (hn : 1 ≤ n) (hε : 0 < ε)
    (hB : outerBound c lam n ≤ B)
    (hv : 1 - ε < (DecisionCompiler.output c (by omega) he U
      (V.sampler.prog,V.decider.prog) lam).val ω n B) :
    1 - delta (coefficient c) exponent lam n ε ≤ V.val ω (2^n) ((2^n)^lam) := by
  have hc1 : 1 ≤ c := by omega
  have hl : 1 ≤ lam := by have := hV.two_le; omega
  have hx : (1 : ℝ) ≤ (lam : ℝ) * n := by
    exact_mod_cast (show 1 ≤ lam * n from Nat.mul_pos hl hn)
  rcases le_or_gt 1 ε with hε1 | hε1
  · have hd : 1 ≤ errorProfile (coefficient c) exponent ((lam : ℝ) * n) ε :=
      one_le_errorProfile (coefficient_one_le c) exponent_pos.le hx hε1
    exact (by linarith : 1 - errorProfile (coefficient c) exponent ((lam : ℝ) * n) ε ≤ 0).trans
      (ω.nonneg _)
  rw [output_val_eq_reference ω c hc1 he U (V.sampler.prog,V.decider.prog) hl hn hB] at hv
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, M, hQ, S, hS⟩ :=
    hA _ (by linarith) hv
  obtain ⟨R, hR⟩ := exists_raw_failure_le c hc1 he U (V.sampler.prog,V.decider.prog) S
    (ε := ε) (by linarith)
  have hraw := source_value_ge_of_raw ω hω c hc he hcb U V hV hn hQ R
    (mul_nonneg detypingLoss_nonneg hε.le) hR
  have hscale := scale_error c hx hε.le
  exact (sub_le_sub_left hscale 1).trans hraw

end MIPRE.Introspection.CompiledSoundness
end

end

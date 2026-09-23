/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.Introspection.NumberedSoundness
import MIPRE.Background.Introspection.CanonicalDecodedStrategy

/-! # Soundness of the actual compiled introspection verifier

The compiled strategy is restricted through finite detyping, decoded to the
canonical quotient game, and passed to the proved QLD theorem. Coordinate
padding is removed and the fixed detyping factor is absorbed into the uniform
error profile. The answer budget may be any budget above the enforced cutoff.
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

/-- A single even parameter constant suffices for all verifier indices. -/
theorem exists_parameter_constant :
    ∃ c : ℕ, 2 ≤ c ∧ Even c ∧ 2 * qldCoefficient + 2 ≤ (c : ℝ) * qldExponent :=
  PauliErrorParameters.exists_even_constant qldCoefficient qldExponent_pos

private theorem scale_error {x ε : ℝ} (c : ℕ) (hx : 1 ≤ x) (hε : 0 ≤ ε) :
    errorProfile (sourceCoefficient c) exponent x (detypingLoss * ε) ≤
      errorProfile (coefficient c) exponent x ε := by
  have h := errorProfile_scaled_power (C := 1) (a := sourceCoefficient c)
    (b := exponent) (c := detypingLoss) (r := 1) (x := x) (ε := ε)
    (by norm_num) (by linarith [sourceCoefficient_one_le c]) detypingLoss_nonneg
    (by norm_num) le_rfl hx hε
  simpa only [coefficient, Real.rpow_one, one_mul, mul_one] using h

local instance power_neZero (c lam n : ℕ) : NeZero (registerPower c lam n) :=
  ⟨Nat.ne_of_gt (registerPower_pos c lam n)⟩

/-- A raw typed strategy already gives the original verifier's source value. -/
theorem source_value_ge_of_raw (c : ℕ) (hc : 2 ≤ c) (he : Even c)
    (hcb : 2 * qldCoefficient + 2 ≤ (c : ℝ) * qldExponent)
    (U : ClockedUniversalMachine) {lam n : ℕ}
    (V : Verifier 7) (hV : V.IsBounded lam) (hn : 1 ≤ n)
    (S : TensorProductStrategy
      (rawGame c (by omega) he U (V.sampler.prog,V.decider.prog) lam n))
    {ε : ℝ} (hε : 0 ≤ ε) (hS : 1 - S.value ≤ ε) :
    1 - errorProfile (sourceCoefficient c) exponent (lam * n) ε ≤
      V.valStar (2^n) ((2^n)^lam) := by
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
    (CanonicalGame.selector_eq c hc1 lam n) R
    (CanonicalDecoded.supported_A c hc1 he U lam n V hs S)
    (CanonicalDecoded.supported_B c hc1 he U lam n V hs S) hε
    (CanonicalDecoded.failure_le c hc1 he U V hV hn hc hs S hS)
  exact hv.trans (VerifierSource.padded_quantumValue_le V hs)

/-- Soundness in exactly the ambient verifier-value form used by the pipeline. -/
theorem output_soundness (c : ℕ) (hc : 2 ≤ c) (he : Even c)
    (hcb : 2 * qldCoefficient + 2 ≤ (c : ℝ) * qldExponent)
    (U : ClockedUniversalMachine) (V : Verifier 7) (lam n B : ℕ) (ε : ℝ)
    (hV : V.IsBounded lam) (hn : 1 ≤ n) (hε : 0 < ε)
    (hB : outerBound c lam n ≤ B)
    (hv : 1 - ε < (DecisionCompiler.output c (by omega) he U
      (V.sampler.prog,V.decider.prog) lam).valStar n B) :
    1 - delta (coefficient c) exponent lam n ε ≤ V.valStar (2^n) ((2^n)^lam) := by
  have hc1 : 1 ≤ c := by omega
  have hl : 1 ≤ lam := by have := hV.two_le; omega
  obtain ⟨S,hS⟩ := exists_raw_failure_le c hc1 he U (V.sampler.prog,V.decider.prog)
    hl hn hB ε hv
  have hraw := source_value_ge_of_raw c hc he hcb U V hV hn S
    (mul_nonneg detypingLoss_nonneg hε.le) hS
  have hx : (1 : ℝ) ≤ (lam : ℝ) * n := by
    exact_mod_cast (show 1 ≤ lam * n from Nat.mul_pos hl hn)
  have hscale := scale_error c hx hε.le
  have hh : 1 - errorProfile (coefficient c) exponent ((lam : ℝ) * n) ε ≤
      V.valStar (2^n) ((2^n)^lam) := by
    exact (sub_le_sub_left hscale 1).trans hraw
  exact hh

end MIPRE.Introspection.CompiledSoundness
end

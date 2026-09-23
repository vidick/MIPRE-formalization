/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.PauliSamplerParams
import MIPRE.Foundations.Introspection.ErrorBounds

/-! # Canonical parameters absorb the actual QLD error tails

At degree one, the QLD loss is `a*m^a*(ε^b+q^(-b)+2^(-b*m))`.
The field size and dyadic point dimension chosen by the executable sampler make
both residual terms polynomially small in `λ*n`, with uniform constants.
-/

noncomputable section
namespace MIPRE.Introspection.PauliErrorParameters
open SourceCompiler PauliSamplerParameters

/-- The degree-one specialization of the external QLD error profile. -/
def qldError (a b m q ε : ℝ) : ℝ :=
  a * m ^ a * (ε ^ b + q ^ (-b) + (2 : ℝ) ^ (-b * m))

theorem qldError_nonneg {a b m q ε : ℝ} (ha : 0 ≤ a) (hm : 0 ≤ m)
    (hq : 0 ≤ q) (hε : 0 ≤ ε) : 0 ≤ qldError a b m q ε := by
  unfold qldError
  positivity

/-- A coefficient covering the dimension factor and both residual tails. -/
def profileCoefficient (a c : ℝ) : ℝ := max 1 (max a (2 * a * (c + 1) ^ a))

theorem profileCoefficient_one_le (a c : ℝ) : 1 ≤ profileCoefficient a c := le_max_left _ _

/-- The two QLD tails are absorbed from elementary lower bounds on `q` and
`2^(2m)`. These bounds are discharged for the executable parameters below. -/
theorem qldError_le_profile {a b c x m q ε : ℝ}
    (ha : 1 ≤ a) (hb0 : 0 < b) (hb1 : b ≤ 1) (hc : 1 ≤ c)
    (hcb : 2 * a + 2 ≤ c * b) (hx : 1 ≤ x) (hm : 0 ≤ m) (hε : 0 ≤ ε)
    (hmx : m ≤ (c + 1) * x) (hqx : x ^ c ≤ q)
    (h2x : x ^ c ≤ (2 : ℝ) ^ (2 * m)) :
    qldError a b m q ε ≤ errorProfile (profileCoefficient a c) b x ε := by
  have ha0 : 0 ≤ a := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hxp : 0 < x := by linarith
  have hcp : 0 ≤ c + 1 := by linarith
  have hxcp := Real.rpow_pos_of_pos hxp c
  have hq := Real.rpow_le_rpow_of_nonpos hxcp hqx (show -b ≤ 0 by linarith)
  rw [← Real.rpow_mul hx0] at hq
  have h2 := Real.rpow_le_rpow_of_nonpos hxcp h2x (show -b / 2 ≤ 0 by linarith)
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_mul hx0] at h2
  have hexp : 2 * m * (-b / 2) = -b * m := by ring
  rw [hexp] at h2
  have hmPow := Real.rpow_le_rpow hm hmx ha0
  rw [Real.mul_rpow hcp hx0] at hmPow
  have hqTail : x ^ a * q ^ (-b) ≤ x ^ (-b) := by
    calc
      _ ≤ x ^ a * x ^ (c * -b) := mul_le_mul_of_nonneg_left hq (Real.rpow_nonneg hx0 _)
      _ = x ^ (a + c * -b) := (Real.rpow_add hxp _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx (by nlinarith)
  have h2Tail : x ^ a * (2 : ℝ) ^ (-b * m) ≤ x ^ (-b) := by
    calc
      _ ≤ x ^ a * x ^ (c * (-b / 2)) :=
        mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hx0 _)
      _ = x ^ (a + c * (-b / 2)) := (Real.rpow_add hxp _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx (by nlinarith)
  let K := a * (c + 1) ^ a
  have hK : 0 ≤ K := mul_nonneg ha0 (Real.rpow_nonneg hcp _)
  have hq0 : 0 ≤ q := hxcp.le.trans hqx
  have hrest : 0 ≤ ε ^ b + q ^ (-b) + (2 : ℝ) ^ (-b * m) := by positivity
  have hmain : qldError a b m q ε ≤ K * (x ^ a * ε ^ b + 2 * x ^ (-b)) := by
    calc
      _ ≤ a * ((c + 1) ^ a * x ^ a) *
          (ε ^ b + q ^ (-b) + (2 : ℝ) ^ (-b * m)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmPow ha0) hrest
      _ = K * (x ^ a * ε ^ b + x ^ a * q ^ (-b) + x ^ a * (2 : ℝ) ^ (-b * m)) := by
        dsimp [K]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hK
  have haA : a ≤ profileCoefficient a c := (le_max_left _ _).trans (le_max_right _ _)
  have hKA : 2 * K ≤ profileCoefficient a c := by
    simpa only [K, profileCoefficient, mul_assoc] using
      ((le_max_right a (2 * a * (c + 1) ^ a)).trans (le_max_right 1 _))
  have hK1 : K ≤ profileCoefficient a c := by linarith
  have hxPow := Real.rpow_le_rpow_of_exponent_le hx haA
  have hεpow := Real.rpow_nonneg hε b
  have hxNeg := Real.rpow_nonneg hx0 (-b)
  have hfirst := mul_le_mul_of_nonneg_right hxPow hεpow
  have hf := mul_le_mul hK1 hfirst (mul_nonneg (Real.rpow_nonneg hx0 _) hεpow)
    (by linarith [profileCoefficient_one_le a c])
  have ht := mul_le_mul_of_nonneg_right hKA hxNeg
  unfold errorProfile
  nlinarith

/-- The executable field has at least `(λ*n)^c` elements. -/
theorem canonical_field_lower (c lam n : ℕ) (hx : 2 ≤ lam * n) :
    (lam * n) ^ c ≤ 2 ^ fieldBits c lam n := by
  have ht : canonicalLog lam n = lam * n := Nat.max_eq_right hx
  have hs : lam * n ≤ 2 ^ (lam * n - 1).size := by
    have := Nat.lt_size_self (lam * n - 1)
    omega
  unfold fieldBits
  rw [ht]
  calc
    (lam * n) ^ c ≤ (2 ^ (lam * n - 1).size) ^ c := Nat.pow_le_pow_left hs c
    _ = 2 ^ ((lam * n - 1).size * c) := (pow_mul _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by nlinarith)

/-- The lower dyadic rounding of `c*λ*n+1` loses at most a factor of two. -/
theorem canonical_register_lower (c lam n : ℕ) (hx : 2 ≤ lam * n) :
    c * (lam * n) ≤ 2 * registerPower c lam n := by
  have ht : canonicalLog lam n = lam * n := Nat.max_eq_right hx
  have hs := Nat.size_pos.mpr (show 0 < c * canonicalLog lam n + 1 by omega)
  have hp := Nat.lt_size_self (c * canonicalLog lam n + 1)
  have he : (c * canonicalLog lam n + 1).size =
      ((c * canonicalLog lam n + 1).size - 1) + 1 := by omega
  rw [he, pow_succ] at hp
  change c * canonicalLog lam n + 1 < registerPower c lam n * 2 at hp
  rw [ht] at hp
  omega

/-- The actual `2^(-b*m)` tail is controlled by taking half the power of this
inequality; the exponent is not replaced by `2^(-2*b*m)`. -/
theorem canonical_exponential_lower (c lam n : ℕ) (hx : 2 ≤ lam * n) :
    (lam * n) ^ c ≤ 2 ^ (2 * registerPower c lam n) := by
  calc
    (lam * n) ^ c ≤ (2 ^ (lam * n)) ^ c :=
      Nat.pow_le_pow_left (Nat.lt_two_pow_self.le) c
    _ = 2 ^ ((lam * n) * c) := (pow_mul _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide)
      (by simpa only [Nat.mul_comm] using canonical_register_lower c lam n hx)

/-- The canonical point dimension has a fixed linear bound. -/
theorem canonical_register_upper (c lam n : ℕ) (hx : 2 ≤ lam * n) :
    registerPower c lam n ≤ (c + 1) * (lam * n) := by
  have ht : canonicalLog lam n = lam * n := Nat.max_eq_right hx
  have hm := registerPower_le c lam n
  rw [ht] at hm
  nlinarith

/-- The QLD profile for the parameters computed by the sampler has the
uniform introspection shape, including both residual terms. -/
theorem canonical_qldError_le_profile {a b : ℝ} (ha : 1 ≤ a)
    (hb0 : 0 < b) (hb1 : b ≤ 1) (c : ℕ) (hc : 2 ≤ c)
    (hcb : 2 * a + 2 ≤ (c : ℝ) * b) (lam n : ℕ) (hx : 2 ≤ lam * n)
    (ε : ℝ) (hε : 0 ≤ ε) :
    qldError a b (registerPower c lam n) (2 ^ fieldBits c lam n : ℕ) ε ≤
      errorProfile (profileCoefficient a c) b (lam * n) ε := by
  apply qldError_le_profile ha hb0 hb1 (by exact_mod_cast (show 1 ≤ c by omega)) hcb
    (by exact_mod_cast (show 1 ≤ lam * n by omega)) (Nat.cast_nonneg _) hε
  · exact_mod_cast canonical_register_upper c lam n hx
  · rw [Real.rpow_natCast]
    exact_mod_cast canonical_field_lower c lam n hx
  · rw [Real.rpow_natCast,
      show (2 : ℝ) * (registerPower c lam n : ℝ) = ((2 * registerPower c lam n : ℕ) : ℝ) by
        push_cast; ring,
      Real.rpow_natCast]
    exact_mod_cast canonical_exponential_lower c lam n hx

/-- The executable sampler can use one even constant meeting the required
tail exponent, independently of the verifier and its index. -/
theorem exists_even_constant (a : ℝ) {b : ℝ} (hb0 : 0 < b) :
    ∃ c : ℕ, 2 ≤ c ∧ Even c ∧ 2 * a + 2 ≤ (c : ℝ) * b := by
  obtain ⟨N, hN⟩ := exists_nat_ge (max 1 ((a + 1) / b))
  have hN1 : 1 ≤ N := by exact_mod_cast ((le_max_left _ _).trans hN)
  have hNb : a + 1 ≤ (N : ℝ) * b :=
    (div_le_iff₀ hb0).mp ((le_max_right _ _).trans hN)
  refine ⟨2 * N, by omega, ⟨N, by omega⟩, ?_⟩
  push_cast
  nlinarith

/-- A single even sampler constant and a single profile coefficient work for
all legal positive indices and all strategy errors. -/
theorem exists_even_parameters {a b : ℝ} (ha : 1 ≤ a) (hb0 : 0 < b) (hb1 : b ≤ 1) :
    ∃ (c : ℕ) (a' : ℝ), 2 ≤ c ∧ Even c ∧ 1 ≤ a' ∧
      ∀ (lam n : ℕ) (ε : ℝ), 2 ≤ lam * n → 0 ≤ ε →
        qldError a b (registerPower c lam n) (2 ^ fieldBits c lam n : ℕ) ε ≤
          errorProfile a' b (lam * n) ε := by
  obtain ⟨c, hc, he, hcb⟩ := exists_even_constant a hb0
  refine ⟨c, profileCoefficient a c, hc, he, profileCoefficient_one_le _ _, ?_⟩
  intro lam n ε hx hε
  exact canonical_qldError_le_profile ha hb0 hb1 c hc hcb lam n hx ε hε

end MIPRE.Introspection.PauliErrorParameters
end

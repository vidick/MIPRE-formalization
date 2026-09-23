/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AdaptivePowerBudget

/-! # Absorbing restriction loss into the introspection error profile

Restriction multiplies the QLD failure by a fixed edge count. The finite-game
argument also needs a budget for the original failure. These lemmas absorb both
changes into constants independent of the verifier index and strategy error.
-/

noncomputable section
namespace MIPRE.Introspection

/-- On the unit interval, the normalized error profile dominates the original
failure, even after increasing that failure by a fixed restriction factor. -/
theorem self_le_errorProfile_scaled {a b c x ε : ℝ}
    (ha : 1 ≤ a) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hc : 1 ≤ c)
    (hx : 1 ≤ x) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ε ≤ errorProfile a b x (c * ε) := by
  have ha0 : 0 ≤ a := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hεc : ε ≤ c * ε := by nlinarith
  have hp := (Real.self_le_rpow_of_le_one hε0 hε1 hb1).trans
    (Real.rpow_le_rpow hε0 hεc hb0)
  have hxa := Real.one_le_rpow hx ha0
  have hn := Real.rpow_nonneg (mul_nonneg hc0 hε0) b
  have hterm : ε ≤ x ^ a * (c * ε) ^ b :=
    hp.trans (by nlinarith)
  have htail := Real.rpow_nonneg hx0 (-b)
  unfold errorProfile
  nlinarith

/-- The normalized profile is already at least one above the unit interval. -/
theorem one_le_errorProfile {a b x ε : ℝ} (ha : 1 ≤ a) (hb : 0 ≤ b)
    (hx : 1 ≤ x) (hε : 1 ≤ ε) : 1 ≤ errorProfile a b x ε := by
  have ha0 : 0 ≤ a := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hxpow := Real.one_le_rpow hx ha0
  have hεpow := Real.one_le_rpow hε hb
  have htail := Real.rpow_nonneg hx0 (-b)
  have hprod : 1 ≤ x ^ a * ε ^ b := by nlinarith
  unfold errorProfile
  nlinarith

/-- A fixed restriction factor and the original-failure budget can both be
absorbed into the two-term profile. The large-error case uses only `v ≥ 0`. -/
theorem errorProfile_of_restricted_bound {C a b c x ε δ v : ℝ} (k : ℕ)
    (hC : 0 ≤ C) (ha : 1 ≤ a) (hb0 : 0 < b) (hb1 : b ≤ 1)
    (hc : 1 ≤ c) (hx : 1 ≤ x) (hε : 0 ≤ ε)
    (hδ : δ ≤ errorProfile a b x (c * ε)) (hv : 0 ≤ v)
    (hvalue : 1 - C * iteratedRoot k (max ε δ) ≤ v) :
    1 - errorProfile
      (powerCoefficient (C * (max 1 (c ^ b)) ^ rootExponent k) a (rootExponent k))
      (b * rootExponent k) x ε ≤ v := by
  by_cases hε1 : ε ≤ 1
  · have hmax : max ε δ ≤ errorProfile a b x (c * ε) := max_le
      (self_le_errorProfile_scaled ha hb0.le hb1 hc hx hε hε1) hδ
    have hp0 := errorProfile_nonneg (a := a) (b := b) (x := x)
      (ε := c * ε) (by linarith) (by linarith) (mul_nonneg (by linarith) hε)
    have hroot := mul_le_mul_of_nonneg_left (iteratedRoot_mono k hmax) hC
    rw [iteratedRoot_eq_rpow k hp0] at hroot
    have hfinal := hroot.trans (errorProfile_scaled_power hC (by linarith)
      (by linarith) (rootExponent_pos k).le (rootExponent_le_one k) hx hε)
    linarith
  · have hlarge := one_le_errorProfile
      (one_le_powerCoefficient (C * (max 1 (c ^ b)) ^ rootExponent k) a (rootExponent k))
      (mul_pos hb0 (rootExponent_pos k)).le hx (le_of_not_ge hε1)
    linarith

end MIPRE.Introspection
end

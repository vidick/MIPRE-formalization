/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Normalizing the final introspection error

The paper's final soundness estimate absorbs any fixed concave power and
constant multiple into `a * (x^a * ε^b + x^(-b))`. The coefficient and the new
exponent are explicit here, including the normalization `a ≥ 1`, `0 < b ≤ 1`.
No induction estimate is assumed or encoded by the definitions in this file.
-/

noncomputable section

namespace MIPRE.Introspection

/-- The two terms of the introspection soundness loss, with `x = λ n`. -/
def errorProfile (a b x ε : ℝ) : ℝ := a * (x ^ a * ε ^ b + x ^ (-b))

theorem errorProfile_nonneg {a b x ε : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) (hε : 0 ≤ ε) :
    0 ≤ errorProfile a b x ε := by unfold errorProfile; positivity

/-- The coefficient prescribed by the paper, enlarged also to be at least one. -/
def powerCoefficient (C a r : ℝ) : ℝ := max 1 (max (C * a ^ r) (a * r))

theorem one_le_powerCoefficient (C a r : ℝ) : 1 ≤ powerCoefficient C a r := le_max_left _ _

theorem mul_rpow_le_powerCoefficient (C a r : ℝ) : C * a ^ r ≤ powerCoefficient C a r :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem mul_le_powerCoefficient (C a r : ℝ) : a * r ≤ powerCoefficient C a r :=
  (le_max_right _ _).trans (le_max_right _ _)

/-- A fixed concave power of the original soundness profile has the required final shape. -/
theorem errorProfile_power {C a b r x ε : ℝ}
    (hC : 0 ≤ C) (ha : 0 ≤ a) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hx : 1 ≤ x) (hε : 0 ≤ ε) :
    C * (errorProfile a b x ε) ^ r ≤
      errorProfile (powerCoefficient C a r) (b * r) x ε := by
  have hx0 : 0 ≤ x := (by norm_num : (0 : ℝ) ≤ 1).trans hx
  have hu : 0 ≤ x ^ a * ε ^ b := mul_nonneg (Real.rpow_nonneg hx0 _) (Real.rpow_nonneg hε _)
  have hv : 0 ≤ x ^ (-b) := Real.rpow_nonneg hx0 _
  have hcoeff : 0 ≤ C * a ^ r := mul_nonneg hC (Real.rpow_nonneg ha _)
  calc
    C * (errorProfile a b x ε) ^ r =
        (C * a ^ r) * (x ^ a * ε ^ b + x ^ (-b)) ^ r := by
      rw [errorProfile, Real.mul_rpow ha (add_nonneg hu hv)]
      ring
    _ ≤ (C * a ^ r) * ((x ^ a * ε ^ b) ^ r + (x ^ (-b)) ^ r) :=
      mul_le_mul_of_nonneg_left (Real.rpow_add_le_add_rpow hu hv hr0 hr1) hcoeff
    _ = (C * a ^ r) * (x ^ (a * r) * ε ^ (b * r) + x ^ (-(b * r))) := by
      rw [Real.mul_rpow (Real.rpow_nonneg hx0 _) (Real.rpow_nonneg hε _),
        ← Real.rpow_mul hx0, ← Real.rpow_mul hε, ← Real.rpow_mul hx0, neg_mul]
    _ ≤ powerCoefficient C a r *
        (x ^ (powerCoefficient C a r) * ε ^ (b * r) + x ^ (-(b * r))) := by
      apply mul_le_mul (mul_rpow_le_powerCoefficient C a r)
      · exact add_le_add
          (mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow_of_exponent_le hx (mul_le_powerCoefficient C a r))
            (Real.rpow_nonneg hε _)) le_rfl
      · positivity
      · exact (by norm_num : (0 : ℝ) ≤ 1).trans (one_le_powerCoefficient C a r)
    _ = errorProfile (powerCoefficient C a r) (b * r) x ε := rfl

/-- The new exponent is positive and at most one whenever the input exponent and power are. -/
theorem power_exponent_bounds {b r : ℝ} (hb0 : 0 < b) (hb1 : b ≤ 1)
    (hr0 : 0 < r) (hr1 : r ≤ 1) : 0 < b * r ∧ b * r ≤ 1 := by
  refine ⟨mul_pos hb0 hr0, ?_⟩
  calc b * r ≤ 1 * r := mul_le_mul_of_nonneg_right hb1 hr0.le
    _ ≤ 1 := by simpa using hr1

/-- Final error absorption, with all constants independent of `x` and `ε`. -/
theorem exists_errorProfile_power {C a b r : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hb0 : 0 < b) (hb1 : b ≤ 1) (hr0 : 0 < r) (hr1 : r ≤ 1) :
    ∃ a' b' : ℝ, 1 ≤ a' ∧ 0 < b' ∧ b' ≤ 1 ∧
      ∀ x ε : ℝ, 1 ≤ x → 0 ≤ ε →
        C * (errorProfile a b x ε) ^ r ≤ errorProfile a' b' x ε := by
  refine ⟨powerCoefficient C a r, b * r, one_le_powerCoefficient C a r,
    (power_exponent_bounds hb0 hb1 hr0 hr1).1,
    (power_exponent_bounds hb0 hb1 hr0 hr1).2, ?_⟩
  intro x ε hx hε
  exact errorProfile_power hC ha hr0.le hr1 hx hε

/-- The exponent after `k` square roots. -/
def rootExponent (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ k

theorem rootExponent_pos (k : ℕ) : 0 < rootExponent k := pow_pos (by norm_num) k

theorem rootExponent_le_one (k : ℕ) : rootExponent k ≤ 1 := by
  exact pow_le_one₀ (by norm_num) (by norm_num)

/-- Applying the square root a fixed finite number of times. -/
def iteratedRoot : ℕ → ℝ → ℝ
  | 0, t => t
  | k + 1, t => Real.sqrt (iteratedRoot k t)

theorem iteratedRoot_eq_rpow (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    iteratedRoot k t = t ^ rootExponent k := by
  induction k with
  | zero => simp [iteratedRoot, rootExponent]
  | succ k ih =>
    rw [iteratedRoot, ih, Real.sqrt_eq_rpow, ← Real.rpow_mul ht]
    simp only [rootExponent, pow_succ]

/-- Every fixed stack of square roots is absorbed with explicit exponent `b / 2^k`. -/
theorem errorProfile_iteratedRoot {C a b x ε : ℝ} (k : ℕ)
    (hC : 0 ≤ C) (ha : 0 ≤ a) (hx : 1 ≤ x) (hε : 0 ≤ ε) :
    C * iteratedRoot k (errorProfile a b x ε) ≤
      errorProfile (powerCoefficient C a (rootExponent k)) (b * rootExponent k) x ε := by
  rw [iteratedRoot_eq_rpow k (errorProfile_nonneg ha (by linarith) hε)]
  exact errorProfile_power hC ha (rootExponent_pos k).le (rootExponent_le_one k) hx hε

/-- A previously proved loss bound can be inserted into the fixed power estimate. -/
theorem errorProfile_power_of_le {C a b r x ε δ : ℝ}
    (hC : 0 ≤ C) (ha : 0 ≤ a) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hx : 1 ≤ x) (hε : 0 ≤ ε) (hδ0 : 0 ≤ δ) (hδ : δ ≤ errorProfile a b x ε) :
    C * δ ^ r ≤ errorProfile (powerCoefficient C a r) (b * r) x ε := by
  exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hδ0 hδ hr0) hC).trans
    (errorProfile_power hC ha hr0 hr1 hx hε)

/-- Scaling the test error, as happens in detyping, changes only a fixed coefficient. -/
theorem errorProfile_scale_input {a b c x ε : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hx : 0 ≤ x) (hε : 0 ≤ ε) :
    errorProfile a b x (c * ε) ≤ max 1 (c ^ b) * errorProfile a b x ε := by
  have hu : 0 ≤ x ^ a * ε ^ b := mul_nonneg (Real.rpow_nonneg hx _) (Real.rpow_nonneg hε _)
  have hv : 0 ≤ x ^ (-b) := Real.rpow_nonneg hx _
  have hfirst := mul_le_mul_of_nonneg_right (le_max_right 1 (c ^ b)) hu
  have hsecond := mul_le_mul_of_nonneg_right (le_max_left 1 (c ^ b)) hv
  unfold errorProfile
  rw [Real.mul_rpow hc hε]
  calc
    a * (x ^ a * (c ^ b * ε ^ b) + x ^ (-b)) ≤
        a * (max 1 (c ^ b) * (x ^ a * ε ^ b) + max 1 (c ^ b) * x ^ (-b)) := by
      apply mul_le_mul_of_nonneg_left _ ha
      nlinarith only [hfirst, hsecond]
    _ = max 1 (c ^ b) * (a * (x ^ a * ε ^ b + x ^ (-b))) := by ring

/-- Constant rescaling of the input error followed by a concave power is absorbed too. -/
theorem errorProfile_scaled_power {C a b c r x ε : ℝ}
    (hC : 0 ≤ C) (ha : 0 ≤ a) (hc : 0 ≤ c) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hx : 1 ≤ x) (hε : 0 ≤ ε) :
    C * (errorProfile a b x (c * ε)) ^ r ≤
      errorProfile (powerCoefficient (C * (max 1 (c ^ b)) ^ r) a r) (b * r) x ε := by
  have hx0 : 0 ≤ x := (by norm_num : (0 : ℝ) ≤ 1).trans hx
  have hscale := Real.rpow_le_rpow (errorProfile_nonneg (b := b) ha hx0 (mul_nonneg hc hε))
    (errorProfile_scale_input (b := b) ha hc hx0 hε) hr0
  have hk : 0 ≤ max 1 (c ^ b) := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  rw [Real.mul_rpow hk (errorProfile_nonneg ha hx0 hε)] at hscale
  have h := mul_le_mul_of_nonneg_left hscale hC
  rw [← mul_assoc] at h
  exact h.trans (errorProfile_power (mul_nonneg hC (Real.rpow_nonneg hk _))
    ha hr0 hr1 hx hε)

/-- The state replacement cost used at the end of soundness remains a square-root loss. -/
theorem state_transfer_loss_le_three_sqrt {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    δ + 2 * Real.sqrt δ ≤ 3 * Real.sqrt δ := by
  have hs := Real.sq_sqrt hδ0
  have hroot := Real.sqrt_nonneg δ
  have hroot1 : Real.sqrt δ ≤ 1 := by nlinarith
  nlinarith [sq_nonneg (Real.sqrt δ - 1)]

/-- One may choose the final exponent strictly below one by taking a strict concave power. -/
theorem power_exponent_lt_one {b r : ℝ} (hb1 : b ≤ 1) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    b * r < 1 := by
  exact (mul_le_mul_of_nonneg_right hb1 hr0).trans_lt (by simpa using hr1)

end MIPRE.Introspection

end

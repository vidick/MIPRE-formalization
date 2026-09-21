/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.ErrorBounds

/-! # One common quantitative budget for the adaptive stage

The three actual-test estimates share one budget. The malformed-answer
contribution is included in the marginal constant. The replacement loss
has three square roots, and the same recurrence can be used at every level.
-/

namespace MIPRE.Introspection

/-- `e` is ordered-edge count times game failure; `z` and `h` are the
primitive Z and fixed hiding errors. `r` is the remaining CL depth. -/
def adaptiveStageBudget (r : ℕ) (e z h : ℝ) : ℝ :=
  64 * z + (512 * (r : ℝ) ^ 2 + 224) * e + 64 * h

theorem adaptiveStageBudget_nonneg (r : ℕ) {e z h : ℝ}
    (he : 0 ≤ e) (hz : 0 ≤ z) (hh : 0 ≤ h) :
    0 ≤ adaptiveStageBudget r e z h := by
  unfold adaptiveStageBudget
  positivity

theorem marginal_le_adaptiveStageBudget (r : ℕ) {e z h : ℝ}
    (he : 0 ≤ e) (hz : 0 ≤ z) (hh : 0 ≤ h) :
    16 * z + 56 * e ≤ adaptiveStageBudget r e z h := by
  unfold adaptiveStageBudget
  nlinarith [mul_nonneg (sq_nonneg (r : ℝ)) he]

theorem Z_le_adaptiveStageBudget (r : ℕ) {e z h : ℝ}
    (he : 0 ≤ e) (hh : 0 ≤ h) :
    64 * z + 224 * e ≤ adaptiveStageBudget r e z h := by
  unfold adaptiveStageBudget
  nlinarith [mul_nonneg (sq_nonneg (r : ℝ)) he]

theorem X_le_adaptiveStageBudget (r : ℕ) {e z h : ℝ}
    (he : 0 ≤ e) (hz : 0 ≤ z) :
    16 * ((32 * (r : ℝ) ^ 2 + 6) * e + 4 * h) ≤
      adaptiveStageBudget r e z h := by
  unfold adaptiveStageBudget
  nlinarith

/-- The exact game-value loss from mixing, common-ancilla dilation, and
projective measurement replacement. -/
noncomputable def adaptiveStepLoss (δ : ℝ) : ℝ :=
  2 * Real.sqrt (2 * Real.sqrt (56 * Real.sqrt δ))

theorem adaptiveStepLoss_nonneg (δ : ℝ) : 0 ≤ adaptiveStepLoss δ := by
  unfold adaptiveStepLoss
  positivity

theorem adaptiveStepLoss_mono {δ η : ℝ} (h : δ ≤ η) :
    adaptiveStepLoss δ ≤ adaptiveStepLoss η := by
  unfold adaptiveStepLoss
  gcongr

/-- One replacement costs at most eight times the third iterated square
root of the common stage budget, with a universal coefficient. -/
theorem adaptiveStepLoss_le_root (δ : ℝ) :
    adaptiveStepLoss δ ≤ 8 * iteratedRoot 3 δ := by
  have h₁ : Real.sqrt (56 * Real.sqrt δ) ≤ 8 * Real.sqrt (Real.sqrt δ) := by
    calc
      _ ≤ Real.sqrt (64 * Real.sqrt δ) := by
        apply Real.sqrt_le_sqrt
        nlinarith [Real.sqrt_nonneg δ]
      _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 64)]; norm_num
  unfold adaptiveStepLoss
  calc
    _ ≤ 2 * Real.sqrt (16 * Real.sqrt (Real.sqrt δ)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.sqrt_le_sqrt
      linarith
    _ = _ := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)]
      norm_num [iteratedRoot]
      ring

/-- An explicit failure recurrence with fixed primitive errors. It records
the loss from each replacement; constructing the strategies is separate. -/
noncomputable def adaptiveFailureBudget (r : ℕ) (edges z h initial : ℝ) : ℕ → ℝ
  | 0 => initial
  | n + 1 => let e := adaptiveFailureBudget r edges z h initial n
      e + adaptiveStepLoss (adaptiveStageBudget r (edges * e) z h)

theorem adaptiveFailureBudget_step (r n : ℕ) (edges z h initial : ℝ) :
    adaptiveFailureBudget r edges z h initial (n + 1) =
      adaptiveFailureBudget r edges z h initial n +
        adaptiveStepLoss (adaptiveStageBudget r
          (edges * adaptiveFailureBudget r edges z h initial n) z h) := rfl

theorem adaptiveFailureBudget_mono (r : ℕ) (edges z h initial : ℝ) :
    Monotone (adaptiveFailureBudget r edges z h initial) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [adaptiveFailureBudget_step]
  exact le_add_of_nonneg_right (adaptiveStepLoss_nonneg _)

end MIPRE.Introspection

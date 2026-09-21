/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AdaptiveStageBudget

/-! # A positive small-error threshold for every adaptive stage

The failure recurrence has an explicit inverse threshold. For any fixed
depth and number of replacements, sufficiently small initial and primitive
errors keep every common stage budget at most one. The construction uses
the proved triple-square-root replacement loss; no stage-smallness premise
is built into the threshold.
-/

noncomputable section
namespace MIPRE.Introspection

theorem adaptiveStageBudget_mono_depth {r s : ℕ} (hrs : r ≤ s)
    {e z h : ℝ} (he : 0 ≤ e) :
    adaptiveStageBudget r e z h ≤ adaptiveStageBudget s e z h := by
  have hrs' : (r : ℝ) ≤ (s : ℝ) := by exact_mod_cast hrs
  have hsquare : (r : ℝ) ^ 2 ≤ (s : ℝ) ^ 2 := by
    nlinarith [(show (0 : ℝ) ≤ r from Nat.cast_nonneg r),
      (show (0 : ℝ) ≤ s from Nat.cast_nonneg s)]
  have hc : (512 * (r : ℝ) ^ 2 + 224) * e ≤
      (512 * (s : ℝ) ^ 2 + 224) * e :=
    mul_le_mul_of_nonneg_right (by linarith) he
  unfold adaptiveStageBudget
  linarith

theorem adaptiveStageBudget_mono_errors (r : ℕ)
    {e e' z z' h h' : ℝ} (he : e ≤ e') (hz : z ≤ z') (hh : h ≤ h') :
    adaptiveStageBudget r e z h ≤ adaptiveStageBudget r e' z' h' := by
  unfold adaptiveStageBudget
  exact add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hz (by norm_num))
    (mul_le_mul_of_nonneg_left he (by positivity)))
    (mul_le_mul_of_nonneg_left hh (by norm_num))

theorem adaptiveFailureBudget_nonneg (r n : ℕ) (edges z h : ℝ)
    {initial : ℝ} (hi : 0 ≤ initial) :
    0 ≤ adaptiveFailureBudget r edges z h initial n := by
  exact hi.trans (adaptiveFailureBudget_mono r edges z h initial (Nat.zero_le n))

/-- Increasing any recurrence parameter increases the resulting failure
bound. Only the original edge multiplier and initial failure need be
nonnegative; the square-root losses themselves are always nonnegative. -/
theorem adaptiveFailureBudget_mono_parameters {r s : ℕ} (hrs : r ≤ s)
    {edges edges' z z' h h' initial initial' : ℝ}
    (hE : 0 ≤ edges) (hEE : edges ≤ edges') (hz : z ≤ z') (hh : h ≤ h')
    (hi0 : 0 ≤ initial) (hi : initial ≤ initial') (n : ℕ) :
    adaptiveFailureBudget r edges z h initial n ≤
      adaptiveFailureBudget s edges' z' h' initial' n := by
  induction n with
  | zero => exact hi
  | succ n ih =>
    rw [adaptiveFailureBudget_step, adaptiveFailureBudget_step]
    apply add_le_add ih
    apply adaptiveStepLoss_mono
    have hn := adaptiveFailureBudget_nonneg r n edges z h hi0
    exact (adaptiveStageBudget_mono_depth hrs (mul_nonneg hE hn)).trans
      (adaptiveStageBudget_mono_errors s
        (mul_le_mul hEE ih hn (hE.trans hEE)) hz hh)

/-- A coefficient controlling the whole stage when its three error inputs
are all at most the same number. -/
def adaptiveBudgetCoefficient (r : ℕ) (edges : ℝ) : ℝ :=
  (512 * (r : ℝ) ^ 2 + 224) * edges + 128

theorem adaptiveBudgetCoefficient_pos (r : ℕ) {edges : ℝ} (hE : 0 ≤ edges) :
    0 < adaptiveBudgetCoefficient r edges := by
  unfold adaptiveBudgetCoefficient
  positivity

theorem adaptiveStageBudget_le_coefficient (r : ℕ) {edges f z h t : ℝ}
    (hE : 0 ≤ edges) (hf : f ≤ t) (hz : z ≤ t) (hh : h ≤ t) :
    adaptiveStageBudget r (edges * f) z h ≤ adaptiveBudgetCoefficient r edges * t := by
  calc
    _ ≤ adaptiveStageBudget r (edges * t) t t :=
      adaptiveStageBudget_mono_errors r (mul_le_mul_of_nonneg_left hf hE) hz hh
    _ = _ := by unfold adaptiveStageBudget adaptiveBudgetCoefficient; ring

/-- A stack of three square roots exactly inverts the eighth power on
nonnegative inputs. -/
theorem iteratedRoot_three_pow_eight {t : ℝ} (ht : 0 ≤ t) :
    iteratedRoot 3 (t ^ 8) = t := by
  have h8 : t ^ 8 = (t ^ 4) ^ 2 := by ring
  have h4 : t ^ 4 = (t ^ 2) ^ 2 := by ring
  simp only [iteratedRoot]
  rw [h8, Real.sqrt_sq (by positivity : 0 ≤ t ^ 4), h4,
    Real.sqrt_sq (sq_nonneg t), Real.sqrt_sq ht]

/-- Explicit inverse thresholds. The half-size term controls the old
failure and the eighth-power term controls the new replacement loss. -/
def adaptiveSmallThreshold (r : ℕ) (edges : ℝ) : ℕ → ℝ
  | 0 => 1 / adaptiveBudgetCoefficient r edges
  | n + 1 => min (adaptiveSmallThreshold r edges n / 2)
      ((adaptiveSmallThreshold r edges n / 16) ^ 8 / adaptiveBudgetCoefficient r edges)

theorem adaptiveSmallThreshold_pos (r n : ℕ) {edges : ℝ} (hE : 0 ≤ edges) :
    0 < adaptiveSmallThreshold r edges n := by
  have hC := adaptiveBudgetCoefficient_pos r hE
  induction n with
  | zero => exact div_pos (by norm_num) hC
  | succ n ih =>
    exact lt_min (div_pos ih (by norm_num))
      (div_pos (pow_pos (div_pos ih (by norm_num)) _) hC)

theorem adaptiveSmallThreshold_antitone (r : ℕ) {edges : ℝ} (hE : 0 ≤ edges) :
    Antitone (adaptiveSmallThreshold r edges) := by
  apply antitone_nat_of_succ_le
  intro n
  calc
    adaptiveSmallThreshold r edges (n + 1) ≤ adaptiveSmallThreshold r edges n / 2 :=
      min_le_left _ _
    _ ≤ adaptiveSmallThreshold r edges n := by
      linarith [adaptiveSmallThreshold_pos r n hE]

/-- One actual numerical recurrence step consumes exactly one inverse
threshold level. In particular, this is derived from the replacement loss
formula, rather than requiring the desired next bound as a hypothesis. -/
theorem adaptiveFailure_step_le_threshold (r n : ℕ) {edges f z h : ℝ}
    (hE : 0 ≤ edges)
    (hf : f ≤ adaptiveSmallThreshold r edges (n + 1))
    (hz : z ≤ adaptiveSmallThreshold r edges (n + 1))
    (hh : h ≤ adaptiveSmallThreshold r edges (n + 1)) :
    f + adaptiveStepLoss (adaptiveStageBudget r (edges * f) z h) ≤
      adaptiveSmallThreshold r edges n := by
  have hC := adaptiveBudgetCoefficient_pos r hE
  have ht := (adaptiveSmallThreshold_pos r n hE).le
  have hs₁ : adaptiveSmallThreshold r edges (n + 1) ≤
      adaptiveSmallThreshold r edges n / 2 := min_le_left _ _
  have hs₂ : adaptiveSmallThreshold r edges (n + 1) ≤
      (adaptiveSmallThreshold r edges n / 16) ^ 8 / adaptiveBudgetCoefficient r edges :=
    min_le_right _ _
  have hb : adaptiveStageBudget r (edges * f) z h ≤
      (adaptiveSmallThreshold r edges n / 16) ^ 8 := by
    refine (adaptiveStageBudget_le_coefficient r hE hf hz hh).trans ?_
    have hs := (le_div_iff₀ hC).mp hs₂
    simpa only [mul_comm] using hs
  have hl := (adaptiveStepLoss_mono hb).trans
    (adaptiveStepLoss_le_root ((adaptiveSmallThreshold r edges n / 16) ^ 8))
  rw [iteratedRoot_three_pow_eight (div_nonneg ht (by norm_num))] at hl
  linarith

/-- If all three initial errors fit the depth-N threshold, the failure
after n replacements fits the threshold with N-n levels remaining. -/
theorem adaptiveFailureBudget_le_threshold (r N : ℕ) {edges z h initial : ℝ}
    (hE : 0 ≤ edges) (hi : initial ≤ adaptiveSmallThreshold r edges N)
    (hz : z ≤ adaptiveSmallThreshold r edges N)
    (hh : h ≤ adaptiveSmallThreshold r edges N) :
    ∀ n, n ≤ N → adaptiveFailureBudget r edges z h initial n ≤
      adaptiveSmallThreshold r edges (N - n) := by
  intro n
  induction n with
  | zero => intro _; simpa only [adaptiveFailureBudget, Nat.sub_zero] using hi
  | succ n ih =>
    intro hn
    have hn' : n ≤ N := (Nat.le_succ n).trans hn
    have hsub : N - n = (N - (n + 1)) + 1 := by omega
    have hlevel : (N - (n + 1)) + 1 ≤ N := by omega
    have ht := adaptiveSmallThreshold_antitone r hE hlevel
    have hf : adaptiveFailureBudget r edges z h initial n ≤
        adaptiveSmallThreshold r edges ((N - (n + 1)) + 1) := by
      simpa only [hsub] using ih hn'
    rw [adaptiveFailureBudget_step]
    exact adaptiveFailure_step_le_threshold r (N - (n + 1)) hE hf
      (hz.trans ht) (hh.trans ht)

/-- An explicit sufficient condition for every stage budget required by a
finite adaptive iteration, including the final numerical bound. -/
theorem adaptiveStageBudget_le_one_of_threshold (r N : ℕ) {edges z h initial : ℝ}
    (hE : 0 ≤ edges) (hi : initial ≤ adaptiveSmallThreshold r edges N)
    (hz : z ≤ adaptiveSmallThreshold r edges N)
    (hh : h ≤ adaptiveSmallThreshold r edges N)
    (n : ℕ) (hn : n ≤ N) :
    adaptiveStageBudget r (edges * adaptiveFailureBudget r edges z h initial n) z h ≤ 1 := by
  have hC := adaptiveBudgetCoefficient_pos r hE
  have ht₀ := adaptiveSmallThreshold_antitone r hE (Nat.zero_le N)
  have htn := adaptiveSmallThreshold_antitone r hE (Nat.zero_le (N - n))
  have hf := (adaptiveFailureBudget_le_threshold r N hE hi hz hh n hn).trans htn
  calc
    _ ≤ adaptiveBudgetCoefficient r edges * adaptiveSmallThreshold r edges 0 :=
      adaptiveStageBudget_le_coefficient r hE hf (hz.trans ht₀) (hh.trans ht₀)
    _ = 1 := by simp [adaptiveSmallThreshold, ne_of_gt hC]

/-- For every finite depth there is a strictly positive, explicitly defined
uniform error threshold making all recurrence stage budgets admissible. -/
theorem exists_adaptive_small_threshold (r N : ℕ) {edges : ℝ} (hE : 0 ≤ edges) :
    ∃ t : ℝ, 0 < t ∧ ∀ initial z h : ℝ, initial ≤ t → z ≤ t → h ≤ t →
      ∀ n, n ≤ N →
        adaptiveStageBudget r (edges * adaptiveFailureBudget r edges z h initial n) z h ≤ 1 := by
  refine ⟨adaptiveSmallThreshold r edges N, adaptiveSmallThreshold_pos r N hE, ?_⟩
  intro initial z h hi hz hh n hn
  exact adaptiveStageBudget_le_one_of_threshold r N hE hi hz hh n hn

end MIPRE.Introspection
end

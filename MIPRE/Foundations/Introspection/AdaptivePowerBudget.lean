/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AdaptiveIterationBudget

/-! # Power bounds for the full finite adaptive recurrence

Each replacement introduces three square roots. For any fixed number of
replacements the actual failure recurrence is bounded by an explicit
constant times the corresponding iterated root of a common primitive
error. A second explicit coefficient makes this bound at least one outside
the proved admissible small-error regime. These numerical statements do not
assume the existence or soundness of the strategy construction.
-/

noncomputable section
namespace MIPRE.Introspection

theorem iteratedRoot_nonneg (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ iteratedRoot n t := by
  cases n with
  | zero => exact ht
  | succ n => exact Real.sqrt_nonneg _

theorem iteratedRoot_pos (n : ℕ) {t : ℝ} (ht : 0 < t) :
    0 < iteratedRoot n t := by
  induction n with
  | zero => exact ht
  | succ n ih => exact Real.sqrt_pos.mpr ih

theorem iteratedRoot_mono (n : ℕ) : Monotone (iteratedRoot n) := by
  induction n with
  | zero => exact fun _ _ h => h
  | succ n ih => exact fun _ _ h => Real.sqrt_le_sqrt (ih h)

theorem iteratedRoot_one (n : ℕ) : iteratedRoot n 1 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [iteratedRoot, ih, Real.sqrt_one]

theorem iteratedRoot_le_one (n : ℕ) {t : ℝ} (ht : t ≤ 1) :
    iteratedRoot n t ≤ 1 := by
  simpa only [iteratedRoot_one] using iteratedRoot_mono n ht

theorem iteratedRoot_add (m n : ℕ) (t : ℝ) :
    iteratedRoot (m + n) t = iteratedRoot m (iteratedRoot n t) := by
  induction m with
  | zero => simp only [Nat.zero_add, iteratedRoot]
  | succ m ih => simp only [Nat.succ_add, iteratedRoot, ih]

private theorem self_le_sqrt_of_unit {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t ≤ Real.sqrt t := by
  have hs := Real.sq_sqrt ht0
  have hr0 := Real.sqrt_nonneg t
  have hr1 := Real.sqrt_le_one.mpr ht1
  nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hr1)]

theorem self_le_iteratedRoot (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t ≤ iteratedRoot n t := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    exact ih.trans (self_le_sqrt_of_unit (iteratedRoot_nonneg n ht0)
      (iteratedRoot_le_one n ht1))

private theorem sqrt_scale_le {c t : ℝ} (hc : 1 ≤ c) :
    Real.sqrt (c * t) ≤ c * Real.sqrt t := by
  rw [Real.sqrt_mul (by linarith : 0 ≤ c)]
  exact mul_le_mul_of_nonneg_right
    (Real.sqrt_le_self_iff.mpr (Or.inr hc)) (Real.sqrt_nonneg t)

/-- A coefficient at least one can be kept unchanged through any fixed
stack of square roots, which is convenient for explicit uniform constants. -/
theorem iteratedRoot_scale_le (n : ℕ) {c t : ℝ} (hc : 1 ≤ c) :
    iteratedRoot n (c * t) ≤ c * iteratedRoot n t := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact (Real.sqrt_le_sqrt ih).trans (sqrt_scale_le hc)

theorem adaptiveBudgetCoefficient_one_le (r : ℕ) {edges : ℝ} (hE : 0 ≤ edges) :
    1 ≤ adaptiveBudgetCoefficient r edges := by
  have hm : 0 ≤ (512 * (r : ℝ) ^ 2 + 224) * edges := by positivity
  unfold adaptiveBudgetCoefficient
  linarith

/-- The coefficient accumulated per replacement in a simple power bound. -/
def adaptivePowerCoefficient (r : ℕ) (edges : ℝ) : ℝ :=
  1 + 8 * adaptiveBudgetCoefficient r edges

theorem adaptivePowerCoefficient_one_le (r : ℕ) {edges : ℝ} (hE : 0 ≤ edges) :
    1 ≤ adaptivePowerCoefficient r edges := by
  unfold adaptivePowerCoefficient
  linarith [adaptiveBudgetCoefficient_pos r hE]

/-- The actual finite recurrence has exponent `8^(-n)`. This estimate has
no stage-admissibility premise and works for any fixed number of steps,
including two full local iterations. -/
theorem adaptiveFailureBudget_le_power (r n : ℕ) {edges z h initial t : ℝ}
    (hE : 0 ≤ edges) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hi : initial ≤ t) (hz : z ≤ t) (hh : h ≤ t) :
    adaptiveFailureBudget r edges z h initial n ≤
      adaptivePowerCoefficient r edges ^ n * iteratedRoot (3 * n) t := by
  have hC := adaptiveBudgetCoefficient_one_le r hE
  have hK := adaptivePowerCoefficient_one_le r hE
  induction n with
  | zero => simpa only [adaptiveFailureBudget, pow_zero, Nat.mul_zero,
      iteratedRoot, one_mul] using hi
  | succ n ih =>
    have hKn : 1 ≤ adaptivePowerCoefficient r edges ^ n := one_le_pow₀ hK
    have hKn0 : 0 ≤ adaptivePowerCoefficient r edges ^ n := by linarith
    have hRn0 := iteratedRoot_nonneg (3 * n) ht0
    have hRn1 := iteratedRoot_le_one (3 * n) ht1
    have htR : t ≤ adaptivePowerCoefficient r edges ^ n * iteratedRoot (3 * n) t := by
      calc
        t ≤ iteratedRoot (3 * n) t := self_le_iteratedRoot _ ht0 ht1
        _ ≤ adaptivePowerCoefficient r edges ^ n * iteratedRoot (3 * n) t := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hKn) hRn0]
    have hb := adaptiveStageBudget_le_coefficient r hE ih (hz.trans htR) (hh.trans htR)
    have hCK : 1 ≤ adaptiveBudgetCoefficient r edges * adaptivePowerCoefficient r edges ^ n := by
      calc
        (1 : ℝ) = 1 * 1 := by ring
        _ ≤ adaptiveBudgetCoefficient r edges * adaptivePowerCoefficient r edges ^ n :=
          mul_le_mul hC hKn (by norm_num) (by linarith)
    have hs := iteratedRoot_scale_le 3
      (t := iteratedRoot (3 * n) t) hCK
    have hl := (adaptiveStepLoss_mono hb).trans
      (adaptiveStepLoss_le_root
        (adaptiveBudgetCoefficient r edges *
          (adaptivePowerCoefficient r edges ^ n * iteratedRoot (3 * n) t)))
    have hl' : adaptiveStepLoss (adaptiveStageBudget r
        (edges * adaptiveFailureBudget r edges z h initial n) z h) ≤
        8 * (adaptiveBudgetCoefficient r edges * adaptivePowerCoefficient r edges ^ n) *
          iteratedRoot 3 (iteratedRoot (3 * n) t) := by
      apply hl.trans
      have hmul := mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 8)
      simpa only [mul_assoc] using hmul
    have hpre := ih.trans (mul_le_mul_of_nonneg_left
      (self_le_iteratedRoot 3 hRn0 hRn1) hKn0)
    have he : iteratedRoot (3 * (n + 1)) t = iteratedRoot 3 (iteratedRoot (3 * n) t) := by
      rw [show 3 * (n + 1) = 3 + 3 * n by omega, iteratedRoot_add]
    rw [adaptiveFailureBudget_step]
    calc
      _ ≤ adaptivePowerCoefficient r edges ^ n * iteratedRoot 3 (iteratedRoot (3 * n) t) +
          8 * (adaptiveBudgetCoefficient r edges * adaptivePowerCoefficient r edges ^ n) *
            iteratedRoot 3 (iteratedRoot (3 * n) t) := add_le_add hpre hl'
      _ = _ := by rw [he, pow_succ]; unfold adaptivePowerCoefficient; ring

/-- A direct paper-profile corollary for the accumulated recurrence in the
unit-error regime. All coefficients are fixed before `x` and `ε` are chosen. -/
theorem adaptiveFailureBudget_le_errorProfile (r n : ℕ)
    {edges z h initial a b x ε : ℝ}
    (hE : 0 ≤ edges) (ha : 0 ≤ a) (hx : 1 ≤ x) (hε : 0 ≤ ε)
    (ht1 : errorProfile a b x ε ≤ 1)
    (hi : initial ≤ errorProfile a b x ε)
    (hz : z ≤ errorProfile a b x ε) (hh : h ≤ errorProfile a b x ε) :
    adaptiveFailureBudget r edges z h initial n ≤
      errorProfile (powerCoefficient (adaptivePowerCoefficient r edges ^ n) a
        (rootExponent (3 * n))) (b * rootExponent (3 * n)) x ε := by
  have ht0 := errorProfile_nonneg (b := b) ha (by linarith : 0 ≤ x) hε
  exact (adaptiveFailureBudget_le_power r n hE ht0 ht1 hi hz hh).trans
    (errorProfile_iteratedRoot (3 * n)
      (pow_nonneg (by linarith [adaptivePowerCoefficient_one_le r hE]) n) ha hx hε)

theorem adaptiveSmallThreshold_le_one (r n : ℕ) {edges : ℝ} (hE : 0 ≤ edges) :
    adaptiveSmallThreshold r edges n ≤ 1 := by
  have hC := adaptiveBudgetCoefficient_pos r hE
  calc
    _ ≤ adaptiveSmallThreshold r edges 0 :=
      adaptiveSmallThreshold_antitone r hE (Nat.zero_le n)
    _ ≤ 1 := by
      change 1 / adaptiveBudgetCoefficient r edges ≤ 1
      exact (div_le_iff₀ hC).mpr (by simpa only [one_mul] using
        adaptiveBudgetCoefficient_one_le r hE)

/-- This fixed coefficient also pays for the trivial probability bound
outside the admissible regime. The denominator is strictly positive. -/
def adaptiveSoundnessCoefficient (r : ℕ) (edges : ℝ) (n : ℕ) : ℝ :=
  max (adaptivePowerCoefficient r edges ^ n)
    (1 / iteratedRoot (3 * n) (adaptiveSmallThreshold r edges n))

theorem adaptiveSoundnessCoefficient_one_le (r n : ℕ) {edges : ℝ} (hE : 0 ≤ edges) :
    1 ≤ adaptiveSoundnessCoefficient r edges n :=
  (one_le_pow₀ (adaptivePowerCoefficient_one_le r hE)).trans (le_max_left _ _)

theorem adaptiveFailureBudget_le_soundness_power (r n : ℕ)
    {edges z h initial t : ℝ} (hE : 0 ≤ edges) (ht0 : 0 ≤ t)
    (ht : t ≤ adaptiveSmallThreshold r edges n)
    (hi : initial ≤ t) (hz : z ≤ t) (hh : h ≤ t) :
    adaptiveFailureBudget r edges z h initial n ≤
      adaptiveSoundnessCoefficient r edges n * iteratedRoot (3 * n) t := by
  exact (adaptiveFailureBudget_le_power r n hE ht0
    (ht.trans (adaptiveSmallThreshold_le_one r n hE)) hi hz hh).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (iteratedRoot_nonneg _ ht0))

/-- If the common input error exceeds the explicit admissible threshold,
the same soundness power bound is at least one. -/
theorem one_le_soundness_power_of_threshold_le (r n : ℕ) {edges t : ℝ}
    (hE : 0 ≤ edges) (ht : adaptiveSmallThreshold r edges n ≤ t) :
    1 ≤ adaptiveSoundnessCoefficient r edges n * iteratedRoot (3 * n) t := by
  have hroot := iteratedRoot_pos (3 * n) (adaptiveSmallThreshold_pos r n hE)
  have hrootle := iteratedRoot_mono (3 * n) ht
  have hroot0 : 0 ≤ iteratedRoot (3 * n) t := hroot.le.trans hrootle
  calc
    (1 : ℝ) = (1 / iteratedRoot (3 * n) (adaptiveSmallThreshold r edges n)) *
        iteratedRoot (3 * n) (adaptiveSmallThreshold r edges n) := by
      simp [ne_of_gt hroot]
    _ ≤ (1 / iteratedRoot (3 * n) (adaptiveSmallThreshold r edges n)) *
        iteratedRoot (3 * n) t :=
      mul_le_mul_of_nonneg_left hrootle (by positivity)
    _ ≤ adaptiveSoundnessCoefficient r edges n * iteratedRoot (3 * n) t :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hroot0

/-- A nonvacuous power bound automatically implies the concrete smallness
needed by the existing strategy constructor. -/
theorem threshold_of_soundness_power_lt_one (r n : ℕ) {edges t : ℝ}
    (hE : 0 ≤ edges)
    (ht : adaptiveSoundnessCoefficient r edges n * iteratedRoot (3 * n) t < 1) :
    t < adaptiveSmallThreshold r edges n := by
  by_contra hn
  exact (not_le_of_gt ht) (one_le_soundness_power_of_threshold_le r n hE (le_of_not_gt hn))

/-- The full numerical dichotomy for any finite number of replacements:
either the original admissibility threshold holds and the actual recurrence
is bounded, or the very same power bound makes probability loss vacuous. -/
theorem adaptiveSoundness_power_cases (r n : ℕ) {edges z h initial t : ℝ}
    (hE : 0 ≤ edges) (ht0 : 0 ≤ t)
    (hi : initial ≤ t) (hz : z ≤ t) (hh : h ≤ t) :
    (t ≤ adaptiveSmallThreshold r edges n ∧
      adaptiveFailureBudget r edges z h initial n ≤
        adaptiveSoundnessCoefficient r edges n * iteratedRoot (3 * n) t) ∨
      1 ≤ adaptiveSoundnessCoefficient r edges n * iteratedRoot (3 * n) t := by
  by_cases ht : t ≤ adaptiveSmallThreshold r edges n
  · exact Or.inl ⟨ht, adaptiveFailureBudget_le_soundness_power r n hE ht0 ht hi hz hh⟩
  · exact Or.inr (one_le_soundness_power_of_threshold_le r n hE (le_of_not_ge ht))

/-- The uniform power controlling both numerical regimes has exactly the
paper's required two-term profile after fixed-power absorption. -/
theorem adaptiveSoundness_power_le_errorProfile (r n : ℕ)
    {edges a b x ε : ℝ} (hE : 0 ≤ edges) (ha : 0 ≤ a)
    (hx : 1 ≤ x) (hε : 0 ≤ ε) :
    adaptiveSoundnessCoefficient r edges n * iteratedRoot (3 * n) (errorProfile a b x ε) ≤
      errorProfile (powerCoefficient (adaptiveSoundnessCoefficient r edges n) a
        (rootExponent (3 * n))) (b * rootExponent (3 * n)) x ε :=
  errorProfile_iteratedRoot (3 * n)
    (by linarith [adaptiveSoundnessCoefficient_one_le r n hE]) ha hx hε

/-- The paper-shaped error bound directly separates the constructible
small-error regime from the trivial large-error regime. -/
theorem adaptiveSoundness_errorProfile_cases (r n : ℕ)
    {edges z h initial a b x ε : ℝ}
    (hE : 0 ≤ edges) (ha : 0 ≤ a) (hx : 1 ≤ x) (hε : 0 ≤ ε)
    (hi : initial ≤ errorProfile a b x ε)
    (hz : z ≤ errorProfile a b x ε) (hh : h ≤ errorProfile a b x ε) :
    let a' := powerCoefficient (adaptiveSoundnessCoefficient r edges n) a (rootExponent (3 * n))
    let b' := b * rootExponent (3 * n)
    (errorProfile a b x ε ≤ adaptiveSmallThreshold r edges n ∧
      adaptiveFailureBudget r edges z h initial n ≤ errorProfile a' b' x ε) ∨
      1 ≤ errorProfile a' b' x ε := by
  dsimp only
  have hp := adaptiveSoundness_power_le_errorProfile (b := b) r n hE ha hx hε
  rcases adaptiveSoundness_power_cases r n hE
    (errorProfile_nonneg (b := b) ha (by linarith : 0 ≤ x) hε) hi hz hh with hsmall | hlarge
  · exact Or.inl ⟨hsmall.1, hsmall.2.trans hp⟩
  · exact Or.inr (hlarge.trans hp)

/-- Constants for the final soundness profile depend only on fixed depth,
edge count, number of replacements, and the primitive profile constants. -/
theorem exists_adaptiveSoundness_errorProfile (r n : ℕ) {edges a b : ℝ}
    (hE : 0 ≤ edges) (ha : 0 ≤ a) (hb0 : 0 < b) (hb1 : b ≤ 1) :
    ∃ a' b' : ℝ, 1 ≤ a' ∧ 0 < b' ∧ b' ≤ 1 ∧
      ∀ x ε : ℝ, 1 ≤ x → 0 ≤ ε →
        adaptiveSoundnessCoefficient r edges n *
          iteratedRoot (3 * n) (errorProfile a b x ε) ≤ errorProfile a' b' x ε := by
  refine ⟨powerCoefficient (adaptiveSoundnessCoefficient r edges n) a (rootExponent (3 * n)),
    b * rootExponent (3 * n), one_le_powerCoefficient _ _ _,
    (power_exponent_bounds hb0 hb1 (rootExponent_pos _) (rootExponent_le_one _)).1,
    (power_exponent_bounds hb0 hb1 (rootExponent_pos _) (rootExponent_le_one _)).2, ?_⟩
  intro x ε hx hε
  exact adaptiveSoundness_power_le_errorProfile r n hE ha hx hε

end MIPRE.Introspection
end

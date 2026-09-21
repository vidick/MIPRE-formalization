/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.Clock

/-! # Uniform runtime bounds for the growing introspection clock

For each fixed positive exponent, clock construction runs in polynomial time
in its unary output budget, uniformly in the parameter and index. The existing
polynomial-exponent absorption lemma then gives another introspection budget.
-/

noncomputable section

namespace MIPRE.Introspection.ClockArithmetic

open Cost Polynomial

def unaryCostPoly : Polynomial ℕ :=
  (X + 2) * ((X + 1) * (4 * X + 14) + 7 * (4 * X + 1) + 8 * X + 90)

theorem esize_le_value {n M : ℕ} (h : n ≤ M) : esize n ≤ 4 * M + 1 := by
  have hs : Nat.size n ≤ n := Nat.size_le.2 Nat.lt_two_pow_self
  exact (esize_nat_le n).trans (by omega)

theorem unaryCost_le {n M : ℕ} (h : n ≤ M) : unaryCost n ≤ unaryCostPoly.eval M := by
  have hs : Nat.size n ≤ M := (Nat.size_le.2 Nat.lt_two_pow_self).trans h
  have he := esize_le_value h
  simp only [unaryCostPoly, eval_add, eval_mul, eval_X, eval_ofNat, eval_one]
  unfold unaryCost
  gcongr

def mulCostPoly : Polynomial ℕ :=
  (X + 1) * ((X + 1) * (4 * X + 2 * (X * X) + 15) +
    4 * X + 4 * (X * X) + 2 * X + 41) + 2 * X + 10

theorem mulCost_le {a b M : ℕ} (ha : a ≤ M) (hb : b ≤ M) :
    mulCost a b ≤ mulCostPoly.eval M := by
  simp only [mulCostPoly, eval_add, eval_mul, eval_X, eval_ofNat, eval_one]
  unfold mulCost
  gcongr

def clockCostPoly (k : ℕ) : Polynomial ℕ :=
  unaryCostPoly + unaryCostPoly + (4 * X + 1) + (4 * X + 1) + 2 * X + 2 * X + 20 +
    mulCostPoly + 2 * (X * X) + 4 + powerBound k +
    (X + 2) * (4 * X + 20) + unaryCostPoly + 5 + (4 * X + 1) + (4 * X + 1) + 3

theorem clock_arguments_le {k lam n : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ lam) (hn : 1 ≤ n) :
    lam ≤ ansBound k lam n ∧ n ≤ ansBound k lam n ∧
      lam * n + 1 ≤ ansBound k lam n ∧ (lam * n + 1) ^ k ≤ ansBound k lam n := by
  have hm : lam * n + 1 ≤ (lam * n + 1) ^ k := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ lam * n + 1) hk
  have hq : (lam * n + 1) ^ k ≤ ansBound k lam n := Nat.lt_two_pow_self.le
  have hlam : lam ≤ lam * n := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left lam hn
  have hnn : n ≤ lam * n := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right n hl
  exact ⟨(by omega : lam ≤ lam * n + 1).trans (hm.trans hq),
    (by omega : n ≤ lam * n + 1).trans (hm.trans hq), hm.trans hq, hq⟩

/-- One polynomial controls all parameter/index instances of the actual clock. -/
theorem growingClock_cost_le {k lam n : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ lam) (hn : 1 ≤ n) :
    uniformCost k lam n + esize lam + esize n + 3 ≤ (clockCostPoly k).eval (ansBound k lam n) := by
  obtain ⟨hlB, hnB, hmB, hqB⟩ := clock_arguments_le hk hl hn
  have hul := unaryCost_le hlB
  have hun := unaryCost_le hnB
  have huB := unaryCost_le (Nat.le_refl (ansBound k lam n))
  have hel := esize_le_value hlB
  have hen := esize_le_value hnB
  have hmul := mulCost_le hlB hnB
  have hp := polynomial_eval_mono (powerBound k) hmB
  have hprod := Nat.mul_le_mul hlB hnB
  have he := Nat.mul_le_mul (Nat.add_le_add_right hqB 2)
    (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hqB) 20)
  simp only [clockCostPoly, eval_add, eval_mul, eval_X, eval_ofNat, eval_one]
  dsimp only [uniformCost]
  omega

end MIPRE.Introspection.ClockArithmetic

namespace MIPRE.Introspection

open Cost ClockArithmetic

theorem growingClock_polynomial_time {k : ℕ} (hk : 1 ≤ k) :
    ∃ Q : Polynomial ℕ, ∀ lam n, 1 ≤ lam → 1 ≤ n →
      HaltsWithin (growingClock k lam).prog (encode n) (Q.eval (ansBound k lam n)) := by
  refine ⟨clockCostPoly k, fun lam n hl hn => ?_⟩
  obtain ⟨r, time, ht, hr⟩ := growingClock_haltsWithin k lam n
  exact ⟨r, time, ht.trans (growingClock_cost_le hk hl hn), hr⟩

/-- Generating the unary clock itself fits a uniformly enlarged introspection budget. -/
theorem growingClock_ansBound_time {k : ℕ} (hk : 1 ≤ k) :
    ∃ C, ∀ lam n, 1 ≤ lam → 1 ≤ n →
      HaltsWithin (growingClock k lam).prog (encode n) (ansBound C lam n) := by
  obtain ⟨C, hC⟩ := polynomial_ansBound (clockCostPoly k) k
  refine ⟨C, fun lam n hl hn => ?_⟩
  obtain ⟨r, time, ht, hr⟩ := growingClock_haltsWithin k lam n
  exact ⟨r, time, ht.trans ((growingClock_cost_le hk hl hn).trans (hC lam n hl hn)), hr⟩

end MIPRE.Introspection

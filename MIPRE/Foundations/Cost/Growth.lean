/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Cost.PolyTime
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.Nat.Size

/-!
# Polynomial versus exponential growth

The arithmetic behind the threshold of the recursive compression argument
(`planning/compression-track.md`, K3 step 4): for every polynomial `Q` over `ℕ` there is a
constant `K` such that `n ≥ 2 ^ (K + 1 + x)` forces `Q (x + log n) ≤ n + 1`
(`exists_threshold`). The proof is elementary: a polynomial is bounded by its coefficient
sum times the top power (`polynomial_eval_le_sum_coeff_mul_pow`), and `A · σ ^ D ≤ 2 ^ σ`
as soon as `σ ≥ A (D + 1) ^ (D + 1)` (`mul_pow_le_two_pow`).
-/

namespace MIPRE.Cost

open Polynomial

/-- A polynomial over `ℕ` is bounded by its coefficient sum times the top power. -/
theorem polynomial_eval_le_sum_coeff_mul_pow (Q : Polynomial ℕ) {y : ℕ} (hy : 1 ≤ y) :
    Q.eval y ≤ (∑ i ∈ Finset.range (Q.natDegree + 1), Q.coeff i) * y ^ Q.natDegree := by
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  exact Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right hy (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))

/-- `A · σ ^ D ≤ 2 ^ σ` for `σ ≥ A (D + 1) ^ (D + 1)`: with `μ = σ / (D + 1)`,
`A σ ^ D ≤ A (D + 1) ^ D (μ + 1) ^ D ≤ μ (μ + 1) ^ D ≤ (μ + 1) ^ (D + 1) ≤ 2 ^ (μ (D + 1)) ≤
2 ^ σ`. -/
theorem mul_pow_le_two_pow (A D σ : ℕ) (h : A * (D + 1) ^ (D + 1) ≤ σ) :
    A * σ ^ D ≤ 2 ^ σ := by
  have hD : 0 < D + 1 := Nat.succ_pos D
  have h1 : A * (D + 1) ^ D ≤ σ / (D + 1) := by
    rw [Nat.le_div_iff_mul_le hD, mul_assoc, ← pow_succ]
    exact h
  have h2 : σ ≤ (D + 1) * (σ / (D + 1) + 1) := (Nat.lt_mul_div_succ σ hD).le
  have h3 : σ / (D + 1) * (D + 1) ≤ σ := Nat.div_mul_le_self σ (D + 1)
  have h4 : σ / (D + 1) + 1 ≤ 2 ^ (σ / (D + 1)) := Nat.lt_two_pow_self
  calc A * σ ^ D ≤ A * ((D + 1) * (σ / (D + 1) + 1)) ^ D :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2 D)
    _ = A * (D + 1) ^ D * (σ / (D + 1) + 1) ^ D := by rw [mul_pow, mul_assoc]
    _ ≤ σ / (D + 1) * (σ / (D + 1) + 1) ^ D := Nat.mul_le_mul_right _ h1
    _ ≤ (σ / (D + 1) + 1) ^ (D + 1) := by
        rw [pow_succ]
        exact Nat.mul_le_mul_right _ (Nat.le_succ _) |>.trans
          (le_of_eq (Nat.mul_comm _ _))
    _ ≤ (2 ^ (σ / (D + 1))) ^ (D + 1) := Nat.pow_le_pow_left h4 _
    _ = 2 ^ (σ / (D + 1) * (D + 1)) := by rw [← pow_mul]
    _ ≤ 2 ^ σ := Nat.pow_le_pow_right (by norm_num) h3

/-- **The threshold lemma.** For a polynomial `Q`, there is a constant `K` such that
`n ≥ 2 ^ (K + 1 + x)` implies `Q (x + log n) ≤ n + 1` (with `log n = Nat.size n`). This is
what makes the threshold `r e = 2 ^ (K + 1 + esize e)` of the compression argument work:
above it, every polynomial overhead in `esize e + log n` is at most `n + 1`. -/
theorem exists_threshold (Q : Polynomial ℕ) :
    ∃ K : ℕ, ∀ x n : ℕ, 2 ^ (K + 1 + x) ≤ n → Q.eval (x + Nat.size n) ≤ n + 1 := by
  obtain ⟨D, hD⟩ : ∃ D, D = Q.natDegree := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = ∑ i ∈ Finset.range (Q.natDegree + 1), Q.coeff i := ⟨_, rfl⟩
  have hQ : ∀ y, 1 ≤ y → Q.eval y ≤ A * y ^ D := fun y hy => by
    rw [hA, hD]; exact polynomial_eval_le_sum_coeff_mul_pow Q hy
  refine ⟨2 * A * 2 ^ D * (D + 1) ^ (D + 1), fun x n hn => ?_⟩
  have hlt : 2 * A * 2 ^ D * (D + 1) ^ (D + 1) + 1 + x < Nat.size n := Nat.lt_size.mpr hn
  have hn' : 2 ^ (Nat.size n - 1) ≤ n := Nat.lt_size.mp (by omega)
  have h1 : Q.eval (x + Nat.size n) ≤ Q.eval (2 * Nat.size n) :=
    polynomial_eval_mono Q (by omega)
  have h2 : Q.eval (2 * Nat.size n) ≤ A * (2 * Nat.size n) ^ D := hQ _ (by omega)
  have h3 : 2 * (A * 2 ^ D * Nat.size n ^ D) ≤ 2 ^ Nat.size n := by
    have := mul_pow_le_two_pow (2 * A * 2 ^ D) D (Nat.size n) (by omega)
    calc 2 * (A * 2 ^ D * Nat.size n ^ D) = 2 * A * 2 ^ D * Nat.size n ^ D := by ring
      _ ≤ 2 ^ Nat.size n := this
  have h4 : 2 ^ Nat.size n = 2 * 2 ^ (Nat.size n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [h4] at h3
  calc Q.eval (x + Nat.size n) ≤ Q.eval (2 * Nat.size n) := h1
    _ ≤ A * (2 * Nat.size n) ^ D := h2
    _ = A * 2 ^ D * Nat.size n ^ D := by rw [mul_pow, mul_assoc]
    _ ≤ 2 ^ (Nat.size n - 1) := by omega
    _ ≤ n := hn'
    _ ≤ n + 1 := Nat.le_succ n

end MIPRE.Cost

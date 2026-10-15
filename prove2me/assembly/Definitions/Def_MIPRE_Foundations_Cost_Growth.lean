/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Growth.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime

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

/-- `2 ^ size n ≤ 2n + 1`. -/
theorem two_pow_size_le (n : ℕ) : 2 ^ Nat.size n ≤ 2 * n + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h : Nat.size n - 1 < Nat.size n := by
      have := Nat.size_pos.2 hn; omega
    have h2 : 2 ^ (Nat.size n - 1) ≤ n := Nat.lt_size.1 h
    have h3 : 2 ^ Nat.size n = 2 * 2 ^ (Nat.size n - 1) := by
      rw [← pow_succ']; congr 1; have := Nat.size_pos.2 hn; omega
    omega

/-- A polynomial over `ℕ` is bounded by its coefficient sum times the top power. -/
theorem polynomial_eval_le_sum_coeff_mul_pow (Q : Polynomial ℕ) {y : ℕ} (hy : 1 ≤ y) :
    Q.eval y ≤ (∑ i ∈ Finset.range (Q.natDegree + 1), Q.coeff i) * y ^ Q.natDegree := by
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  exact Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right hy (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))

end MIPRE.Cost

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.Repeat.SamplerCost
public import MIPRE.Tailored.Repeat.Calls

@[expose] public section

/-!
# Domination tools for the repeated tailored programs

The running times of the repeated programs (issue #280) are bounded in the shape
`c (W + 1)^m X^{e (K + 1)}` of `MIPRE.Repeat.Dom`, with `W` a bound on the parameters, `X` the
size of the input plus one and `K` the input programs' degree. Their stages are polynomial-time
functions and calls to the input programs, so two facts do most of the work: a polynomial of a
dominated quantity is dominated (`dom_poly`), and a size linear in `X` raised to the power `K` is
dominated once `10^K ≤ W` (`dom_powK`).
-/

namespace MIPRE.Repeat

open Cost

variable {W X K : ℕ}

/-- A linear combination of `W` and `X`. -/
theorem Dom.ofLin (hX : 1 ≤ X) {a b c v : ℕ} (h : v ≤ a * W + b * X + c) :
    Dom W X K (a + b + c) 1 1 v := by
  unfold Dom
  have hXp : X ≤ X ^ (1 * (K + 1)) := by
    rw [one_mul]; exact Nat.le_self_pow (by omega) X
  have h1 : 1 ≤ X ^ (1 * (K + 1)) := Nat.one_le_pow _ _ hX
  rw [pow_one]
  calc v ≤ a * W + b * X + c := h
    _ ≤ (a + b + c) * (W + 1) * X ^ (1 * (K + 1)) := by
      have e1 : a * W ≤ a * (W + 1) * X ^ (1 * (K + 1)) := by
        calc a * W ≤ a * (W + 1) := Nat.mul_le_mul_left _ (by omega)
          _ ≤ a * (W + 1) * X ^ (1 * (K + 1)) := Nat.le_mul_of_pos_right _ h1
      have e2 : b * X ≤ b * (W + 1) * X ^ (1 * (K + 1)) := by
        calc b * X ≤ b * X ^ (1 * (K + 1)) := Nat.mul_le_mul_left _ hXp
          _ ≤ b * (W + 1) * X ^ (1 * (K + 1)) := by
            rw [Nat.mul_assoc]
            exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
      have e3 : c ≤ c * (W + 1) * X ^ (1 * (K + 1)) := by
        calc c ≤ c * (W + 1) := Nat.le_mul_of_pos_right _ (by omega)
          _ ≤ c * (W + 1) * X ^ (1 * (K + 1)) := Nat.le_mul_of_pos_right _ h1
      have : (a + b + c) * (W + 1) * X ^ (1 * (K + 1)) =
          a * (W + 1) * X ^ (1 * (K + 1)) + b * (W + 1) * X ^ (1 * (K + 1)) +
            c * (W + 1) * X ^ (1 * (K + 1)) := by ring
      omega

/-- **A polynomial of a dominated quantity is dominated.** -/
theorem dom_poly (P : Polynomial ℕ) (cy my ey : ℕ) : ∃ c m e, ∀ (W X K : ℕ) {y : ℕ}, 1 ≤ X →
    Dom W X K cy my ey y → Dom W X K c m e (P.eval y) := by
  exact ⟨_, _, _, fun W X K {y} hX h => by
    have h1 := polynomial_eval_le_sum_coeff_mul_pow P (y := y + 1) (by omega)
    have h2 := polynomial_eval_mono P (Nat.le_succ y)
    exact ((Dom.const _).mul ((h.add hX (Dom.const 1)).pow P.natDegree)).of_le (h2.trans h1)⟩

/-- **A size linear in `X`, to the power `K`**, is dominated when `10^K ≤ W`. -/
theorem dom_powK (hX : 1 ≤ X) (hW : 10 ^ K ≤ W) {a j y : ℕ} (ha : a ≤ 10 ^ j) (hy : y ≤ a * X) :
    Dom W X K 1 j 1 (y ^ K) := by
  unfold Dom
  calc y ^ K ≤ (a * X) ^ K := Nat.pow_le_pow_left hy K
    _ = a ^ K * X ^ K := Nat.mul_pow _ _ _
    _ ≤ (10 ^ j) ^ K * X ^ K := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left ha K)
    _ = (10 ^ K) ^ j * X ^ K := by rw [← pow_mul, ← pow_mul, Nat.mul_comm j K]
    _ ≤ (W + 1) ^ j * X ^ (1 * (K + 1)) := by
      refine Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) j) ?_
      exact Nat.pow_le_pow_right hX (by omega)
    _ = 1 * (W + 1) ^ j * X ^ (1 * (K + 1)) := by ring

/-- The cost of the loop of calls, dominated. -/
theorem dom_mapCallCost (cm mm em cT mT eT cC mC eC cZ mZ eZ : ℕ) : ∃ c m e, ∀ (W X K : ℕ)
    {M T C Z : ℕ}, 1 ≤ X → Dom W X K cm mm em M → Dom W X K cT mT eT T →
    Dom W X K cC mC eC C → Dom W X K cZ mZ eZ Z →
    Dom W X K c m e (Tailored.Calls.mapCallCost M T C Z) := by
  exact ⟨_, _, _, fun W X K {M T C Z} hX hM hT hC hZ => by
    unfold Tailored.Calls.mapCallCost
    exact (((((hM.add hX (Dom.const 1)).mul ((((hT.add hX ((Dom.const 3).mul hC)).add hX
      ((Dom.const 2).mul hZ)).add hX (Dom.const 25)))).add hX
      ((hM.add hX (Dom.const 2)).mul (hZ.add hX (Dom.const 13)))).add hX
      ((Dom.const 4).mul hC)).add hX ((Dom.const 3).mul hZ)).add hX (Dom.const 20)⟩

end MIPRE.Repeat

end

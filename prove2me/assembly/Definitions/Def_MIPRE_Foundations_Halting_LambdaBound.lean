/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/LambdaBound.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The parameter inequality of the halting verifier

Blueprint `lem:lambda-bound` (ledger node `1.6.4`): for all `C, C' ≥ 1`, all
`λ ≥ 4 · max ((4C) ^ (8C)) (C · log₂ C')` and all `n ≥ 2`,

  `C · (C' · λ · n) ^ C ≤ n ^ λ`.

This is the arithmetic that makes a `λ`-boundedness accounting go through. Every verifier the
pipeline produces has running times *polynomial in the level and in `λ`* — `poly(n, λ)`, the
shape `MIPRE.GapCompression.decider_time` and `sampler_time` state — while
`MIPRE.Verifier.IsBounded λ` asks for `n ^ λ`. The inequality says that once `λ` is large
enough in terms of the polynomial's degree alone, the second dominates the first at every
level `n ≥ 2`; and `λ` large enough is what blueprint `lem:lambda` chooses. `C` is the degree
and `C'` the coefficient, so the threshold is exponential in the degree and only logarithmic in
the coefficient — which is what keeps `λ` polynomial in the description length rather than
exponential in it.

`log` is `Nat.log 2` throughout, so the hypothesis is the integer reading of the blueprint's;
nothing below needs it to be the real logarithm, and reading it as `Nat.log 2` makes the
threshold no larger.

The proof is the obvious one made finite. Bound each factor of the left-hand side by a power of
`n` — `C' ≤ 2 ^ (log₂ C' + 1)` and `λ ≤ 2 ^ (log₂ λ + 1)` and `C ≤ 2 ^ C`, with `2 ≤ n` — so
that the claim reduces to the *linear* statement `4C + C · log₂ C' + C · log₂ λ ≤ λ`. Two of
those three terms are a quarter of `λ` by hypothesis outright. The third,
`C · log₂ λ ≤ λ / 4`, is the only one with content: it is `λ < 2 ^ (λ / (4C))`, which holds
once `λ / (4C)` exceeds `8C + 4`, because `2 ^ q` overtakes `q ^ 2` at `q = 4`
(`Nat.sq_le_two_pow_of_four_le`) and `q ^ 2 ≥ q · (8C + 4) > 4C · (q + 1)` there.
-/

namespace MIPRE.Halting

/-! ## Two facts about powers of two -/

/-- `q ^ 2 ≤ 2 ^ q` from `q = 4` on. The induction step is `(q + 1) ^ 2 ≤ 2 q ^ 2`, which is
`q ^ 2 ≥ 2 q + 1`, true from `q = 3`. -/
theorem sq_le_two_pow_of_four_le : ∀ {q : ℕ}, 4 ≤ q → q ^ 2 ≤ 2 ^ q := by
  intro q hq
  induction q with
  | zero => omega
  | succ q ih =>
    rcases Nat.lt_or_ge q 4 with hlt | hge
    · have hq3 : q = 3 := by omega
      subst hq3
      norm_num
    · have h := ih hge
      have hq3 : 2 * q + 1 ≤ q * q := by nlinarith
      have e1 : (q + 1) ^ 2 = q * q + 2 * q + 1 := by ring
      have e2 : 2 * 2 ^ q = 2 ^ (q + 1) := by rw [pow_succ]; ring
      have e3 : q ^ 2 = q * q := by ring
      omega

/-- The crossover the parameter inequality runs on: for `C ≥ 1` and `q ≥ 8C + 4`, the linear
function `4C(q + 1)` is already below `2 ^ q`. -/
theorem four_mul_succ_lt_two_pow {C q : ℕ} (hC : 1 ≤ C) (hq : 8 * C + 4 ≤ q) :
    4 * C * (q + 1) < 2 ^ q := by
  have h4 : 4 ≤ q := by omega
  have hsq : q ^ 2 ≤ 2 ^ q := sq_le_two_pow_of_four_le h4
  have h1 : q * (8 * C + 4) ≤ q * q := Nat.mul_le_mul_left q hq
  have h2 : 4 * C * (q + 1) < q * (8 * C + 4) := by nlinarith
  have e : q ^ 2 = q * q := by ring
  omega

/-- **`C · log₂ λ` is below `λ / (4C)`**, once `λ` is past the crossover. This is the only clause
of the parameter inequality with content. -/
theorem log_lt_div {C lam : ℕ} (hC : 1 ≤ C) (hlam : 4 * C * (8 * C + 4) ≤ lam) :
    Nat.log 2 lam < lam / (4 * C) := by
  have hCpos : 0 < 4 * C := by omega
  have hq : 8 * C + 4 ≤ lam / (4 * C) :=
    (Nat.le_div_iff_mul_le hCpos).2 (by linarith [hlam])
  have hmod : 4 * C * (lam / (4 * C)) + lam % (4 * C) = lam := Nat.div_add_mod lam (4 * C)
  have hmlt : lam % (4 * C) < 4 * C := Nat.mod_lt lam hCpos
  have hlampos : 1 ≤ lam := by nlinarith
  have hlt : lam < 4 * C * (lam / (4 * C) + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  exact Nat.log_lt_of_lt_pow (by omega) (lt_trans hlt (four_mul_succ_lt_two_pow hC hq))

/-! ## The parameter inequality -/

end MIPRE.Halting

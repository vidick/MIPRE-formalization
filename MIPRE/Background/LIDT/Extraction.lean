/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.LIDT.Coefficients
import MIPRE.Foundations.CrossConsistency
import MIPRE.Foundations.Pasting
import MIPRE.Foundations.RegisterReindex

/-!
# Extracting exactly linear combined codewords

Blueprint `lem:lidt-ldc-extraction`, the paper's Step 4 of the proof of `lem:ld-soundness` for
general `ldc` (`ldt.tex`, Claims 4 and 5 and the measurements `H`, `G`). The simultaneous test with
`r` codewords is reduced to the single-codeword test in `K + m` variables by *combining*: a point
`(x, y) ∈ F^K × F^m` is answered by `∑_{j < r} x_j b_j`, where `b ∈ F^r` is the original point
answer at `y`. The single-codeword theorem then returns a measurement `R` of polynomials `g` in the
`K + m` variables, consistent with the combined point answers. This file turns `R` back into a
measurement of `r`-tuples of polynomials in the `m` original variables.

## The extraction

A polynomial `g(x, y)` is **exactly `x`-linear** (`IsXLin`) if it is `∑_i x_i g_i(y)`: every
monomial has exactly one `x`-variable, to the first power. `extract` reads off `(g_1, …, g_r)` from
such a `g` and returns `0` otherwise; it is a deterministic relabelling of outcomes, so applied to a
projective measurement it gives a projective measurement.

## The estimate

`inconsistency_extract_right_le` (and `_left_le`, the extracted measurement on the other
party): the extracted tuple, evaluated at a uniform `y`, disagrees with
the original point answer at most `(K + m) d / q` more often than `g(x, y)` disagrees with the
combined answer at a uniform `(x, y)`. Fix `y`, the original answer `b` and the outcome `g`, and
average over `x` alone --- the Born probabilities do not see `x`, since the original point
measurement is asked `y` only and `R` is asked nothing:

* if `g` is exactly `x`-linear and its extracted tuple is `b` at `y`, there is nothing to prove;
* if `g` is exactly `x`-linear and the tuple differs from `b`, then `x ↦ g(x, y)` and the combined
  answer are two different linear forms, so they agree at a uniform `x` with probability at most
  `K d / q` (`pevY_eq_linPoly`, then Schwartz--Zippel in `K` variables, `card_agree_le`);
* if `g` is not exactly `x`-linear, a monomial with a forbidden `x`-part has a nonzero coefficient
  `Q_g`, a polynomial in `y` alone. Where `Q_g(y) ≠ 0` the same Schwartz--Zippel step applies; and
  `Q_g(y) = 0` has probability at most `m d / q` over `y`, which is paid once per outcome `g`,
  weighted by `g`'s total Born weight, because summing the Born probabilities over `b` removes `y`
  (`sum_agreeX_le`, `sum_uniform_badInd_le`).

The paper splits the last case the same way (its Claims 4 and 5). The linear-forms case costs
`K d / q` here rather than the paper's `1 / q`: the same Schwartz--Zippel lemma serves all three
cases, and the difference is absorbed by the final constants.

## The partial evaluation

`pevY g y` is the coefficient vector, in the `K` combining variables, of `x ↦ g(x, y)`
(`eval_pevY`). It is what lets Schwartz--Zippel in `K` variables be applied with `y` fixed.
-/

noncomputable section

namespace MIPRE.LIDT.Simul

open Finset MIPRE MIPRE.LIDT
open scoped Kronecker

/-! ## Polynomials in the combining and original variables -/

section Poly

variable {F : Type*} [Field F] {K m d r : ℕ}

/-- **The partial evaluation at `y`**: the coefficient vector, in the `K` combining variables, of
`x ↦ g(x, y)`. -/
def pevY (g : LowIndDegPoly (F := F) (m := K + m) (d := d)) (y : Point F m) :
    LowIndDegPoly (F := F) (m := K) (d := d) :=
  fun ex => ∑ ey : Fin m → Fin (d + 1), g (Fin.append ex ey) * ∏ j, y j ^ (ey j : ℕ)

theorem eval_pevY (g : LowIndDegPoly (F := F) (m := K + m) (d := d)) (x : Point F K)
    (y : Point F m) : (pevY g y).eval x = g.eval (Fin.append x y) := by
  classical
  simp only [LowIndDegPoly.eval, pevY]
  rw [← Fintype.sum_equiv (Fin.appendEquiv K m)
    (fun p => g (Fin.appendEquiv K m p)
      * ∏ k, Fin.append x y k ^ ((Fin.appendEquiv K m p k : Fin (d + 1)) : ℕ))
    _ fun p => rfl, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ex _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun ey _ => ?_
  simp only [Fin.appendEquiv_apply, Fin.prod_univ_add, Fin.append_left, Fin.append_right]
  rw [show Fin.appendEquiv K m (ex, ey) = Fin.append ex ey from rfl]
  ring

/-- Evaluation of coefficient vectors is additive in the vector. -/
theorem eval_sub (p q : LowIndDegPoly (F := F) (m := K) (d := d)) (x : Point F K) :
    (p - q).eval x = p.eval x - q.eval x := by
  simp only [LowIndDegPoly.eval, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- The exponent vector of the variable `x_i`. -/
def unitExp (hd : 1 ≤ d) (i : Fin K) : Fin K → Fin (d + 1) :=
  Pi.single i ⟨1, Nat.lt_succ_of_le hd⟩

theorem unitExp_injective (hd : 1 ≤ d) : Function.Injective (unitExp (K := K) hd) := by
  intro i j h
  by_contra hij
  have := congrFun h i
  simp only [unitExp, Pi.single_eq_same, Pi.single_eq_of_ne hij] at this
  exact absurd (congrArg Fin.val this) (by simp)

theorem prod_pow_unitExp (hd : 1 ≤ d) (i : Fin K) (x : Point F K) :
    ∏ k, x k ^ ((unitExp hd i k : Fin (d + 1)) : ℕ) = x i := by
  classical
  rw [Finset.prod_eq_single i (fun k _ hki => by simp [unitExp, Pi.single_eq_of_ne hki])
    (fun h => absurd (mem_univ i) h)]
  simp [unitExp]

/-- **The linear form `x ↦ ∑_i c_i x_i`**, as a coefficient vector. -/
def linPoly (hd : 1 ≤ d) (c : Point F K) : LowIndDegPoly (F := F) (m := K) (d := d) :=
  fun ex => ∑ i, if ex = unitExp hd i then c i else 0

theorem eval_linPoly (hd : 1 ≤ d) (c x : Point F K) :
    (linPoly hd c).eval x = ∑ i, c i * x i := by
  classical
  simp only [LowIndDegPoly.eval, linPoly, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single (unitExp hd i) (fun ex _ hex => by rw [if_neg hex, zero_mul])
    (fun h => absurd (mem_univ _) h), if_pos rfl, prod_pow_unitExp]

theorem linPoly_unitExp (hd : 1 ≤ d) (c : Point F K) (i : Fin K) :
    linPoly hd c (unitExp hd i) = c i := by
  classical
  rw [linPoly, Finset.sum_eq_single i (fun j _ hji => if_neg fun h =>
    hji (unitExp_injective hd h).symm) (fun h => absurd (mem_univ i) h), if_pos rfl]

theorem linPoly_of_forall_ne (hd : 1 ≤ d) (c : Point F K) {ex : Fin K → Fin (d + 1)}
    (hex : ∀ i, ex ≠ unitExp hd i) : linPoly hd c ex = 0 :=
  Finset.sum_eq_zero fun i _ => if_neg (hex i)

theorem linPoly_injective (hd : 1 ≤ d) : Function.Injective (linPoly (F := F) (K := K) hd) :=
  fun c c' h => funext fun i => by
    rw [← linPoly_unitExp hd c i, ← linPoly_unitExp hd c' i, h]

/-- **Exactly `x`-linear**: every monomial with a nonzero coefficient has an `x`-part equal to a
single variable to the first power. -/
def IsXLin (hd : 1 ≤ d) (g : LowIndDegPoly (F := F) (m := K + m) (d := d)) : Prop :=
  ∀ (ex : Fin K → Fin (d + 1)) (ey : Fin m → Fin (d + 1)),
    (∀ i, ex ≠ unitExp hd i) → g (Fin.append ex ey) = 0

/-- The coefficient of `x_i`, a polynomial in `y`. -/
def xCoef (hd : 1 ≤ d) (g : LowIndDegPoly (F := F) (m := K + m) (d := d)) (i : Fin K) :
    LowIndDegPoly (F := F) (m := m) (d := d) :=
  fun ey => g (Fin.append (unitExp hd i) ey)

/-- **An exactly `x`-linear polynomial is, at each `y`, the linear form of its coefficients.** -/
theorem pevY_eq_linPoly {hd : 1 ≤ d} {g : LowIndDegPoly (F := F) (m := K + m) (d := d)}
    (hg : IsXLin hd g) (y : Point F m) :
    pevY g y = linPoly hd (fun i => (xCoef hd g i).eval y) := by
  classical
  funext ex
  by_cases hex : ∃ i, ex = unitExp hd i
  · obtain ⟨i, rfl⟩ := hex
    rw [linPoly_unitExp]
    rfl
  · push Not at hex
    rw [linPoly_of_forall_ne hd _ hex, pevY]
    exact Finset.sum_eq_zero fun ey _ => by rw [hg ex ey hex, zero_mul]

/-- **A forbidden coefficient.** A polynomial that is not exactly `x`-linear has a monomial with a
forbidden `x`-part and a nonzero coefficient; that coefficient, as a polynomial in `y`, is
nonzero, and where it does not vanish the partial evaluation is no linear form. -/
theorem exists_badCoef {hd : 1 ≤ d} {g : LowIndDegPoly (F := F) (m := K + m) (d := d)}
    (hg : ¬ IsXLin hd g) :
    ∃ ex : Fin K → Fin (d + 1), (∀ i, ex ≠ unitExp hd i) ∧
      (fun ey => g (Fin.append ex ey) : LowIndDegPoly (F := F) (m := m) (d := d)) ≠ 0 := by
  unfold IsXLin at hg
  push Not at hg
  obtain ⟨ex, ey, hex, hne⟩ := hg
  exact ⟨ex, hex, fun h => hne (congrFun h ey)⟩

theorem pevY_apply (g : LowIndDegPoly (F := F) (m := K + m) (d := d)) (y : Point F m)
    (ex : Fin K → Fin (d + 1)) :
    pevY g y ex
      = LowIndDegPoly.eval (F := F) (m := m) (d := d) (fun ey => g (Fin.append ex ey)) y :=
  rfl

/-- The answer `b ∈ F^r`, padded with zeros to the `K` combining coordinates. -/
def padB (b : Fin r → F) : Point F K :=
  fun i => if h : (i : ℕ) < r then b ⟨i, h⟩ else 0

theorem padB_castLE (hr : r ≤ K) (b : Fin r → F) (j : Fin r) :
    padB (K := K) b (Fin.castLE hr j) = b j := by
  simp [padB, j.isLt]

/-- **The extraction**: the first `r` coefficients of an exactly `x`-linear polynomial, and the
zero tuple otherwise. -/
def extract (hd : 1 ≤ d) (hr : r ≤ K) (g : LowIndDegPoly (F := F) (m := K + m) (d := d)) :
    Fin r → LowIndDegPoly (F := F) (m := m) (d := d) := by
  classical
  exact if IsXLin hd g then fun j => xCoef hd g (Fin.castLE hr j) else 0

/-- The extracted tuple, evaluated at `y`. -/
def extEval (hd : 1 ≤ d) (hr : r ≤ K) (g : LowIndDegPoly (F := F) (m := K + m) (d := d))
    (y : Point F m) : Fin r → F :=
  fun j => (extract hd hr g j).eval y

/-- The forbidden coefficient of a polynomial that is not exactly `x`-linear (`0` for one that
is). -/
def badQ (hd : 1 ≤ d) (g : LowIndDegPoly (F := F) (m := K + m) (d := d)) :
    LowIndDegPoly (F := F) (m := m) (d := d) := by
  classical
  exact if h : IsXLin hd g then 0 else fun ey => g (Fin.append (exists_badCoef h).choose ey)

theorem badQ_ne_zero {hd : 1 ≤ d} {g : LowIndDegPoly (F := F) (m := K + m) (d := d)}
    (hg : ¬ IsXLin hd g) : badQ hd g ≠ 0 := by
  classical
  rw [badQ, dif_neg hg]
  exact (exists_badCoef hg).choose_spec.2

theorem pevY_badQ {hd : 1 ≤ d} {g : LowIndDegPoly (F := F) (m := K + m) (d := d)}
    (hg : ¬ IsXLin hd g) (y : Point F m) :
    ∃ ex : Fin K → Fin (d + 1), (∀ i, ex ≠ unitExp hd i) ∧ pevY g y ex = (badQ hd g).eval y := by
  classical
  refine ⟨(exists_badCoef hg).choose, (exists_badCoef hg).choose_spec.1, ?_⟩
  rw [pevY_apply, badQ, dif_neg hg]

end Poly

/-! ## Schwartz--Zippel at a fixed `y` -/

section Agree

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ}

/-- Two different coefficient vectors in `K` variables agree at a uniform point with probability at
most `K d / q`. -/
theorem card_agree_le {p p' : LowIndDegPoly (F := F) (m := K) (d := d)} (h : p ≠ p') :
    ((univ.filter fun x : Point F K => p.eval x = p'.eval x).card : ℝ)
        / (Fintype.card F : ℝ) ^ K ≤ K * d / Fintype.card F := by
  have hne : p - p' ≠ 0 := sub_ne_zero.mpr h
  have hc := card_eval_eq_zero_le hne
  have hset : (univ.filter fun x : Point F K => p.eval x = p'.eval x)
      = univ.filter fun x : Point F K => (p - p').eval x = 0 := by
    ext x
    simp [eval_sub, sub_eq_zero]
  rw [hset]
  exact hc

/-- The agreement, at a uniform `x`, of the combined answer with the outcome `g` evaluated at
`(x, y)`, as a fraction. -/
def agreeX (hd : 1 ≤ d) (g : LowIndDegPoly (F := F) (m := K + m) (d := d))
    (y : Point F m) (b : Fin r → F) : ℝ :=
  ((univ.filter fun x : Point F K =>
      (linPoly hd (padB b)).eval x = g.eval (Fin.append x y)).card : ℝ)
    / (Fintype.card F : ℝ) ^ K

theorem agreeX_le_one (hd : 1 ≤ d) (g : LowIndDegPoly (F := F) (m := K + m) (d := d))
    (y : Point F m) (b : Fin r → F) : agreeX hd g y b ≤ 1 := by
  have hpos : (0 : ℝ) < (Fintype.card F : ℝ) ^ K := by
    have : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
    positivity
  rw [agreeX, div_le_one hpos]
  have := Finset.card_filter_le (univ : Finset (Point F K))
    (fun x => (linPoly hd (padB b)).eval x = g.eval (Fin.append x y))
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at this
  exact_mod_cast this

/-- The indicator that `g` is not exactly `x`-linear and its forbidden coefficient vanishes at
`y`. -/
def badInd (hd : 1 ≤ d) (g : LowIndDegPoly (F := F) (m := K + m) (d := d)) (y : Point F m) : ℝ := by
  classical
  exact if IsXLin hd g then 0 else if (badQ hd g).eval y = 0 then 1 else 0

/-- **The pointwise bound.** At a fixed `y`, answer `b` and outcome `g`, the combined answer and
`g(·, y)` agree at a uniform `x` with probability at most: one if the extracted tuple is `b`; one
if `g` is not exactly `x`-linear and its forbidden coefficient vanishes at `y`; and `K d / q`
otherwise. -/
theorem agreeX_le (hd : 1 ≤ d) (hr : r ≤ K) (g : LowIndDegPoly (F := F) (m := K + m) (d := d))
    (y : Point F m) (b : Fin r → F) :
    agreeX hd g y b
      ≤ (if extEval hd hr g y = b then 1 else 0) + K * d / Fintype.card F + badInd hd g y := by
  classical
  have hK : (0 : ℝ) ≤ K * d / Fintype.card F := by positivity
  have h1 := agreeX_le_one hd g y b
  have hbad0 : 0 ≤ badInd hd g y := by
    unfold badInd; split_ifs <;> norm_num
  by_cases hb : extEval hd hr g y = b
  · rw [if_pos hb]; linarith
  rw [if_neg hb, zero_add]
  -- the set of good `x` is the agreement set of two coefficient vectors in `K` variables
  have hset : (univ.filter fun x : Point F K =>
      (linPoly hd (padB b)).eval x = g.eval (Fin.append x y))
      = univ.filter fun x : Point F K => (pevY g y).eval x = (linPoly hd (padB b)).eval x := by
    ext x
    simp [eval_pevY, eq_comm]
  by_cases hg : IsXLin hd g
  · -- two different linear forms
    have hne : pevY g y ≠ linPoly hd (padB b) := by
      rw [pevY_eq_linPoly hg]
      intro h
      apply hb
      funext j
      have := congrFun (linPoly_injective hd h) (Fin.castLE hr j)
      show (extract hd hr g j).eval y = b j
      rw [extract, if_pos hg]
      exact this.trans (padB_castLE hr b j)
    have hsz := card_agree_le hne
    rw [agreeX, hset]
    linarith
  · by_cases hq : (badQ hd g).eval y = 0
    · have : badInd hd g y = 1 := by rw [badInd, if_neg hg, if_pos hq]
      linarith
    · obtain ⟨ex, hex, hval⟩ := pevY_badQ hg y
      have hne : pevY g y ≠ linPoly hd (padB b) := by
        intro h
        apply hq
        rw [← hval, h, linPoly_of_forall_ne hd _ hex]
      have hsz := card_agree_le hne
      rw [agreeX, hset]
      linarith

/-- The forbidden coefficient vanishes at a uniform `y` with probability at most `m d / q`. -/
theorem sum_uniform_badInd_le (hd : 1 ≤ d) (g : LowIndDegPoly (F := F) (m := K + m) (d := d)) :
    ∑ y : Point F m, uniform (Point F m) y * badInd hd g y ≤ m * d / Fintype.card F := by
  classical
  by_cases hg : IsXLin hd g
  · simp only [badInd, if_pos hg, mul_zero, Finset.sum_const_zero]
    positivity
  · have hc := card_eval_eq_zero_le (badQ_ne_zero hg)
    simp only [badInd, if_neg hg, uniform]
    rw [← Finset.mul_sum, Finset.sum_boole, Fintype.card_fun, Fintype.card_fin]
    push_cast at hc ⊢
    rw [inv_mul_eq_div]
    exact hc

theorem sum_uniform_one (X : Type*) [Fintype X] [Nonempty X] : ∑ x, uniform X x = 1 := by
  simp [uniform, Finset.card_univ]

/-- **The weighted bound.** For nonnegative weights `β y b g` whose sum over the answer `b` does
not depend on `y` and totals one over the outcomes, the average agreement of the combined answer
exceeds the average agreement of the extracted tuple by at most `(K + m) d / q`. -/
theorem sum_agreeX_le (hd : 1 ≤ d) (hr : r ≤ K)
    (β : Point F m → (Fin r → F) → LowIndDegPoly (F := F) (m := K + m) (d := d) → ℝ)
    (hβ0 : ∀ y b g, 0 ≤ β y b g) (w : LowIndDegPoly (F := F) (m := K + m) (d := d) → ℝ)
    (hw : ∀ y g, ∑ b, β y b g = w g) (hw1 : ∑ g, w g = 1) :
    ∑ y : Point F m, uniform (Point F m) y * ∑ b, ∑ g, β y b g * agreeX hd g y b
      ≤ ∑ y : Point F m, uniform (Point F m) y *
          ∑ b, ∑ g, β y b g * (if extEval hd hr g y = b then 1 else 0)
        + (K + m) * d / Fintype.card F := by
  classical
  have hu0 : ∀ y, 0 ≤ uniform (Point F m) y := fun y => by simp only [uniform]; positivity
  have hw0 : ∀ g, 0 ≤ w g := fun g => by
    rw [← hw 0 g]; exact Finset.sum_nonneg fun b _ => hβ0 0 b g
  -- the pointwise bound, weighted
  have hpt : ∀ y, ∑ b, ∑ g, β y b g * agreeX hd g y b
      ≤ ∑ b, ∑ g, β y b g * (if extEval hd hr g y = b then 1 else 0)
        + K * d / Fintype.card F + ∑ g, w g * badInd hd g y := by
    intro y
    have hsplit : ∀ b g, β y b g * agreeX hd g y b
        ≤ β y b g * (if extEval hd hr g y = b then 1 else 0)
          + β y b g * (K * d / Fintype.card F) + β y b g * badInd hd g y := by
      intro b g
      have := mul_le_mul_of_nonneg_left (agreeX_le hd hr g y b) (hβ0 y b g)
      linarith [this]
    have hK : ∑ b, ∑ g, β y b g * (K * d / Fintype.card F) = K * d / Fintype.card F := by
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul, hw, hw1, one_mul]
    have hB : ∑ b, ∑ g, β y b g * badInd hd g y = ∑ g, w g * badInd hd g y := by
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul, hw]
    calc ∑ b, ∑ g, β y b g * agreeX hd g y b
        ≤ ∑ b, ∑ g, (β y b g * (if extEval hd hr g y = b then 1 else 0)
            + β y b g * (K * d / Fintype.card F) + β y b g * badInd hd g y) :=
          Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun g _ => hsplit b g
      _ = _ := by
          simp only [Finset.sum_add_distrib]
          rw [hK, hB]
  have hbad : ∑ y : Point F m, uniform (Point F m) y * ∑ g, w g * badInd hd g y
      ≤ m * d / Fintype.card F := by
    calc ∑ y : Point F m, uniform (Point F m) y * ∑ g, w g * badInd hd g y
        = ∑ g, w g * ∑ y : Point F m, uniform (Point F m) y * badInd hd g y := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun y _ => by ring
      _ ≤ ∑ g, w g * (m * d / Fintype.card F) :=
          Finset.sum_le_sum fun g _ =>
            mul_le_mul_of_nonneg_left (sum_uniform_badInd_le hd g) (hw0 g)
      _ = m * d / Fintype.card F := by rw [← Finset.sum_mul, hw1, one_mul]
  have hu1 := sum_uniform_one (Point F m)
  calc ∑ y : Point F m, uniform (Point F m) y * ∑ b, ∑ g, β y b g * agreeX hd g y b
      ≤ ∑ y : Point F m, uniform (Point F m) y *
          (∑ b, ∑ g, β y b g * (if extEval hd hr g y = b then 1 else 0)
            + K * d / Fintype.card F + ∑ g, w g * badInd hd g y) :=
        Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hpt y) (hu0 y)
    _ = ∑ y : Point F m, uniform (Point F m) y *
          ∑ b, ∑ g, β y b g * (if extEval hd hr g y = b then 1 else 0)
        + K * d / Fintype.card F
        + ∑ y : Point F m, uniform (Point F m) y * ∑ g, w g * badInd hd g y := by
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hu1, one_mul]
    _ ≤ _ := by
        have : (K + m : ℝ) * d / Fintype.card F
            = K * d / Fintype.card F + m * d / Fintype.card F := by ring
        rw [this]
        linarith

end Agree

/-! ## The operator form -/

section Operators

open Matrix

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ}
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

/-- **`inconsistency` is one minus the average agreement**, for POVMs on a unit vector and a
probability distribution on the questions. -/
theorem inconsistency_eq_one_sub {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
    {μ : X → ℝ} (hμ1 : ∑ x, μ x = 1) {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (M : X → POVM A dA) (N : X → POVM A dB) :
    inconsistency μ ψ M N
      = 1 - ∑ x, μ x * ∑ a, bornProb ψ (((M x).mats a).val) (((N x).mats a).val) := by
  have hx : ∀ x, (∑ a, ∑ b, if a = b then (0 : ℝ) else
      (star ψ ⬝ᵥ ((((M x).mats a).val ⊗ₖ ((N x).mats b).val) *ᵥ ψ)).re)
      = 1 - ∑ a, bornProb ψ (((M x).mats a).val) (((N x).mats a).val) := by
    intro x
    have h1 := sum_bornProb hψ (M x) (N x)
    have hsplit : ∀ a, (∑ b, if a = b then (0 : ℝ) else
        (star ψ ⬝ᵥ ((((M x).mats a).val ⊗ₖ ((N x).mats b).val) *ᵥ ψ)).re)
        = ∑ b, bornProb ψ (((M x).mats a).val) (((N x).mats b).val)
          - bornProb ψ (((M x).mats a).val) (((N x).mats a).val) := by
      intro a
      have : ∀ b, (if a = b then (0 : ℝ) else
          (star ψ ⬝ᵥ ((((M x).mats a).val ⊗ₖ ((N x).mats b).val) *ᵥ ψ)).re)
          = bornProb ψ (((M x).mats a).val) (((N x).mats b).val)
            - if a = b then bornProb ψ (((M x).mats a).val) (((N x).mats b).val) else 0 := by
        intro b
        split_ifs <;> simp [bornProb]
      rw [Finset.sum_congr rfl fun b _ => this b, Finset.sum_sub_distrib, Finset.sum_ite_eq,
        if_pos (Finset.mem_univ a)]
    rw [Finset.sum_congr rfl fun a _ => hsplit a, Finset.sum_sub_distrib, h1]
  unfold inconsistency
  rw [Finset.sum_congr rfl fun x _ => by rw [hx x],
    Finset.sum_congr rfl fun x _ => mul_sub (μ x) 1 _, Finset.sum_sub_distrib]
  simp [hμ1]

/-- Relabelling the second family: `∑_c ⟨P_c ⊗ (N.map f)_c⟩ = ∑_a ⟨P_{f a} ⊗ N_a⟩`. -/
theorem sum_bornProb_map_right {A C : Type*} [Fintype A] [Fintype C] [DecidableEq C]
    (ψ : dA × dB → ℂ) (P : C → Matrix dA dA ℂ) (N : POVM A dB) (f : A → C) :
    ∑ c, bornProb ψ (P c) (((N.map f).mats c).val)
      = ∑ a, bornProb ψ (P (f a)) ((N.mats a).val) := by
  classical
  simp only [POVM.map_mats, bornProb_sum_right]
  rw [← Finset.sum_fiberwise (univ : Finset A) f fun a => bornProb ψ (P (f a)) ((N.mats a).val)]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a ha => ?_
  rw [(Finset.mem_filter.mp ha).2]

/-- Relabelling the first family. -/
theorem sum_bornProb_map_left {A C : Type*} [Fintype A] [Fintype C] [DecidableEq C]
    (ψ : dA × dB → ℂ) (M : POVM A dA) (Q : C → Matrix dB dB ℂ) (f : A → C) :
    ∑ c, bornProb ψ (((M.map f).mats c).val) (Q c)
      = ∑ a, bornProb ψ ((M.mats a).val) (Q (f a)) := by
  classical
  simp only [POVM.map_mats, bornProb_sum_left]
  rw [← Finset.sum_fiberwise (univ : Finset A) f fun a => bornProb ψ ((M.mats a).val) (Q (f a))]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a ha => ?_
  rw [(Finset.mem_filter.mp ha).2]

/-- The combining coordinates of a padded point. -/
def xOf (u : Point F (K + m)) : Point F K := fun i => u (Fin.castAdd m i)

/-- The original coordinates of a padded point. -/
def yOf (u : Point F (K + m)) : Point F m := fun j => u (Fin.natAdd K j)

omit [Field F] [DecidableEq F] in
/-- **The uniform padded point is a uniform pair.** -/
theorem sum_uniform_pad (f : Point F K → Point F m → ℝ) :
    ∑ u : Point F (K + m), uniform (Point F (K + m)) u * f (xOf u) (yOf u)
      = ∑ y : Point F m, uniform (Point F m) y *
          ∑ x : Point F K, uniform (Point F K) x * f x y := by
  classical
  rw [← Fintype.sum_equiv (Fin.appendEquiv K m)
    (fun p => uniform (Point F (K + m)) (Fin.appendEquiv K m p)
      * f (xOf (Fin.appendEquiv K m p)) (yOf (Fin.appendEquiv K m p))) _ fun p => rfl,
    Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hx : xOf (Fin.appendEquiv K m (x, y)) = x := funext fun i => Fin.append_left x y i
  have hy : yOf (Fin.appendEquiv K m (x, y)) = y := funext fun j => Fin.append_right x y j
  rw [hx, hy]
  simp only [uniform, Fintype.card_fun, Fintype.card_fin]
  rw [pow_add]
  push_cast
  ring

/-- The average of an indicator over a uniform `x`, as `agreeX`. -/
theorem sum_uniform_agree (hd : 1 ≤ d)
    (g : LowIndDegPoly (F := F) (m := K + m) (d := d)) (y : Point F m) (b : Fin r → F) :
    ∑ x : Point F K, uniform (Point F K) x *
        (if (linPoly hd (padB b)).eval x = g.eval (Fin.append x y) then 1 else 0)
      = agreeX hd g y b := by
  classical
  simp only [uniform, agreeX, Fintype.card_fun, Fintype.card_fin]
  rw [← Finset.mul_sum, Finset.sum_boole]
  push_cast
  rw [inv_mul_eq_div]

/-- **The extraction bound, the extracted measurement on the second party.** -/
theorem inconsistency_extract_right_le (hd : 1 ≤ d) (hr : r ≤ K) {ψ : dA × dB → ℂ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (A : Point F m → POVM (Fin r → F) dA)
    (R : POVM (LowIndDegPoly (F := F) (m := K + m) (d := d)) dB) :
    inconsistency (uniform (Point F m)) ψ A (fun y => R.map fun g => extEval hd hr g y)
      ≤ inconsistency (uniform (Point F (K + m))) ψ
          (fun u => (A (yOf u)).map fun b => (linPoly hd (padB b)).eval (xOf u))
          (fun u => R.map fun g => g.eval u)
        + (K + m) * d / Fintype.card F := by
  classical
  set β : Point F m → (Fin r → F) → LowIndDegPoly (F := F) (m := K + m) (d := d) → ℝ :=
    fun y b g => bornProb ψ (((A y).mats b).val) ((R.mats g).val) with hβ
  have hβ0 : ∀ y b g, 0 ≤ β y b g := fun y b g =>
    bornProb_nonneg ψ ((A y).posSemidef b) (R.posSemidef g)
  have hw : ∀ y g, ∑ b, β y b g = bornProb ψ 1 ((R.mats g).val) := fun y g => by
    simp only [hβ]
    rw [← bornProb_sum_left, POVM.sum_val]
  have hw1 : ∑ g, bornProb ψ (1 : Matrix dA dA ℂ) ((R.mats g).val) = 1 := by
    rw [← bornProb_sum_right, POVM.sum_val, bornProb, Matrix.one_kronecker_one,
      Matrix.one_mulVec, hψ, Complex.one_re]
  have hmain := sum_agreeX_le hd hr β hβ0 _ hw hw1
  rw [inconsistency_eq_one_sub (sum_uniform_one _) hψ,
    inconsistency_eq_one_sub (sum_uniform_one _) hψ]
  -- the extracted agreement
  have hL : ∀ y, ∑ c, bornProb ψ (((A y).mats c).val)
        (((R.map fun g => extEval hd hr g y).mats c).val)
      = ∑ b, ∑ g, β y b g * (if extEval hd hr g y = b then 1 else 0) := by
    intro y
    rw [sum_bornProb_map_right, Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Finset.sum_eq_single (extEval hd hr g y) (fun b _ hb => by
      rw [if_neg (Ne.symm hb), mul_zero]) (fun h => absurd (Finset.mem_univ _) h), if_pos rfl,
      mul_one]
  -- the combined agreement
  have hR : ∀ u : Point F (K + m), ∑ c,
      bornProb ψ ((((A (yOf u)).map fun b => (linPoly hd (padB b)).eval (xOf u)).mats c).val)
        (((R.map fun g => g.eval u).mats c).val)
      = ∑ b, ∑ g, β (yOf u) b g *
          (if (linPoly hd (padB b)).eval (xOf u) = g.eval (Fin.append (xOf u) (yOf u))
            then 1 else 0) := by
    intro u
    have hu : Fin.append (xOf u) (yOf u) = u := by
      funext k
      refine Fin.addCases (fun i => ?_) (fun j => ?_) k
      · rw [Fin.append_left]; rfl
      · rw [Fin.append_right]; rfl
    rw [hu, sum_bornProb_map (MA := fun _ : Unit => A (yOf u)) (MB := fun _ : Unit => R)
      (x := ()) (y := ())]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun g _ => by ring
  simp only [hL, hR]
  rw [sum_uniform_pad (fun x y => ∑ b, ∑ g, β y b g *
      (if (linPoly hd (padB b)).eval x = g.eval (Fin.append x y) then 1 else 0))]
  have hswap : ∀ y, ∑ x : Point F K, uniform (Point F K) x * ∑ b, ∑ g, β y b g *
        (if (linPoly hd (padB b)).eval x = g.eval (Fin.append x y) then 1 else 0)
      = ∑ b, ∑ g, β y b g * agreeX hd g y b := by
    intro y
    simp only [Finset.mul_sum, ← sum_uniform_agree hd]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun x _ => by ring
  simp only [hswap]
  linarith

/-- **The extraction bound, the extracted measurement on the first party.** -/
theorem inconsistency_extract_left_le (hd : 1 ≤ d) (hr : r ≤ K) {ψ : dA × dB → ℂ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (R : POVM (LowIndDegPoly (F := F) (m := K + m) (d := d)) dA)
    (B : Point F m → POVM (Fin r → F) dB) :
    inconsistency (uniform (Point F m)) ψ (fun y => R.map fun g => extEval hd hr g y) B
      ≤ inconsistency (uniform (Point F (K + m))) ψ
          (fun u => R.map fun g => g.eval u)
          (fun u => (B (yOf u)).map fun b => (linPoly hd (padB b)).eval (xOf u))
        + (K + m) * d / Fintype.card F := by
  classical
  set β : Point F m → (Fin r → F) → LowIndDegPoly (F := F) (m := K + m) (d := d) → ℝ :=
    fun y b g => bornProb ψ ((R.mats g).val) (((B y).mats b).val) with hβ
  have hβ0 : ∀ y b g, 0 ≤ β y b g := fun y b g =>
    bornProb_nonneg ψ (R.posSemidef g) ((B y).posSemidef b)
  have hw : ∀ y g, ∑ b, β y b g = bornProb ψ ((R.mats g).val) 1 := fun y g => by
    simp only [hβ]
    rw [← bornProb_sum_right, POVM.sum_val]
  have hw1 : ∑ g, bornProb ψ ((R.mats g).val) (1 : Matrix dB dB ℂ) = 1 := by
    rw [← bornProb_sum_left, POVM.sum_val, bornProb, Matrix.one_kronecker_one,
      Matrix.one_mulVec, hψ, Complex.one_re]
  have hmain := sum_agreeX_le hd hr β hβ0 _ hw hw1
  rw [inconsistency_eq_one_sub (sum_uniform_one _) hψ,
    inconsistency_eq_one_sub (sum_uniform_one _) hψ]
  have hL : ∀ y, ∑ c, bornProb ψ (((R.map fun g => extEval hd hr g y).mats c).val)
        (((B y).mats c).val)
      = ∑ b, ∑ g, β y b g * (if extEval hd hr g y = b then 1 else 0) := by
    intro y
    rw [sum_bornProb_map_left, Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Finset.sum_eq_single (extEval hd hr g y) (fun b _ hb => by
      rw [if_neg (Ne.symm hb), mul_zero]) (fun h => absurd (Finset.mem_univ _) h), if_pos rfl,
      mul_one]
  have hR : ∀ u : Point F (K + m), ∑ c,
      bornProb ψ (((R.map fun g => g.eval u).mats c).val)
        ((((B (yOf u)).map fun b => (linPoly hd (padB b)).eval (xOf u)).mats c).val)
      = ∑ b, ∑ g, β (yOf u) b g *
          (if (linPoly hd (padB b)).eval (xOf u) = g.eval (Fin.append (xOf u) (yOf u))
            then 1 else 0) := by
    intro u
    have hu : Fin.append (xOf u) (yOf u) = u := by
      funext k
      refine Fin.addCases (fun i => ?_) (fun j => ?_) k
      · rw [Fin.append_left]; rfl
      · rw [Fin.append_right]; rfl
    rw [hu, sum_bornProb_map (MA := fun _ : Unit => R) (MB := fun _ : Unit => B (yOf u))
      (x := ()) (y := ()), Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun g _ => by
      simp only [hβ, eq_comm]; ring
  simp only [hL, hR]
  rw [sum_uniform_pad (fun x y => ∑ b, ∑ g, β y b g *
      (if (linPoly hd (padB b)).eval x = g.eval (Fin.append x y) then 1 else 0))]
  have hswap : ∀ y, ∑ x : Point F K, uniform (Point F K) x * ∑ b, ∑ g, β y b g *
        (if (linPoly hd (padB b)).eval x = g.eval (Fin.append x y) then 1 else 0)
      = ∑ b, ∑ g, β y b g * agreeX hd g y b := by
    intro y
    simp only [Finset.mul_sum, ← sum_uniform_agree hd]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun x _ => by ring
  simp only [hswap]
  linarith

end Operators

/-! ## The extracted measurements, and the three conclusions -/

section Assembly

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ}
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

/-- **Data processing for `inconsistency`**: relabelling both families' outcomes the same way can
only decrease the disagreement. -/
theorem inconsistency_map_le {X A C : Type*} [Fintype X] [Fintype A] [DecidableEq A] [Fintype C]
    [DecidableEq C] {μ : X → ℝ} (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1) {ψ : dA × dB → ℂ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (M : X → POVM A dA) (N : X → POVM A dB) (f : A → C) :
    inconsistency μ ψ (fun x => (M x).map f) (fun x => (N x).map f) ≤ inconsistency μ ψ M N := by
  classical
  rw [inconsistency_eq_one_sub hμ1 hψ, inconsistency_eq_one_sub hμ1 hψ]
  have hx : ∀ x, ∑ a, bornProb ψ (((M x).mats a).val) (((N x).mats a).val)
      ≤ ∑ c, bornProb ψ ((((M x).map f).mats c).val) ((((N x).map f).mats c).val) := by
    intro x
    rw [sum_bornProb_map (MA := M) (MB := N) (x := x) (y := x)]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), if_pos rfl, one_mul]
    have : 0 ≤ ∑ b ∈ Finset.univ.erase a, (if f a = f b then (1 : ℝ) else 0)
        * bornProb ψ (((M x).mats a).val) (((N x).mats b).val) :=
      Finset.sum_nonneg fun b _ => mul_nonneg (by split_ifs <;> norm_num)
        (bornProb_nonneg ψ ((M x).posSemidef a) ((N x).posSemidef b))
    linarith
  have := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hx x) (hμ0 x)
  linarith

/-- A projective measurement's matrices form a projective family. -/
theorem isPVM_pm {X A : Type*} [Fintype A] {n : Type*} [Fintype n] [DecidableEq n]
    (P : ProjectiveMeasurement X A (Matrix n n ℂ)) (x : X) : IsPVM (P.M x) where
  isSelfAdjoint a := by rw [← Matrix.star_eq_conjTranspose]; exact P.selfAdjoint x a
  idem a := P.projective x a
  sum_eq_one := P.normalized x

/-- **The extracted measurement**: `R` coarse-grained by `extract`, still projective. -/
def extractPM (hd : 1 ≤ d) (hr : r ≤ K) {n : Type*} [Fintype n] [DecidableEq n]
    (R : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := K + m) (d := d))
      (Matrix n n ℂ)) :
    ProjectiveMeasurement Unit (Fin r → LowIndDegPoly (F := F) (m := m) (d := d))
      (Matrix n n ℂ) := by
  classical
  exact ProjectiveMeasurement.ofIsPVM (fun _ => (R.toPOVM ()).map (extract hd hr)) fun _ => by
    have h := (isPVM_pm R ()).coarse (extract hd hr)
    convert h using 1
    funext c
    rw [POVM.map_mats]
    rfl

theorem extractPM_toPOVM (hd : 1 ≤ d) (hr : r ≤ K) {n : Type*} [Fintype n] [DecidableEq n]
    (R : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := K + m) (d := d))
      (Matrix n n ℂ)) :
    (extractPM hd hr R).toPOVM () = (R.toPOVM ()).map (extract hd hr) := by
  classical
  unfold extractPM
  convert ProjectiveMeasurement.toPOVM_ofIsPVM _ _ ()

/-- A measurement of `r`-tuples of polynomials, evaluated at `y`. -/
def evalTuplePOVM {n : Type*} [Fintype n] [DecidableEq n]
    (G : ProjectiveMeasurement Unit (Fin r → LowIndDegPoly (F := F) (m := m) (d := d))
      (Matrix n n ℂ)) (y : Point F m) : POVM (Fin r → F) n :=
  (G.toPOVM ()).map fun g j => (g j).eval y

theorem evalTuplePOVM_extractPM (hd : 1 ≤ d) (hr : r ≤ K) {n : Type*} [Fintype n]
    [DecidableEq n]
    (R : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := K + m) (d := d))
      (Matrix n n ℂ)) (y : Point F m) :
    evalTuplePOVM (extractPM hd hr R) y = (R.toPOVM ()).map fun g => extEval hd hr g y := by
  rw [evalTuplePOVM, extractPM_toPOVM, POVM.map_map]
  rfl

/-- The combined point measurement: at the padded point `(x, y)`, measure the original point
measurement at `y` and answer `∑_{j < r} x_j b_j`. -/
def combPOVM {n : Type*} [Fintype n] [DecidableEq n] (hd : 1 ≤ d)
    (A : Point F m → POVM (Fin r → F) n) (u : Point F (K + m)) : POVM F n :=
  (A (yOf u)).map fun b => (linPoly hd (padB b)).eval (xOf u)

/-- **From the single-codeword conclusions to the simultaneous ones** (the paper's Step 4). If the
two players' measurements `RA`, `RB` of polynomials in the `K + m` variables satisfy the three
conclusions of the single-codeword theorem against the combined point measurements, with error
`δ`, then their extractions satisfy the three conclusions of the simultaneous theorem against the
original point measurements, with error `δ + (K + m) d / q` for the two point conclusions and `δ`
for the full-tuple one. -/
theorem extracted_conclusions (hd : 1 ≤ d) (hr : r ≤ K) {ψ : dA × dB → ℂ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (A : Point F m → POVM (Fin r → F) dA)
    (B : Point F m → POVM (Fin r → F) dB)
    (RA : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := K + m) (d := d))
      (Matrix dA dA ℂ))
    (RB : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := K + m) (d := d))
      (Matrix dB dB ℂ)) {δ : ℝ}
    (h1 : inconsistency (uniform (Point F (K + m))) ψ (combPOVM hd A) (evalPOVM RB) ≤ δ)
    (h2 : inconsistency (uniform (Point F (K + m))) ψ (evalPOVM RA) (combPOVM hd B) ≤ δ)
    (h3 : inconsistency (uniform Unit) ψ (fun _ => RA.toPOVM ()) (fun _ => RB.toPOVM ()) ≤ δ) :
    inconsistency (uniform (Point F m)) ψ A (evalTuplePOVM (extractPM hd hr RB))
        ≤ δ + (K + m) * d / Fintype.card F ∧
      inconsistency (uniform (Point F m)) ψ (evalTuplePOVM (extractPM hd hr RA)) B
        ≤ δ + (K + m) * d / Fintype.card F ∧
      inconsistency (uniform Unit) ψ (fun _ => (extractPM hd hr RA).toPOVM ())
        (fun _ => (extractPM hd hr RB).toPOVM ()) ≤ δ := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · have h := inconsistency_extract_right_le hd hr hψ A (RB.toPOVM ())
    have heq : (fun y => evalTuplePOVM (extractPM hd hr RB) y)
        = fun y => (RB.toPOVM ()).map fun g => extEval hd hr g y :=
      funext fun y => evalTuplePOVM_extractPM hd hr RB y
    rw [show evalTuplePOVM (extractPM hd hr RB) = fun y => evalTuplePOVM (extractPM hd hr RB) y
      from rfl, heq]
    exact h.trans (by unfold combPOVM evalPOVM at h1; linarith)
  · have h := inconsistency_extract_left_le hd hr hψ (RA.toPOVM ()) B
    have heq : (fun y => evalTuplePOVM (extractPM hd hr RA) y)
        = fun y => (RA.toPOVM ()).map fun g => extEval hd hr g y :=
      funext fun y => evalTuplePOVM_extractPM hd hr RA y
    rw [show evalTuplePOVM (extractPM hd hr RA) = fun y => evalTuplePOVM (extractPM hd hr RA) y
      from rfl, heq]
    exact h.trans (by unfold combPOVM evalPOVM at h2; linarith)
  · rw [extractPM_toPOVM, extractPM_toPOVM]
    exact (inconsistency_map_le (fun _ => by simp only [uniform]; positivity)
      (sum_uniform_one Unit) hψ (fun _ => RA.toPOVM ()) (fun _ => RB.toPOVM ())
      (extract hd hr)).trans h3

end Assembly

end MIPRE.LIDT.Simul

end

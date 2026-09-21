/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.MvPolynomial.Degrees
import MIPRE.Foundations.LowDegree.Encoding

/-!
# Restricting a polynomial to a line

The expansion stage's line measurements are indexed by the *restriction to a line* of the
low-degree encoding of the ancilla's measurement outcome. This file is that operation: substitute
the affine parametrization `t -> u0 + t . w` into a multivariate polynomial and read off the
univariate coefficients.

Two facts are all the consumers need:

* `eval_lineRestrict` --- evaluating the restriction at `t` is evaluating the polynomial at the
  point `u0 + t . w`, so the restriction carries the same information along the line;
* `natDegree_lineRestrict_le` --- the restriction has degree at most the total degree, so a
  multilinear polynomial in `m` variables restricts to degree at most `m` and the coefficient
  vector fits in a `LinePoly F m`.

`lineCoeffs` packages the coefficients as the `LinePoly` the games use, and `eval_lineCoeffs`
is the composite of the two.
-/

noncomputable section

namespace MIPRE.LowDegree

open Finset

variable {F : Type*} [Field F] {m : ℕ}

/-- **The restriction of a multivariate polynomial to the line** `t ↦ u₀ + t • w`, as a
univariate polynomial. -/
def lineRestrict (u₀ w : Fin m → F) (p : MvPolynomial (Fin m) F) : Polynomial F :=
  MvPolynomial.aeval (fun i => Polynomial.C (u₀ i) + Polynomial.X * Polynomial.C (w i)) p

@[simp] theorem lineRestrict_zero (u₀ w : Fin m → F) :
    lineRestrict u₀ w (0 : MvPolynomial (Fin m) F) = 0 := by
  rw [lineRestrict, map_zero]

/-- **Evaluating the restriction is evaluating along the line.** -/
theorem eval_lineRestrict (u₀ w : Fin m → F) (p : MvPolynomial (Fin m) F) (t : F) :
    (lineRestrict u₀ w p).eval t = MvPolynomial.eval (u₀ + t • w) p := by
  have key : ((Polynomial.aeval t).comp (MvPolynomial.aeval
      (fun i => Polynomial.C (u₀ i) + Polynomial.X * Polynomial.C (w i))) :
        MvPolynomial (Fin m) F →ₐ[F] F) = MvPolynomial.aeval (u₀ + t • w) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    simp
    ring
  simpa [lineRestrict] using congrArg (fun φ => φ p) key

/-- **The restriction has degree at most the total degree.** -/
theorem natDegree_lineRestrict_le (u₀ w : Fin m → F) (p : MvPolynomial (Fin m) F) :
    (lineRestrict u₀ w p).natDegree ≤ p.totalDegree := by
  have hlin : ∀ a b : F, (Polynomial.C a + Polynomial.X * Polynomial.C b).natDegree ≤ 1 := by
    intro a b
    refine le_trans (Polynomial.natDegree_add_le _ _) (max_le (by simp) ?_)
    exact le_trans Polynomial.natDegree_mul_le (by simp)
  rw [lineRestrict, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun d hd => ?_
  refine le_trans (Polynomial.natDegree_mul_le) ?_
  have h0 : (algebraMap F (Polynomial F) (MvPolynomial.coeff d p)).natDegree = 0 := by
    simp [Polynomial.algebraMap_eq]
  rw [h0, zero_add]
  refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
  refine le_trans (Finset.sum_le_sum fun i _ => ?_) (MvPolynomial.le_totalDegree hd)
  calc ((Polynomial.C (u₀ i) + Polynomial.X * Polynomial.C (w i)) ^ d i).natDegree
      ≤ d i * (Polynomial.C (u₀ i) + Polynomial.X * Polynomial.C (w i)).natDegree :=
        Polynomial.natDegree_pow_le
    _ ≤ d i * 1 := Nat.mul_le_mul_left _ (hlin _ _)
    _ = d i := mul_one _

/-- **On an axis-parallel line the restriction has degree at most the individual degree in that
coordinate.** Along `u_0 + t e_j` only the `j`-th variable moves, so every other substitution is a
constant and the degree in `t` is the degree of `p` in `X_j`. This is what makes a *multilinear*
encoding restrict to an affine function of the line parameter. -/
theorem natDegree_lineRestrict_single_le (u₀ : Fin m → F) (j : Fin m)
    (p : MvPolynomial (Fin m) F) :
    (lineRestrict u₀ (Pi.single j 1) p).natDegree ≤ p.degreeOf j := by
  classical
  rw [lineRestrict, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun dd hdd => ?_
  refine le_trans Polynomial.natDegree_mul_le ?_
  have h0 : (algebraMap F (Polynomial F) (MvPolynomial.coeff dd p)).natDegree = 0 := by
    simp [Polynomial.algebraMap_eq]
  rw [h0, zero_add]
  have hterm : ∀ i : Fin m,
      (((Polynomial.C (u₀ i) + Polynomial.X
          * Polynomial.C ((Pi.single j 1 : Fin m → F) i)) ^ dd i) : Polynomial F).natDegree
        ≤ if i = j then dd i else 0 := by
    intro i
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      refine le_trans Polynomial.natDegree_pow_le ?_
      refine le_trans (Nat.mul_le_mul_left _ ?_) (le_of_eq (mul_one _))
      refine le_trans (Polynomial.natDegree_add_le _ _) (max_le (by simp) ?_)
      exact le_trans Polynomial.natDegree_mul_le (by simp)
    · rw [if_neg hij, Pi.single_eq_of_ne hij, map_zero, mul_zero, add_zero, ← Polynomial.C_pow,
        Polynomial.natDegree_C]
  refine le_trans (le_trans (Polynomial.natDegree_prod_le _ _)
    (Finset.sum_le_sum fun i _ => hterm i)) ?_
  rw [Finset.sum_ite_eq' dd.support j (fun i => dd i)]
  by_cases hj : j ∈ dd.support
  · rw [if_pos hj]
    exact MvPolynomial.monomial_le_degreeOf j hdd
  · rw [if_neg hj]
    exact Nat.zero_le _

/-- **The coefficient vector of the restriction, evaluated at `t`.** This is the form the games
use: a polynomial of degree at most `n` is a vector of `n + 1` coefficients, and evaluating that
vector at `t` is evaluating the polynomial along the line. -/
theorem sum_coeff_lineRestrict {n : ℕ} {p : MvPolynomial (Fin m) F} (hp : p.totalDegree ≤ n)
    (u₀ w : Fin m → F) (t : F) :
    ∑ i : Fin (n + 1), (lineRestrict u₀ w p).coeff (i : ℕ) * t ^ (i : ℕ)
      = MvPolynomial.eval (u₀ + t • w) p := by
  rw [← eval_lineRestrict u₀ w p t, Fin.sum_univ_eq_sum_range
    (fun i => (lineRestrict u₀ w p).coeff i * t ^ i) (n + 1)]
  exact (Polynomial.eval_eq_sum_range'
    (Nat.lt_succ_of_le ((natDegree_lineRestrict_le u₀ w p).trans hp)) t).symm

end MIPRE.LowDegree

end

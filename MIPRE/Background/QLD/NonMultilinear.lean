/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.LowDegree.SchwartzZippel
import MIPRE.Foundations.LowDegree.Encoding

/-!
# The non-multilinear mass, and Schwartz--Zippel in the agreement direction

This file is the repair of the campaign's critical finding at ledger node `1.2.2.15`, recorded in
blueprint `rem:qld-admitted`.

The separating stage of the appendix needs to replace, inside a Born average, the evaluation
`g(u)` of an outcome `g` of individual degree at most `d` by the evaluation
`Coded(g) . ind_m(u)` --- which is the evaluation at `u` of the *multilinear* interpolant of `g`'s
values on the cube `{0,1}^m`. The two agree for multilinear `g` and not otherwise.

An earlier revision of the paper bounded the substitution error by `2 E_u 1[g(u) != g_k(u)] <=
2md/q`. **That applies Schwartz--Zippel backwards.** What Schwartz--Zippel gives is that two
*distinct* polynomials of total degree at most `md` *agree* on at most an `md/q` fraction of
`F_q^m`; so for a non-multilinear `g` the *disagreement* indicator has expectation close to `1`,
not close to `0`, and the step as written was equivalent to an unproven assertion.

The two halves of the correct argument are the two halves of this file, and neither mentions the
game.

## The agreement bound, in the right direction

`prob_agree_ldEnc_le_of_not_multilinear`: a polynomial of individual degree at most `d` that is
**not** multilinear agrees with the multilinear interpolant of *any* boolean-cube data on at most
an `md/q` fraction of points. The point is that non-multilinearity makes `g` distinct from every
multilinear polynomial at once, so a single application of
`MIPRE.LowDegree.prob_agree_le_individualDegree` covers every `k` uniformly --- which is what the
next step needs, since it sums over `k`.

## The mass bound

`nonMultilinear_mass_le`: the combinatorial step that turns the agreement bound into a bound on the
*mass* the outcome distribution places on non-multilinear outcomes. Stated for abstract
nonnegative weights, because that is all it uses: a distribution `S` on outcomes, a subdistribution
`T` dominated by it, a set `ML` of good outcomes, the agreement bound `T g <= c * S g` off `ML`,
and a lower bound `1 - eta` on `T`'s total. The conclusion is `S (ML^c) <= eta + c`.

`sum_sub_le_of_eq_on`: the substitution error itself, once the mass is bounded. Two families
agreeing on `ML` and each dominated by `S` in absolute value differ in total by at most twice the
mass off `ML`.

## What is not here

That the substituted quantity agrees with the original *on* the multilinear outcomes --- the
paper's parenthesis "there `g_{Coded(g)} = g`" --- is the statement that a multilinear polynomial
is the interpolant of its own values on `{0,1}^m`, i.e. that multilinear interpolation is unique.
It is an independent fact about `MvPolynomial`, not part of this repair, and it is an outstanding
ingredient: `sum_sub_le_of_eq_on` accordingly takes the agreement on the good set as a
hypothesis rather than deriving it.
-/

noncomputable section

namespace MIPRE.QLD

open Finset MvPolynomial MIPRE.LowDegree

/-! ## Schwartz--Zippel against every multilinear polynomial at once -/

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ}

/-- **A non-multilinear polynomial of individual degree at most `d` agrees with the multilinear
interpolant of any cube data on at most an `md/q` fraction of `F_q^m`.**

This is Schwartz--Zippel in the *agreement* direction, which is the direction the appendix needs
and the direction an earlier revision of the paper had backwards. The hypothesis is that `g` fails
to be multilinear, and the conclusion is uniform in the interpolated data `a` --- both matter: the
consumer sums over all of `F_q^M`, and would gain nothing from a bound depending on `a`. -/
theorem prob_agree_ldEnc_le_of_not_multilinear {g : MvPolynomial (Fin m) F}
    (hg : ∀ i, g.degreeOf i ≤ d) (hd : 1 ≤ d) (hnml : ¬ ∀ i, g.degreeOf i ≤ 1)
    (a : (Fin m → Bool) → F) :
    ((agree g (ldEnc a)).card : ℝ) / (Fintype.card F : ℝ) ^ m
      ≤ (m : ℝ) * d / Fintype.card F := by
  have hne : g ≠ ldEnc a := fun h => hnml fun i => by
    rw [h]; exact degreeOf_ldEnc_le a i
  exact prob_agree_le_individualDegree hne hg fun i => (degreeOf_ldEnc_le a i).trans hd

/-! ## The mass the outcome distribution places off a good set -/

variable {G : Type*} [Fintype G] [DecidableEq G]

/-- **The mass bound.** If `T` is dominated by the distribution `S`, is at most `c` times `S` away
from the good set `ML`, and still carries total weight at least `1 - eta`, then `S` puts at most
`eta + c` off `ML`.

This is the appendix's aggregation step, and it is the shape the repaired argument needs: the
agreement bound of `prob_agree_ldEnc_le_of_not_multilinear` is exactly the hypothesis `hoff` at
`c = md/q`. The proof is one split of the total: on `ML` only the domination `T <= S` is available,
off `ML` the agreement bound applies, and comparing with `sum S = 1` isolates the mass off `ML`. -/
theorem nonMultilinear_mass_le {S T : G → ℝ} {ML : Finset G} {c eta : ℝ}
    (hS : ∀ g, 0 ≤ S g) (hsum : ∑ g, S g = 1) (hT : ∀ g, T g ≤ S g)
    (hoff : ∀ g ∉ ML, T g ≤ c * S g) (hc : 0 ≤ c) (hlow : 1 - eta ≤ ∑ g, T g) :
    ∑ g ∈ univ \ ML, S g ≤ eta + c := by
  classical
  have hsplit : ∀ f : G → ℝ, ∑ g ∈ univ \ ML, f g + ∑ g ∈ ML, f g = ∑ g, f g :=
    fun f => Finset.sum_sdiff (Finset.subset_univ ML)
  -- on the good set only domination is available
  have hgood : ∑ g ∈ ML, T g ≤ ∑ g ∈ ML, S g := Finset.sum_le_sum fun g _ => hT g
  -- off it the agreement bound applies, and the remaining mass is at most one
  have hbadS : ∑ g ∈ univ \ ML, S g ≤ 1 := by
    have h0 : 0 ≤ ∑ g ∈ ML, S g := Finset.sum_nonneg fun g _ => hS g
    have := hsplit S
    linarith
  have hbad : ∑ g ∈ univ \ ML, T g ≤ c * ∑ g ∈ univ \ ML, S g := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun g hg => hoff g (Finset.mem_sdiff.mp hg).2
  have hbad' : ∑ g ∈ univ \ ML, T g ≤ c := le_trans hbad (by nlinarith)
  have hS' := hsplit S
  have hT' := hsplit T
  linarith

/-- **The substitution error.** Two families that agree on `ML` and are each dominated in absolute
value by `S` differ in total by at most twice the mass off `ML`. -/
theorem sum_sub_le_of_eq_on {A B S : G → ℝ} {ML : Finset G}
    (hon : ∀ g ∈ ML, A g = B g) (hA : ∀ g, |A g| ≤ S g) (hB : ∀ g, |B g| ≤ S g) :
    |∑ g, A g - ∑ g, B g| ≤ 2 * ∑ g ∈ univ \ ML, S g := by
  classical
  have hsplit : ∀ f : G → ℝ, ∑ g, f g = ∑ g ∈ univ \ ML, f g + ∑ g ∈ ML, f g :=
    fun f => (Finset.sum_sdiff (Finset.subset_univ ML)).symm
  have hML : ∑ g ∈ ML, A g = ∑ g ∈ ML, B g := Finset.sum_congr rfl hon
  have hdiff : ∑ g, A g - ∑ g, B g
      = ∑ g ∈ univ \ ML, A g - ∑ g ∈ univ \ ML, B g := by
    rw [hsplit A, hsplit B, hML]; ring
  have h1 : |∑ g ∈ univ \ ML, A g| ≤ ∑ g ∈ univ \ ML, S g :=
    le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun g _ => hA g)
  have h2 : |∑ g ∈ univ \ ML, B g| ≤ ∑ g ∈ univ \ ML, S g :=
    le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun g _ => hB g)
  rw [abs_le] at h1 h2
  rw [hdiff, abs_le]
  exact ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩

end MIPRE.QLD

end

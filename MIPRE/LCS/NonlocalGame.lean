/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Games
import MIPRE.LCS.EPR

/-!
# The Nonlocal Game of a Linear Constraint System

This file interprets an LCS instance (`MIPRE.LCS.Game`) as a two-player one-round
nonlocal game in the sense of `MIPRE.Game`, connecting the operator-algebraic
perfect-play formalism of `MIPRE.LCS` with the game-value framework of
`MIPRE.Foundations.Games`.

## Main definitions

- `MIPRE.LCS.Game.toNonlocalGame`: the nonlocal game of an LCS instance. The referee
  samples an equation `i` uniformly at random, then a uniformly random variable
  `j ∈ V i`; Alice answers a full assignment (of which only the restriction to the
  support of `i` is read), Bob answers the value of his variable, and they win if
  Alice's assignment satisfies equation `i` and agrees with Bob's answer at `j`.

## Main statements

- `MIPRE.LCS.exists_tensorStrategy_value_eq_one_of_localLoss_annihilates_epr` (sorried):
  a bipartite observable strategy whose local loss operators annihilate the
  (unnormalized) EPR vector yields a perfect tensor-product strategy for the
  associated nonlocal game.
-/

namespace MIPRE.LCS

open Matrix

variable {G : Layout}

/-- The nonlocal game associated with an LCS instance: the referee samples an equation
`i` uniformly at random, then a uniformly random variable `j ∈ V i`. Alice answers a
full assignment `a : Fin G.s → ZMod 2` (only its restriction to the support of `i` is
read), Bob answers the value `b` of his variable, and the answers are accepted if `a`
satisfies equation `i` and `a j = b`.

The question distribution assigns probability `1 / (G.r * (G.V i).card)` to each pair
`(i, j)` with `j ∈ G.V i`, matching the normalization of `winningOperator`. The
hypotheses `hr` and `hV` guarantee that it is a probability distribution. The decision
predicate deliberately ignores whether `j ∈ G.V i`, since `μ` vanishes off-support. -/
noncomputable def Game.toNonlocalGame (game : Game G)
    (hr : 0 < G.r) (hV : ∀ i, (G.V i).Nonempty) :
    MIPRE.Game (Fin G.r) (Fin G.s) (Fin G.s → ZMod 2) (ZMod 2) where
  μ i j := if j ∈ G.V i then 1 / ((G.r : ℝ) * ((G.V i).card : ℝ)) else 0
  μ_nonneg i j := by split_ifs <;> positivity
  μ_sum_one := by
    have hr' : ((G.r : ℝ)) ≠ 0 := by
      exact_mod_cast hr.ne'
    calc ∑ i, ∑ j, (if j ∈ G.V i then 1 / ((G.r : ℝ) * ((G.V i).card : ℝ)) else 0)
        = ∑ i : Fin G.r, 1 / (G.r : ℝ) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          have hcard : (((G.V i).card : ℝ)) ≠ 0 := by
            exact_mod_cast (hV i).card_pos.ne'
          rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
          field_simp
      _ = 1 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
  D i j a b := decide ((∑ k ∈ G.V i, a k) = game.b i ∧ a j = b)

/-- A bipartite observable strategy whose local loss operators all annihilate the
(unnormalized) EPR vector yields a perfect tensor-product strategy for the associated
nonlocal game.

Intended proof: take `dA = dB = Fintype.card n`, let `ψ` be the normalized EPR state
transported along an equivalence `n ≃ Fin (Fintype.card n)`, let Alice's projective
measurement for question `i` be the joint measurement `strat.toProjectorStrategy.E i`
restricted to the first tensor factor, and let Bob's projective measurement for
question `j` be the binary measurement of `strat.obs j`. The `[Nonempty n]` hypothesis
is necessary: for empty `n` the hypothesis `hLoss` is vacuous while no unit vector
exists. -/
theorem exists_tensorStrategy_value_eq_one_of_localLoss_annihilates_epr
    (game : Game G) (hr : 0 < G.r) (hV : ∀ i, (G.V i).Nonempty)
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (strat : BipartiteObservableStrategy n G)
    (hLoss : ∀ (i : Fin G.r) (j : G.V i),
      localLossOperator game strat.toProjectorStrategy i j *ᵥ eprVec n = 0) :
    ∃ S : MIPRE.TensorProductStrategy (game.toNonlocalGame hr hV), S.value = 1 :=
  sorry

end MIPRE.LCS

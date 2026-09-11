/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.Repetition.CommutingRepetition.MainTheorem.Main
import MIPRE.Background.Repetition.Direct
import MIPRE.Foundations.CommutingOperator

/-!
# Direct parallel repetition for commuting-operator strategies

The uniform direct parallel repetition theorem for commuting-operator strategies
(blueprint `thm:direct-repetition-co`), in the vocabulary of this repository, transferred
from the vendored development `MIPRE/Background/Repetition/CommutingRepetition/`
(Vidick, *Uniform direct parallel repetition for two-player commuting-operator
strategies*, 2026): there is a universal `c > 0` such that for every game `G` with
nonempty alphabets and every `n ≥ 1`,
`valco(G^{⊗n}) ≤ exp(-c·n·ε⁷/(ε + log(|A||B|)))` where `ε = 1 - valco(G)`.

The transfer is a field-by-field identification: a `MIPRE.Game` is a game of the vendored
development with `{0,1}`-valued payoff, `MIPRE.CommutingOperatorStrategy` is its
`CommutingStrategy` at universe `0`, the two suprema defining the value range over the
same set of reals, and the two direct repetitions agree (a product of `{0,1}`-valued
payoffs is the indicator of the conjunction).
-/

namespace MIPRE.Repetition

open scoped BigOperators InnerProductSpace

section Bridge

variable {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- A game of this repository as a game of the vendored development: the decision
predicate becomes a `{0,1}`-valued payoff. -/
def toCR (G : Game X Y A B) : CommutingRepetition.Game X Y A B where
  questionWeight := G.μ
  weight_nonneg := G.μ_nonneg
  weight_normalized := G.μ_sum_one
  payoff x y a b := if G.D x y a b then 1 else 0
  payoff_nonneg x y a b := by split_ifs <;> norm_num
  payoff_le_one x y a b := by split_ifs <;> norm_num

/-- A commuting-operator strategy of this repository as one of the vendored development. -/
def toCRStrategy (S : CommutingOperatorStrategy X Y A B) :
    CommutingRepetition.CommutingStrategy.{0} X Y A B where
  H := S.H
  ψ := S.ψ
  ψ_norm := S.ψ_norm
  E := S.E
  F := S.F
  E_pos := S.E_pos
  F_pos := S.F_pos
  E_sum := S.E_sum
  F_sum := S.F_sum
  commutes := S.commutes

/-- A commuting-operator strategy of the vendored development as one of this repository. -/
def ofCRStrategy (S : CommutingRepetition.CommutingStrategy.{0} X Y A B) :
    CommutingOperatorStrategy X Y A B where
  H := S.H
  ψ := S.ψ
  ψ_norm := S.ψ_norm
  E := S.E
  F := S.F
  E_pos := S.E_pos
  F_pos := S.F_pos
  E_sum := S.E_sum
  F_sum := S.F_sum
  commutes := S.commutes

/-- The value of a strategy is its winning probability in the vendored development. -/
theorem win_toCRStrategy (G : Game X Y A B) (S : CommutingOperatorStrategy X Y A B) :
    (toCR G).win (toCRStrategy S).correlation = S.value G :=
  rfl

/-- The commuting-operator value of this repository is the commuting-operator value of
the vendored development: the two suprema range over the same set of reals. -/
theorem commutingOperatorValue_eq_omegaCO (G : Game X Y A B) :
    commutingOperatorValue G = (toCR G).omegaCO := by
  unfold commutingOperatorValue CommutingRepetition.Game.omegaCO iSup
  congr 1
  ext r
  constructor
  · rintro ⟨S, rfl⟩
    exact ⟨toCRStrategy S, rfl⟩
  · rintro ⟨S, rfl⟩
    exact ⟨ofCRStrategy S, rfl⟩

/-- The payoff of the repeated game of the vendored development is the indicator of the
conjunction of the coordinate predicates. -/
theorem payoff_repeat (G : Game X Y A B) (n : ℕ) (xs : Fin n → X) (ys : Fin n → Y)
    (as : Fin n → A) (bs : Fin n → B) :
    (toCR (G.repeat n)).payoff xs ys as bs = ((toCR G).«repeat» n).payoff xs ys as bs := by
  simp [toCR, Game.repeat, CommutingRepetition.Game.repeat, Finset.prod_boole]

/-- The direct repetition of this repository, transported, has the value of the direct
repetition of the vendored development. -/
theorem omegaCO_repeat_eq (G : Game X Y A B) (n : ℕ) :
    (toCR (G.repeat n)).omegaCO = ((toCR G).«repeat» n).omegaCO := by
  have hw : ∀ p, (toCR (G.repeat n)).win p = ((toCR G).«repeat» n).win p := by
    intro p
    unfold CommutingRepetition.Game.win
    refine Finset.sum_congr rfl fun xs _ => Finset.sum_congr rfl fun ys _ =>
      Finset.sum_congr rfl fun as _ => Finset.sum_congr rfl fun bs _ => ?_
    rw [payoff_repeat]
    rfl
  unfold CommutingRepetition.Game.omegaCO
  simp only [hw]

end Bridge

/-- **Uniform direct parallel repetition for commuting-operator strategies** (blueprint
`thm:direct-repetition-co`; Vidick 2026, Theorem 7.1, via the vendored root
`CommutingRepetition.uniform_parallel_repetition`): there is a universal constant `c > 0`
such that for every game `G` with nonempty alphabets and every `n ≥ 1`,
`valco(G^{⊗n}) ≤ exp(-c·n·ε⁷/(ε + log(|A||B|)))` with `ε = 1 - valco(G)` (when
`ε = log(|A||B|) = 0` the quotient is `0 / 0 = 0`). -/
theorem commutingOperatorValue_repeat_le :
    ∃ c : ℝ, 0 < c ∧
      ∀ (X Y A B : Type) [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
        [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
        (G : Game X Y A B) (n : ℕ), 1 ≤ n →
        commutingOperatorValue (G.repeat n) ≤
          Real.exp
            (-(c * ((1 - commutingOperatorValue G) ^ 7 /
              ((1 - commutingOperatorValue G) +
                Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)))))
              * (n : ℝ)) := by
  obtain ⟨c, hc, h⟩ := CommutingRepetition.uniform_parallel_repetition
  refine ⟨c, hc, ?_⟩
  intro X Y A B _ _ _ _ _ _ _ _ G n hn
  rw [commutingOperatorValue_eq_omegaCO, commutingOperatorValue_eq_omegaCO, omegaCO_repeat_eq]
  exact h X Y A B (toCR G) n hn

end MIPRE.Repetition

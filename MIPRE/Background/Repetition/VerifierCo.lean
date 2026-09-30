/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Repetition.Commuting
public import MIPRE.Background.Repetition.Verifier

@[expose] public section

/-!
# Parallel repetition of normal form verifiers in the commuting-operator model

The soundness clause of `thm:parallel-repetition` read in `ω_co` (item "repetition" of Phase 2
of `planning/mipco-track.md`). Nothing about the verifier is new: the output's game is the
repeated game in every value model (`MIPRE.val_repVerifier`), so soundness in a model is the
game-level repetition bound in that model (`MIPRE.val_repVerifier_le`). What this file adds is
that bound for `ω_co`, from the vendored uniform theorem
`MIPRE.Repetition.commutingOperatorValue_repeat_le` (`thm:direct-repetition-co`):

* `valco(G^{⊗k}) ≤ exp(-c ε'^7 k / (ε' + log(|𝒜||ℬ|)))` with `ε' = 1 - valco(G) ≥ ε`; the
  exponent `7` is better than the tensor theorem's `13`, and `ε^13 ≤ ε'^7` because
  `ε ≤ ε' ≤ 1`, so the arithmetic of the tensor bound applies unchanged
  (`Repetition.exp_le_soundBound`), with its own constant `repConstCo`
  (`gameSoundIn_commuting`).
* One procedure must serve both models, and the structure `Repetition` has one constant, which
  the compression uses to choose the number of repetitions. So the commuting-operator reading
  is `repetitionCo`, the same procedure at the smaller of the two constants
  (`Repetition.withConst`), sound in both models (`repetitionCo_soundIn_commuting`; the tensor
  clause is its field). The main theorem keeps `repetition` itself, whose constant does not
  mention the commuting-operator theorem, so `MIP* = RE` does not depend on it.
-/

namespace MIPRE

namespace Repetition

/-- The universal constant of `thm:direct-repetition-co`. -/
noncomputable def repConstCo₀ : ℝ := commutingOperatorValue_repeat_le.choose

theorem repConstCo₀_pos : 0 < repConstCo₀ := commutingOperatorValue_repeat_le.choose_spec.1

theorem commutingOperatorValue_repeat_le_spec (X Y A B : Type) [Fintype X] [Fintype Y]
    [Fintype A] [Fintype B] [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
    (G : Game X Y A B) (n : ℕ) (hn : 1 ≤ n) :
    commutingOperatorValue (G.repeat n) ≤
      Real.exp (-(repConstCo₀ * ((1 - commutingOperatorValue G) ^ 7 /
        ((1 - commutingOperatorValue G) +
          Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ))))) * (n : ℝ)) :=
  commutingOperatorValue_repeat_le.choose_spec.2 X Y A B G n hn

/-- The constant of the commuting-operator repetition bound for answers of bounded length:
`c / (1 + 2 log 3)`. -/
noncomputable def repConstCo : ℝ := repConstCo₀ / (1 + 2 * Real.log 3)

theorem repConstCo_pos : 0 < repConstCo :=
  div_pos repConstCo₀_pos one_add_two_log_three_pos

open Verifier in
/-- **Game-level soundness of direct repetition for commuting-operator strategies**, in the form
of `Repetition.soundness`: for a game with answers of length at most `B`, `valco(G) ≤ 1 - ε`
gives `valco(G^{⊗k}) ≤ exp(-c' ε^13 k / (B + 1))`. -/
theorem commutingOperatorValue_repeat_le_soundBound {X : Type} [Fintype X] [Nonempty X] {B : ℕ}
    (G : Game X X (Answers B) (Answers B)) {ε : ℝ} (hε : 0 < ε)
    (hG : commutingOperatorValue G ≤ 1 - ε) {k : ℕ} (hk : 0 < k) :
    commutingOperatorValue (G.repeat k) ≤ Repetition.soundBound repConstCo ε k B := by
  have hεε' : ε ≤ 1 - commutingOperatorValue G := by linarith
  have hε'1 : 1 - commutingOperatorValue G ≤ 1 := by
    linarith [commutingOperatorValue_nonneg G]
  have hp : ε ^ 13 ≤ (1 - commutingOperatorValue G) ^ 7 :=
    (pow_le_pow_of_le_one hε.le (hεε'.trans hε'1) (by norm_num : 7 ≤ 13)).trans
      (pow_le_pow_left₀ hε.le hεε' 7)
  exact (commutingOperatorValue_repeat_le_spec X X (Answers B) (Answers B) G k hk).trans
    (exp_le_soundBound repConstCo₀_pos hε hεε' hε'1 hp B k)

/-- The commuting-operator model has the direct repetition bound at `repConstCo`. -/
theorem gameSoundIn_commuting : GameSoundIn .commuting repConstCo :=
  fun _ _ _ _ G _ hε hG _ hk => commutingOperatorValue_repeat_le_soundBound G hε hG hk

/-- The constant of the procedure read in both models: the smaller of `repConst` and
`repConstCo`. -/
noncomputable def repConstBoth : ℝ := min repConst repConstCo

theorem repConstBoth_pos : 0 < repConstBoth := lt_min repConst_pos repConstCo_pos

end Repetition

/-- **Parallel repetition of normal form verifiers for both values**: `repetition ℓ` at the
constant `Repetition.repConstBoth`, the smaller of the two repetition constants. It is the same
procedure — sampler, decider, complexity clause and completeness are those of `repetition ℓ` —
and its soundness clause holds in both models. -/
noncomputable def repetitionCo (ℓ : ℕ) : Repetition ℓ :=
  (repetition ℓ).withConst Repetition.repConstBoth Repetition.repConstBoth_pos (min_le_left _ _)

/-- **Parallel repetition is sound in the commuting-operator model** (blueprint
`thm:parallel-repetition-co`): the procedure's soundness clause read in `ω_co`, from the
vendored commuting-operator repetition theorem through the value-independent bridge from the
verifier to the repeated game. -/
theorem repetitionCo_soundIn_commuting (ℓ : ℕ) : (repetitionCo ℓ).SoundIn .commuting :=
  repetition_withConst_soundIn Repetition.gameSoundIn_commuting _ _ _ (min_le_right _ _)

end MIPRE

end

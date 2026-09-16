/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.Repetition.Entangled
import MIPRE.Foundations.Pipeline.Repetition

/-!
# The repetition bound in the form the pipeline consumes

The soundness half of `thm:parallel-repetition` at the level of games. The vendored theorem
`MIPRE.Repetition.quantumValue_repeat_le` (`thm:direct-repetition-q`) bounds
`val*(G^{⊗k})` by `exp(-c ε^{13} k / (ε + log(|𝒜||ℬ|)))` with `ε = 1 - val*(G)`. The structure
`MIPRE.Repetition` asks for `exp(-c' ε^{13} k / (B + 1))` for answer alphabets of strings of
length at most `B` (`Verifier.Answers B`) and a hypothesis `val*(G) ≤ 1 - ε` that need not be
tight:

* `|Answers B| ≤ 3^{B+1}` (`card_answers_le`, by `Answers.getElem?_injective`), so
  `log(|𝒜||ℬ|) ≤ 2(B + 1) log 3`, and `ε ≤ 1 ≤ B + 1`, so the denominator is at most
  `(B + 1)(1 + 2 log 3)`; `c' = c / (1 + 2 log 3)` (`repConst`).
* The exponent is monotone in the gap, so `1 - val*(G) ≥ ε` suffices.

`quantumValue_repeat_le_soundBound` is the statement the assembly of `Repetition ℓ` uses.
-/

namespace MIPRE.Repetition

open Verifier

/-- The universal constant of `thm:direct-repetition-q`. -/
noncomputable def repConst₀ : ℝ := quantumValue_repeat_le.choose

theorem repConst₀_pos : 0 < repConst₀ := quantumValue_repeat_le.choose_spec.1

theorem quantumValue_repeat_le_spec (X Y A B : Type) [Fintype X] [Fintype Y] [Fintype A]
    [Fintype B] (G : Game X Y A B) (hA : Nonempty A) (hB : Nonempty B)
    (hε : 0 < 1 - quantumValue G) (n : ℕ) (hn : 0 < n) :
    quantumValue (G.repeat n) ≤
      Real.exp (-(repConst₀ * ((1 - quantumValue G) ^ 13 /
        ((1 - quantumValue G) + Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ))))) *
        (n : ℝ)) :=
  quantumValue_repeat_le.choose_spec.2 X Y A B G hA hB hε n hn

/-- The constant of the repetition bound for answers of bounded length:
`c / (1 + 2 log 3)`. -/
noncomputable def repConst : ℝ := repConst₀ / (1 + 2 * Real.log 3)

theorem one_add_two_log_three_pos : 0 < 1 + 2 * Real.log 3 := by
  have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3); linarith

theorem repConst_pos : 0 < repConst :=
  div_pos repConst₀_pos one_add_two_log_three_pos

/-- `|Answers T| ≤ 3^{T + 1}`. -/
theorem card_answers_le (T : ℕ) : Fintype.card (Answers T) ≤ 3 ^ (T + 1) := by
  have h := Fintype.card_le_of_injective _ (Answers.getElem?_injective T)
  simpa [Fintype.card_fun, Fintype.card_option, Fintype.card_bool, Fintype.card_fin] using h

theorem log_card_answers_mul_le (T : ℕ) :
    Real.log ((Fintype.card (Answers T) : ℝ) * (Fintype.card (Answers T) : ℝ)) ≤
      2 * ((T : ℝ) + 1) * Real.log 3 := by
  have hc : (Fintype.card (Answers T) : ℝ) ≤ 3 ^ (T + 1) := by
    exact_mod_cast card_answers_le T
  have hpos : (0 : ℝ) < Fintype.card (Answers T) := by
    exact_mod_cast Fintype.card_pos
  calc Real.log ((Fintype.card (Answers T) : ℝ) * (Fintype.card (Answers T) : ℝ))
      ≤ Real.log ((3 : ℝ) ^ (T + 1) * 3 ^ (T + 1)) :=
        Real.log_le_log (by positivity) (mul_le_mul hc hc hpos.le (by positivity))
    _ = 2 * ((T : ℝ) + 1) * Real.log 3 := by
        rw [← pow_add, Real.log_pow]; push_cast; ring

/-- **Game-level soundness of direct repetition**, in the form of `Repetition.soundness`: for a
game with answers of length at most `B`, `val*(G) ≤ 1 - ε` gives
`val*(G^{⊗k}) ≤ exp(-c' ε^{13} k / (B + 1))`. -/
theorem quantumValue_repeat_le_soundBound {X : Type} [Fintype X] {B : ℕ}
    (G : Game X X (Answers B) (Answers B)) {ε : ℝ} (hε : 0 < ε)
    (hG : quantumValue G ≤ 1 - ε) {k : ℕ} (hk : 0 < k) :
    quantumValue (G.repeat k) ≤ Repetition.soundBound repConst ε k B := by
  set ε' := 1 - quantumValue G with hε'
  have hεε' : ε ≤ ε' := by rw [hε']; linarith
  have hε'0 : 0 < ε' := lt_of_lt_of_le hε hεε'
  have hε'1 : ε' ≤ 1 := by rw [hε']; have := quantumValue_nonneg G; linarith
  have h := quantumValue_repeat_le_spec X X (Answers B) (Answers B) G inferInstance inferInstance
    hε'0 k hk
  refine h.trans ?_
  unfold Repetition.soundBound
  rw [Real.exp_le_exp]
  set L := Real.log ((Fintype.card (Answers B) : ℝ) * (Fintype.card (Answers B) : ℝ)) with hL
  have hL0 : 0 ≤ L := by
    rw [hL]
    refine Real.log_nonneg ?_
    have : (1 : ℝ) ≤ Fintype.card (Answers B) := by exact_mod_cast Fintype.card_pos
    nlinarith
  have hLle : L ≤ 2 * ((B : ℝ) + 1) * Real.log 3 := log_card_answers_mul_le B
  have hden : ε' + L ≤ ((B : ℝ) + 1) * (1 + 2 * Real.log 3) := by
    have hB0 : (0 : ℝ) ≤ B := by positivity
    have : ε' ≤ (B : ℝ) + 1 := by linarith
    nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)]
  have hnum : ε ^ 13 ≤ ε' ^ 13 := pow_le_pow_left₀ hε.le hεε' 13
  have hkey : repConst * ε ^ 13 / ((B : ℝ) + 1) ≤ repConst₀ * (ε' ^ 13 / (ε' + L)) := by
    have h1 : 0 < ε' + L := by linarith
    have hpos3 := one_add_two_log_three_pos
    have hB1 : (0 : ℝ) < (B : ℝ) + 1 := by positivity
    have e1 : repConst * ε ^ 13 / ((B : ℝ) + 1) =
        repConst₀ * ε ^ 13 / (((B : ℝ) + 1) * (1 + 2 * Real.log 3)) := by
      rw [repConst]; field_simp
    have e2 : repConst₀ * (ε' ^ 13 / (ε' + L)) = repConst₀ * ε' ^ 13 / (ε' + L) := by ring
    rw [e1, e2]
    exact div_le_div₀ (mul_nonneg repConst₀_pos.le (pow_nonneg hε'0.le _))
      (mul_le_mul_of_nonneg_left hnum repConst₀_pos.le) h1 hden
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hmul := mul_le_mul_of_nonneg_right hkey hk0
  rw [← hε']
  calc -(repConst₀ * (ε' ^ 13 / (ε' + L))) * (k : ℝ)
      = -(repConst₀ * (ε' ^ 13 / (ε' + L)) * (k : ℝ)) := by ring
    _ ≤ -(repConst * ε ^ 13 / ((B : ℝ) + 1) * (k : ℝ)) := by
        rw [neg_le_neg_iff]; exact hmul
    _ = -(repConst * ε ^ 13 * (k : ℝ) / ((B : ℝ) + 1)) := by ring

end MIPRE.Repetition

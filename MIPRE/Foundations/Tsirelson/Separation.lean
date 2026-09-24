/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import Mathlib.Computability.PartrecCode
import MIPRE.Foundations.Tsirelson.Closed

/-!
# An explicit separation of the quantum and commuting-operator values

Blueprint `thm:separation` (`planning/explicit-separation.md`): a described game `G` with
`val*(G) ≤ 1/2` and `ω_co(G) = 1`, and a commuting-operator correlation of payoff `1` that lies
outside `C_qa`. Both analytic inputs are hypotheses here, as in `MIPRE.Foundations.Tsirelson.
Conditional`: the halting reduction `HaltingReductionQuantum` and the upper semidecider
`CommutingUpperRE`. `MIPRE/Tsirelson.lean` discharges them.

**The fixed point** (`exists_quantumValue_le_half_commutingOperatorValue_eq_one`). Let `g` be the
halting reduction. The predicate `c ↦ ω_co(g c) < 1` is r.e., so Kleene's recursion theorem
(`Nat.Partrec.Code.fixed_point₂`) gives a code `e` that halts on the empty input exactly when
`ω_co(g e) < 1`. If `e` halted, then `val*(g e) = 1`, so `ω_co(g e) = 1` and `e` would not halt.
So `e` does not halt: `val*(g e) ≤ 1/2`, and `ω_co(g e) = 1` because it is not below `1`. The
game is `g e`, uniform in the codes of `g` and of the semidecider. Unlike the paper's `G^sep`,
nothing about entanglement is needed: the case `ω_co = 1` is the non-halting case of the
reduction, whose soundness is already the value-form compression chain.

**The correlation** (`exists_mem_Cqc_payoff_eq_commutingOperatorValue`). The payoff is continuous
and `C_qc` is compact and nonempty, so the payoff attains its maximum on `C_qc`, and the maximum
is the commuting-operator value. For the game above, that correlation has payoff `1`, and it is
outside `C_qa`, where payoffs are at most `val* ≤ 1/2`.

## Main declarations

* `exists_mem_Cqc_payoff_eq_commutingOperatorValue`;
* `exists_quantumValue_le_half_commutingOperatorValue_eq_one`;
* `separation_of_upperRE`.
-/

namespace MIPRE

open HaltingGameValue (GameData HaltsOnEmptyInput)
open Nat.Partrec (Code)

variable {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- **The commuting-operator value is attained on `C_qc`**: some commuting-operator correlation
has payoff exactly `ω_co(G)`, since the payoff is continuous and `C_qc` is compact. -/
theorem exists_mem_Cqc_payoff_eq_commutingOperatorValue [Nonempty A] [Nonempty B]
    (G : Game X Y A B) :
    ∃ p ∈ Cqc X Y A B, G.payoff p = commutingOperatorValue G := by
  have hne : (Cqc X Y A B).Nonempty :=
    ⟨_, ⟨Classical.arbitrary (CommutingOperatorStrategy X Y A B), rfl⟩⟩
  obtain ⟨p, hp, hmax⟩ := isCompact_Cqc.exists_isMaxOn hne G.continuous_payoff.continuousOn
  refine ⟨p, hp, le_antisymm (payoff_le_commutingOperatorValue_of_mem_Cqc G hp) ?_⟩
  exact ciSup_le fun S => hmax ⟨S, rfl⟩

/-- **The fixed-point game**: given the halting reduction and an upper semidecider for the
commuting-operator value, some described game has quantum value at most `1/2` and
commuting-operator value `1`. -/
theorem exists_quantumValue_le_half_commutingOperatorValue_eq_one
    (hred : HaltingReductionQuantum) (hU : CommutingUpperRE) :
    ∃ d : GameData, quantumValue d.game ≤ 1 / 2 ∧ commutingOperatorValue d.game = 1 := by
  obtain ⟨g, hg, hgap⟩ := hred
  -- `c ↦ ω_co(g c) < 1` is r.e.: the semidecider at the threshold `p / q = 1 / 1`
  have hP : REPred fun c : Code =>
      commutingOperatorValue (g c).game < ((1 : ℕ) : ℝ) / (1 : ℕ) :=
    Partrec.comp hU (hg.pair (Computable.const ((1, 1) : ℕ × ℕ)))
  have hf : Partrec₂ fun (c : Code) (_ : ℕ) =>
      (Part.assert (commutingOperatorValue (g c).game < ((1 : ℕ) : ℝ) / (1 : ℕ))
        fun _ => Part.some ()).map fun _ => (0 : ℕ) :=
    Partrec.map (hP.comp Computable.fst) (Computable.const (0 : ℕ)).to₂
  -- the recursion theorem: a code that halts exactly when its own game has `ω_co < 1`
  obtain ⟨e, he⟩ := Nat.Partrec.Code.fixed_point₂ hf
  have hdom : HaltsOnEmptyInput e ↔ commutingOperatorValue (g e).game < 1 := by
    show (e.eval 0).Dom ↔ _
    rw [he]
    simp only [Part.map_Dom]
    show (∃ _ : _ < _, (Part.some ()).Dom) ↔ _
    simp
  have hnot : ¬ HaltsOnEmptyInput e := by
    intro h
    have h1 := (hgap e).1 h
    have h2 := hdom.1 h
    have := quantumValue_le_commutingOperatorValue (g e).game
    linarith
  refine ⟨g e, (hgap e).2 hnot, le_antisymm (commutingOperatorValue_le_one _) ?_⟩
  exact not_lt.1 fun h => hnot (hdom.2 h)

/-- **The explicit separation, given an upper semidecider** (blueprint `thm:separation`): given
the halting reduction and an upper semidecider for the commuting-operator value, some described
game `G` has `val*(G) ≤ 1/2` and `ω_co(G) = 1`, and some commuting-operator correlation in its
scenario has payoff `1` and lies outside `C_qa`. -/
theorem separation_of_upperRE (hred : HaltingReductionQuantum) (hU : CommutingUpperRE) :
    ∃ d : GameData, quantumValue d.game ≤ 1 / 2 ∧ commutingOperatorValue d.game = 1 ∧
      ∃ p ∈ Cqc (Fin (d.nX + 1)) (Fin (d.nX + 1)) (Fin (d.nA + 1)) (Fin (d.nA + 1)),
        d.game.payoff p = 1 ∧
          p ∉ Cqa (Fin (d.nX + 1)) (Fin (d.nX + 1)) (Fin (d.nA + 1)) (Fin (d.nA + 1)) := by
  obtain ⟨d, hq, hco⟩ := exists_quantumValue_le_half_commutingOperatorValue_eq_one hred hU
  obtain ⟨p, hp, hpay⟩ := exists_mem_Cqc_payoff_eq_commutingOperatorValue d.game
  refine ⟨d, hq, hco, p, hp, hpay.trans hco, fun hqa => ?_⟩
  have := payoff_le_quantumValue_of_mem_Cqa d.game hqa
  linarith

end MIPRE

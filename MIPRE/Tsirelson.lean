/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.MainTheorem
import MIPRE.Foundations.Tsirelson.UpperRE
import MIPRE.Foundations.Tsirelson.Separation

/-!
# Tsirelson's problem has a negative answer

The closure `C_qa` of the finite-dimensional quantum correlations is strictly contained in the
commuting-operator correlations `C_qc` in some finite bipartite scenario (blueprint
`cor:tsirelson`).

`MIPRE.tsirelson_of_haltingReduction` (`MIPRE/Foundations/Tsirelson/UpperRE.lean`) proves it
from the halting reduction to the quantum value alone: the commuting-operator value is
recursively enumerable from above (`MIPRE.commutingUpperRE`, through exact sum-of-squares
certificates), `C_qc` is closed (`MIPRE.isClosed_Cqc`, through a compact state space and the
GNS construction), and if the two values agreed on every described game, non-halting would be
recursively enumerable. This module supplies the reduction,
`MIPRE.Halting.halting_reduction_quantum` of `MIPRE/MainTheorem.lean`; it sits beside that
module because `MIPRE/Foundations/` does not import it.

The witness scenario has one question alphabet `Fin (nX + 1)` and one answer alphabet
`Fin (nA + 1)`, shared by the two players.

The same two inputs give an explicit separating game (blueprint `thm:separation`,
`MIPRE.separation`): Kleene's recursion theorem, applied to the halting reduction and the upper
semidecider, gives a described game of quantum value at most `1/2` and commuting-operator value
`1` (`MIPRE.separation_of_upperRE`, `MIPRE/Foundations/Tsirelson/Separation.lean`).
-/

namespace MIPRE

/-- **Tsirelson's problem, negative answer** (blueprint `cor:tsirelson`): in some finite
bipartite scenario, `C_qa ⊊ C_qc`. -/
theorem tsirelson :
    ∃ nX nA : ℕ, Cqa (Fin (nX + 1)) (Fin (nX + 1)) (Fin (nA + 1)) (Fin (nA + 1)) ⊂
      Cqc (Fin (nX + 1)) (Fin (nX + 1)) (Fin (nA + 1)) (Fin (nA + 1)) :=
  tsirelson_of_haltingReduction Halting.halting_reduction_quantum

open HaltingGameValue (GameData) in
/-- **An explicit separation of the quantum and commuting-operator values** (blueprint
`thm:separation`): some described game `G` has `val*(G) ≤ 1/2` and `ω_co(G) = 1`, and some
commuting-operator correlation in its scenario has payoff `1` and lies outside `C_qa`. -/
theorem separation :
    ∃ d : GameData, quantumValue d.game ≤ 1 / 2 ∧ commutingOperatorValue d.game = 1 ∧
      ∃ p ∈ Cqc (Fin (d.nX + 1)) (Fin (d.nX + 1)) (Fin (d.nA + 1)) (Fin (d.nA + 1)),
        d.game.payoff p = 1 ∧
          p ∉ Cqa (Fin (d.nX + 1)) (Fin (d.nX + 1)) (Fin (d.nA + 1)) (Fin (d.nA + 1)) :=
  separation_of_upperRE Halting.halting_reduction_quantum commutingUpperRE

end MIPRE

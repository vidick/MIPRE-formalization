/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.MainTheorem
import MIPRE.Foundations.Tsirelson.UpperRE

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
-/

namespace MIPRE

/-- **Tsirelson's problem, negative answer** (blueprint `cor:tsirelson`): in some finite
bipartite scenario, `C_qa ⊊ C_qc`. -/
theorem tsirelson :
    ∃ nX nA : ℕ, Cqa (Fin (nX + 1)) (Fin (nX + 1)) (Fin (nA + 1)) (Fin (nA + 1)) ⊂
      Cqc (Fin (nX + 1)) (Fin (nX + 1)) (Fin (nA + 1)) (Fin (nA + 1)) :=
  tsirelson_of_haltingReduction Halting.halting_reduction_quantum

end MIPRE

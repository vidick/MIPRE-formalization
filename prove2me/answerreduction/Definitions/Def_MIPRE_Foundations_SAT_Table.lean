/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/Table.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula

/-!
# Every Boolean function has a circuit

The formula of a Boolean function on `N` bits from its truth table (`Fml.table`): a mux tree
on the bits, of size at most `7 · 2^N`. Its circuit is well-formed (`Fml.toCircuit_wellFormed`)
and computes the function (`Fml.eval_table`). This is how the check circuit of the
Cook–Levin tableau of the interpreter machine is obtained: from the truth table of the
local check predicate, as in the paper's `lem:pack-check-size`
(`planning/succinct-cook-levin.md`, S3).
-/

namespace MIPRE.SAT

namespace Fml

/-- The formula of a Boolean function on `N` bits: a mux tree on the bits, the leaves being
the entries of the truth table. -/
def table : (N : ℕ) → ((Fin N → Bool) → Bool) → Fml
  | 0, f => const (f Fin.elim0)
  | N + 1, f =>
    or (and (inp N) (table N fun x => f (Fin.snoc x true)))
      (and (not (inp N)) (table N fun x => f (Fin.snoc x false)))

end Fml

end MIPRE.SAT

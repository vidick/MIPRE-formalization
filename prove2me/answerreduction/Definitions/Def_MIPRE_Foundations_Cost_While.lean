/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/While.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary

/-!
# Iterating a polynomial-time step, and running programs in sequence

Two program combinators for routines whose running time is not polynomial in the size of their
input, such as the computation of `(λn + 1)^μ` from binary `λ, n, μ`:

* `whileProg f` iterates a total step `f : Data → Bool × Data` from a state, continuing on
  `(true, s')` with the state `s'` and stopping on `(false, r)` with the result `r`; a run of
  `N + 1` steps costs the sum of the steps' bounds (`whileProg_runs`);
* `seqProg p q` runs `q` on the output of `p` (`seqProg_runs`).
-/

namespace MIPRE.Cost

open PolyTimeFun

/-- Iterate the step `f` until it stops. -/
def whileProg (f : PolyTimeFun Data (Bool × Data)) : Prog := .loop f.code

/-- Run `q` on the output of `p`. -/
def seqProg (p q : Prog) : Prog := .let_ p q

end MIPRE.Cost

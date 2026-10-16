/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Lists.lean (delta bundle: declarations the new statements need that the published bundle Def_MIPRE_Foundations_Halting_Lists does not carry);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists

/-!
# Bounded walks over lists, in the ambient model

The programs with which the wrapper decider of `Halting/Wrapper.lean` performs the paper's
format checks: the questions must be bit strings of the sampler's length, the answers bit
strings within the answer-length budget, and equal questions must carry equal answers. All of
them walk their input under a *budget*, so that their cost is the budget times the size of the
input — the shape `T · (|input| + 1)` of `Decider.TimeBoundAt` — rather than a power of it.

* `Prog.bitWalkProg`: on `cons l u`, walk `l` against the budget `u` (a list, typically a unary
  numeral), checking that each element passed is a bit; the result is `nil` on a non-bit
  element, and otherwise the pair of what remains of `l` and of `u` (`Data.bitWalk`). Both
  format checks read off it: `|l| = |u|` is the result `cons nil nil`, `|l| ≤ |u|` a result
  `cons nil _`.
* `Prog.eqBitsProg`: equality of two bit lists (`Data.eqBits`).
* `Prog.normBinProg`: the normalization `Data.normBin` of a parameter, by a walk recording the
  last bit seen (`Data.canonWalk`).

Every walk copies the remainder of the lists at each step, which is what the ambient model
charges; the cost bounds are `(budget + 1) · (S + c)` for `S` the size of the input.
-/

namespace MIPRE.Cost

namespace Data

/-- Walk `l` against the budget `u`, checking that every element passed is a bit: `nil` on a
non-bit, otherwise the pair of the remainders. -/
def bitWalk : Data → Data → Data
  | nil, u => cons nil u
  | cons h l', nil => cons (cons h l') nil
  | cons h l', cons _ u' => if isBit h then bitWalk l' u' else nil

end Data

namespace Prog

open Data

/-! ## The bounded bit walk -/

/-- Body of `bitWalkProg`, on the state `cons l u`: stop with `cons nil u` if `l` is empty,
with `cons l nil` if the budget is exhausted, with `nil` if the head of `l` is not a bit, and
otherwise continue with the two tails. -/
def bitWalkBody : Prog :=
  .elim 0 .nil
    (.elim 0 (.cons .nil (.cons .nil (.var 1)))
      (.elim 3 (.cons .nil (.cons (.var 2) .nil))
        (.elim 2 (.cons (.cons .nil .nil) (.cons (.var 3) (.var 1)))
          (.elim 0 (.elim 1 (.cons (.cons .nil .nil) (.cons (.var 5) (.var 3)))
              (.cons .nil .nil))
            (.cons .nil .nil)))))

/-- The bounded bit walk: on `cons l u`, compute `bitWalk l u`. -/
def bitWalkProg : Prog := .loop bitWalkBody

/-! ## Equality of bit lists -/

/-! ## Normalization of the parameter -/

end Prog

end MIPRE.Cost

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/BitQuery.lean (statement stub of MIPRE.Cost.Prog.bitAtBody_succ);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Definitions.Def_MIPRE_Foundations_Cost_BitQuery

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Prog

theorem MIPRE.Cost.Prog.bitAtBody_succ (b : Bool) (ys mb mb' : BitStr) (hz : mb.any id = true) (tz td : ℕ)
    (hzr : Eval [encode mb] isZeroProg (encode (mb.any id)) tz)
    (hd : Eval [encode mb] decProg (encode mb') td) :
    Eval [.cons (encode (b :: ys)) (encode mb)] bitAtBody
      (.cons (.cons .nil .nil) (.cons (encode ys) (encode mb')))
      (2 * (encode mb).size + tz + td + (encode ys).size + 14) := by sorry

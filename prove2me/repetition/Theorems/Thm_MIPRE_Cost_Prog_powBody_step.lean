/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/Prims.lean (statement stub of MIPRE.Cost.Prog.powBody_step);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Tactic.Linarith
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
import Definitions.Def_MIPRE_Foundations_Halting_Lists_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Repeat_Prims

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Prog
open MIPRE.Cost.Data

theorem MIPRE.Cost.Prog.powBody_step (e : ℕ) (bl bn acc : List Data) :
    ∃ t ≤ (bn.length + 1) * ((Data.list bl).size + (Data.list bn).size + (Data.list acc).size +
        2 * bn.length + 13) +
      (bl.length + 1) * ((Data.list bl).size + (Data.list bn).size + (Data.list acc).size +
        2 * bn.length + 2 * bl.length + 13) +
      4 * ((Data.list bl).size + (Data.list bn).size + (Data.list acc).size + 2 * e + 2 * bn.length +
        2 * bl.length) + 40,
      Eval [powState (e + 1) bl bn acc] powBody
        (.cons (.cons .nil .nil)
          (powState e bl bn (List.replicate (bl.length + bn.length) .nil ++ acc))) t := by sorry

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/Prims.lean (statement stub of MIPRE.Cost.Prog.powLoop_runs);
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

theorem MIPRE.Cost.Prog.powLoop_runs (e : ℕ) (bl bn acc : List Data) (env : Env) :
    ∃ t ≤ powCost e (bl.length + bn.length)
        ((Data.list bl).size + (Data.list bn).size + (Data.list acc).size),
      Eval (powState e bl bn acc :: env) (.loop powBody)
        (.list (List.replicate (e * (bl.length + bn.length)) .nil ++ acc)) t := by sorry

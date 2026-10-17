/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Arith.lean (statement stub of MIPRE.Cost.Prog.mulLoop_runs);
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
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Halting_Lists_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Halting_Arith_B

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Prog
open Polynomial
open MIPRE.Cost.Data

theorem MIPRE.Cost.Prog.mulLoop_runs (a b acc : ℕ) (rest : Env) (P : ℕ) (hP : acc + a * b ≤ P) :
    ∃ t ≤ (b + 1) * ((a + 1) * (4 * a + 2 * P + 15) + 4 * a + 4 * P + 2 * b + 41),
      Eval (Data.cons (ofNat b) (ofNat acc) :: ofNat a :: rest) (.loop mulBody)
        (ofNat (acc + a * b)) t := by sorry

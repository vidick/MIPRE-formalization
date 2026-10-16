/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/MapLoop.lean (statement stub of MIPRE.Cost.Prog.mapBody_step);
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
import Definitions.Def_MIPRE_Foundations_Repeat_MapLoop

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Prog
open MIPRE.Cost.Data

theorem MIPRE.Cost.Prog.mapBody_step {univ : Prog} (hU : univ.WellScoped 1) (s : ℕ) (h : Data)
    (l remY : List Data) (sD nD kD wD jD : Data) (acc : List Data) {r : Data} {tu : ℕ}
    (hr : Eval [mapQuery sD nD kD wD jD (list ((h :: l).take s)) (list (remY.take s))] univ r tu) :
    ∃ t ≤ mapStepCost s (list (h :: l)).size (list remY).size (mapCtx sD nD kD wD jD).size
        (list acc).size tu,
      Eval [mapState s (h :: l) remY (mapCtx sD nD kD wD jD) acc] (mapBody univ)
        (.cons (.cons .nil .nil)
          (mapState s ((h :: l).drop s) (remY.drop s) (mapCtx sD nD kD wD jD)
            ((toList r).reverse ++ acc))) t := by sorry

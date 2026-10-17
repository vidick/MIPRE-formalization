/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/UnaryDegreeArithmetic.lean (statement stub of MIPRE.LowDegree.DegreeArithmetic.mem_descendingUnary_iff);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_Cost_Iterates
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryDegreeArithmetic

open MIPRE
open MIPRE.LowDegree
open MIPRE.LowDegree.DegreeArithmetic
open MIPRE.Cost MIPRE.Cost.PolyTimeFun Polynomial

theorem MIPRE.LowDegree.DegreeArithmetic.mem_descendingUnary_iff (u d : Unary) : d ∈ descendingUnary u ↔ d.length ≤ u.length := by sorry

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/DetypingProgBranches.lean (statement stub of MIPRE.CL.Detyping.Program.route_marginal_early);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_TypedSampler
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Cost_BinaryCompare
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgFinite
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgParse
import Definitions.Def_MIPRE_Foundations_CL_DetypingQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCall
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgRoute

open MIPRE
open MIPRE.CL
open MIPRE.CL.Detyping
open MIPRE.CL.Detyping.Program
open MIPRE.Cost MIPRE.Cost.PolyTimeFun
variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T]
variable (E : T → T → Prop) [DecidableRel E]

theorem MIPRE.CL.Detyping.Program.route_marginal_early (n : ℕ) (w : Player) (j : ℕ) (z : BitStr)
    (hj : 1 ≤ j) (hj' : j ≤ 2) :
    route E (encode (n, Sampler.Query.marginal w j z)) =
      directResult (graphBits (((Graph.presentation E w.toBool).truncate j).eval (graphOfBits z)) ++
        pad false (content (graphDim T) z)) := by sorry

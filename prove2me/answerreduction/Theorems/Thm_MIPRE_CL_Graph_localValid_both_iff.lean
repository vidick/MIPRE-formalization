/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/Graph.lean (statement stub of MIPRE.CL.Graph.localValid_both_iff);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Graph

open MIPRE
open MIPRE.CL
open MIPRE.CL.Graph
open Finset Classical
variable {T : Type*} [Fintype T] [DecidableEq T]

theorem MIPRE.CL.Graph.localValid_both_iff (E : T → T → Prop) [DecidableRel E]
    (hE : ∀ u v, E u v → E v u) (z : Coord T → ZMod 2) :
    localValid E false z ∧ localValid E true z ↔
      ∃ uv : T × T, E uv.1 uv.2 ∧ z = pairSeed E uv := by sorry

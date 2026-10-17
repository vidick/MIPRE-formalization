/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/DetypingLaw.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping

/-! # The joint law of detyped questions

On an ordered edge the graph view depends only on the player's own type.
Conditioning on the valid-edge event gives the uniform ordered-edge law and
one shared uniform content seed, exactly as in `types.tex`, `def:detyped-CL`.
-/

noncomputable section

namespace MIPRE.CL.Detyping

open Finset Classical

variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]

set_option linter.unusedSectionVars false

/-- The fixed valid graph question of one type, independent of the neighboring type. -/
def view (E : T → T → Prop) [DecidableRel E] (w : Bool) (u : T) : Graph.Coord T → ZMod 2 :=
  fun p => if p.1 = w then Graph.encode E u p.2 else if p = (!w, (true, u)) then 1 else 0

end MIPRE.CL.Detyping

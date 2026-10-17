/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/DetypingLaw.lean (statement stub of MIPRE.CL.Detyping.sum_valid_questions);
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
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw

open MIPRE
open MIPRE.CL
open MIPRE.CL.Detyping
open Finset Classical
set_option linter.unusedSectionVars false
variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]

theorem MIPRE.CL.Detyping.sum_valid_questions {ℓ : ℕ} {M : Type*} [AddCommMonoid M]
    (E : T → T → Prop) [DecidableRel E] (hE : ∀ u v, E u v → E v u)
    (P : Bool → T → CLFun (ZMod 2) ι ℓ) (hP : ∀ w t, (P w t).ExactlyOn univ) (hℓ : 0 < ℓ)
    (f : (Coord T ι → ZMod 2) → (Coord T ι → ZMod 2) → M) :
    ∑ g ∈ Graph.validSeeds E, ∑ v : ι → ZMod 2,
      f ((presentation E false (P false)).eval (Sum.elim g v))
        ((presentation E true (P true)).eval (Sum.elim g v)) =
    ∑ uv ∈ Graph.edges E, ∑ v : ι → ZMod 2,
      f (Sum.elim (view E false uv.1) ((P false uv.1).eval v))
        (Sum.elim (view E true uv.2) ((P true uv.2).eval v)) := by sorry

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/DetypingQueries.lean (statement stub of MIPRE.CL.CLFun.truncate_concat_le);
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
import Definitions.Def_MIPRE_Foundations_CL_DetypingQueries

open MIPRE
open MIPRE.CL
open MIPRE.CL.CLFun
open Finset Classical
variable {F ι : Type*} [Semiring F] [DecidableEq ι] {k ℓ : ℕ}

theorem MIPRE.CL.CLFun.truncate_concat_le (L : CLFun F ι k) (R : (ι → F) → CLFun F ι ℓ)
    (j : ℕ) (hj : j ≤ k) : (L.concat R).truncate j = L.truncate j := by sorry

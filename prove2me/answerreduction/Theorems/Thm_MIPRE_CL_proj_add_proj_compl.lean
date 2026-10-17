/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/Register.lean (statement stub of MIPRE.CL.proj_add_proj_compl);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register

open MIPRE
open MIPRE.CL
variable {F : Type*} [Semiring F] {ι : Type*} [DecidableEq ι]

theorem MIPRE.CL.proj_add_proj_compl [Fintype ι] (S : Finset ι) (x : ι → F) :
    proj S x + proj Sᶜ x = x := by sorry

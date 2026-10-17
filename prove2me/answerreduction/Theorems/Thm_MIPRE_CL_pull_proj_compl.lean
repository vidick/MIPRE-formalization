/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/Embedding.lean (statement stub of MIPRE.CL.pull_proj_compl);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Embedding

open MIPRE
open MIPRE.CL
open Classical
set_option linter.unusedSectionVars false
variable {F ι κ : Type*} [Semiring F] [DecidableEq ι] [DecidableEq κ]

theorem MIPRE.CL.pull_proj_compl [Fintype ι] [Fintype κ] (e : ι ↪ κ) (S : Finset ι)
    (x : κ → F) : pull e (proj (S.map e)ᶜ x) = proj Sᶜ (pull e x) := by sorry

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/SamplingPrefix.lean (statement stub of MIPRE.CL.CLFun.ExactlyOn.outputPrefix_self);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Introspection_SamplingPrefix

open MIPRE
open MIPRE.CL
open MIPRE.CL.CLFun
open Finset
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

theorem MIPRE.CL.CLFun.ExactlyOn.outputPrefix_self {P : CLFun F ι ℓ} {T : Finset ι}
    (hP : P.ExactlyOn T) (y : ι → F) : P.outputPrefix ℓ (proj T y) = proj T y := by sorry

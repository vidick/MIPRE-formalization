/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/Closure.lean (statement stub of MIPRE.CL.CLFun.ExactlyOn.directSum);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B

open MIPRE
open MIPRE.CL
open MIPRE.CL.CLFun
universe u v
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {k ℓ : ℕ}

theorem MIPRE.CL.CLFun.ExactlyOn.directSum {P Q : CLFun F ι ℓ} {T T' : Finset ι} (hP : P.ExactlyOn T)
    (hQ : Q.ExactlyOn T') (hTT' : Disjoint T T') : (P.directSum Q).ExactlyOn (T ∪ T') := by sorry

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/Basic.lean (statement stub of MIPRE.CL.CLFun.SupportedOn.eval_truncate_eq_sum);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic

open MIPRE
open MIPRE.CL
open MIPRE.CL.CLFun
universe u v
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {ℓ : ℕ}
variable [Fintype ι]

theorem MIPRE.CL.CLFun.SupportedOn.eval_truncate_eq_sum {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.SupportedOn T)
    (k : ℕ) (x : ι → F) : (P.truncate k).eval x = ∑ i ∈ Finset.range k, P.mapAt i x x := by sorry

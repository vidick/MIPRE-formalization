/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/Repeat.lean (statement stub of MIPRE.CL.CLFun.factorOfPrefix_famSum);
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
import Definitions.Def_MIPRE_Foundations_CL_Repeat

open MIPRE
open MIPRE.CL
open MIPRE.CL.CLFun
set_option linter.unusedSectionVars false
universe u v w
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] [Fintype ι] {κ : Type w}
  [DecidableEq κ] [Fintype κ] {k : ℕ}
variable {ℓ : ℕ}
variable (e : Fin k × ι ≃ κ)

theorem MIPRE.CL.CLFun.factorOfPrefix_famSum : ∀ (ℓ : ℕ) (P : Fin k → CLFun F ι ℓ) (j : ℕ) (u : κ → F),
    (famSum e ℓ P).factorOfPrefix j u = blockSet e fun i => (P i).factorOfPrefix j (block e i u) := by sorry

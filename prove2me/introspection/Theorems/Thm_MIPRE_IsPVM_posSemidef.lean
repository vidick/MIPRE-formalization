/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/PVM.lean (statement stub of MIPRE.IsPVM.posSemidef);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B

open MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {n Λ : Type*} [Fintype n] [DecidableEq n] [Fintype Λ] [DecidableEq Λ]
variable {P : Λ → Matrix n n ℂ}
omit [DecidableEq Λ]

theorem MIPRE.IsPVM.posSemidef (h : IsPVM P) (a : Λ) : (P a).PosSemidef := by sorry

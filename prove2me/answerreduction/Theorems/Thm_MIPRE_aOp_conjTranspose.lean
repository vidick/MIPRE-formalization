/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/OpBound.lean (statement stub of MIPRE.aOp_conjTranspose);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Definitions.Def_MIPRE_Foundations_OpBound

open MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder
open Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N]
variable [DecidableEq N]
variable {HA HB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]

theorem MIPRE.aOp_conjTranspose (X : Matrix HA HA ℂ) :
    (aOp X : Matrix (HA × HB) _ ℂ)ᴴ = aOp (Xᴴ) := by sorry

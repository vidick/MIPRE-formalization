/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/POVMValue.lean (statement stub of MIPRE.sum_bornProb);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_POVMValue

open MIPRE
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

theorem MIPRE.sum_bornProb {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (MA : POVM A dA)
    (MB : POVM B dB) :
    ∑ a, ∑ b, bornProb ψ (((MA.mats a).val)) (((MB.mats b).val)) = 1 := by sorry

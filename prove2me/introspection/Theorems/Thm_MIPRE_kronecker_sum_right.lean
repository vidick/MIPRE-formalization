/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/POVMValue.lean (statement stub of MIPRE.kronecker_sum_right);
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

theorem MIPRE.kronecker_sum_right {dA dB ι : Type*} (M : Matrix dA dA ℂ) (s : Finset ι)
    (f : ι → Matrix dB dB ℂ) : M ⊗ₖ (∑ i ∈ s, f i) = ∑ i ∈ s, M ⊗ₖ f i := by sorry

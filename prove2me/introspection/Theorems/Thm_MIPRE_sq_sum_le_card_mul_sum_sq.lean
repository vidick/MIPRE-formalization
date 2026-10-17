/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Closeness.lean (statement stub of MIPRE.sq_sum_le_card_mul_sum_sq);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness

open MIPRE
open Finset ComplexOrder Matrix
variable {n : Type*} [Fintype n]

theorem MIPRE.sq_sum_le_card_mul_sum_sq {ι : Type*} [Fintype ι] (t : ι → ℝ) (ht : ∀ i, 0 ≤ t i) :
    (∑ i, t i) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, t i ^ 2 := by sorry

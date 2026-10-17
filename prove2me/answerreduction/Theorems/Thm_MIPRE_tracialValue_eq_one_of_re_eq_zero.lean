/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/PerfectStrategy.lean (statement stub of MIPRE.tracialValue_eq_one_of_re_eq_zero);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy

open MIPRE
open Finset
open scoped ComplexOrder
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
variable {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Module ℂ 𝒜]

theorem MIPRE.tracialValue_eq_one_of_re_eq_zero (G : SynchronousGame X A) (τ : TracialState 𝒜)
    (P : ProjectiveMeasurement X A 𝒜)
    (h : ∀ x y, 0 < G.μ x y → ∀ a b, G.D x y a b = false →
      (τ (P.M x a * P.M y b)).re = 0) :
    tracialValue G τ P = 1 := by sorry

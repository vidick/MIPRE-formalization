/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Games.lean (statement stub of MIPRE.ProjectiveMeasurement.consistency);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games

open MIPRE
open MIPRE.ProjectiveMeasurement
open ComplexOrder Kronecker Matrix
open scoped MatrixOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {𝒜 ℬ : Type*} [Ring 𝒜] [StarRing 𝒜] [Module ℂ 𝒜]
  [Ring ℬ] [StarRing ℬ] [Module ℂ ℬ]
variable [DecidableEq A]
omit [Fintype X]

theorem MIPRE.ProjectiveMeasurement.consistency (P : ProjectiveMeasurement X A 𝒜) (τ : TracialState 𝒜) (x : X)
    {a b : A} (hab : a ≠ b) : τ (P.M x a * P.M x b) = 0 := by sorry

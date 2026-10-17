/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/OracularSound.lean (statement stub of MIPRE.SeededGame.sum_dist_mul);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_OracularGame
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_OracularSound

open MIPRE
open MIPRE.SeededGame
open Finset Matrix
variable {A : Type*} [Inhabited A]
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] [Fintype A] [DecidableEq A]
variable (S : SeededGame V A)
omit [Nonempty V] [Fintype A] [DecidableEq A] [Inhabited A]

theorem MIPRE.SeededGame.sum_dist_mul (F : V → V → ℝ) :
    ∑ x, ∑ y, S.dist x y * F x y
      = (Fintype.card V : ℝ)⁻¹ * ∑ z, F (S.LA z) (S.LB z) := by sorry

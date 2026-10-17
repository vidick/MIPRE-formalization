/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Distances.lean (statement stub of MIPRE.POVM.ext_prime);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances

open MIPRE
open MIPRE.POVM
open ComplexOrder Matrix
variable {n : Type*} [Fintype n]
variable {X A d : Type*} [Fintype X] [Fintype A] [Fintype d] [DecidableEq d]

theorem MIPRE.POVM.ext_prime {M N : POVM A d} (h : ∀ a, (((M.mats a)).val) = (((N.mats a)).val)) : M = N := by sorry

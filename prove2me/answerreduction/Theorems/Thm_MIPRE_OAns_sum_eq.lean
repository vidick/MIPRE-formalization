/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/OracularGame.lean (statement stub of MIPRE.OAns.sum_eq);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_OracularGame

open MIPRE
open MIPRE.OAns
open Finset
variable {V A : Type*} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
omit [DecidableEq A]

theorem MIPRE.OAns.sum_eq {M : Type*} [AddCommMonoid M] (f : OAns A → M) :
    ∑ u, f u = (∑ p : A × A, f (.pair p.1 p.2)) + ∑ a, f (.single a) := by sorry

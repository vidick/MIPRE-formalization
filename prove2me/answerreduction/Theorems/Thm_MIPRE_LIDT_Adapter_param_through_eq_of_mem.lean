/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Geometry.lean (statement stub of MIPRE.LIDT.Adapter.param_through_eq_of_mem);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Geometry

open MIPRE
open MIPRE.LIDT
open MIPRE.LIDT.Adapter
open Finset Submodule Module MIPRE.CL
variable {F : Type*} [Field F] {n : ℕ}
variable [DecidableEq F]

theorem MIPRE.LIDT.Adapter.param_through_eq_of_mem {v : Fin n → F} (hv : ∃ j, v j ≠ 0) (u : Fin n → F) (t : F) :
    Line.param (Line.through u v) ((Line.through u v).1 + t • (Line.through u v).2) = t := by sorry

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SampledGame.lean (statement stub of MIPRE.SampledGame.dist_eq_card);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_SampledGame

open MIPRE
open MIPRE.SampledGame
open Finset Classical
set_option linter.unusedSectionVars false
variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]

theorem MIPRE.SampledGame.dist_eq_card (qA : S → X) (qB : S → Y) (x : X) (y : Y) :
    dist qA qB x y = ((univ.filter fun s => qA s = x ∧ qB s = y).card : ℝ) / Fintype.card S := by sorry

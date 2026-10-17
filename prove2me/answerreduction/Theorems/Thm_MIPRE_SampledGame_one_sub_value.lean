/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SampledGame.lean (statement stub of MIPRE.SampledGame.one_sub_value);
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

theorem MIPRE.SampledGame.one_sub_value [Nonempty S] {A B : Type*} [Fintype A] [Fintype B]
    (qA : S → X) (qB : S → Y) (D : X → Y → A → B → Bool)
    (R : TensorProductStrategy (game qA qB D)) :
    1 - R.value = (∑ s, R.failAt (qA s) (qB s)) / Fintype.card S := by sorry

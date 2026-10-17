/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/GameAdapt.lean (statement stub of MIPRE.TensorProductStrategy.succAt_adapt_eq);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameAdapt

open MIPRE
open MIPRE.TensorProductStrategy
open Matrix Kronecker Finset
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {X' Y' A' B' : Type*} [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
variable {G : Game X Y A B}
variable [DecidableEq A'] [DecidableEq B']

theorem MIPRE.TensorProductStrategy.succAt_adapt_eq (S : TensorProductStrategy G) (G' : Game X' Y' A' B')
    (qA : X' → X) (qB : Y' → Y) (rA : X' → A → A') (rB : Y' → B → B') (x' : X') (y' : Y') :
    (S.adapt G' qA qB rA rB).succAt x' y'
      = ∑ a, ∑ b, (if G'.D x' y' (rA x' a) (rB y' b) then 1 else 0)
          * S.born (qA x') (qB y') a b := by sorry

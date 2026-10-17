/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/GameAdapt.lean (statement stub of MIPRE.TensorProductStrategy.one_sub_value_adapt_le_sum);
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
variable [DecidableEq X] [DecidableEq Y]

theorem MIPRE.TensorProductStrategy.one_sub_value_adapt_le_sum (S : TensorProductStrategy G) (G' : Game X' Y' A' B')
    (qA : X' → X) (qB : Y' → Y) (rA : X' → A → A') (rB : Y' → B → B')
    (hD : ∀ x' y' a b, G'.μ x' y' ≠ 0 →
      G.D (qA x') (qB y') a b = true → G'.D x' y' (rA x' a) (rB y' b) = true) :
    1 - (S.adapt G' qA qB rA rB).value
      ≤ ∑ x, ∑ y, (∑ x' ∈ Finset.univ.filter (fun x' => qA x' = x),
          ∑ y' ∈ Finset.univ.filter (fun y' => qB y' = y), G'.μ x' y') * S.failAt x y := by sorry

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/GameTransportByQuestion.lean (statement stub of MIPRE.TensorProductStrategy.value_le_mergeAnswersByQuestion);
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
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameTransportByQuestion

open MIPRE
open MIPRE.TensorProductStrategy
open Matrix Kronecker Finset Classical
variable {X Y A B A' B' : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype A'] [Fintype B'] [DecidableEq A] [DecidableEq B]

theorem MIPRE.TensorProductStrategy.value_le_mergeAnswersByQuestion {G' : Game X Y A' B'}
    (S' : TensorProductStrategy G') (G : Game X Y A B)
    (rA : X → A' → A) (rB : Y → B' → B) (hμ : ∀ x y, G.μ x y = G'.μ x y)
    (hD : ∀ x y a' b', G'.D x y a' b' = true → G.D x y (rA x a') (rB y b') = true) :
    S'.value ≤ (S'.mergeAnswersByQuestion G rA rB).value := by sorry

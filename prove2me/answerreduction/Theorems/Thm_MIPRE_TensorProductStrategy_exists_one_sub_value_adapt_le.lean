/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/GameAdapt.lean (statement stub of MIPRE.TensorProductStrategy.exists_one_sub_value_adapt_le);
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

theorem MIPRE.TensorProductStrategy.exists_one_sub_value_adapt_le {Seed : Type*} [Fintype Seed] [Nonempty Seed]
    (S : TensorProductStrategy G) (G' : Game X' Y' A' B')
    (qA : Seed → X' → X) (qB : Seed → Y' → Y) (rA : Seed → X' → A → A')
    (rB : Seed → Y' → B → B') (C : ℝ)
    (hD : ∀ σ x' y' a b, G'.μ x' y' ≠ 0 →
      G.D (qA σ x') (qB σ y') a b = true → G'.D x' y' (rA σ x' a) (rB σ y' b) = true)
    (hμ : ∀ x y, (∑ σ, ∑ x' ∈ Finset.univ.filter (fun x' => qA σ x' = x),
        ∑ y' ∈ Finset.univ.filter (fun y' => qB σ y' = y), G'.μ x' y')
      ≤ (Fintype.card Seed : ℝ) * (C * G.μ x y)) :
    ∃ σ : Seed,
      1 - (S.adapt G' (qA σ) (qB σ) (rA σ) (rB σ)).value ≤ C * (1 - S.value) := by sorry

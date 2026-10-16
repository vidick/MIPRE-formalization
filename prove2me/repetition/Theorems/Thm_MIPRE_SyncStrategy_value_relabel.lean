/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/GameTransport.lean (statement stub of MIPRE.SyncStrategy.value_relabel);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_GameTransport

open MIPRE
open MIPRE.SyncStrategy
open Matrix Kronecker
open scoped ComplexOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [DecidableEq A] {G : SynchronousGame X A}

theorem MIPRE.SyncStrategy.value_relabel {X' A' : Type*} [Fintype X'] [Fintype A'] [DecidableEq A']
    (S : SyncStrategy G) (G' : SynchronousGame X' A') (eX : X' ≃ X) (eA : A' ≃ A)
    (hμ : ∀ x' y', G'.μ x' y' = G.μ (eX x') (eX y'))
    (hD : ∀ x' y' a' b', G'.D x' y' a' b' = G.D (eX x') (eX y') (eA a') (eA b')) :
    (S.relabel G' eX eA).value = S.value := by sorry

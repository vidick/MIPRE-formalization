/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SyncPushQ.lean (statement stub of MIPRE.SyncStrategy.value_pushQ_eq_one);
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
import Definitions.Def_MIPRE_Foundations_SyncPushQ

open MIPRE
open MIPRE.SyncStrategy
open Finset
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A] {G : SynchronousGame X A}

theorem MIPRE.SyncStrategy.value_pushQ_eq_one (S : SyncStrategy G) {X' A' : Type*} [Fintype X'] [Fintype A']
    [DecidableEq A'] (G' : SynchronousGame X' A') (g : X' → X) (f : X' → A → A')
    (hZ : ∀ x y, 0 < G.μ x y → ∀ a b, G.D x y a b = false → S.P.M x a * S.P.M y b = 0)
    (h : ∀ x' y', 0 < G'.μ x' y' → 0 < G.μ (g x') (g y') ∧ ∀ a b,
      (0 < G.μ (g x') (g x') → G.D (g x') (g x') a a = true) →
      (0 < G.μ (g y') (g y') → G.D (g y') (g y') b b = true) →
      G.D (g x') (g y') a b = true → G'.D x' y' (f x' a) (f y' b) = true) :
    (S.pushQ G' g f).value = 1 := by sorry

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/TwirlDistance.lean (statement stub of MIPRE.Introspection.unitaryTwirl_dist_le);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_Introspection_TwirlDistance

open MIPRE
open MIPRE.Introspection
open Finset Matrix
variable {dA dB I : Type*} [Fintype dA] [DecidableEq dA]
  [Fintype dB] [DecidableEq dB] [Fintype I]

theorem MIPRE.Introspection.unitaryTwirl_dist_le (μ : I → ℝ) (hμ0 : ∀ u, 0 ≤ μ u) (hμ1 : ∑ u, μ u = 1)
    (U : I → Matrix dA dA ℂ) (hU : ∀ u, (U u)ᴴ * U u = 1)
    (ψ : dA × dB → ℂ) (M : Matrix dA dA ℂ) :
    stateSqNorm ψ (unitaryTwirl μ U M - M) ≤
      ∑ u, μ u * stateSqNorm ψ (M * (U u)ᴴ - (U u)ᴴ * M) := by sorry

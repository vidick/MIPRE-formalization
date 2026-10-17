/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/TwirlDistance.lean (definition bundle: declarations the uploaded statements rest on);
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

/-! # Approximate commutation controls twirling in the state-dependent norm

This is the paper's `lem:mixing-U`, with constant one and all outcome sums explicit.
The state need not be invariant under any of the unitaries.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix

variable {dA dB I : Type*} [Fintype dA] [DecidableEq dA]
  [Fintype dB] [DecidableEq dB] [Fintype I]

/-- Twirling against a finitely supported probability distribution. -/
def unitaryTwirl (μ : I → ℝ) (U : I → Matrix dA dA ℂ) (M : Matrix dA dA ℂ) :
    Matrix dA dA ℂ := ∑ u, (μ u : ℂ) • (U u * M * (U u)ᴴ)

end MIPRE.Introspection

end

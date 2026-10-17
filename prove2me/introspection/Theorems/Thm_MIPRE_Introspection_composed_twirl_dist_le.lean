/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/ComposedTwirl.lean (statement stub of MIPRE.Introspection.composed_twirl_dist_le);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Introspection_TwirlDistance

open MIPRE
open MIPRE.Introspection
open Finset Matrix
variable {dA dB I J A : Type*} [Fintype dA] [DecidableEq dA]
  [Fintype dB] [DecidableEq dB] [Fintype I] [Fintype J] [Fintype A]

theorem MIPRE.Introspection.composed_twirl_dist_le (μ : I → ℝ) (ν : J → ℝ)
    (hμ0 : ∀ i, 0 ≤ μ i) (hν0 : ∀ j, 0 ≤ ν j)
    (hμ1 : ∑ i, μ i = 1) (hν1 : ∑ j, ν j = 1)
    (ψ : dA × dB → ℂ) (M : POVM A dA)
    (U : I → Matrix dA dA ℂ) (V : J → Matrix dA dA ℂ) (W : J → Matrix dB dB ℂ)
    (hUsa : ∀ i, (U i)ᴴ = U i) (hUid : ∀ i, U i * U i = 1)
    (hVsa : ∀ j, (V j)ᴴ = V j) (hVid : ∀ j, V j * V j = 1)
    (hW : ∀ j, (W j)ᴴ * W j = 1) (hmirror : ∀ j, xSqNorm ψ (V j) (W j) = 0) :
    (∑ a, stateSqNorm ψ
      (unitaryTwirl ν V (unitaryTwirl μ U (M.mats a).val) - (M.mats a).val)) ≤
      4 * (∑ i, μ i * ∑ a, stateSqNorm ψ ((M.mats a).val * U i - U i * (M.mats a).val)) +
      4 * (∑ j, ν j * ∑ a, stateSqNorm ψ ((M.mats a).val * V j - V j * (M.mats a).val)) := by sorry

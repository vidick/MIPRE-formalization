/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/TwoSidedCommutation.lean (statement stub of MIPRE.Introspection.two_sided_commutation_avg);
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

open MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N A : Type*} [Fintype N] [DecidableEq N] [Fintype A]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

theorem MIPRE.Introspection.two_sided_commutation_avg {X I J : Type*} [Fintype X] [Fintype I] [Fintype J]
    (D : X → ℝ) (hD : ∀ x, 0 ≤ D x)
    (μ : X → I → ℝ) (ν : X → J → ℝ)
    (hμ0 : ∀ x i, 0 ≤ μ x i) (hν0 : ∀ x j, 0 ≤ ν x j)
    (hμ1 : ∀ x, ∑ i, μ x i = 1) (hν1 : ∀ x, ∑ j, ν x j = 1)
    (ψ : dA × dB → ℂ) (M : X → POVM A dA)
    (U : X → I → Matrix dA dA ℂ) (V : X → J → Matrix dA dA ℂ)
    (W : X → J → Matrix dB dB ℂ)
    (hU : ∀ x i, (U x i)ᴴ * U x i = 1) (hW : ∀ x j, (W x j)ᴴ * W x j = 1) :
    (∑ x, D x * ∑ i, μ x i * ∑ j, ν x j * ∑ a,
      stateSqNorm ψ (((M x).mats a).val * (U x i * V x j) -
        (U x i * V x j) * ((M x).mats a).val)) ≤
      4 * (∑ x, D x * ∑ i, μ x i * ∑ a,
        stateSqNorm ψ (((M x).mats a).val * U x i - U x i * ((M x).mats a).val)) +
      4 * (∑ x, D x * ∑ j, ν x j * ∑ a,
        stateSqNorm ψ (((M x).mats a).val * V x j - V x j * ((M x).mats a).val)) +
      8 * (∑ x, D x * ∑ j, ν x j * xSqNorm ψ (V x j) (W x j)) := by sorry

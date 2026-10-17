/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/TwoSidedCommutation.lean (statement stub of MIPRE.Introspection.commutator_product_bound);
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

theorem MIPRE.Introspection.commutator_product_bound (ψ : N → ℂ) (M : A → Matrix N N ℂ)
    (hM : ∑ a, (M a)ᴴ * M a ≤ (1 : Matrix N N ℂ))
    (U V W : Matrix N N ℂ) (hU : Uᴴ * U = 1) (hW : Wᴴ * W = 1)
    (hWU : W * U = U * W) (hWM : ∀ a, W * M a = M a * W) :
    (∑ a, snorm ψ (M a * (U * V) - (U * V) * M a) ^ 2) ≤
      4 * (∑ a, snorm ψ (M a * U - U * M a) ^ 2) +
      4 * (∑ a, snorm ψ (M a * V - V * M a) ^ 2) +
      8 * snorm ψ (V - W) ^ 2 := by sorry

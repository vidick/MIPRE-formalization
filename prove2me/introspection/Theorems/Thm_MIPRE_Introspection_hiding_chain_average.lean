/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/HidingTests.lean (statement stub of MIPRE.Introspection.hiding_chain_average);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
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
import Definitions.Def_MIPRE_Foundations_Introspection_SamplingPrefix

open MIPRE
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {X Y A B C J H K : Type*}
  [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype A] [Fintype B] [Fintype C] [DecidableEq C]
  [Fintype J] [DecidableEq J] [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

theorem MIPRE.Introspection.hiding_chain_average (ψ : H × K → ℂ) (D : J → ℝ) (hD : ∀ j, 0 ≤ D j)
    (P : ℕ → J → C → Matrix H H ℂ) (n : ℕ) (δ : ℕ → ℝ)
    (hstep : ∀ i < n, (∑ j, D j * ∑ z, stateSqNorm ψ (P i j z - P (i + 1) j z)) ≤ δ i) :
    (∑ j, D j * ∑ z, stateSqNorm ψ (P 0 j z - P n j z)) ≤
      (n : ℝ) * ∑ i ∈ Finset.range n, δ i := by sorry

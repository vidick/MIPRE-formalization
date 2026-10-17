/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CrossConsistency.lean (statement stub of MIPRE.sum_condFail_le_of_pushforward);
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

open MIPRE
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
variable {ε : ℝ}

theorem MIPRE.sum_condFail_le_of_pushforward {ι : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq X] [DecidableEq Y]
    (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue G ψ MA MB ≤ ε) (ν : ι → ℝ)
    (q : ι → X × Y) {c : ℝ} (hc : 0 < c)
    (hpush : ∀ p : X × Y, c * ∑ i ∈ univ.filter fun i => q i = p, ν i ≤ G.μ p.1 p.2) :
    ∑ i, ν i * condFail G ψ MA MB (q i).1 (q i).2 ≤ ε / c := by sorry

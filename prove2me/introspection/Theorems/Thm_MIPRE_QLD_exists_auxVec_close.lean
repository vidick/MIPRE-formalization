/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/SwapState.lean (statement stub of MIPRE.QLD.exists_auxVec_close);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
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
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_Expanded
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_Linearity
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Background_QLD_ExactPauli
import Definitions.Def_MIPRE_Background_QLD_SwapUnitary
import Definitions.Def_MIPRE_Background_QLD_SwapState

open MIPRE
open MIPRE.QLD
open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [Fintype R] [DecidableEq R]

theorem MIPRE.QLD.exists_auxVec_close (θ : R × ((n → F) × (n → F)) → ℂ) (hθ : star θ ⬝ᵥ θ = 1)
    {δ : ℝ} (hδ : 0 ≤ δ) (hlt : 2 * Real.sqrt δ + 2 * δ < 1)
    (hX : 1 - δ / 2
      ≤ (star θ ⬝ᵥ ((bOp (twirl (wX (F := F) (n := n))) :
          Matrix (R × ((n → F) × (n → F))) (R × ((n → F) × (n → F))) ℂ) *ᵥ θ)).re)
    (hZ : 1 - δ / 2
      ≤ (star θ ⬝ᵥ ((bOp (twirl (wZ (F := F) (n := n))) :
          Matrix (R × ((n → F) × (n → F))) (R × ((n → F) × (n → F))) ℂ) *ᵥ θ)).re) :
    ∃ aux : R → ℂ, ‖evec (auxVec (F := F) (n := n) aux)‖ = 1 ∧
      ‖evec θ - evec (auxVec (F := F) (n := n) aux)‖ ^ 2
        ≤ 2 - 2 * Real.sqrt (1 - (2 * Real.sqrt δ + 2 * δ)) := by sorry

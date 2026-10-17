/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Pasting.lean (statement stub of MIPRE.abs_sand_sub_ord_le);
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
import Definitions.Def_MIPRE_Foundations_Pasting

open MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {R1 R2 K : Type*} [Fintype R1] [DecidableEq R1] [Fintype R2] [DecidableEq R2]
  [Fintype K] [DecidableEq K]
variable {R : R1 → Matrix dB dB ℂ} {G : K → Matrix dB dB ℂ}

theorem MIPRE.abs_sand_sub_ord_le {ψ : dA × dB → ℂ} (hψ : ‖evec ψ‖ = 1)
    {A : R1 × R2 → Matrix dA dA ℂ} (hA : IsPVM A) (hG : IsPVM G) (e : K → R2) :
    |(∑ a : R1, ∑ g : K, bornProb ψ (A (a, e g)) (G g * R a * G g))
        - ∑ a : R1, ∑ g : K, bornProb ψ (A (a, e g)) (G g * R a)|
      ≤ Real.sqrt (∑ a : R1, ∑ g : K,
          snorm ψ (bOp (R a * G g - G g * R a) : Matrix (dA × dB) _ ℂ) ^ 2) := by sorry

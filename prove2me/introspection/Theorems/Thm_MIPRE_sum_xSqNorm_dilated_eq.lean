/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Sandwich.lean (statement stub of MIPRE.sum_xSqNorm_dilated_eq);
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

open MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {A : Type*} [Fintype A] [DecidableEq A]
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {ψ : dA × dB → ℂ}
  {Q : (A × A) → Matrix (dA × (A × A)) (dA × (A × A)) ℂ}
  {Q' : (A × A) → Matrix (dB × (A × A)) (dB × (A × A)) ℂ}
  {R : (A × A) → Matrix dA dA ℂ} {R' : (A × A) → Matrix dB dB ℂ}

theorem MIPRE.sum_xSqNorm_dilated_eq (hψ : star ψ ⬝ᵥ ψ = 1) (a₀ : A × A)
    (hQ : IsPVM Q) (hQ' : IsPVM Q')
    (hkA : ∀ p, (ancillaEmbed dA a₀)ᴴ * (Q p * ancillaEmbed dA a₀) = R p)
    (hkB : ∀ p, (ancillaEmbed dB a₀)ᴴ * (Q' p * ancillaEmbed dB a₀) = R' p)
    (hR : ∑ p : A × A, R p = 1) (hR' : ∑ p : A × A, R' p = 1) :
    ∑ p : A × A, xSqNorm (extVec2 ψ a₀ a₀) (Q p) (Q' p)
      = 2 * (1 - ∑ p : A × A, bornProb ψ (R p) (R' p)) := by sorry

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Sandwich.lean (statement stub of MIPRE.exists_projective_joint);
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

theorem MIPRE.exists_projective_joint {ι : Type*} [Fintype ι] {w : ι → ℝ}
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (a₀ : A × A)
    {X Z : ι → A → Matrix dA dA ℂ} {X' Z' : ι → A → Matrix dB dB ℂ}
    (hX : ∀ i, IsPVM (X i)) (hZ : ∀ i, IsPVM (Z i))
    (hX' : ∀ i, IsPVM (X' i)) (hZ' : ∀ i, IsPVM (Z' i))
    {cA cB α β : ℝ}
    (hcA : ∑ i, w i * ∑ p : A × A,
        stateSqNorm ψ (X i p.1 * Z i p.2 - Z i p.2 * X i p.1) ≤ cA)
    (hcB : ∑ i, w i * ∑ p : A × A,
        ‖stateVecB ψ (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1)‖ ^ 2 ≤ cB)
    (hα : ∑ i, w i * ∑ a : A, xSqNorm ψ (X i a) (X' i a) ≤ α)
    (hβ : ∑ i, w i * ∑ b : A, xSqNorm ψ (Z i b) (Z' i b) ≤ β) :
    ∃ (QA : ι → (A × A) → Matrix (dA × (A × A)) (dA × (A × A)) ℂ)
      (QB : ι → (A × A) → Matrix (dB × (A × A)) (dB × (A × A)) ℂ),
      (∀ i, IsPVM (QA i)) ∧ (∀ i, IsPVM (QB i))
      ∧ (∀ i p, (ancillaEmbed dA a₀)ᴴ * (QA i p * ancillaEmbed dA a₀) = sand (X i) (Z i) p)
      ∧ (∀ i p, (ancillaEmbed dB a₀)ᴴ * (QB i p * ancillaEmbed dB a₀) = sand (X' i) (Z' i) p)
      ∧ (∑ i, w i * ∑ p : A × A, xSqNorm (extVec2 ψ a₀ a₀) (QA i p) (QB i p)
          ≤ 2 * (Real.sqrt cA + Real.sqrt cB + Real.sqrt (α / 2) + β / 2))
      ∧ (∑ i, w i * ∑ p : A × A,
            xSqNorm (extVec2 ψ a₀ a₀) (QA i p) (aOp (Z' i p.2 * X' i p.1))
          ≤ 4 * (Real.sqrt cA + Real.sqrt cB + Real.sqrt (α / 2) + β / 2) + 2 * cB)
      ∧ (∑ i, w i * ∑ p : A × A,
            xSqNorm (extVec2 ψ a₀ a₀) (QA i p) (aOp (X' i p.1 * Z' i p.2))
          ≤ 4 * (Real.sqrt cA + Real.sqrt cB + Real.sqrt (α / 2) + β / 2) + 8 * cB) := by sorry

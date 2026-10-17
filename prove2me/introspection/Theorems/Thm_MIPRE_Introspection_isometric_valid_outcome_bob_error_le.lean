/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/ValidOutcomeError.lean (statement stub of MIPRE.Introspection.isometric_valid_outcome_bob_error_le);
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
import Definitions.Def_MIPRE_Foundations_Swap
import Definitions.Def_MIPRE_Foundations_Introspection_ValueStability
import Definitions.Def_MIPRE_Foundations_Introspection_IsometricStrategy

open MIPRE
open MIPRE.Introspection
open Finset Matrix Classical
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {N A B : Type*} [Fintype N] [DecidableEq N]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
variable {H R S : Type*} [Fintype H] [DecidableEq H]
  [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]

theorem MIPRE.Introspection.isometric_valid_outcome_bob_error_le (V : Matrix S H ℂ) (hV : Vᴴ * V = 1)
    (ψ : R × S → ℂ) (hψ : ‖evec ψ‖ = 1) (M : POVM B H)
    (f : B → Option A) (v : A → B) (hv : ∀ a, f (v a) = some a)
    (P : Option A → Matrix S S ℂ) (hP : IsPVM P) (hPnone : P none = 0)
    {δ : ℝ} (hclose : ∑ a, snorm ψ
      (bOp (isometricImage V (M.mats (v a)).val - P (some a))) ^ 2 ≤ δ) :
    (∑ a, snorm ψ (bOp (isometricImage V ((M.map f).mats a).val - P a)) ^ 2) ≤
      2 * δ + 4 * Real.sqrt δ := by sorry

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/BlockRetention.lean (statement stub of MIPRE.Introspection.block_retention_dist_avg);
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
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
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
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Definitions.Def_MIPRE_Foundations_Introspection_BlockTwirl
import Definitions.Def_MIPRE_Foundations_Introspection_BlockPOVM
import Definitions.Def_MIPRE_Foundations_Introspection_BlockRetention

open MIPRE
open MIPRE.Introspection
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
variable {V H Y A : Type*} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]
  [Fintype Y] [DecidableEq Y] [Fintype A] [DecidableEq A]
variable {B : Type*} [Fintype B] [DecidableEq B]

theorem MIPRE.Introspection.block_retention_dist_avg {X : Type*} [Fintype X]
    (D : X → ℝ) (hD0 : ∀ x, 0 ≤ D x) (hD1 : ∑ x, D x = 1)
    (ψ : (V × H) × B → ℂ) (hψ : ‖evec ψ‖ = 1)
    (M : X → Y × A → Matrix (V × H) (V × H) ℂ) (hM : ∀ x, IsPVM (M x))
    (P : X → Y → Matrix V V ℂ) (hP : ∀ x, IsPVM (P x))
    (Q : X → Y → POVM (Y × A) H) (R : X → Y → Matrix B B ℂ) (hR : ∀ x, IsPVM (R x))
    (hPR : ∀ x y, aOp (aOp (P x y) : Matrix (V × H) _ ℂ) *ᵥ ψ = bOp (R x y) *ᵥ ψ)
    {δ : ℝ} (hclose : ∑ x, D x *
      (2 * (∑ y, stateSqNorm ψ ((∑ a, M x (y, a)) - aOp (P x y))) +
       2 * (∑ p : Y × A, stateSqNorm ψ (M x p - ∑ z, P x z ⊗ₖ ((Q x z).mats p).val))) ≤ δ) :
    (∑ x, D x * ∑ p : Y × A, stateSqNorm ψ
      (M x p - P x p.1 ⊗ₖ (((Q x p.1).map Prod.snd).mats p.2).val)) ≤
      2 * δ + 4 * Real.sqrt δ := by sorry

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/RegisterMixing.lean (statement stub of MIPRE.Introspection.exists_register_mixing_sqrt);
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
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Foundations_Introspection_TwirlDistance
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Definitions.Def_MIPRE_Foundations_Introspection_CommutatorParseval
import Definitions.Def_MIPRE_Foundations_Introspection_BlockTwirl
import Definitions.Def_MIPRE_Foundations_Introspection_BlockPOVM
import Definitions.Def_MIPRE_Foundations_Introspection_EPR
import Definitions.Def_MIPRE_Foundations_Introspection_BlockRetention
import Definitions.Def_MIPRE_Foundations_Introspection_PauliMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterTransport
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterEPR
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterMixing

open MIPRE
open MIPRE.Introspection
open Finset Matrix MIPRE.Weyl Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {I R H K A : Type*} [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype A] [DecidableEq A] {n : ℕ}
variable {X : Type*} [Fintype X] {n : X → ℕ} {I R : X → Type*}
  [∀ x, Fintype (I x)] [∀ x, DecidableEq (I x)]
  [∀ x, Fintype (R x)] [∀ x, DecidableEq (R x)] [∀ x, Nonempty (R x)]

theorem MIPRE.Introspection.exists_register_mixing_sqrt
    (D : X → ℝ) (hD0 : ∀ x, 0 ≤ D x) (hD1 : ∑ x, D x = 1)
    (e : (x : X) → I x ≃ (Fin (n x) → F) × R x)
    (L : (x : X) → (Fin (n x) → F) →ₗ[F] (Fin (n x) → F))
    (ξ : H × K → ℂ) (hξ : ‖evec ξ‖ = 1)
    (M : (x : X) → POVM ((Fin (n x) → F) × A) (I x × H))
    (hM : ∀ x, IsPVM (fun p => ((M x).mats p).val))
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hmarg : ∑ x, D x * registerMarginalError (e x) (L x) ξ
      (fun p => ((M x).mats p).val) ≤ ε)
    (hZ : ∑ x, D x * registerCommutatorError (e x) ξ
      (fun p => ((M x).mats p).val) wZ LinearMap.id ≤ ε)
    (hX : ∑ x, D x * registerCommutatorError (e x) ξ
      (fun p => ((M x).mats p).val) wX (CL.lperp (L x)) ≤ ε) :
    ∃ Q : (x : X) → (Fin (n x) → F) → POVM A (R x × H),
      (∑ x, D x * ∑ p : (Fin (n x) → F) × A, stateSqNorm (registerState (I x) ξ)
        (((M x).mats p).val - registerOp (registerParty (e x) H)
          (synOf wZ (L x) p.1 ⊗ₖ ((Q x p.1).mats p.2).val))) ≤ 56 * Real.sqrt ε := by sorry

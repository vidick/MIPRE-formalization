/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/RegisterMixing.lean (definition bundle: declarations the uploaded statements rest on);
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

/-! # Pauli mixing in the original local register

The basis equivalence explicitly splits the retained coordinates from the local
complement. Hypotheses and the conclusion are stated on the original EPR state,
and the output POVMs act only on that local complement and the original ancilla.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Weyl Classical
open scoped Kronecker

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {I R H K A : Type*} [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype A] [DecidableEq A] {n : ℕ}

/-- Read a Pauli linear map on the selected coordinates of the original register. -/
def registerReadout (e : I ≃ (Fin n → F) × R)
    (w : (Fin n → F) → Matrix (Fin n → F) (Fin n → F) ℂ)
    (L : (Fin n → F) →ₗ[F] (Fin n → F)) (y : Fin n → F) :
    Matrix (I × H) (I × H) ℂ :=
  registerOp (registerParty e H) (aOp (synOf w L y))

/-- The first marginal consistency error in the original coordinates. -/
def registerMarginalError (e : I ≃ (Fin n → F) × R)
    (L : (Fin n → F) →ₗ[F] (Fin n → F)) (ξ : H × K → ℂ)
    (M : (Fin n → F) × A → Matrix (I × H) (I × H) ℂ) : ℝ :=
  ∑ y, stateSqNorm (registerState I ξ)
    ((∑ a, M (y, a)) - registerReadout e wZ L y)

/-- The readout commutation error in the original coordinates. -/
def registerCommutatorError (e : I ≃ (Fin n → F) × R) (ξ : H × K → ℂ)
    (M : (Fin n → F) × A → Matrix (I × H) (I × H) ℂ)
    (w : (Fin n → F) → Matrix (Fin n → F) (Fin n → F) ℂ)
    (L : (Fin n → F) →ₗ[F] (Fin n → F)) : ℝ :=
  ∑ p, ∑ y, stateSqNorm (registerState I ξ)
    (M p * registerReadout e w L y - registerReadout e w L y * M p)

section Varying

variable {X : Type*} [Fintype X] {n : X → ℕ} {I R : X → Type*}
  [∀ x, Fintype (I x)] [∀ x, DecidableEq (I x)]
  [∀ x, Fintype (R x)] [∀ x, DecidableEq (R x)] [∀ x, Nonempty (R x)]

end Varying

end MIPRE.Introspection

end

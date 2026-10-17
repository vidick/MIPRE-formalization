/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/PauliMixing.lean (definition bundle: declarations the uploaded statements rest on);
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

/-! # Pauli mixing with a retained classical fibre

The sampled register has a fixed coordinate presentation, with arbitrary auxiliary systems.
The output consists of actual ancillary POVMs. Consistency and the two readout commutator
errors control the squared state distance by an explicit square-root estimate.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Weyl Classical
open scoped Kronecker

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {n : ℕ} {H K A : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype A] [DecidableEq A]

/-- Sum of the commutator errors against a linear-map readout, over all outcomes and fibres. -/
def readoutCommutatorError {B : Type*} [Fintype B]
    (ψ : ((Fin n → F) × H) × K → ℂ)
    (M : B → Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ)
    (w : (Fin n → F) → Matrix (Fin n → F) (Fin n → F) ℂ)
    (L : (Fin n → F) →ₗ[F] (Fin n → F)) : ℝ :=
  ∑ a, ∑ y : Fin n → F, stateSqNorm ψ
    (M a * aOp (synOf w L y) - aOp (synOf w L y) * M a)

/-- The first marginal's consistency error with the retained `Z` readout. -/
def readoutMarginalError (L : (Fin n → F) →ₗ[F] (Fin n → F))
    (ψ : ((Fin n → F) × H) × K → ℂ)
    (M : (Fin n → F) × A → Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) : ℝ :=
  ∑ y, stateSqNorm ψ ((∑ a, M (y, a)) - aOp (synOf wZ L y))

/-- The error before completing the retained submeasurement: coefficients `2, 8, 8`. -/
def mixingError (L : (Fin n → F) →ₗ[F] (Fin n → F)) (ξ : H × K → ℂ)
    (M : POVM ((Fin n → F) × A) ((Fin n → F) × H)) : ℝ :=
  2 * readoutMarginalError L (eprWithAux ξ) (fun p => (M.mats p).val) +
  8 * readoutCommutatorError (eprWithAux ξ) (fun p => (M.mats p).val) wZ LinearMap.id +
  8 * readoutCommutatorError (eprWithAux ξ) (fun p => (M.mats p).val) wX (CL.lperp L)

end MIPRE.Introspection

end

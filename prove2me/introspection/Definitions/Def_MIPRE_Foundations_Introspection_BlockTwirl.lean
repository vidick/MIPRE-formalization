/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/BlockTwirl.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
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
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement

/-! # Entry formulas for Pauli twirls with an ancillary space -/

noncomputable section

namespace MIPRE.Introspection

open Finset Weyl Classical Matrix Kronecker

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ} {H : Type*} [Fintype H] [DecidableEq H]

def amplify (A : Matrix (Fin n → F) (Fin n → F) ℂ) :
    Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ := A ⊗ₖ (1 : Matrix H H ℂ)

/-- Average over the full `Z` Pauli family on the first tensor factor. -/
def dephaseZ (M : Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) :
    Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ :=
  (Fintype.card (Fin n → F) : ℂ)⁻¹ •
    ∑ v : Fin n → F, amplify (H := H) (wZ v) * M * amplify (H := H) (wZ v)

/-- Average the `X` Pauli conjugations belonging to a subspace. -/
def averageX (K : Submodule F (Fin n → F))
    (M : Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) :
    Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ :=
  (Fintype.card K : ℂ)⁻¹ • ∑ v : K, amplify (H := H) (wX v.1) * M * amplify (H := H) (wX v.1)

/-- The diagonal ancillary block obtained by averaging the fiber through `x`. -/
def averagedBlock (K : Submodule F (Fin n → F))
    (M : Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) (x : Fin n → F) : Matrix H H ℂ :=
  (Fintype.card K : ℂ)⁻¹ • ∑ v : K, M.submatrix (fun a => (x + v.1, a)) (fun a => (x + v.1, a))

end MIPRE.Introspection

end

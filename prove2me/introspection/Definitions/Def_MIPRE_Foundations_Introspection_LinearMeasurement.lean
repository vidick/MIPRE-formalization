/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/LinearMeasurement.lean (definition bundle: declarations the uploaded statements rest on);
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

/-!
# Fourier formulas for a linear-map measurement

The two identities of `lem:pauli-linear-fourier`, in characteristic two. The
formulas hold for either Weyl family, and more generally for any operator family
with its Fourier-defined spectral operators. Orthogonality is the actual dot
product perpendicular subspace, not a canonical direct-sum complement.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Weyl Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ}

/-- Restrict the trace character to a linear subspace, viewed over the binary field. -/
def subspaceTrace (S : Submodule F (Fin n → F)) (c : Fin n → F) :
    S →ₗ[ZMod 2] ZMod 2 :=
  (trDotL c).comp (S.subtype.restrictScalars (ZMod 2))

@[simp] theorem subspaceTrace_apply (S : Submodule F (Fin n → F)) (c : Fin n → F) (v : S) :
    subspaceTrace S c v = trDot v.1 c := rfl

/-- Pick a preimage only to state the Fourier coefficients; this is not an executable choice. -/
def linearPreimage (L : (Fin n → F) →ₗ[F] (Fin n → F)) (a : Fin n → F) : Fin n → F :=
  if h : ∃ x, L x = a then h.choose else 0

end MIPRE.Introspection

end

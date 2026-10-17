/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/BlockTwirl.lean (statement stub of MIPRE.Introspection.linear_twirl_blocks);
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
import Definitions.Def_MIPRE_Foundations_Introspection_BlockTwirl

open MIPRE
open MIPRE.Introspection
open Finset MIPRE.Weyl Classical Matrix Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ} {H : Type*} [Fintype H] [DecidableEq H]

theorem MIPRE.Introspection.linear_twirl_blocks (L : (Fin n → F) →ₗ[F] (Fin n → F))
    (M : Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) :
    averageX L.ker (dephaseZ M) =
      ∑ a : Fin n → F, synOf wZ L a ⊗ₖ averagedBlock L.ker M (linearPreimage L a) := by sorry

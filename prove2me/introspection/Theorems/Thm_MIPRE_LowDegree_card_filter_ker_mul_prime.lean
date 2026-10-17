/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/Anticomm.lean (statement stub of MIPRE.LowDegree.card_filter_ker_mul_prime);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.Trace.Basic
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm

open MIPRE
open MIPRE.LowDegree
open Finset MvPolynomial
variable {F V : Type*} [Field F] [Fintype F] [DecidableEq F] [AddCommGroup V] [Module F V]
  [Fintype V] [DecidableEq V]
omit [DecidableEq V]

theorem MIPRE.LowDegree.card_filter_ker_mul_prime (τ : V →ₗ[F] F) (hτ : τ ≠ 0) :
    #{r ∈ (univ : Finset V) | τ r = 0} * Fintype.card F = Fintype.card V := by sorry

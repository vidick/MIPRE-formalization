/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/NonMultilinear.lean (statement stub of MIPRE.QLD.sum_sub_le_of_eq_on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel

open MIPRE
open Finset MvPolynomial MIPRE.LowDegree
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ}
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem MIPRE.QLD.sum_sub_le_of_eq_on {A B S : G → ℝ} {ML : Finset G}
    (hon : ∀ g ∈ ML, A g = B g) (hA : ∀ g, |A g| ≤ S g) (hB : ∀ g, |B g| ≤ S g) :
    |∑ g, A g - ∑ g, B g| ≤ 2 * ∑ g ∈ univ \ ML, S g := by sorry

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/SchwartzZippel.lean (statement stub of MIPRE.LowDegree.prob_agree_le_individualDegree);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel

open MIPRE
open MIPRE.LowDegree
open Finset MvPolynomial
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}

theorem MIPRE.LowDegree.prob_agree_le_individualDegree {f g : MvPolynomial (Fin m) F} (hfg : f ≠ g) {d : ℕ}
    (hf : ∀ i, f.degreeOf i ≤ d) (hg : ∀ i, g.degreeOf i ≤ d) :
    ((agree f g).card : ℝ) / (Fintype.card F : ℝ) ^ m ≤ (m : ℝ) * d / Fintype.card F := by sorry

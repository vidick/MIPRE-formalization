/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/Encoding.lean (statement stub of MIPRE.LowDegree.degreeOf_ind_le);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding

open MIPRE
open MIPRE.LowDegree
open Finset MvPolynomial
variable {F : Type*} [CommRing F] {m : ℕ}

theorem MIPRE.LowDegree.degreeOf_ind_le [Nontrivial F] (y : Fin m → Bool) (i : Fin m) :
    (ind y : MvPolynomial (Fin m) F).degreeOf i ≤ 1 := by sorry

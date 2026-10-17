/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/Encoding.lean (solution of MIPRE.LowDegree.degreeOf_ind_le);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree
open Finset MvPolynomial
variable {F : Type*} [CommRing F] {m : ℕ}
theorem _root_.solution [Nontrivial F] (y : Fin m → Bool) (i : Fin m) :
    (ind y : MvPolynomial (Fin m) F).degreeOf i ≤ 1 := by
  have hfac : ∀ j : Fin m, (if y j then (X j : MvPolynomial (Fin m) F) else 1 - X j).degreeOf i
      ≤ if i = j then 1 else 0 := by
    intro j
    have hX : (X j : MvPolynomial (Fin m) F).degreeOf i ≤ if i = j then 1 else 0 := by
      by_cases h : i = j
      · subst h; simp
      · rw [if_neg h, MvPolynomial.degreeOf_X_of_ne h]
    cases hy : y j
    · simp only [Bool.false_eq_true, if_false]
      exact (MvPolynomial.degreeOf_sub_le i 1 (X j)).trans (by simpa using hX)
    · simpa [hy] using hX
  rw [ind]
  refine (MvPolynomial.degreeOf_prod_le i univ
    (fun j => if y j then (X j : MvPolynomial (Fin m) F) else 1 - X j)).trans ?_
  refine (Finset.sum_le_sum fun j _ => hfac j).trans ?_
  simp
end MIPRE.LowDegree

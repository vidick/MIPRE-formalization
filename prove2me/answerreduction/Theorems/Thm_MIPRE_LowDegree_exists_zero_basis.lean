/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/ZeroBasis.lean (statement stub of MIPRE.LowDegree.exists_zero_basis);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_ZeroBasis

open MIPRE
open MIPRE.LowDegree
open Finset MvPolynomial
variable {F : Type*} [Field F] {m : ℕ}

theorem MIPRE.LowDegree.exists_zero_basis (f : MvPolynomial (Fin m) F) {d : ℕ}
    (hd : ∀ i, f.degreeOf i ≤ d) (hf : ∀ y : Fin m → Bool, eval (pt y) f = 0) :
    ∃ c : Fin m → MvPolynomial (Fin m) F,
      f = ∑ i, c i * cubeZero i ∧ ∀ i j, (c i).degreeOf j ≤ d := by sorry

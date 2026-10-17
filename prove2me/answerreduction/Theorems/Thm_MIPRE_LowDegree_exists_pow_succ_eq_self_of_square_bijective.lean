/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/FiniteReducedComponents.lean (statement stub of MIPRE.LowDegree.exists_pow_succ_eq_self_of_square_bijective);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteReducedComponents

open MIPRE
open MIPRE.LowDegree
variable {R : Type*} [CommRing R] [Finite R]

theorem MIPRE.LowDegree.exists_pow_succ_eq_self_of_square_bijective
    (hsq : Function.Bijective (fun x : R => x * x)) (x : R) :
    ∃ n : ℕ, 0 < n ∧ x ^ (n + 1) = x := by sorry

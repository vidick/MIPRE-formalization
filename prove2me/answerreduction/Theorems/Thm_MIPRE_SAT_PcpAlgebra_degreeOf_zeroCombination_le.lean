/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/PcpAlgebra.lean (statement stub of MIPRE.SAT.PcpAlgebra.degreeOf_zeroCombination_le);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_ZeroBasis
import Definitions.Def_MIPRE_Foundations_SAT_PcpAlgebra

open MIPRE
open MIPRE.SAT
open MIPRE.SAT.PcpAlgebra
open Finset MvPolynomial MIPRE.LowDegree
variable {F : Type*} [Field F] {m : ℕ}

theorem MIPRE.SAT.PcpAlgebra.degreeOf_zeroCombination_le (c : Fin m → MvPolynomial (Fin m) F) {d : ℕ}
    (hc : ∀ i j, (c i).degreeOf j ≤ d) (j : Fin m) :
    (zeroCombination c).degreeOf j ≤ d + 2 := by sorry

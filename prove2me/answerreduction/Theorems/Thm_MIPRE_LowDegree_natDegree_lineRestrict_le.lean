/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/LineRestrict.lean (statement stub of MIPRE.LowDegree.natDegree_lineRestrict_le);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Degree
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_LineRestrict

open MIPRE
open MIPRE.LowDegree
open Finset
variable {F : Type*} [Field F] {m : ℕ}

theorem MIPRE.LowDegree.natDegree_lineRestrict_le (u₀ w : Fin m → F) (p : MvPolynomial (Fin m) F) :
    (lineRestrict u₀ w p).natDegree ≤ p.totalDegree := by sorry

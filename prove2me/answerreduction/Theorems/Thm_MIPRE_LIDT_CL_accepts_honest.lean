/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/CLHonest.lean (statement stub of MIPRE.LIDT.CL.accepts_honest);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Background_LIDT_Presentation
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_LineRestrict
import Definitions.Def_MIPRE_Background_LIDT_CLHonest

open MIPRE
open MIPRE.LIDT
open MIPRE.LIDT.CL
open Finset MIPRE.CL MIPRE.LowDegree
variable {F : Type*} [Field F] {m : ℕ}
variable [Fintype F] [DecidableEq F] [NeZero m] (hm : m ∣ Fintype.card F) {d ldc : ℕ}
variable {hm}

theorem MIPRE.LIDT.CL.accepts_honest {G : Fin ldc → MvPolynomial (Fin m) F}
    (hG : ∀ j i, (G j).degreeOf i ≤ d) (sm : Sample F m) (τ τ' : Ty) :
    accepts hm (sm.question hm τ) (sm.question hm τ')
      (honest hm (d := d) G (sm.question hm τ)) (honest hm (d := d) G (sm.question hm τ'))
      = true := by sorry

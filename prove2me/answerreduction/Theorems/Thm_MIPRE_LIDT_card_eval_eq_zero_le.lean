/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Coefficients.lean (statement stub of MIPRE.LIDT.card_eval_eq_zero_le);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Background_LIDT_Coefficients

open MIPRE
open MIPRE.LIDT
open Finset
variable {F : Type*} [Field F] {n d : ℕ}

theorem MIPRE.LIDT.card_eval_eq_zero_le [Fintype F] [DecidableEq F]
    {G : LowIndDegPoly (F := F) (m := n) (d := d)} (hG : G ≠ 0) :
    ((univ.filter fun u : Point F n => G.eval u = 0).card : ℝ) / (Fintype.card F : ℝ) ^ n
      ≤ (n : ℝ) * d / Fintype.card F := by sorry

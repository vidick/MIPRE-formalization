/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Coefficients.lean (delta bundle: declarations the new statements need that the published bundle Def_MIPRE_Background_LIDT_Coefficients does not carry);
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
import Theorems.Thm_MIPRE_LowDegree_prob_agree_le_individualDegree

/-!
# Coefficient vectors of low-individual-degree polynomials

`LowIndDegPoly F n d` is a coefficient vector indexed by exponent vectors with entries at most `d`.
This file is the algebra of those vectors that more than one analysis needs, moved here from the
Pauli basis test's `Dummy.lean` and `Linear.lean` (where it was first written) so that the
simultaneous low-degree test, which sits below the Pauli test in the import graph, can use it.
The names are unchanged.

* **Schwartz--Zippel for any finite variable type** (`prob_agreeOn_le_individualDegree`), and the
  bridge `LowIndDegPoly.toMv` to `MvPolynomial` with its evaluation, coefficient and
  individual-degree facts; `card_eval_eq_zero_le` is the form a nonzero coefficient vector needs.
* **Coefficients of a monomial pattern.** `LowIndDegPoly.coef g T t` is the coefficient vector, in
  the variables outside `T`, of the monomial `∏_{k ∈ T} u_k^{t k}`, and `eval_eq_sum_coef` is the
  decomposition `g(u) = ∑_t u^t_T · (coef g T t)(u)`.
-/

noncomputable section

/-! ## Schwartz--Zippel for any finite variable type -/

namespace MIPRE.LowDegree

open Finset MvPolynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {σ : Type*} [Fintype σ] [DecidableEq σ]

end MIPRE.LowDegree

/-! ## Coefficient vectors as polynomials -/

namespace MIPRE.LIDT

open Finset MvPolynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n d : ℕ}

end MIPRE.LIDT

/-! ## Coefficients of a monomial pattern -/

namespace MIPRE.LIDT

open Finset

variable {F : Type*} [Field F] {n d : ℕ}

/-- The exponent vector `e` with its coordinates in `T` replaced by those of the pattern `t`. -/
def patch (T : Finset (Fin n)) (t e : Fin n → Fin (d + 1)) : Fin n → Fin (d + 1) :=
  fun k => if k ∈ T then t k else e k

/-- The part of an exponent vector on `T`. -/
def maskOn (T : Finset (Fin n)) (e : Fin n → Fin (d + 1)) : Fin n → Fin (d + 1) :=
  fun k => if k ∈ T then e k else 0

/-- The part of an exponent vector off `T`. -/
def maskOff (T : Finset (Fin n)) (e : Fin n → Fin (d + 1)) : Fin n → Fin (d + 1) :=
  fun k => if k ∈ T then 0 else e k

/-- **The coefficient of a monomial pattern**: the coefficient vector, in the variables outside
`T`, of the monomial `∏_{k ∈ T} u_k^{t k}` in `g`; zero unless the pattern is supported in `T`. -/
def LowIndDegPoly.coef (g : LowIndDegPoly (F := F) (m := n) (d := d)) (T : Finset (Fin n))
    (t : Fin n → Fin (d + 1)) : LowIndDegPoly (F := F) (m := n) (d := d) :=
  fun e => if (∀ k ∈ T, e k = 0) ∧ (∀ k ∉ T, t k = 0) then g (patch T t e) else 0

end MIPRE.LIDT

end

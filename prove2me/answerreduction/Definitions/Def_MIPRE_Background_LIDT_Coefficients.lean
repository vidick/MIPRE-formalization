/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Coefficients.lean (definition bundle: declarations the uploaded statements rest on);
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

/-- The points of `F^σ` at which two polynomials agree. -/
def agreeOn (f g : MvPolynomial σ F) : Finset (σ → F) := {x ∈ univ | eval x f = eval x g}

@[simp] theorem mem_agreeOn {f g : MvPolynomial σ F} {x : σ → F} :
    x ∈ agreeOn f g ↔ eval x f = eval x g := by
  simp [agreeOn]

end MIPRE.LowDegree

/-! ## Coefficient vectors as polynomials -/

namespace MIPRE.LIDT

open Finset MvPolynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n d : ℕ}

/-- An exponent vector with entries at most `d`, as a finitely supported function. -/
def expFinsupp (e : Fin n → Fin (d + 1)) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => (e i : ℕ)

@[simp] theorem expFinsupp_apply (e : Fin n → Fin (d + 1)) (i : Fin n) :
    expFinsupp e i = (e i : ℕ) := rfl

/-- **The polynomial a coefficient vector denotes.** -/
def LowIndDegPoly.toMv (g : LowIndDegPoly (F := F) (m := n) (d := d)) : MvPolynomial (Fin n) F :=
  ∑ e, monomial (expFinsupp e) (g e)

end MIPRE.LIDT

/-! ## Coefficients of a monomial pattern -/

namespace MIPRE.LIDT

open Finset

variable {F : Type*} [Field F] {n d : ℕ}

end MIPRE.LIDT

end

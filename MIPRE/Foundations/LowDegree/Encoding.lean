/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# The low-degree code

The paper's `sec:ld-encoding`: the multilinear indicator polynomials of the Boolean subcube,
the *low-degree encoding* `g_a` of a vector indexed by the subcube, and the decoding map
`Coded_H`. This is the code the PCP of `thm:pcp-decider` commits to, and the `a = Coded(g₁)`
of its soundness conclusion.

* `ind y = ∏_{i : yᵢ = 1} Xᵢ · ∏_{i : yᵢ = 0} (1 - Xᵢ)` — on the subcube, `1` at `y` and `0`
  elsewhere (`eval_ind`);
* `pt y` is the subcube point of `y : Fin m → Bool`, identifying `{0,1}` with `{0, 1} ⊆ F`;
* `ldEnc a = ∑_y a y · ind y` — the multilinear polynomial with `g_a(y) = a y`
  (`eval_ldEnc`), of individual degree at most `1` (`degreeOf_ldEnc_le`);
* `codedOn H g` reads `g` back off the subcube, replacing a value outside `H` by `0`. It is a
  left inverse of `ldEnc` on `H`-valued vectors (`codedOn_ldEnc`), and `coded = codedOn {0,1}`
  is the Boolean decoding map, which always returns a `{0,1}`-valued vector (`coded_eq`).

Nothing here is about the cost model: these are polynomials, and the verifier's arithmetic on
their bit representations is a separate matter (the admissible field of `lem:self-dual-basis`).
-/

noncomputable section

namespace MIPRE.LowDegree

open Finset MvPolynomial

variable {F : Type*} [CommRing F] {m : ℕ}

/-! ## The subcube -/

/-- `{0,1} ⊆ F` on single bits. -/
def ofBool (b : Bool) : F := if b then 1 else 0

/-- The point of `F^m` corresponding to `y ∈ {0,1}^m`, under `{0,1} ⊆ F`. -/
def pt (y : Fin m → Bool) : Fin m → F := fun i => ofBool (y i)

/-! ## The indicator polynomials -/

/-- `ind y`, the multilinear polynomial that is `1` at the subcube point `y` and `0` at every
other subcube point. -/
def ind (y : Fin m → Bool) : MvPolynomial (Fin m) F :=
  ∏ i, if y i then X i else 1 - X i

theorem eval_ind (y z : Fin m → Bool) :
    eval (pt z) (ind y) = if y = z then (1 : F) else 0 := by
  have key : ∀ i : Fin m, eval (pt z) (if y i then X i else 1 - X i)
      = if y i = z i then (1 : F) else 0 := by
    intro i
    cases hy : y i <;> cases hz : z i <;> simp [pt, ofBool, hz]
  rw [ind, map_prod]
  simp only [key]
  by_cases h : y = z
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (mem_univ i) (by simp [hi])

theorem degreeOf_ind_le [Nontrivial F] (y : Fin m → Bool) (i : Fin m) :
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

/-! ## The encoding -/

/-- The **low-degree encoding** of `a : {0,1}^m → F`: the multilinear polynomial with
`g_a(y) = a y` on the subcube. -/
def ldEnc (a : (Fin m → Bool) → F) : MvPolynomial (Fin m) F :=
  ∑ y : Fin m → Bool, C (a y) * ind y

@[simp] theorem eval_ldEnc (a : (Fin m → Bool) → F) (y : Fin m → Bool) :
    eval (pt y) (ldEnc a) = a y := by
  rw [ldEnc, map_sum]
  simp only [map_mul, eval_C, eval_ind]
  rw [Finset.sum_eq_single y]
  · simp
  · intro z _ hz; simp [if_neg (fun h : z = y => hz h)]
  · intro h; exact absurd (mem_univ y) h

theorem degreeOf_ldEnc_le [Nontrivial F] (a : (Fin m → Bool) → F) (i : Fin m) :
    (ldEnc a).degreeOf i ≤ 1 := by
  rw [ldEnc]
  refine (MvPolynomial.degreeOf_sum_le i univ (fun y => C (a y) * ind y)).trans ?_
  refine Finset.sup_le fun y _ => ?_
  exact (MvPolynomial.degreeOf_mul_le i _ _).trans (by simpa using degreeOf_ind_le (F := F) y i)

theorem totalDegree_ind_le [Nontrivial F] (y : Fin m → Bool) :
    (ind y : MvPolynomial (Fin m) F).totalDegree ≤ m := by
  have hfac : ∀ j : Fin m,
      (if y j then (X j : MvPolynomial (Fin m) F) else 1 - X j).totalDegree ≤ 1 := by
    intro j
    cases hy : y j
    · simp only [Bool.false_eq_true, if_false]
      exact le_trans (MvPolynomial.totalDegree_sub 1 (X j)) (by simp)
    · simp
  rw [ind]
  refine le_trans (MvPolynomial.totalDegree_finsetProd _ _) ?_
  refine le_trans (Finset.sum_le_sum fun j _ => hfac j) ?_
  simp

/-- **The encoding is multilinear, hence of total degree at most `m`.** This is the bound that
makes the restriction of `g_a` to a line a polynomial of degree at most `m`. -/
theorem totalDegree_ldEnc_le [Nontrivial F] (a : (Fin m → Bool) → F) :
    (ldEnc a).totalDegree ≤ m := by
  rw [ldEnc]
  refine MvPolynomial.totalDegree_finsetSum_le fun y _ => ?_
  refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  exact totalDegree_ind_le y

/-! ## The decoding map -/

variable [DecidableEq F]

/-- `Coded_H g`: read `g` off the subcube, replacing any value outside `H` by `0`. -/
def codedOn (H : Finset F) (g : MvPolynomial (Fin m) F) : (Fin m → Bool) → F :=
  fun y => if eval (pt y) g ∈ H then eval (pt y) g else 0

theorem codedOn_ldEnc {H : Finset F} {a : (Fin m → Bool) → F} (ha : ∀ y, a y ∈ H) :
    codedOn H (ldEnc a) = a := by
  funext y; simp [codedOn, ha y]

/-- The Boolean decoding map `Coded = Coded_{0,1}`. -/
def coded (g : MvPolynomial (Fin m) F) : (Fin m → Bool) → F :=
  codedOn {0, 1} g

/-- `Coded g` is always `{0,1}`-valued. -/
theorem coded_eq (g : MvPolynomial (Fin m) F) (y : Fin m → Bool) :
    coded g y = 0 ∨ coded g y = 1 := by
  by_cases h : eval (pt y) g ∈ ({0, 1} : Finset F)
  · have hv : eval (pt y) g = 0 ∨ eval (pt y) g = 1 := by simpa using h
    simpa only [coded, codedOn, if_pos h] using hv
  · exact Or.inl (by simp [coded, codedOn, h])

theorem coded_ldEnc_ofBool (a : (Fin m → Bool) → Bool) :
    coded (ldEnc fun y => (ofBool (a y) : F)) = fun y => ofBool (a y) :=
  codedOn_ldEnc fun y => by cases h : a y <;> simp [ofBool]

end MIPRE.LowDegree

end

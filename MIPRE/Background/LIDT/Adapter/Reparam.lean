/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.LIDT.Game
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# The seeded-CL adapter, part 2: affine reparametrization of a line answer

Both tests answer a line question with a univariate polynomial in *the parameter of the line*,
and they parametrize the same line differently: the base points differ by a multiple of the
direction and the directions differ by a scalar (see
`MIPRE.Background.LIDT.Adapter.Geometry`, and the correction in
`planning/lidt-cl-adapter.md`). So converting an answer means substituting an affine map
`t ↦ a t + b` into the polynomial — the "canonicalization and rebasing" of
`rem:lidt-cl-adapter`.

Answers are coefficient vectors (`LinePoly F k = Fin (k+1) → F`), and the substitution has to
preserve the degree bound exactly, since the bound *is* the answer alphabet: an adapter that
raised the degree would not be producing an answer of the canonical-line test at all.

Doing this directly on coefficient vectors means a Taylor shift, hence the binomial theorem by
hand. Going through `Polynomial F` avoids that entirely: `toPoly` and `ofPoly` are mutually
inverse between coefficient vectors and polynomials of degree at most `k`
(`ofPoly_toPoly`, `toPoly_ofPoly`), `natDegree_comp_le` gives the degree bound for free, and
the inverse substitution is the composition with the inverse affine map, so `reparamEquiv` is a
bijection with no computation on coefficients at all.
-/

namespace MIPRE.LIDT.Adapter

open Finset Polynomial

variable {F : Type*} [Field F] {k : ℕ}

/-! ## Coefficient vectors and polynomials -/

/-- A coefficient vector, as a polynomial. -/
noncomputable def toPoly (f : LinePoly F k) : F[X] :=
  ∑ i, Polynomial.C (f i) * Polynomial.X ^ (i : ℕ)

/-- A polynomial's coefficients, truncated to degree `k`. -/
def ofPoly (p : F[X]) : LinePoly F k := fun i => p.coeff (i : ℕ)

@[simp] theorem ofPoly_apply (p : F[X]) (i : Fin (k + 1)) :
    (ofPoly p : LinePoly F k) i = p.coeff (i : ℕ) := rfl

theorem natDegree_toPoly_le (f : LinePoly F k) : (toPoly f).natDegree ≤ k := by
  refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  calc (Polynomial.C (f i) * Polynomial.X ^ (i : ℕ)).natDegree
      ≤ (i : ℕ) := by
        simpa using natDegree_C_mul_le (f i) (Polynomial.X ^ (i : ℕ))
    _ ≤ k := Nat.lt_succ_iff.mp i.isLt

@[simp] theorem coeff_toPoly (f : LinePoly F k) (i : Fin (k + 1)) :
    (toPoly f).coeff (i : ℕ) = f i := by
  rw [toPoly, finsetSum_coeff]
  rw [Finset.sum_eq_single i (fun j _ hj => ?_) (fun h => absurd (Finset.mem_univ i) h)]
  · simp
  · rw [coeff_C_mul, coeff_X_pow, if_neg (fun hc => hj (Fin.ext hc.symm)), mul_zero]

@[simp] theorem ofPoly_toPoly (f : LinePoly F k) : (ofPoly (toPoly f) : LinePoly F k) = f := by
  funext i
  exact coeff_toPoly f i

/-- Evaluation agrees with `Polynomial.eval`. -/
theorem eval_toPoly (f : LinePoly F k) (t : F) : (toPoly f).eval t = f.eval t := by
  rw [toPoly, eval_finsetSum, LinePoly.eval]
  exact Finset.sum_congr rfl fun i _ => by simp

/-- On polynomials of degree at most `k`, truncation loses nothing. -/
theorem toPoly_ofPoly {p : F[X]} (hp : p.natDegree ≤ k) :
    toPoly (ofPoly p : LinePoly F k) = p := by
  ext j
  by_cases hj : j ≤ k
  · have h := coeff_toPoly (ofPoly p : LinePoly F k) ⟨j, Nat.lt_succ_of_le hj⟩
    simpa using h
  · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp (by omega)),
      coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (natDegree_toPoly_le (ofPoly p : LinePoly F k)) (by omega))]

/-- Evaluating the truncation of a polynomial of degree at most `k`. -/
theorem eval_ofPoly {p : F[X]} (hp : p.natDegree ≤ k) (t : F) :
    (ofPoly p : LinePoly F k).eval t = p.eval t := by
  rw [← eval_toPoly, toPoly_ofPoly hp]

/-! ## The affine substitution -/

/-- The affine map to substitute. -/
noncomputable def affineMap (a b : F) : F[X] := Polynomial.C a * Polynomial.X + Polynomial.C b

theorem natDegree_affineMap_le (a b : F) : (affineMap a b).natDegree ≤ 1 := by
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · simpa using natDegree_C_mul_le a Polynomial.X
  · simp

@[simp] theorem eval_affineMap (a b t : F) : (affineMap a b).eval t = a * t + b := by
  simp [affineMap]

/-- **Affine reparametrization of an answer**: `reparam a b f` is the coefficient vector of
`t ↦ f (a t + b)`, of the same degree bound. -/
noncomputable def reparam (a b : F) (f : LinePoly F k) : LinePoly F k :=
  ofPoly ((toPoly f).comp (affineMap a b))

theorem natDegree_comp_affineMap_le (a b : F) (f : LinePoly F k) :
    ((toPoly f).comp (affineMap a b)).natDegree ≤ k :=
  (natDegree_comp_le).trans (by
    calc (toPoly f).natDegree * (affineMap a b).natDegree
        ≤ (toPoly f).natDegree * 1 :=
          Nat.mul_le_mul_left _ (natDegree_affineMap_le a b)
      _ ≤ k := by rw [mul_one]; exact natDegree_toPoly_le f)

@[simp] theorem eval_reparam (a b : F) (f : LinePoly F k) (t : F) :
    (reparam a b f).eval t = f.eval (a * t + b) := by
  rw [reparam, eval_ofPoly (natDegree_comp_affineMap_le a b f), eval_comp, eval_affineMap,
    eval_toPoly]

/-- The inverse substitution. -/
theorem affineMap_comp_affineMap {a : F} (ha : a ≠ 0) (b : F) :
    (affineMap a b).comp (affineMap a⁻¹ (-(a⁻¹ * b))) = Polynomial.X := by
  simp only [affineMap, add_comp, mul_comp, C_comp, X_comp, mul_add, ← mul_assoc,
    ← Polynomial.C_mul]
  rw [mul_inv_cancel₀ ha, Polynomial.C_1, one_mul,
    show a * -(a⁻¹ * b) = -b from by field_simp, Polynomial.C_neg, add_assoc,
    neg_add_cancel, add_zero]

theorem reparam_reparam {a : F} (ha : a ≠ 0) (b : F) (f : LinePoly F k) :
    reparam a⁻¹ (-(a⁻¹ * b)) (reparam a b f) = f := by
  rw [reparam, reparam, toPoly_ofPoly (natDegree_comp_affineMap_le a b f), comp_assoc,
    affineMap_comp_affineMap ha, comp_X, ofPoly_toPoly]

/-- **Affine reparametrization is a bijection of the answer alphabet.** The degree bound is
preserved in both directions, so an answer of one test becomes an answer of the other with no
change of alphabet. -/
noncomputable def reparamEquiv {a : F} (ha : a ≠ 0) (b : F) :
    LinePoly F k ≃ LinePoly F k where
  toFun := reparam a b
  invFun := reparam a⁻¹ (-(a⁻¹ * b))
  left_inv f := reparam_reparam ha b f
  right_inv f := by
    have h := reparam_reparam (a := a⁻¹) (inv_ne_zero ha) (-(a⁻¹ * b)) f
    rwa [inv_inv, show -(a * -(a⁻¹ * b)) = b by field_simp] at h

end MIPRE.LIDT.Adapter

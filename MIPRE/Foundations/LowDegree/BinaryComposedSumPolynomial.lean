/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryQuotientTranslation
import MIPRE.Foundations.LowDegree.BinaryCoprimeDegree

/-! # Binary composed-sum polynomials as products of Frobenius translates -/

noncomputable section

namespace MIPRE.LowDegree.BinaryQuotient

open Polynomial

variable {R : Type*} [CommRing R] [Algebra (ZMod 2) R]

/-- Translate a binary polynomial by an element of the ambient binary algebra. -/
def translatedPolynomial (g : Polynomial (ZMod 2)) (x : R) : Polynomial R :=
  (g.map (algebraMap (ZMod 2) R)).comp (X + C x)

/-- Product of all specified Frobenius translates of a binary polynomial. -/
def composedSumPolynomial (g : Polynomial (ZMod 2)) (x : R) (n : ℕ) : Polynomial R :=
  (List.ofFn (fun i : Fin n => translatedPolynomial g (x ^ (2 ^ (i : ℕ))))).prod

@[simp] theorem composedSumPolynomial_zero (g : Polynomial (ZMod 2)) (x : R) :
    composedSumPolynomial g x 0 = 1 := rfl

theorem composedSumPolynomial_succ (g : Polynomial (ZMod 2)) (x : R) (n : ℕ) :
    composedSumPolynomial g x (n + 1) = translatedPolynomial g x * composedSumPolynomial g (x ^ 2) n := by
  rw [composedSumPolynomial, List.ofFn_succ, List.prod_cons]
  simp only [Fin.val_zero, pow_zero, pow_one, Fin.val_succ]
  congr 1
  congr 1
  congr 1
  funext i
  rw [pow_succ, Nat.mul_comm (2 ^ (i : ℕ)) 2, pow_mul]

theorem composedSumPolynomial_succ' (g : Polynomial (ZMod 2)) (x : R) (n : ℕ) :
    composedSumPolynomial g x (n + 1) =
      composedSumPolynomial g x n * translatedPolynomial g (x ^ (2 ^ n)) := by
  rw [composedSumPolynomial, List.ofFn_succ', List.prod_concat]
  rfl

/-- Translating a monic polynomial preserves monicity. -/
theorem translatedPolynomial_monic (g : Polynomial (ZMod 2)) (hg : g.Monic) (x : R) :
    (translatedPolynomial g x).Monic := by
  nontriviality R
  exact (hg.map _).comp (monic_X_add_C x) (by simp)

@[simp] theorem natDegree_translatedPolynomial [IsDomain R]
    (g : Polynomial (ZMod 2)) (x : R) : (translatedPolynomial g x).natDegree = g.natDegree := by
  rw [translatedPolynomial, natDegree_comp, natDegree_X_add_C, mul_one, natDegree_map]

/-- The product is monic even when its translates repeat. -/
theorem composedSumPolynomial_monic (g : Polynomial (ZMod 2)) (hg : g.Monic) (x : R) (n : ℕ) :
    (composedSumPolynomial g x n).Monic := by
  induction n generalizing x with
  | zero => exact monic_one
  | succ n ih =>
    rw [composedSumPolynomial_succ]
    exact (translatedPolynomial_monic g hg x).mul (ih _)

@[simp] theorem natDegree_composedSumPolynomial [IsDomain R]
    (g : Polynomial (ZMod 2)) (hg : g.Monic) (x : R) (n : ℕ) :
    (composedSumPolynomial g x n).natDegree = n * g.natDegree := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [composedSumPolynomial_succ,
      (translatedPolynomial_monic g hg x).natDegree_mul (composedSumPolynomial_monic g hg _ _),
      natDegree_translatedPolynomial, ih]
    ring

/-- Coefficient Frobenius commutes with translation of a binary polynomial. -/
theorem map_frobenius_translatedPolynomial [CharP R 2] (g : Polynomial (ZMod 2)) (x : R) :
    (translatedPolynomial g x).map (frobenius R 2) = translatedPolynomial g (x ^ 2) := by
  have hbase : (frobenius R 2).comp (algebraMap (ZMod 2) R) = algebraMap (ZMod 2) R := by
    ext z
    change (algebraMap (ZMod 2) R z) ^ 2 = algebraMap (ZMod 2) R z
    rw [← map_pow]
    have hz : z ^ 2 = z := by simp
    rw [hz]
  rw [translatedPolynomial, Polynomial.map_comp, Polynomial.map_map, hbase,
    Polynomial.map_add, Polynomial.map_X, Polynomial.map_C, frobenius_def]
  rfl

/-- Coefficient Frobenius shifts the translate orbit by one place. -/
theorem map_frobenius_composedSumPolynomial [CharP R 2]
    (g : Polynomial (ZMod 2)) (x : R) (n : ℕ) :
    (composedSumPolynomial g x n).map (frobenius R 2) = composedSumPolynomial g (x ^ 2) n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [composedSumPolynomial_succ, Polynomial.map_mul, map_frobenius_translatedPolynomial,
      ih, composedSumPolynomial_succ]

/-- Closing the translate orbit fixes every product coefficient under Frobenius. -/
theorem map_frobenius_composedSumPolynomial_of_closed [IsDomain R] [CharP R 2]
    (g : Polynomial (ZMod 2)) (hg : g.Monic) (x : R) (n : ℕ) (hx : x ^ (2 ^ n) = x) :
    (composedSumPolynomial g x n).map (frobenius R 2) = composedSumPolynomial g x n := by
  rw [map_frobenius_composedSumPolynomial]
  apply mul_left_cancel₀ (translatedPolynomial_monic g hg x).ne_zero
  rw [← composedSumPolynomial_succ, composedSumPolynomial_succ', hx, mul_comm]

/-- The coefficients of a closed product of binary translates are binary. -/
theorem composedSumPolynomial_coeff_zero_or_one [IsDomain R] [CharP R 2]
    (g : Polynomial (ZMod 2)) (hg : g.Monic) (x : R) (n : ℕ) (hx : x ^ (2 ^ n) = x) (i : ℕ) :
    (composedSumPolynomial g x n).coeff i = 0 ∨ (composedSumPolynomial g x n).coeff i = 1 := by
  have h := congrArg (fun p : Polynomial R => p.coeff i)
    (map_frobenius_composedSumPolynomial_of_closed g hg x n hx)
  rw [coeff_map, frobenius_def] at h
  have hz : (composedSumPolynomial g x n).coeff i * ((composedSumPolynomial g x n).coeff i - 1) = 0 := by
    rw [mul_sub, mul_one, ← pow_two, h, sub_self]
  rcases mul_eq_zero.mp hz with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

/-- A nonempty translate product vanishes at the sum of the translating element and any root. -/
theorem eval_composedSumPolynomial [CharP R 2]
    (g : Polynomial (ZMod 2)) (x y : R) (n : ℕ) (hn : 0 < n) (hy : aeval y g = 0) :
    (composedSumPolynomial g x n).eval (x + y) = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [composedSumPolynomial_succ, eval_mul]
  have h : (translatedPolynomial g x).eval (x + y) = 0 := by
    rw [translatedPolynomial, eval_comp, eval_add, eval_X, eval_C]
    have he : x + y + x = y := by
      rw [add_right_comm, CharTwo.add_self_eq_zero, zero_add]
    rw [he, eval_map, ← aeval_def]
    exact hy
  rw [h, zero_mul]


variable {S : Type*} [CommRing S] [Algebra (ZMod 2) S]

/-- Translation commutes with an algebra embedding of the coefficient field. -/
theorem map_translatedPolynomial (φ : R →ₐ[ZMod 2] S) (g : Polynomial (ZMod 2)) (x : R) :
    (translatedPolynomial g x).map φ.toRingHom = translatedPolynomial g (φ x) := by
  have hbase : φ.toRingHom.comp (algebraMap (ZMod 2) R) = algebraMap (ZMod 2) S := by
    ext z
    exact φ.commutes z
  rw [translatedPolynomial, Polynomial.map_comp, Polynomial.map_map, hbase,
    Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]
  rfl

/-- The composed-sum product commutes with coefficient-field embeddings. -/
theorem map_composedSumPolynomial (φ : R →ₐ[ZMod 2] S) (g : Polynomial (ZMod 2)) (x : R) (n : ℕ) :
    (composedSumPolynomial g x n).map φ.toRingHom = composedSumPolynomial g (φ x) n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [composedSumPolynomial_succ, Polynomial.map_mul, map_translatedPolynomial, ih,
      map_pow, composedSumPolynomial_succ]

end MIPRE.LowDegree.BinaryQuotient

end

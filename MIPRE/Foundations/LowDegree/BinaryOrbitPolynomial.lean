/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryQuotientOrbit

/-! # Algebra of closed binary Frobenius-orbit polynomials -/

noncomputable section

namespace MIPRE.LowDegree.BinaryQuotient

open Polynomial

variable {R : Type*} [CommRing R]

/-- The monic polynomial product over a specified initial Frobenius orbit. -/
def orbitPolynomial (x : R) (n : ℕ) : Polynomial R :=
  (List.ofFn (fun i : Fin n => X + C (x ^ (2 ^ (i : ℕ))))).prod

@[simp] theorem orbitPolynomial_zero (x : R) : orbitPolynomial x 0 = 1 := rfl

/-- Splitting off the first conjugate shifts the remaining orbit by squaring. -/
theorem orbitPolynomial_succ (x : R) (n : ℕ) :
    orbitPolynomial x (n + 1) = (X + C x) * orbitPolynomial (x ^ 2) n := by
  rw [orbitPolynomial, List.ofFn_succ, List.prod_cons]
  simp only [Fin.val_zero, pow_zero, pow_one, Fin.val_succ]
  congr 1
  congr 1
  congr 1
  funext i
  rw [pow_succ, Nat.mul_comm (2 ^ (i : ℕ)) 2, pow_mul]

/-- Splitting off the last conjugate gives the other endpoint of the same product. -/
theorem orbitPolynomial_succ' (x : R) (n : ℕ) :
    orbitPolynomial x (n + 1) = orbitPolynomial x n * (X + C (x ^ (2 ^ n))) := by
  rw [orbitPolynomial, List.ofFn_succ', List.prod_concat]
  rfl

/-- Every orbit polynomial is monic, including the empty orbit. -/
theorem orbitPolynomial_monic (x : R) (n : ℕ) : (orbitPolynomial x n).Monic := by
  induction n generalizing x with
  | zero => exact monic_one
  | succ n ih => rw [orbitPolynomial_succ]; exact (monic_X_add_C x).mul (ih _)

/-- The degree is the specified orbit length even when conjugates repeat. -/
@[simp] theorem natDegree_orbitPolynomial [Nontrivial R] (x : R) (n : ℕ) :
    (orbitPolynomial x n).natDegree = n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [orbitPolynomial_succ, (monic_X_add_C x).natDegree_mul (orbitPolynomial_monic _ _),
      natDegree_X_add_C, ih]
    omega

/-- Applying Frobenius to coefficients shifts the starting element by one conjugate. -/
theorem map_frobenius_orbitPolynomial [CharP R 2] (x : R) (n : ℕ) :
    (orbitPolynomial x n).map (frobenius R 2) = orbitPolynomial (x ^ 2) n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [orbitPolynomial_succ, Polynomial.map_mul, Polynomial.map_add,
      Polynomial.map_X, Polynomial.map_C, frobenius_def, ih, orbitPolynomial_succ]

/-- A closed orbit gives a polynomial fixed by coefficient Frobenius. -/
theorem map_frobenius_orbitPolynomial_of_closed [IsDomain R] [CharP R 2]
    (x : R) (n : ℕ) (hx : x ^ (2 ^ n) = x) :
    (orbitPolynomial x n).map (frobenius R 2) = orbitPolynomial x n := by
  rw [map_frobenius_orbitPolynomial]
  apply mul_left_cancel₀ (monic_X_add_C x).ne_zero
  rw [← orbitPolynomial_succ, orbitPolynomial_succ', hx, mul_comm]

/-- Coefficients of a closed binary orbit polynomial belong to the prime field. -/
theorem orbitPolynomial_coeff_zero_or_one [IsDomain R] [CharP R 2]
    (x : R) (n : ℕ) (hx : x ^ (2 ^ n) = x) (i : ℕ) :
    (orbitPolynomial x n).coeff i = 0 ∨ (orbitPolynomial x n).coeff i = 1 := by
  have h := congrArg (fun p : Polynomial R => p.coeff i)
    (map_frobenius_orbitPolynomial_of_closed x n hx)
  rw [coeff_map, frobenius_def] at h
  have hz : (orbitPolynomial x n).coeff i * ((orbitPolynomial x n).coeff i - 1) = 0 := by
    rw [mul_sub, mul_one, ← pow_two, h, sub_self]
  rcases mul_eq_zero.mp hz with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)


/-- A nonempty binary orbit product vanishes at its starting element. -/
theorem eval_orbitPolynomial [CharP R 2] (x : R) (n : ℕ) (hn : 0 < n) :
    (orbitPolynomial x n).eval x = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [orbitPolynomial_succ, eval_mul, eval_add, eval_X, eval_C,
    CharTwo.add_self_eq_zero, zero_mul]

end MIPRE.LowDegree.BinaryQuotient

end

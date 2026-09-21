/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin

/-!
# Prime-power degree decomposition

This list is used only in the proof of the all-degrees constructor. The
executable constructor computes the same prime-power factors by bounded unary
arithmetic. Indices outside the prime support contribute the neutral factor one.
-/

namespace MIPRE.LowDegree.BinaryDegreeFactors

/-- Prime-power degree factors in ascending base order, including neutral factors. -/
def degreeFactors (n : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin (n + 1) => (i : ℕ) ^ n.factorization (i : ℕ))

/-- The complete bounded list reconstructs every positive input degree. -/
theorem degreeFactors_prod (n : ℕ) (hn : 0 < n) : (degreeFactors n).prod = n := by
  rw [degreeFactors, List.prod_ofFn,
    Fin.prod_univ_eq_prod_range (fun i => i ^ n.factorization i)]
  have hs : n.primeFactors ⊆ Finset.range (n + 1) := by
    intro p hp
    exact Finset.mem_range.mpr (by have := Nat.le_of_mem_primeFactors hp; omega)
  have he : (∏ p ∈ n.primeFactors, p ^ n.factorization p) =
      ∏ p ∈ Finset.range (n + 1), p ^ n.factorization p := by
    apply Finset.prod_subset hs
    intro p _ hp
    have hz : n.factorization p = 0 := Finsupp.notMem_support_iff.mp hp
    simp [hz]
  rw [← he, ← Nat.prod_primeFactors_pow_factorization hn.ne']

/-- Distinct prime indices contribute coprime powers; all other indices contribute one. -/
theorem degreeFactors_pairwise (n : ℕ) : (degreeFactors n).Pairwise Nat.Coprime := by
  rw [degreeFactors, List.pairwise_ofFn]
  intro i j hij
  by_cases hi : (i : ℕ).Prime
  · by_cases hj : (j : ℕ).Prime
    · exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hi hj).mpr
        (by exact ne_of_lt (show (i : ℕ) < (j : ℕ) from hij)))
    · simp [Nat.factorization_eq_zero_of_not_prime n hj]
  · simp [Nat.factorization_eq_zero_of_not_prime n hi]

/-- Every listed factor divides the requested degree. -/
theorem degreeFactors_dvd (n : ℕ) (hn : 0 < n) {d : ℕ} (hd : d ∈ degreeFactors n) : d ∣ n := by
  rw [← degreeFactors_prod n hn]
  exact List.dvd_prod hd

/-- Every listed factor is positive, including neutral factors. -/
theorem degreeFactors_pos (n : ℕ) (hn : 0 < n) {d : ℕ} (hd : d ∈ degreeFactors n) : 0 < d := by
  apply Nat.pos_of_ne_zero
  intro hz
  have h := degreeFactors_dvd n hn hd
  rw [hz, zero_dvd_iff] at h
  omega

/-- The degree cap applies to every listed prime power. -/
theorem degreeFactors_le (n : ℕ) (hn : 0 < n) {d : ℕ} (hd : d ∈ degreeFactors n) : d ≤ n :=
  Nat.le_of_dvd hn (degreeFactors_dvd n hn hd)

/-- Each prefix product remains a divisor of the requested degree. -/
theorem prefix_prod_dvd (n : ℕ) (hn : 0 < n) (pre post : List ℕ)
    (h : degreeFactors n = pre ++ post) : pre.prod ∣ n := by
  rw [← degreeFactors_prod n hn, h, List.prod_append]
  exact dvd_mul_right _ _

end MIPRE.LowDegree.BinaryDegreeFactors
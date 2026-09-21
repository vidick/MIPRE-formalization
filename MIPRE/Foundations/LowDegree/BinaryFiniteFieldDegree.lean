/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.FieldTheory.Finite.Extension

/-! # Finite-field membership and exact degree in power-of-two extensions -/

noncomputable section

namespace MIPRE.LowDegree.BinaryFiniteField

open Polynomial

/-- The fixed points of the base field's cardinality power are exactly that field. -/
theorem mem_range_iff_pow_card {K L : Type*} [Field K] [Field L] [Finite K]
    [Algebra K L] (x : L) :
    x ∈ (algebraMap K L).range ↔ x ^ Nat.card K = x := by
  constructor
  · rintro ⟨y, rfl⟩
    have : Fintype K := Fintype.ofFinite K
    rw [← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  · intro hx
    apply (Polynomial.splits_X_pow_nat_card_sub_X (K := K)).mem_range_of_isRoot
      (FiniteField.X_pow_card_sub_X_ne_zero K (Finite.one_lt_card))
    change eval x ((X ^ Nat.card K - X : K[X]).map (algebraMap K L)) = 0
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, eval_sub,
      eval_pow, eval_X, sub_eq_zero]
    exact hx

/-- In a binary extension of degree `2^(t+1)`, every element outside the
index-two subfield has the full extension degree. -/
theorem minpoly_natDegree_of_not_mem_range {K L : Type*} [Field K] [Field L]
    [Finite K] [Algebra K L] [Algebra (ZMod 2) L] [FiniteDimensional (ZMod 2) L]
    (t : ℕ) (hK : Nat.card K = 2 ^ (2 ^ t))
    (hL : Module.finrank (ZMod 2) L = 2 ^ (t + 1)) (x : L)
    (hx : x ∉ (algebraMap K L).range) :
    (minpoly (ZMod 2) x).natDegree = 2 ^ (t + 1) := by
  have hi : IsIntegral (ZMod 2) x := IsIntegral.of_finite (ZMod 2) x
  have hd : (minpoly (ZMod 2) x).natDegree ∣ 2 ^ (t + 1) := hL ▸ minpoly.degree_dvd hi
  obtain ⟨j, hj, hdeg⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  by_cases heq : j = t + 1
  · simpa [heq] using hdeg
  have hjt : j ≤ t := by omega
  have hd' : (minpoly (ZMod 2) x).natDegree ∣ 2 ^ t := by
    rw [hdeg]
    exact pow_dvd_pow 2 hjt
  have hp := (minpoly.irreducible hi).natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X.mp hd'
  have hpzero : aeval x (X ^ (Nat.card (ZMod 2)) ^ (2 ^ t) - X : (ZMod 2)[X]) = 0 := by
    exact (minpoly.dvd_iff).1 hp
  have hfix : x ^ Nat.card K = x := by
    simpa only [map_sub, map_pow, aeval_X, Nat.card_eq_fintype_card, ZMod.card,
      sub_eq_zero, hK] using hpzero
  exact False.elim (hx ((mem_range_iff_pow_card x).2 hfix))

end MIPRE.LowDegree.BinaryFiniteField

end
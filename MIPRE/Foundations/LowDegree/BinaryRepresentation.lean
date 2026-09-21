/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Cost.Encoding
import MIPRE.Foundations.LowDegree.Encoding
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.ZMod.Basic

/-!
# Binary coefficient representations

The coefficient interpretation used by the public Shoup contract and by the
independent polynomial algorithms. This module does not assume that an
irreducible polynomial has already been constructed.
-/

namespace MIPRE.LowDegree

open Cost

/-- The polynomial over `𝔽₂` whose coefficient of `Tⁱ` is bit `i` of `l`, least significant
first --- the repository's little-endian bit convention (`Cost.bitsVal`, `bitsOfNat`). -/
noncomputable def polyOfBits (l : List Bool) : Polynomial (ZMod 2) :=
  ∑ i ∈ Finset.range l.length, Polynomial.monomial i (if l.getD i false then 1 else 0)

namespace BinaryPolynomial

/-- The polynomial used by Shoup's contract reads the same coefficient bits. -/
theorem coeff_polyOfBits (l : BitStr) (i : ℕ) :
    (polyOfBits l).coeff i = ofBool (l.getD i false) := by
  simp only [polyOfBits, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  by_cases hi : i < l.length
  · simp [hi, ofBool]
  · simp [hi, ofBool, List.getD_eq_getElem?_getD]

theorem polyOfBits_cons (b : Bool) (l : BitStr) :
    polyOfBits (b :: l) = Polynomial.C (ofBool b) + Polynomial.X * polyOfBits l := by
  ext i
  cases i <;> simp [coeff_polyOfBits, Polynomial.coeff_X_mul]

/-- A monic polynomial's leading coefficient is present in its coefficient list. -/
theorem natDegree_lt_length (l : BitStr) (h : (polyOfBits l).Monic) :
    (polyOfBits l).natDegree < l.length := by
  have hc : (polyOfBits l).coeff (polyOfBits l).natDegree = 1 := h.coeff_natDegree
  by_contra hn
  rw [coeff_polyOfBits] at hc
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega :
    l.length ≤ (polyOfBits l).natDegree), ofBool] at hc

/-- Remove trailing zero coefficients and separate the leading monic coefficient. -/
theorem normalize_monic (l : BitStr) (h : (polyOfBits l).Monic) :
    polyOfBits (l.take (polyOfBits l).natDegree ++ [true]) = polyOfBits l := by
  let k := (polyOfBits l).natDegree
  have hk : k < l.length := natDegree_lt_length l h
  have htake : (l.take k).length = k := by simp [min_eq_left (by omega : k ≤ l.length)]
  ext i
  change (polyOfBits (l.take k ++ [true])).coeff i = (polyOfBits l).coeff i
  rw [coeff_polyOfBits]
  by_cases hi : i < k
  · rw [coeff_polyOfBits]
    congr 1
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega), List.getElem?_take_of_lt hi]
  · by_cases heq : i = k
    · subst i
      rw [h.coeff_natDegree]
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by omega), htake, Nat.sub_self]
      rfl
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : (polyOfBits l).natDegree < i)]
      have hlen : (l.take k ++ [true]).length ≤ i := by
        simp only [List.length_append, List.length_singleton]
        omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen, ofBool]

end BinaryPolynomial

end MIPRE.LowDegree

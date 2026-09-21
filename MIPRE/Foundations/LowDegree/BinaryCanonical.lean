/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryDivision
import Mathlib.Algebra.Polynomial.Div

/-! # Canonical binary polynomial degrees and monic division -/

namespace MIPRE.LowDegree.BinaryPolynomial

open Cost Polynomial

/-- The polynomial represented by a coefficient list has degree below its width. -/
theorem degree_polyOfBits_lt_length (a : BitStr) :
    (polyOfBits a).degree < (a.length : WithBot ℕ) := by
  rw [degree_lt_iff_coeff_zero]
  exact fun i hi => coeff_polyOfBits_eq_zero a i hi

/-- Appending a leading one makes the represented monic modulus explicit. -/
theorem polyOfBits_append_true (p : BitStr) :
    polyOfBits (p ++ [true]) = polyOfBits p + X ^ p.length := by
  simp only [polyOfBits_eq_evalBits, evalBits_append, evalBits_cons, evalBits_nil,
    ofBool, if_true, mul_zero, add_zero, mul_one]

/-- Every lower-coefficient vector specifies a monic polynomial. -/
theorem monic_polyOfBits_append_true (p : BitStr) :
    (polyOfBits (p ++ [true])).Monic := by
  rw [polyOfBits_append_true]
  apply (monic_X.pow p.length).add_of_right
  simpa only [degree_X_pow] using degree_polyOfBits_lt_length p

/-- The degree of a supplied monic modulus is exactly its lower-coefficient width. -/
theorem natDegree_polyOfBits_append_true (p : BitStr) :
    (polyOfBits (p ++ [true])).natDegree = p.length := by
  rw [polyOfBits_append_true, natDegree_add_eq_right_of_degree_lt, natDegree_X_pow]
  simpa only [degree_X_pow] using degree_polyOfBits_lt_length p

/-- A list with a true leading bit decomposes into its lower coefficients and that bit. -/
theorem dropLast_append_true (a : BitStr) (h : a.getLastD false = true) :
    a.dropLast ++ [true] = a := by
  have hn : a ≠ [] := by intro he; simp [he] at h
  have hh : a.getLast hn = true := by
    cases a with
    | nil => exact (hn rfl).elim
    | cons b a => simpa only [List.getLast_eq_getLastD, List.getLastD_cons] using h
  simpa only [hh] using List.dropLast_append_getLast hn

/-- A coefficient list with leading bit one represents a monic polynomial. -/
theorem monic_polyOfBits_of_getLast (a : BitStr) (h : a.getLastD false = true) :
    (polyOfBits a).Monic := by
  rw [← dropLast_append_true a h]
  exact monic_polyOfBits_append_true _

/-- For a nonzero canonical representation, width is degree plus one. -/
theorem natDegree_add_one_of_getLast (a : BitStr) (h : a.getLastD false = true) :
    (polyOfBits a).natDegree + 1 = a.length := by
  have hn : a ≠ [] := by intro he; simp [he] at h
  have hl : 0 < a.length := List.length_pos_iff.mpr hn
  have hd := natDegree_polyOfBits_append_true a.dropLast
  rw [dropLast_append_true a h, List.length_dropLast] at hd
  omega

/-- Normalizing produces the empty list exactly when the polynomial is zero. -/
theorem normalizeBits_eq_nil_iff (a : BitStr) :
    normalizeBits a = [] ↔ polyOfBits a = 0 := by
  constructor
  · intro h
    rw [← polyOfBits_normalizeBits a, h]
    simp [polyOfBits]
  · intro h
    rcases normalizeBits_getLast a with hn | hn
    · exact hn
    · have hm := monic_polyOfBits_of_getLast _ hn
      rw [polyOfBits_normalizeBits, h] at hm
      exact (hm.ne_zero rfl).elim

/-- A normalized nonzero input has degree plus one coefficients. -/
theorem length_normalizeBits (a : BitStr) (ha : polyOfBits a ≠ 0) :
    (normalizeBits a).length = (polyOfBits a).natDegree + 1 := by
  rcases normalizeBits_getLast a with hn | hn
  · exact (ha ((normalizeBits_eq_nil_iff a).mp hn)).elim
  · simpa only [polyOfBits_normalizeBits] using (natDegree_add_one_of_getLast _ hn).symm

/-- Over the binary field, every nonzero polynomial represented by bits is monic. -/
theorem monic_polyOfBits (a : BitStr) (ha : polyOfBits a ≠ 0) :
    (polyOfBits a).Monic := by
  rcases normalizeBits_getLast a with hn | hn
  · exact (ha ((normalizeBits_eq_nil_iff a).mp hn)).elim
  · simpa only [polyOfBits_normalizeBits] using monic_polyOfBits_of_getLast _ hn

/-- The executable division agrees with Mathlib's monic quotient and remainder. -/
theorem divModBits_eq_div_modByMonic (p a : BitStr) :
    (polyOfBits (divModBits p a).1, polyOfBits (divModBits p a).2) =
      (polyOfBits a /ₘ polyOfBits (p ++ [true]), polyOfBits a %ₘ polyOfBits (p ++ [true])) := by
  have h := div_modByMonic_unique (polyOfBits (divModBits p a).1)
    (polyOfBits (divModBits p a).2) (monic_polyOfBits_append_true p) (And.intro
      (by simpa only [add_comm] using polyOfBits_divModBits p a)
      (by simpa only [degree_eq_natDegree (monic_polyOfBits_append_true p).ne_zero,
        natDegree_polyOfBits_append_true] using degree_divModBits_remainder_lt p a))
  exact Prod.ext h.1.symm h.2.symm

end MIPRE.LowDegree.BinaryPolynomial

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryFactorization

/-! # Canonical factor outputs and the executable irreducibility test -/

namespace MIPRE.LowDegree.BinaryQuotient

open Cost Polynomial BinaryPolynomial

/-- Every printed factor uses a canonical coefficient representation. -/
theorem factorBitsProg_canonical (p : BitStr) :
    ∀ a ∈ factorBitsProg p, a = [] ∨ a.getLastD false = true := by
  intro a ha
  change a ∈ (quotientComponentsProg p).map
    (fun e => gcdBits (p ++ [true]) (xorBits e (oneBits p))) at ha
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp ha
  exact gcdBits_canonical _ _

/-- Factorization of a canonical full polynomial reconstructs it. -/
theorem factor_dropLast_prod (a : BitStr) (ha : a.getLastD false = true)
    (hp : 0 < (polyOfBits a).natDegree) (hs : Squarefree (polyOfBits a)) :
    ((factorBitsProg a.dropLast).map polyOfBits).prod = polyOfBits a := by
  have hd := natDegree_add_one_of_getLast a ha
  apply factorBitsProg_prod (polyOfBits a) (monic_polyOfBits_of_getLast a ha)
  · simp only [List.length_dropLast]; omega
  · rw [dropLast_append_true a ha]
  · intro he
    have hl := congrArg List.length he
    simp only [List.length_dropLast, List.length_nil] at hl
    omega
  · exact hs

/-- Every factor of a positive-degree squarefree canonical polynomial is irreducible. -/
theorem factor_dropLast_factors (a : BitStr) (ha : a.getLastD false = true)
    (hp : 0 < (polyOfBits a).natDegree) (hs : Squarefree (polyOfBits a)) :
    ∀ b ∈ factorBitsProg a.dropLast,
      b.getLastD false = true ∧ (polyOfBits b).Monic ∧ Irreducible (polyOfBits b) := by
  have hd := natDegree_add_one_of_getLast a ha
  have hf := factorBitsProg_factors (polyOfBits a) (monic_polyOfBits_of_getLast a ha)
    a.dropLast (by simp only [List.length_dropLast]; omega)
    (by rw [dropLast_append_true a ha])
    (by intro he; have hl := congrArg List.length he
        simp only [List.length_dropLast, List.length_nil] at hl; omega) hs
  intro b hb
  have hi := hf b hb
  refine ⟨?_, hi⟩
  rcases factorBitsProg_canonical a.dropLast b hb with h | h
  · subst b
    exact (hi.2.ne_zero (by simp [polyOfBits])).elim
  · exact h

/-- Positive-degree inputs always produce at least one factor. -/
theorem factor_dropLast_ne_nil (a : BitStr) (ha : a.getLastD false = true)
    (hp : 0 < (polyOfBits a).natDegree) (hs : Squarefree (polyOfBits a)) :
    factorBitsProg a.dropLast ≠ [] := by
  intro h
  have he := factor_dropLast_prod a ha hp hs
  rw [h, List.map_nil, List.prod_nil] at he
  rw [← he, natDegree_one] at hp
  omega

/-- The list stopping test is exactly irreducibility on valid factorization inputs. -/
theorem factor_dropLast_tail_isEmpty_iff (a : BitStr) (ha : a.getLastD false = true)
    (hp : 0 < (polyOfBits a).natDegree) (hs : Squarefree (polyOfBits a)) :
    (factorBitsProg a.dropLast).tail.isEmpty = true ↔ Irreducible (polyOfBits a) := by
  have hprod := factor_dropLast_prod a ha hp hs
  have hfac := factor_dropLast_factors a ha hp hs
  have hne := factor_dropLast_ne_nil a ha hp hs
  cases hl : factorBitsProg a.dropLast with
  | nil => exact (hne hl).elim
  | cons b l =>
    rw [hl] at hprod hfac
    cases l with
    | nil =>
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hprod
      simp only [List.tail_cons, List.isEmpty_nil, true_iff]
      rw [← hprod]
      exact (hfac b (by simp)).2.2
    | cons c l =>
      simp only [List.tail_cons, List.isEmpty_cons, Bool.false_eq_true, false_iff]
      intro hi
      have hbi := (hfac b (by simp)).2.2
      have hci := (hfac c (by simp)).2.2
      simp only [List.map_cons, List.prod_cons] at hprod
      have hu := (hi.isUnit_or_isUnit hprod.symm).resolve_left hbi.not_isUnit
      exact hci.not_isUnit (isUnit_of_dvd_unit (dvd_mul_right _ _) hu)

end MIPRE.LowDegree.BinaryQuotient

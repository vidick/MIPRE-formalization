/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryPolynomial

/-!
# Normalizing binary coefficient lists

Remove trailing false coefficients by a right fold. The empty list represents
zero; every nonzero result ends in true. Both semantics and the ambient bound
hold on arbitrary coefficient lists, including redundant trailing zeros.
-/

namespace MIPRE.LowDegree.BinaryPolynomial

open Cost Cost.PolyTimeFun Polynomial

/-- Prepend a coefficient, suppressing zero coefficients above the leading term. -/
def normalizeStep (a : BitStr) (b : Bool) : BitStr :=
  if b then true :: a else if a.isEmpty then [] else false :: a

/-- Canonical coefficient list, with no trailing false coefficients. -/
def normalizeBits (a : BitStr) : BitStr := a.foldr (fun b s => normalizeStep s b) []

@[simp] theorem normalizeBits_nil : normalizeBits [] = [] := rfl

@[simp] theorem normalizeBits_cons (b : Bool) (a : BitStr) :
    normalizeBits (b :: a) = normalizeStep (normalizeBits a) b := rfl

/-- Normalizing cannot increase the coefficient width. -/
theorem length_normalizeStep_le (a : BitStr) (b : Bool) :
    (normalizeStep a b).length ≤ a.length + 1 := by
  cases b <;> simp [normalizeStep]
  split <;> simp

/-- The normalized representation is no longer than its input. -/
theorem length_normalizeBits_le (a : BitStr) : (normalizeBits a).length ≤ a.length := by
  induction a with
  | nil => simp
  | cons b a ih =>
    rw [normalizeBits_cons]
    have hs := length_normalizeStep_le (normalizeBits a) b
    simp only [List.length_cons]
    omega

/-- Suppression of high zero coefficients preserves evaluation in every ring. -/
theorem evalBits_normalizeStep {R : Type*} [CommRing R] (z : R) (a : BitStr) (b : Bool) :
    evalBits z (normalizeStep a b) = ofBool b + z * evalBits z a := by
  cases b <;> cases a <;> simp [normalizeStep, ofBool]

/-- Normalization preserves Horner evaluation. -/
theorem evalBits_normalizeBits {R : Type*} [CommRing R] (z : R) (a : BitStr) :
    evalBits z (normalizeBits a) = evalBits z a := by
  induction a with
  | nil => rfl
  | cons b a ih => rw [normalizeBits_cons, evalBits_normalizeStep, ih, evalBits_cons]

/-- The polynomial interpretation is Horner evaluation at the indeterminate. -/
theorem polyOfBits_eq_evalBits (a : BitStr) :
    polyOfBits a = evalBits (X : Polynomial (ZMod 2)) a := by
  induction a with
  | nil => simp [polyOfBits]
  | cons b a ih =>
    rw [polyOfBits_cons, evalBits_cons, ih]
    cases b <;> simp [ofBool]

/-- Normalization preserves the polynomial itself. -/
theorem polyOfBits_normalizeBits (a : BitStr) :
    polyOfBits (normalizeBits a) = polyOfBits a := by
  simpa only [polyOfBits_eq_evalBits] using evalBits_normalizeBits (X : Polynomial (ZMod 2)) a

/-- A nonempty normalized list has a leading coefficient equal to one. -/
theorem normalizeBits_getLast (a : BitStr) :
    normalizeBits a = [] ∨ (normalizeBits a).getLastD false = true := by
  induction a with
  | nil => exact Or.inl rfl
  | cons b a ih =>
    rcases ih with h | h
    · cases b <;> simp [normalizeBits_cons, normalizeStep, h]
    · have hn : normalizeBits a ≠ [] := by intro he; simp [he] at h
      cases ha : normalizeBits a with
      | nil => exact (hn ha).elim
      | cons c a =>
        cases b <;> simpa [normalizeBits_cons, normalizeStep, ha, List.getLastD_cons] using h

private noncomputable def normalizeStepProg : PolyTimeFun (BitStr × Bool) BitStr :=
  congr (ite snd (cons (const true) fst)
    ((casesList (const []) (cons (const false) fst)).comp (fst.pair fst)))
    (fun p => normalizeStep p.1 p.2) (by rintro ⟨a, b⟩; cases b <;> cases a <;> rfl)

private theorem normalizeStepProg_apply (a : BitStr) (b : Bool) :
    normalizeStepProg (a, b) = normalizeStep a b := by
  cases b <;> cases a <;> rfl

private theorem normalizeStep_esize (a : BitStr) (b : Bool) :
    esize (normalizeStep a b) ≤ esize a + esize b + 1 := by
  cases b <;> cases a <;> simp [normalizeStep, esize_list_cons] <;> omega

private theorem fold_normalizeStep_esize (l : BitStr) (a : BitStr) :
    esize (l.foldl normalizeStep a) ≤ esize a + esize l := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
    have hs := normalizeStep_esize a b
    have hi := ih (normalizeStep a b)
    simp only [List.foldl_cons, esize_list_cons]
    omega

private theorem normalizeStep_bounded : FoldBounded normalizeStepProg X := by
  intro l s pre post h
  change esize (pre.foldl normalizeStep s) ≤ _
  have hp := fold_normalizeStep_esize pre s
  have he := esize_list_append pre post
  simp only [esize_prod, Polynomial.eval_X]
  rw [← h] at he
  omega

/-- One fixed ambient program for canonical polynomial coefficient lists. -/
noncomputable def normalizeBitsProg : PolyTimeFun BitStr BitStr :=
  congr ((foldl normalizeStepProg X normalizeStep_bounded).comp
    (reverse.pair (const []))) normalizeBits (by
      intro a
      change a.reverse.foldl normalizeStep [] = a.foldr (fun b s => normalizeStep s b) []
      rw [List.foldl_reverse])

@[simp] theorem normalizeBitsProg_apply (a : BitStr) :
    normalizeBitsProg a = normalizeBits a := rfl

end MIPRE.LowDegree.BinaryPolynomial

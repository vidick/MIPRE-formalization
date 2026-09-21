/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryCanonical
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Polynomial.Content

/-!
# Deterministic binary polynomial gcd

Euclidean division decreases the canonical divisor width. The original divisor
list supplies the iteration budget, and a zero-divisor state is absorbing.
The same width bound holds for malformed states, so the ambient program has a
global polynomial bound rather than a promise only on well-formed inputs.
-/

namespace MIPRE.LowDegree.BinaryPolynomial

open Cost Cost.PolyTimeFun Polynomial

/-- Two successive remainders in the Euclidean algorithm. -/
abbrev GCDState := BitStr × BitStr

/-- One bounded Euclidean iteration; its second input serves only as fuel. -/
def gcdStep (s : GCDState) (_ : Bool) : GCDState :=
  if s.2.isEmpty then s else (s.2, (divModBits s.2.dropLast s.1).2)

/-- The divisor width decreases on every nonterminal step, even on malformed states. -/
theorem gcdStep_second_length (s : GCDState) (b : Bool) :
    (gcdStep s b).2.length ≤ s.2.length - 1 := by
  by_cases hs : s.2 = []
  · simp [gcdStep, hs]
  · simpa only [gcdStep, List.isEmpty_eq_false_iff.mpr hs, Bool.false_eq_true, if_false,
      List.length_dropLast] using (divModBits_width s.2.dropLast s.1).2

/-- Both state components stay within the original maximum width. -/
theorem gcdStep_width (s : GCDState) (b : Bool) :
    max (gcdStep s b).1.length (gcdStep s b).2.length ≤ max s.1.length s.2.length := by
  unfold gcdStep
  split
  · exact le_rfl
  · have h := (divModBits_width s.2.dropLast s.1).2
    simp only [List.length_dropLast] at h
    exact max_le (le_max_right _ _) (h.trans ((Nat.sub_le _ _).trans (le_max_right _ _)))

/-- An entire bounded loop retains the original width bound. -/
theorem fold_gcdStep_width (l : BitStr) (s : GCDState) :
    max (l.foldl gcdStep s).1.length (l.foldl gcdStep s).2.length ≤
      max s.1.length s.2.length := by
  induction l generalizing s with
  | nil => exact le_rfl
  | cons b l ih => exact (ih (gcdStep s b)).trans (gcdStep_width s b)

/-- Each fuel bit removes one possible remaining divisor coefficient. -/
theorem fold_gcdStep_second_length (l : BitStr) (s : GCDState) :
    (l.foldl gcdStep s).2.length ≤ s.2.length - l.length := by
  induction l generalizing s with
  | nil => simp
  | cons b l ih =>
    have hi := ih (gcdStep s b)
    have hs := gcdStep_second_length s b
    simp only [List.foldl_cons, List.length_cons]
    omega

/-- Binary polynomials are already normalized as elements of the gcd monoid. -/
theorem normalize_polyOfBits (a : BitStr) : normalize (polyOfBits a) = polyOfBits a := by
  by_cases h : polyOfBits a = 0
  · simp [h]
  · exact (monic_polyOfBits a h).normalize_eq_self

/-- Each division step preserves the polynomial gcd and the canonical-divisor invariant. -/
theorem gcdStep_correct (s : GCDState) (b : Bool)
    (hs : s.2 = [] ∨ s.2.getLastD false = true) :
    gcd (polyOfBits (gcdStep s b).1) (polyOfBits (gcdStep s b).2) =
      gcd (polyOfBits s.1) (polyOfBits s.2) ∧
    ((gcdStep s b).2 = [] ∨ (gcdStep s b).2.getLastD false = true) := by
  by_cases hz : s.2 = []
  · simp [gcdStep, hz]
  · have hlead : s.2.getLastD false = true := hs.resolve_left hz
    simp only [gcdStep, List.isEmpty_eq_false_iff.mpr hz, Bool.false_eq_true, if_false]
    refine ⟨?_, ?_⟩
    · have hdiv := polyOfBits_divModBits s.2.dropLast s.1
      rw [dropLast_append_true s.2 hlead] at hdiv
      have hd : polyOfBits s.2 ∣ polyOfBits s.1 - polyOfBits (divModBits s.2.dropLast s.1).2 := by
        refine ⟨polyOfBits (divModBits s.2.dropLast s.1).1, ?_⟩
        rw [← hdiv]
        ring
      rw [← gcd_eq_of_dvd_sub_right hd, gcd_comm]
    · unfold divModBits
      split
      · exact Or.inl rfl
      · exact normalizeBits_getLast _

/-- The complete Euclidean loop preserves the polynomial gcd. -/
theorem fold_gcdStep_correct (l : BitStr) (s : GCDState)
    (hs : s.2 = [] ∨ s.2.getLastD false = true) :
    gcd (polyOfBits (l.foldl gcdStep s).1) (polyOfBits (l.foldl gcdStep s).2) =
      gcd (polyOfBits s.1) (polyOfBits s.2) := by
  induction l generalizing s with
  | nil => rfl
  | cons b l ih =>
    have h := gcdStep_correct s b hs
    exact (ih (gcdStep s b) h.2).trans h.1

/-- The binary Euclidean algorithm uses one iteration per original divisor bit. -/
def gcdBits (a b : BitStr) : BitStr :=
  (b.foldl gcdStep (normalizeBits a, normalizeBits b)).1

/-- The executable algorithm computes Mathlib's normalized polynomial gcd. -/
theorem polyOfBits_gcdBits (a b : BitStr) :
    polyOfBits (gcdBits a b) = gcd (polyOfBits a) (polyOfBits b) := by
  have hlen := fold_gcdStep_second_length b (normalizeBits a, normalizeBits b)
  have hb := length_normalizeBits_le b
  have hz : (b.foldl gcdStep (normalizeBits a, normalizeBits b)).2 = [] := by
    apply List.length_eq_zero_iff.mp
    simp only at hlen
    omega
  have h := fold_gcdStep_correct b (normalizeBits a, normalizeBits b) (normalizeBits_getLast b)
  rw [hz, show polyOfBits [] = 0 by simp [polyOfBits], gcd_zero_right,
    normalize_polyOfBits, polyOfBits_normalizeBits, polyOfBits_normalizeBits] at h
  exact h

/-- Both Euclidean state entries retain a canonical binary representation. -/
theorem fold_gcdStep_canonical (l : BitStr) (s : GCDState)
    (ha : s.1 = [] ∨ s.1.getLastD false = true)
    (hb : s.2 = [] ∨ s.2.getLastD false = true) :
    ((l.foldl gcdStep s).1 = [] ∨ (l.foldl gcdStep s).1.getLastD false = true) ∧
    ((l.foldl gcdStep s).2 = [] ∨ (l.foldl gcdStep s).2.getLastD false = true) := by
  induction l generalizing s with
  | nil => exact ⟨ha, hb⟩
  | cons b l ih =>
    apply ih (gcdStep s b)
    · unfold gcdStep
      split
      · exact ha
      · exact hb
    · exact (gcdStep_correct s b hb).2

/-- The gcd output has no trailing zero coefficient. -/
theorem gcdBits_canonical (a b : BitStr) :
    gcdBits a b = [] ∨ (gcdBits a b).getLastD false = true :=
  (fold_gcdStep_canonical b (normalizeBits a, normalizeBits b)
    (normalizeBits_getLast a) (normalizeBits_getLast b)).1

/-- Output width is bounded by the larger input representation. -/
theorem gcdBits_width (a b : BitStr) : (gcdBits a b).length ≤ max a.length b.length := by
  have h := fold_gcdStep_width b (normalizeBits a, normalizeBits b)
  exact (le_max_left _ _).trans (h.trans (max_le_max
    (length_normalizeBits_le a) (length_normalizeBits_le b)))

private noncomputable def isEmptyProg : PolyTimeFun BitStr Bool :=
  congr ((casesList (const true) (const false)).comp ((const ()).pair (PolyTimeFun.id _)))
    List.isEmpty (by intro a; cases a <;> rfl)

private noncomputable def tailBitsProg : PolyTimeFun BitStr BitStr :=
  congr ((casesList (const []) (snd.comp snd)).comp ((const ()).pair (PolyTimeFun.id _)))
    List.tail (by intro a; cases a <;> rfl)

/-- Remove the implicit leading coefficient before passing a canonical divisor to division. -/
noncomputable def dropLastBitsProg : PolyTimeFun BitStr BitStr :=
  congr (PolyTimeFun.reverse.comp (tailBitsProg.comp PolyTimeFun.reverse)) List.dropLast (by
    intro a
    change a.reverse.tail.reverse = a.dropLast
    rw [List.tail_reverse, List.reverse_reverse])

@[simp] theorem dropLastBitsProg_apply (a : BitStr) : dropLastBitsProg a = a.dropLast := rfl

private noncomputable def gcdStepProg : PolyTimeFun (GCDState × Bool) GCDState :=
  ite (isEmptyProg.comp (snd.comp fst)) fst
    ((snd.comp fst).pair (snd.comp (divModBitsProg.comp
      ((dropLastBitsProg.comp (snd.comp fst)).pair (fst.comp fst)))))

private theorem gcdStepProg_apply (s : GCDState) (b : Bool) :
    gcdStepProg (s, b) = gcdStep s b := rfl

private theorem gcdStep_bounded : FoldBounded gcdStepProg (10 * X + 10) := by
  intro l s pre post _
  change esize (pre.foldl gcdStep s) ≤ _
  have hw := fold_gcdStep_width pre s
  have h1 := esize_bitStr_le (pre.foldl gcdStep s).1
  have h2 := esize_bitStr_le (pre.foldl gcdStep s).2
  have hs1 := length_le_esize_list s.1
  have hs2 := length_le_esize_list s.2
  have hs : esize s = esize s.1 + esize s.2 + 1 := rfl
  change esize (pre.foldl gcdStep s).1 + esize (pre.foldl gcdStep s).2 + 1 ≤ _
  simp only [esize_prod, hs, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_X]
  omega

/-- A fixed deterministic ambient program for binary polynomial gcd. -/
noncomputable def gcdBitsProg : PolyTimeFun (BitStr × BitStr) BitStr :=
  congr (fst.comp ((foldl gcdStepProg (10 * X + 10) gcdStep_bounded).comp
    (snd.pair ((normalizeBitsProg.comp fst).pair (normalizeBitsProg.comp snd)))))
    (fun s => gcdBits s.1 s.2) (by intro s; rfl)

@[simp] theorem gcdBitsProg_apply (a b : BitStr) : gcdBitsProg (a, b) = gcdBits a b := rfl

end MIPRE.LowDegree.BinaryPolynomial

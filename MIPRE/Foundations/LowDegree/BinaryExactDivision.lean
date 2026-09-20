/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryGCD

/-! # Total polynomial quotient on binary coefficient lists -/

namespace MIPRE.LowDegree.BinaryPolynomial

open Cost Cost.PolyTimeFun Polynomial

/-- Polynomial quotient on arbitrary coefficient lists. A zero divisor returns zero;
for a nonzero divisor its canonical leading one is passed implicitly to monic division. -/
def quotientBits (a b : BitStr) : BitStr :=
  if (normalizeBits b).isEmpty then []
  else (divModBits (normalizeBits b).dropLast a).1

/-- The total quotient program agrees with Mathlib polynomial division. -/
theorem polyOfBits_quotientBits (a b : BitStr) :
    polyOfBits (quotientBits a b) = polyOfBits a / polyOfBits b := by
  by_cases hb : polyOfBits b = 0
  · rw [quotientBits, (normalizeBits_eq_nil_iff b).mpr hb]
    rw [hb]
    simp [polyOfBits]
  · have hn : normalizeBits b ≠ [] := mt (normalizeBits_eq_nil_iff b).mp hb
    have hl := (normalizeBits_getLast b).resolve_left hn
    have hd := congrArg Prod.fst (divModBits_eq_div_modByMonic (normalizeBits b).dropLast a)
    simp only [dropLast_append_true _ hl, polyOfBits_normalizeBits] at hd
    rw [quotientBits, List.isEmpty_eq_false_iff.mpr hn]
    simpa only [Bool.false_eq_true, if_false, modByMonic_eq_mod,
      divByMonic_eq_div _ (monic_polyOfBits b hb)] using hd

/-- Exact divisibility reconstructs the dividend, with no search or field enumeration. -/
theorem polyOfBits_quotientBits_mul (a b : BitStr) (hb : polyOfBits b ≠ 0)
    (hdiv : polyOfBits b ∣ polyOfBits a) :
    polyOfBits b * polyOfBits (quotientBits a b) = polyOfBits a := by
  rw [polyOfBits_quotientBits]
  exact EuclideanDomain.mul_div_cancel' hb hdiv

/-- Quotient width never exceeds dividend width, even for malformed inputs. -/
theorem quotientBits_width (a b : BitStr) : (quotientBits a b).length ≤ a.length := by
  unfold quotientBits
  split
  · exact Nat.zero_le _
  · exact (divModBits_width _ _).1

private noncomputable def isEmptyProg : PolyTimeFun BitStr Bool :=
  congr ((casesList (const true) (const false)).comp ((const ()).pair (PolyTimeFun.id _)))
    List.isEmpty (by intro a; cases a <;> rfl)

/-- One uniform ambient program for polynomial quotient, hence for exact division. -/
noncomputable def quotientBitsProg : PolyTimeFun (BitStr × BitStr) BitStr :=
  ite (isEmptyProg.comp (normalizeBitsProg.comp snd)) (const [])
    (fst.comp (divModBitsProg.comp
      ((dropLastBitsProg.comp (normalizeBitsProg.comp snd)).pair fst)))

@[simp] theorem quotientBitsProg_apply (a b : BitStr) :
    quotientBitsProg (a, b) = quotientBits a b := rfl

end MIPRE.LowDegree.BinaryPolynomial

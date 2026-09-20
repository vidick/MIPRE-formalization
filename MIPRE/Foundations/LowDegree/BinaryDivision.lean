/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryNormalize
import MIPRE.Foundations.LowDegree.BinaryConstants

/-!
# Division by binary monic polynomials

The divisor is represented by its lower coefficients `p`; the leading one is
implicit. Horner long division keeps a fixed-width remainder and records each
discarded leading coefficient in the quotient. Division by the constant one
has a separate branch. No irreducibility or field structure is assumed.
-/

namespace MIPRE.LowDegree.BinaryPolynomial

open Cost Cost.PolyTimeFun Polynomial

variable {R : Type*} [CommRing R] [CharP R 2]

/-- The discarded bit records exactly the multiple of the monic modulus
removed by one reduction step, without any assumption that the modulus vanishes. -/
theorem evalBits_shiftReduce_division (z : R) (p a : BitStr)
    (hlen : a.length = p.length) :
    evalBits z (shiftReduce p a) +
      (evalBits z p + z ^ p.length) * ofBool (a.getLastD false) = z * evalBits z a := by
  have h := evalBits_shiftLow z a
  unfold shiftReduce
  cases hb : a.getLastD false
  · rw [hb] at h
    simpa only [Bool.false_eq_true, if_false, ofBool, mul_zero, add_zero] using h
  · rw [hb] at h
    simp only [if_true, ofBool, mul_one]
    rw [evalBits_xor z _ _ ((length_shiftLow a).trans hlen)]
    calc
      evalBits z (shiftLow a) + evalBits z p + (evalBits z p + z ^ p.length) =
          evalBits z (shiftLow a) + z ^ p.length + (evalBits z p + evalBits z p) := by ring
      _ = z * evalBits z a := by
        rw [CharTwo.add_self_eq_zero, add_zero]
        simpa only [hlen, ofBool, if_true, mul_one] using h

/-- Modulus, quotient, and remainder for a Horner division step. -/
abbrev DivisionState := BitStr × BitStr × BitStr

/-- One input coefficient is appended to the Horner computation. -/
def divisionStep (s : DivisionState) (b : Bool) : DivisionState :=
  (s.1, s.2.2.getLastD false :: s.2.1,
    if b then xorBits (shiftReduce s.1 s.2.2) (oneBits s.1)
    else shiftReduce s.1 s.2.2)

/-- Quotient width increases once per input coefficient; remainder width cannot grow. -/
theorem divisionStep_width (s : DivisionState) (b : Bool) :
    (divisionStep s b).1 = s.1 ∧
    (divisionStep s b).2.1.length = s.2.1.length + 1 ∧
    (divisionStep s b).2.2.length ≤ s.2.2.length := by
  refine ⟨rfl, rfl, ?_⟩
  cases b
  · exact length_shiftReduce_le _ _
  · change (xorBits (shiftReduce s.1 s.2.2) (oneBits s.1)).length ≤ _
    rw [length_xorBits]
    exact (min_le_left _ _).trans (length_shiftReduce_le _ _)

/-- The width invariant holds for arbitrary initial states, including malformed ones. -/
theorem fold_divisionStep_width (l : BitStr) (s : DivisionState) :
    (l.foldl divisionStep s).1 = s.1 ∧
    (l.foldl divisionStep s).2.1.length = s.2.1.length + l.length ∧
    (l.foldl divisionStep s).2.2.length ≤ s.2.2.length := by
  induction l generalizing s with
  | nil => simp
  | cons b l ih =>
    obtain ⟨hp, hq, hr⟩ := ih (divisionStep s b)
    obtain ⟨hp', hq', hr'⟩ := divisionStep_width s b
    refine ⟨hp.trans hp', ?_, hr.trans hr'⟩
    simp only [List.foldl_cons, List.length_cons]
    omega

/-- On well-formed states, a division step preserves the fixed remainder width. -/
theorem divisionStep_length (p q r : BitStr) (b : Bool) (hr : r.length = p.length) :
    (divisionStep (p, q, r) b).2.2.length = p.length := by
  cases b <;> simp [divisionStep, length_shiftReduce p r hr]

/-- Unnormalized Horner division result. -/
def divisionFold (p a : BitStr) : DivisionState :=
  a.foldr (fun b s => divisionStep s b) (p, [], zeroBits p)

/-- The right-fold state retains its modulus and its prescribed remainder width. -/
theorem divisionFold_width (p a : BitStr) :
    (divisionFold p a).1 = p ∧
    (divisionFold p a).2.1.length = a.length ∧
    (divisionFold p a).2.2.length = p.length := by
  induction a with
  | nil => simp [divisionFold]
  | cons b a ih =>
    change (divisionStep (divisionFold p a) b).1 = p ∧
      (divisionStep (divisionFold p a) b).2.1.length = (b :: a).length ∧
      (divisionStep (divisionFold p a) b).2.2.length = p.length
    refine ⟨ih.1, ?_, ?_⟩
    · simpa only [divisionStep, List.length_cons] using congrArg (· + 1) ih.2.1
    · exact (divisionStep_length _ _ _ b
        (ih.2.2.trans (congrArg List.length ih.1).symm)).trans (congrArg List.length ih.1)

/-- The division-step invariant is an identity in any characteristic-two ring. -/
theorem evalBits_divisionStep (z : R) (p q r : BitStr) (b : Bool) (hp : p ≠ [])
    (hr : r.length = p.length) :
    (evalBits z p + z ^ p.length) * evalBits z (divisionStep (p, q, r) b).2.1 +
      evalBits z (divisionStep (p, q, r) b).2.2 =
    ofBool b + z * ((evalBits z p + z ^ p.length) * evalBits z q + evalBits z r) := by
  have hs := evalBits_shiftReduce_division z p r hr
  have hl : (shiftReduce p r).length = (oneBits p).length := by
    rw [length_shiftReduce p r hr, length_oneBits]
  have h0 : (ofBool false : R) = 0 := rfl
  have h1 : (ofBool true : R) = 1 := rfl
  cases b <;> simp only [divisionStep, Bool.false_eq_true, if_false, if_true, evalBits_cons,
    h0, h1, zero_add, evalBits_xor z _ _ hl, evalBits_oneBits z p hp]
  · calc
      _ = z * ((evalBits z p + z ^ p.length) * evalBits z q) +
          (evalBits z (shiftReduce p r) +
            (evalBits z p + z ^ p.length) * ofBool (r.getLastD false)) := by ring
      _ = _ := by rw [hs]; ring
  · calc
      _ = 1 + z * ((evalBits z p + z ^ p.length) * evalBits z q) +
          (evalBits z (shiftReduce p r) +
            (evalBits z p + z ^ p.length) * ofBool (r.getLastD false)) := by ring
      _ = _ := by rw [hs]; ring

/-- Horner long division reconstructs the dividend. -/
theorem evalBits_divisionFold (z : R) (p a : BitStr) (hp : p ≠ []) :
    (evalBits z p + z ^ p.length) * evalBits z (divisionFold p a).2.1 +
      evalBits z (divisionFold p a).2.2 = evalBits z a := by
  induction a with
  | nil => simp [divisionFold]
  | cons b a ih =>
    have hw := divisionFold_width p a
    change (evalBits z p + z ^ p.length) *
      evalBits z (divisionStep (divisionFold p a) b).2.1 +
      evalBits z (divisionStep (divisionFold p a) b).2.2 = _
    have hs := evalBits_divisionStep z (divisionFold p a).1 (divisionFold p a).2.1
      (divisionFold p a).2.2 b (by simpa only [hw.1] using hp)
      (hw.2.2.trans (congrArg List.length hw.1).symm)
    change (evalBits z (divisionFold p a).1 + z ^ (divisionFold p a).1.length) *
      evalBits z (divisionStep (divisionFold p a) b).2.1 +
      evalBits z (divisionStep (divisionFold p a) b).2.2 = _ at hs
    rw [hw.1, ih] at hs
    exact hs

/-- Quotient and remainder by the monic polynomial `polyOfBits (p ++ [true])`.
The degree-zero case divides by one; all outputs are normalized. -/
def divModBits (p a : BitStr) : BitStr × BitStr :=
  if p.isEmpty then (normalizeBits a, [])
  else (normalizeBits (divisionFold p a).2.1, normalizeBits (divisionFold p a).2.2)

/-- Output widths are bounded by the input and divisor widths. -/
theorem divModBits_width (p a : BitStr) :
    (divModBits p a).1.length ≤ a.length ∧ (divModBits p a).2.length ≤ p.length := by
  unfold divModBits
  split
  · exact ⟨length_normalizeBits_le a, Nat.zero_le _⟩
  · have hw := divisionFold_width p a
    exact ⟨(length_normalizeBits_le _).trans hw.2.1.le,
      (length_normalizeBits_le _).trans hw.2.2.le⟩

/-- Monic division is correct as a polynomial identity, including division by one. -/
theorem polyOfBits_divModBits (p a : BitStr) :
    polyOfBits (p ++ [true]) * polyOfBits (divModBits p a).1 +
      polyOfBits (divModBits p a).2 = polyOfBits a := by
  by_cases hp : p = []
  · subst p
    change polyOfBits [true] * polyOfBits (normalizeBits a) + polyOfBits [] = _
    rw [polyOfBits_normalizeBits]
    simp [polyOfBits]
  · simp only [divModBits, List.isEmpty_eq_false_iff.mpr hp, Bool.false_eq_true, if_false]
    rw [polyOfBits_normalizeBits, polyOfBits_normalizeBits]
    simpa only [polyOfBits_eq_evalBits, evalBits_append, evalBits_cons, evalBits_nil,
      ofBool, if_true, mul_zero, add_zero, mul_one] using
      evalBits_divisionFold (X : Polynomial (ZMod 2)) p a hp

/-- Coefficients past a representation's width vanish. -/
theorem coeff_polyOfBits_eq_zero (a : BitStr) (i : ℕ) (hi : a.length ≤ i) :
    (polyOfBits a).coeff i = 0 := by
  simp [coeff_polyOfBits, List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, ofBool]

/-- The remainder has degree strictly smaller than the monic divisor. -/
theorem degree_divModBits_remainder_lt (p a : BitStr) :
    (polyOfBits (divModBits p a).2).degree < (p.length : WithBot ℕ) := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro i hi
  exact coeff_polyOfBits_eq_zero _ _ ((divModBits_width p a).2.trans hi)

private noncomputable def headBitProg : PolyTimeFun BitStr Bool :=
  congr ((casesList (const false) (fst.comp snd)).comp
    ((const ()).pair (PolyTimeFun.id _)))
    (fun a => a.headD false) (by intro a; cases a <;> rfl)

private noncomputable def lastBitProg : PolyTimeFun BitStr Bool :=
  congr (headBitProg.comp PolyTimeFun.reverse)
    (fun a => a.getLastD false) (by
      intro a
      change a.reverse.headD false = a.getLastD false
      simp only [List.headD_eq_head?_getD, List.head?_reverse, List.getLastD_eq_getLast?])

private noncomputable def divisionStepProg : PolyTimeFun (DivisionState × Bool) DivisionState :=
  let p := fst.comp fst
  let q := fst.comp (snd.comp fst)
  let r := snd.comp (snd.comp fst)
  p.pair ((cons (lastBitProg.comp r) q).pair
    (ite snd (xorBitsProg.comp ((shiftReduceProg.comp (p.pair r)).pair (oneBitsProg.comp p)))
      (shiftReduceProg.comp (p.pair r))))

private theorem divisionStepProg_apply (s : DivisionState) (b : Bool) :
    divisionStepProg (s, b) = divisionStep s b := rfl

private theorem divisionStep_bounded : FoldBounded divisionStepProg (12 * X + 12) := by
  intro l s pre post h
  change esize (pre.foldl divisionStep s) ≤ _
  obtain ⟨hp, hq, hr⟩ := fold_divisionStep_width pre s
  have hqsize := esize_bitStr_le (pre.foldl divisionStep s).2.1
  have hrsize := esize_bitStr_le (pre.foldl divisionStep s).2.2
  have hqin := length_le_esize_list s.2.1
  have hrin := length_le_esize_list s.2.2
  have hpre : pre.length ≤ l.length := by rw [h, List.length_append]; omega
  have hlin := length_le_esize_list l
  have hs : esize s = esize s.1 + (esize s.2.1 + esize s.2.2 + 1) + 1 := rfl
  change esize (pre.foldl divisionStep s).1 +
    (esize (pre.foldl divisionStep s).2.1 + esize (pre.foldl divisionStep s).2.2 + 1) + 1 ≤ _
  rw [hp]
  simp only [esize_prod, hs, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X]
  omega

/-- Ambient Horner long division, with one iteration per dividend coefficient. -/
noncomputable def divisionFoldProg : PolyTimeFun (BitStr × BitStr) DivisionState :=
  congr ((foldl divisionStepProg (12 * X + 12) divisionStep_bounded).comp
    ((PolyTimeFun.reverse.comp snd).pair (fst.pair ((const []).pair (zeroBitsProg.comp fst)))))
    (fun s => divisionFold s.1 s.2) (by
      intro s
      change s.2.reverse.foldl divisionStep (s.1, [], zeroBits s.1) = _
      rw [List.foldl_reverse]
      rfl)

@[simp] theorem divisionFoldProg_apply (p a : BitStr) :
    divisionFoldProg (p, a) = divisionFold p a := rfl

private noncomputable def isEmptyBitsProg : PolyTimeFun BitStr Bool :=
  congr ((casesList (const true) (const false)).comp ((const ()).pair (PolyTimeFun.id _)))
    List.isEmpty (by intro a; cases a <;> rfl)

/-- Uniform deterministic polynomial-time division by any binary monic polynomial. -/
noncomputable def divModBitsProg : PolyTimeFun (BitStr × BitStr) (BitStr × BitStr) :=
  congr (ite (isEmptyBitsProg.comp fst) ((normalizeBitsProg.comp snd).pair (const []))
    (((normalizeBitsProg.comp (fst.comp snd)).pair (normalizeBitsProg.comp (snd.comp snd))).comp
      divisionFoldProg))
    (fun s => divModBits s.1 s.2) (by intro s; rfl)

@[simp] theorem divModBitsProg_apply (p a : BitStr) :
    divModBitsProg (p, a) = divModBits p a := rfl

end MIPRE.LowDegree.BinaryPolynomial

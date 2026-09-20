/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Cost.Numeric
import MIPRE.Foundations.LowDegree.BinaryConstants

/-!
# Binary exponentiation in a polynomial-basis field

The exponent remains a little-endian bit string. The loop performs one squaring
and at most one multiplication per bit and keeps fixed-width coefficient vectors.
Its polynomial bound also holds for malformed inputs.
-/

namespace MIPRE.LowDegree.BinaryPolynomial

open Cost Cost.PolyTimeFun Polynomial

abbrev PowerState := BitStr × BitStr × BitStr

def powerStep (s : PowerState) (b : Bool) : PowerState :=
  (s.1, mulReduce s.1 s.2.1 s.2.1,
    if b then mulReduce s.1 s.2.2 s.2.1 else s.2.2)

theorem powerStep_width (s : PowerState) (b : Bool) :
    (powerStep s b).1 = s.1 ∧
    (powerStep s b).2.1.length ≤ s.2.1.length ∧
    (powerStep s b).2.2.length ≤ s.2.2.length := by
  refine ⟨rfl, length_mulReduce_le _ _ _, ?_⟩
  cases b
  · exact le_rfl
  · exact length_mulReduce_le _ _ _

theorem fold_powerStep_width (l : BitStr) (s : PowerState) :
    (l.foldl powerStep s).1 = s.1 ∧
    (l.foldl powerStep s).2.1.length ≤ s.2.1.length ∧
    (l.foldl powerStep s).2.2.length ≤ s.2.2.length := by
  induction l generalizing s with
  | nil => exact ⟨rfl, le_rfl, le_rfl⟩
  | cons b l ih =>
    obtain ⟨hp, ha, hc⟩ := ih (powerStep s b)
    obtain ⟨_, ha', hc'⟩ := powerStep_width s b
    exact ⟨hp, ha.trans ha', hc.trans hc'⟩

theorem fold_powerStep_length (l : BitStr) (p a c : BitStr)
    (ha : a.length = p.length) (hc : c.length = p.length) :
    (l.foldl powerStep (p, a, c)).2.2.length = p.length := by
  induction l generalizing a c with
  | nil => exact hc
  | cons b l ih =>
    change (l.foldl powerStep
      (p, mulReduce p a a, if b then mulReduce p c a else c)).2.2.length = _
    apply ih _ _ (length_mulReduce _ _ _ ha)
    cases b
    · exact hc
    · exact length_mulReduce _ _ _ hc

/-- Repeated squaring with a binary exponent. -/
def powerBits (p a e : BitStr) : BitStr :=
  (e.foldl powerStep (p, a, oneBits p)).2.2

theorem length_powerBits (p a e : BitStr) (ha : a.length = p.length) :
    (powerBits p a e).length = p.length :=
  fold_powerStep_length e p a (oneBits p) ha (length_oneBits p)

variable {R : Type*} [CommRing R] [CharP R 2]

theorem evalBits_fold_powerStep (z : R) (p a c e : BitStr)
    (hroot : z ^ p.length = evalBits z p)
    (ha : a.length = p.length) (hc : c.length = p.length) :
    evalBits z (e.foldl powerStep (p, a, c)).2.2 =
      evalBits z c * evalBits z a ^ bitsVal e := by
  induction e generalizing a c with
  | nil => simp [bitsVal]
  | cons b e ih =>
    change evalBits z (e.foldl powerStep
      (p, mulReduce p a a, if b then mulReduce p c a else c)).2.2 = _
    cases b
    · simp only [Bool.false_eq_true, if_false]
      rw [ih _ _ (length_mulReduce _ _ _ ha) hc, evalBits_mulReduce z p a a ha hroot]
      simp [bitsVal_cons, Nat.bit, pow_mul, pow_two]
    · simp only [if_true]
      rw [ih _ _ (length_mulReduce _ _ _ ha) (length_mulReduce _ _ _ hc),
        evalBits_mulReduce z p a a ha hroot, evalBits_mulReduce z p c a hc hroot]
      simp only [bitsVal_cons, Nat.bit, Bool.cond_true]
      rw [pow_add, pow_one, pow_mul]
      ring

/-- Correctness for every characteristic-two ring containing a root of the modulus. -/
theorem evalBits_powerBits (z : R) (p a e : BitStr) (hp : p ≠ [])
    (hroot : z ^ p.length = evalBits z p) (ha : a.length = p.length) :
    evalBits z (powerBits p a e) = evalBits z a ^ bitsVal e := by
  rw [powerBits, evalBits_fold_powerStep z p a _ e hroot ha (length_oneBits p),
    evalBits_oneBits z p hp, one_mul]

private noncomputable def powerStepProg : PolyTimeFun (PowerState × Bool) PowerState :=
  let p := fst.comp fst
  let a := fst.comp (snd.comp fst)
  let c := snd.comp (snd.comp fst)
  p.pair ((mulReduceProg.comp (p.pair (a.pair a))).pair
    (ite snd (mulReduceProg.comp (p.pair (c.pair a))) c))

private theorem powerStepProg_apply (s : PowerState) (b : Bool) :
    powerStepProg (s, b) = powerStep s b := rfl

private theorem powerStep_bounded : FoldBounded powerStepProg (9 * X + 9) := by
  intro l s pre post _
  change esize (pre.foldl powerStep s) ≤ _
  obtain ⟨hp, ha, hc⟩ := fold_powerStep_width pre s
  have ha0 := length_le_esize_list s.2.1
  have hc0 := length_le_esize_list s.2.2
  have hsa := esize_bitStr_le (pre.foldl powerStep s).2.1
  have hsc := esize_bitStr_le (pre.foldl powerStep s).2.2
  have hs : esize s = esize s.1 + (esize s.2.1 + esize s.2.2 + 1) + 1 := rfl
  rw [esize_prod, esize_prod, hp]
  grw [hsa, hsc, ha, hc, ha0, hc0]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, esize_prod]
  omega

/-- One uniform ambient program for exponentiation with binary exponent input. -/
noncomputable def powerBitsProg : PolyTimeFun (BitStr × BitStr × BitStr) BitStr :=
  congr ((snd.comp snd).comp
    ((foldl powerStepProg (9 * X + 9) powerStep_bounded).comp
      ((snd.comp snd).pair
        (fst.pair ((fst.comp snd).pair (oneBitsProg.comp fst))))))
    (fun a => powerBits a.1 a.2.1 a.2.2) (by intro a; rfl)

@[simp] theorem powerBitsProg_apply (p a e : BitStr) :
    powerBitsProg (p, a, e) = powerBits p a e := rfl

end MIPRE.LowDegree.BinaryPolynomial

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryPolynomial

/-! # Uniform sums and products of coefficient vectors -/

namespace MIPRE.LowDegree.BinaryPolynomial

open Cost Cost.PolyTimeFun Polynomial

def arithmeticStep (mul : Bool) (s : BitStr × BitStr) (b : BitStr) : BitStr × BitStr :=
  (s.1, if mul then mulReduce s.1 s.2 b else xorBits s.2 b)

theorem arithmeticStep_width (mul : Bool) (s : BitStr × BitStr) (b : BitStr) :
    (arithmeticStep mul s b).2.length ≤ s.2.length := by
  cases mul
  · change (xorBits s.2 b).length ≤ s.2.length
    rw [length_xorBits]
    exact min_le_left _ _
  · exact length_mulReduce_le _ _ _

theorem fold_arithmeticStep (mul : Bool) (l : List BitStr) (s : BitStr × BitStr) :
    (l.foldl (arithmeticStep mul) s).1 = s.1 ∧
      (l.foldl (arithmeticStep mul) s).2.length ≤ s.2.length := by
  induction l generalizing s with
  | nil => exact ⟨rfl, le_rfl⟩
  | cons b l ih =>
    obtain ⟨hp, hl⟩ := ih (arithmeticStep mul s b)
    exact ⟨hp, hl.trans (arithmeticStep_width mul s b)⟩

/-- Sum or product, starting from a supplied coefficient vector. -/
def arithmeticFold (mul : Bool) (p a : BitStr) (l : List BitStr) : BitStr :=
  (l.foldl (arithmeticStep mul) (p, a)).2

theorem arithmeticFold_cons (mul : Bool) (p a b : BitStr) (l : List BitStr) :
    arithmeticFold mul p a (b :: l) =
      arithmeticFold mul p (if mul then mulReduce p a b else xorBits a b) l := rfl

theorem arithmeticFold_mul_width (p a : BitStr) (l : List BitStr) (ha : a.length = p.length) :
    (arithmeticFold true p a l).length = p.length := by
  induction l generalizing a with
  | nil => exact ha
  | cons b l ih => exact ih _ (length_mulReduce _ _ _ ha)

theorem arithmeticFold_add_width (p a : BitStr) (l : List BitStr) (ha : a.length = p.length)
    (hl : ∀ b ∈ l, b.length = p.length) :
    (arithmeticFold false p a l).length = p.length := by
  induction l generalizing a with
  | nil => exact ha
  | cons b l ih =>
    apply ih _ (by simp only [Bool.false_eq_true, if_false, length_xorBits, ha, hl b (by simp), min_self])
    exact fun c hc => hl c (by simp [hc])

variable {R : Type*} [CommRing R] [CharP R 2]

/-- A modular product fold computes the product of all decoded operands. -/
theorem evalBits_arithmeticFold_mul (z : R) (p a : BitStr) (l : List BitStr)
    (ha : a.length = p.length) (hroot : z ^ p.length = evalBits z p) :
    evalBits z (arithmeticFold true p a l) = evalBits z a * (l.map (evalBits z)).prod := by
  induction l generalizing a with
  | nil => simp [arithmeticFold]
  | cons b l ih =>
    rw [arithmeticFold_cons]
    simp only [if_true]
    rw [ih _ (length_mulReduce _ _ _ ha), evalBits_mulReduce z p _ _ ha hroot]
    simp only [List.map_cons, List.prod_cons, mul_assoc]

/-- A fixed-width XOR fold computes the sum of all decoded operands. -/
theorem evalBits_arithmeticFold_add (z : R) (p a : BitStr) (l : List BitStr)
    (ha : a.length = p.length) (hl : ∀ b ∈ l, b.length = p.length) :
    evalBits z (arithmeticFold false p a l) = evalBits z a + (l.map (evalBits z)).sum := by
  induction l generalizing a with
  | nil => simp [arithmeticFold]
  | cons b l ih =>
    have hb := hl b (by simp)
    rw [arithmeticFold_cons]
    simp only [Bool.false_eq_true, if_false]
    rw [ih _ (by simp only [length_xorBits, ha, hb, min_self])
      (fun c hc => hl c (by simp [hc])), evalBits_xor z a b (ha.trans hb.symm)]
    simp only [List.map_cons, List.sum_cons, add_assoc]

private noncomputable def arithmeticStepProg (mul : Bool) :
    PolyTimeFun ((BitStr × BitStr) × BitStr) (BitStr × BitStr) :=
  (fst.comp fst).pair (ite (const mul)
    (mulReduceProg.comp ((fst.comp fst).pair ((snd.comp fst).pair snd)))
    (xorBitsProg.comp ((snd.comp fst).pair snd)))

private theorem arithmeticStepProg_apply (mul : Bool) (s : BitStr × BitStr) (b : BitStr) :
    arithmeticStepProg mul (s, b) = arithmeticStep mul s b := rfl

private theorem arithmeticStep_bounded (mul : Bool) :
    FoldBounded (arithmeticStepProg mul) (5 * X + 5) := by
  intro l s pre post _
  change esize (pre.foldl (arithmeticStep mul) s) ≤ _
  obtain ⟨hp, hw⟩ := fold_arithmeticStep mul pre s
  have hs : esize s = esize s.1 + esize s.2 + 1 := rfl
  have hi := length_le_esize_list s.2
  have ho := esize_bitStr_le (pre.foldl (arithmeticStep mul) s).2
  rw [esize_prod, hp]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, esize_prod]
  omega

/-- Globally polynomial-time summation or multiplication of coefficient vectors.
The modulus and initial accumulator are explicit inputs. -/
noncomputable def arithmeticFoldProg (mul : Bool) :
    PolyTimeFun (BitStr × BitStr × List BitStr) BitStr :=
  congr (snd.comp
    ((foldl (arithmeticStepProg mul) (5 * X + 5) (arithmeticStep_bounded mul)).comp
      ((snd.comp snd).pair (fst.pair (fst.comp snd)))))
    (fun p => arithmeticFold mul p.1 p.2.1 p.2.2) (by intro p; rfl)

@[simp] theorem arithmeticFoldProg_apply (mul : Bool) (p a : BitStr) (l : List BitStr) :
    arithmeticFoldProg mul (p, a, l) = arithmeticFold mul p a l := rfl

end MIPRE.LowDegree.BinaryPolynomial

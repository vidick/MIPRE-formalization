/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Cost.Fold
import MIPRE.Foundations.LowDegree.BinaryRepresentation
import Mathlib.Algebra.CharP.Two

/-!
# Binary polynomial arithmetic on coefficient lists

Coefficient lists are little-endian. XOR implements addition, and multiplication
by the indeterminate is reduced using the lower coefficients of a monic modulus.
The semantic lemmas work in every characteristic-two commutative ring containing
a root of that modulus; the programs are uniform in the coefficient lists.
-/

namespace MIPRE.LowDegree.BinaryPolynomial

open Cost

variable {R : Type*} [CommRing R]

/-- Evaluate a little-endian binary coefficient list by Horner's rule. -/
def evalBits (z : R) : BitStr → R
  | [] => 0
  | b :: l => ofBool b + z * evalBits z l

@[simp] theorem evalBits_nil (z : R) : evalBits z [] = 0 := rfl

@[simp] theorem evalBits_cons (z : R) (b : Bool) (l : BitStr) :
    evalBits z (b :: l) = ofBool b + z * evalBits z l := rfl

/-- Horner semantics agrees with evaluation of the coefficient polynomial. -/
theorem eval₂_polyOfBits (f : ZMod 2 →+* R) (z : R) (l : BitStr) :
    (polyOfBits l).eval₂ f z = evalBits z l := by
  induction l with
  | nil => simp [polyOfBits]
  | cons b l ih =>
    rw [polyOfBits_cons]
    cases b <;> simp [Polynomial.eval₂_add, Polynomial.eval₂_mul, ih, ofBool]

theorem evalBits_append (z : R) (a b : BitStr) :
    evalBits z (a ++ b) = evalBits z a + z ^ a.length * evalBits z b := by
  induction a with
  | nil => simp
  | cons x a ih => simp only [List.cons_append, evalBits_cons, ih, List.length_cons, pow_succ]; ring

@[simp] theorem evalBits_zero (z : R) (n : ℕ) :
    evalBits z (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ofBool, ih]

/-- Fixed-width XOR, used only with equal-width operands in correctness lemmas. -/
def xorBits (a b : BitStr) : BitStr := List.zipWith Bool.xor a b

@[simp] theorem length_xorBits (a b : BitStr) :
    (xorBits a b).length = min a.length b.length := by simp [xorBits]

theorem evalBits_xor [CharP R 2] (z : R) (a b : BitStr) (hlen : a.length = b.length) :
    evalBits z (xorBits a b) = evalBits z a + evalBits z b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [xorBits]
  | cons x a ih =>
    cases b with
    | nil => simp at hlen
    | cons y b =>
      have hb : (ofBool (Bool.xor x y) : R) = ofBool x + ofBool y := by
        cases x <;> cases y <;> simp [ofBool, CharTwo.add_self_eq_zero]
      simp only [xorBits, List.zipWith_cons_cons, evalBits_cons, hb]
      have ht := ih b (by simpa using hlen)
      change evalBits z (List.zipWith Bool.xor a b) = _ at ht
      rw [ht]
      ring

/-- Shift by one coefficient and discard the new highest coefficient. -/
def shiftLow (a : BitStr) : BitStr := (false :: a).dropLast

/-- Multiply by the indeterminate modulo `X^k + p`, with `p` represented by
exactly `k` lower coefficients. -/
def shiftReduce (p a : BitStr) : BitStr :=
  if a.getLastD false then xorBits (shiftLow a) p else shiftLow a

@[simp] theorem length_shiftLow (a : BitStr) : (shiftLow a).length = a.length := by
  simp [shiftLow]

theorem length_shiftReduce_le (p a : BitStr) : (shiftReduce p a).length ≤ a.length := by
  unfold shiftReduce
  split <;> simp

theorem length_shiftReduce (p a : BitStr) (h : a.length = p.length) :
    (shiftReduce p a).length = p.length := by
  unfold shiftReduce
  split <;> simp [h]

theorem evalBits_shiftLow (z : R) (a : BitStr) :
    evalBits z (shiftLow a) + z ^ a.length * ofBool (a.getLastD false) =
      z * evalBits z a := by
  have h : shiftLow a ++ [a.getLastD false] = false :: a := by
    simpa only [shiftLow, List.getLast_eq_getLastD] using
      List.dropLast_append_getLast (List.cons_ne_nil false a)
  have he := congrArg (evalBits z) h
  simpa [evalBits_append, ofBool] using he

/-- Reduction is correct whenever the chosen element satisfies the monic modulus. -/
theorem evalBits_shiftReduce [CharP R 2] (z : R) (p a : BitStr)
    (hlen : a.length = p.length) (hroot : z ^ p.length = evalBits z p) :
    evalBits z (shiftReduce p a) = z * evalBits z a := by
  have h := evalBits_shiftLow z a
  unfold shiftReduce
  split <;> rename_i hb
  · rw [evalBits_xor z _ _ (by simp [hlen])]
    rw [hb] at h
    simpa [ofBool, hlen, hroot] using h
  · have hb' : a.getLastD false = false := Bool.eq_false_iff.mpr hb
    rw [hb'] at h
    simpa [ofBool] using h

/-- Horner multiplication, reducing after every shift. -/
def mulReduce (p a b : BitStr) : BitStr :=
  b.foldr (fun bit acc =>
    if bit then xorBits (shiftReduce p acc) a else shiftReduce p acc)
    (List.replicate a.length false)

/-- Even malformed moduli and operands cannot increase the accumulator width. -/
theorem length_mulReduce_le (p a b : BitStr) : (mulReduce p a b).length ≤ a.length := by
  induction b with
  | nil => simp [mulReduce]
  | cons bit b ih =>
    change (if bit then xorBits (shiftReduce p (mulReduce p a b)) a
      else shiftReduce p (mulReduce p a b)).length ≤ _
    split
    · rw [length_xorBits]
      exact (min_le_left _ _).trans ((length_shiftReduce_le _ _).trans ih)
    · exact (length_shiftReduce_le _ _).trans ih

theorem length_mulReduce (p a b : BitStr) (h : a.length = p.length) :
    (mulReduce p a b).length = p.length := by
  induction b with
  | nil => simp [mulReduce, h]
  | cons bit b ih =>
    change (if bit then xorBits (shiftReduce p (mulReduce p a b)) a
      else shiftReduce p (mulReduce p a b)).length = _
    split <;> simp [length_shiftReduce p _ ih, h]

/-- The reduced multiplication algorithm computes multiplication in every
characteristic-two algebra in which the specified monic modulus vanishes. -/
theorem evalBits_mulReduce [CharP R 2] (z : R) (p a b : BitStr)
    (hlen : a.length = p.length) (hroot : z ^ p.length = evalBits z p) :
    evalBits z (mulReduce p a b) = evalBits z a * evalBits z b := by
  induction b with
  | nil => simp [mulReduce]
  | cons bit b ih =>
    change evalBits z (if bit then xorBits (shiftReduce p (mulReduce p a b)) a
      else shiftReduce p (mulReduce p a b)) = _
    have hl := length_mulReduce p a b hlen
    cases bit
    · simp only [Bool.false_eq_true, if_false, evalBits_cons, ofBool, zero_add]
      rw [evalBits_shiftReduce z p _ hl hroot, ih]
      ring
    · simp only [if_true, evalBits_cons, ofBool]
      rw [evalBits_xor z _ _ (by rw [length_shiftReduce p _ hl, hlen]),
        evalBits_shiftReduce z p _ hl hroot, ih]
      ring

section Programs

open PolyTimeFun

/-- Take a unary-specified number of coefficients in polynomial time. -/
noncomputable def takeBitsProg : PolyTimeFun (Unary × BitStr) BitStr :=
  PolyTimeFun.congr ((map snd).comp zip) (fun p => p.2.take p.1.length) (by
    rintro ⟨u, l⟩
    change (u.zip l).map Prod.snd = l.take u.length
    induction u generalizing l with
    | nil => simp
    | cons x u ih => cases l <;> simp [ih])

@[simp] theorem takeBitsProg_apply (p : Unary × BitStr) :
    takeBitsProg p = p.2.take p.1.length := rfl

/-- XOR of two bits, as an ambient program. -/
noncomputable def xorBitProg : PolyTimeFun (Bool × Bool) Bool :=
  PolyTimeFun.congr (ite fst (ite snd (const false) (const true)) snd) (fun p => p.1 ^^ p.2)
    (by rintro ⟨a, b⟩; cases a <;> cases b <;> rfl)

/-- Uniform polynomial-time addition of fixed-width coefficient vectors. -/
noncomputable def xorBitsProg : PolyTimeFun (BitStr × BitStr) BitStr :=
  PolyTimeFun.congr ((map xorBitProg).comp zip) (fun p => xorBits p.1 p.2) (by
    intro p
    change (p.1.zip p.2).map (fun q => q.1 ^^ q.2) = List.zipWith Bool.xor p.1 p.2
    exact List.map_zip_eq_zipWith)

@[simp] theorem xorBitsProg_apply (p : BitStr × BitStr) :
    xorBitsProg p = xorBits p.1 p.2 := rfl

private noncomputable def headProg : PolyTimeFun BitStr Bool :=
  PolyTimeFun.congr
    ((casesList (const false) (fst.comp snd)).comp ((const ()).pair (PolyTimeFun.id _)))
    (fun a => a.headD false) (by intro a; cases a <;> rfl)

private noncomputable def tailProg : PolyTimeFun BitStr BitStr :=
  PolyTimeFun.congr
    ((casesList (const []) (snd.comp snd)).comp ((const ()).pair (PolyTimeFun.id _)))
    List.tail (by intro a; cases a <;> rfl)

private noncomputable def shiftLowProg : PolyTimeFun BitStr BitStr :=
  PolyTimeFun.congr
    (reverse.comp (tailProg.comp (reverse.comp (cons (const false) (PolyTimeFun.id _)))))
    shiftLow (by
      intro a
      change ((false :: a).reverse.tail).reverse = (false :: a).dropLast
      rw [List.tail_reverse, List.reverse_reverse])

/-- Uniform polynomial-time multiplication by the indeterminate modulo a binary
monic polynomial. The input is the lower-coefficient vector and the operand. -/
noncomputable def shiftReduceProg : PolyTimeFun (BitStr × BitStr) BitStr :=
  PolyTimeFun.congr
    (ite (headProg.comp (reverse.comp snd))
      (xorBitsProg.comp ((shiftLowProg.comp snd).pair fst)) (shiftLowProg.comp snd))
    (fun p => shiftReduce p.1 p.2) (by
      intro p
      change (if p.2.reverse.headD false then xorBits (shiftLow p.2) p.1 else shiftLow p.2) = _
      simp only [List.headD_eq_head?_getD, List.head?_reverse, ← List.getLastD_eq_getLast?]
      rfl)

@[simp] theorem shiftReduceProg_apply (p : BitStr × BitStr) :
    shiftReduceProg p = shiftReduce p.1 p.2 := rfl

private abbrev MulState := BitStr × BitStr × BitStr

private def mulStep (s : MulState) (bit : Bool) : MulState :=
  (s.1, s.2.1, if bit then xorBits (shiftReduce s.1 s.2.2) s.2.1
    else shiftReduce s.1 s.2.2)

private noncomputable def mulStepProg : PolyTimeFun (MulState × Bool) MulState :=
  let p := fst.comp fst
  let a := fst.comp (snd.comp fst)
  let acc := snd.comp (snd.comp fst)
  let shifted := shiftReduceProg.comp (p.pair acc)
  p.pair (a.pair (ite snd (xorBitsProg.comp (shifted.pair a)) shifted))

private theorem mulStepProg_apply (s : MulState) (bit : Bool) :
    mulStepProg (s, bit) = mulStep s bit := rfl

private theorem mulStep_length (s : MulState) (bit : Bool) :
    (mulStep s bit).2.2.length ≤ s.2.2.length := by
  unfold mulStep
  split
  · change (xorBits (shiftReduce s.1 s.2.2) s.2.1).length ≤ _
    rw [length_xorBits]
    exact (min_le_left _ _).trans (length_shiftReduce_le _ _)
  · exact length_shiftReduce_le _ _

private theorem foldl_mulStep (l : BitStr) (s : MulState) :
    (l.foldl mulStep s).1 = s.1 ∧
      (l.foldl mulStep s).2.1 = s.2.1 ∧
      (l.foldl mulStep s).2.2.length ≤ s.2.2.length := by
  induction l generalizing s with
  | nil => exact ⟨rfl, rfl, le_rfl⟩
  | cons bit l ih =>
    obtain ⟨hp, ha, hacc⟩ := ih (mulStep s bit)
    exact ⟨hp, ha, hacc.trans (mulStep_length s bit)⟩

private theorem mulStepProg_bounded :
    PolyTimeFun.FoldBounded mulStepProg (4 * Polynomial.X + 4) := by
  intro l s pre xs _
  change esize (pre.foldl mulStep s) ≤ _
  obtain ⟨hp, ha, hacc⟩ := foldl_mulStep pre s
  have he := esize_bitStr_le (pre.foldl mulStep s).2.2
  have hinit := length_le_esize_list s.2.2
  change esize (pre.foldl mulStep s).1 +
    (esize (pre.foldl mulStep s).2.1 + esize (pre.foldl mulStep s).2.2 + 1) + 1 ≤ _
  rw [hp, ha]
  have hs : esize s = esize s.1 + (esize s.2.1 + esize s.2.2 + 1) + 1 := rfl
  simp only [esize_prod, hs, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_X]
  omega

private theorem foldr_mulStep (l : BitStr) (p a acc : BitStr) :
    l.foldr (fun bit s => mulStep s bit) (p, a, acc) =
      (p, a, l.foldr (fun bit v =>
        if bit then xorBits (shiftReduce p v) a else shiftReduce p v) acc) := by
  induction l with
  | nil => rfl
  | cons bit l ih => rw [List.foldr_cons, ih]; rfl

/-- Uniform polynomial-time multiplication modulo a binary monic polynomial.
The input carries its lower coefficients and the two operands. -/
noncomputable def mulReduceProg : PolyTimeFun (BitStr × BitStr × BitStr) BitStr :=
  let p : PolyTimeFun MulState BitStr := fst
  let a : PolyTimeFun MulState BitStr := fst.comp snd
  let b : PolyTimeFun MulState BitStr := snd.comp snd
  let zero := replicate.comp ((length.comp a).pair (const false))
  PolyTimeFun.congr
    ((snd.comp snd).comp
      ((foldl mulStepProg (4 * Polynomial.X + 4) mulStepProg_bounded).comp
        ((reverse.comp b).pair (p.pair (a.pair zero)))))
    (fun s => mulReduce s.1 s.2.1 s.2.2) (by
      intro s
      simp only [p, a, b, zero, comp_apply, fst_apply, snd_apply, pair_apply,
        reverse_apply, foldl_apply, replicate_apply, length_apply, length_unary,
        const_apply, mulStepProg_apply]
      change (s.2.2.reverse.foldl mulStep (s.1, s.2.1,
        List.replicate s.2.1.length false)).2.2 = _
      rw [List.foldl_reverse, foldr_mulStep]
      rfl)

@[simp] theorem mulReduceProg_apply (s : BitStr × BitStr × BitStr) :
    mulReduceProg s = mulReduce s.1 s.2.1 s.2.2 := rfl

end Programs

end MIPRE.LowDegree.BinaryPolynomial

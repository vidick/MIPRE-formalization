/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryQuotientPolynomial

/-! # Translating binary polynomials in a supplied polynomial quotient -/

noncomputable section

namespace MIPRE.LowDegree.BinaryQuotient

open Cost Cost.PolyTimeFun BinaryPolynomial Polynomial

/-- Horner translation by the represented element `a`. -/
def translateBits (p a : BitStr) : BitStr → List BitStr
  | [] => []
  | b :: bs => linearMulCarry p a (if b then oneBits p else zeroBits p) (translateBits p a bs)

@[simp] theorem length_translateBits (p a g : BitStr) :
    (translateBits p a g).length = g.length := by
  induction g <;> simp [translateBits, *]

/-- Translation bounds coefficient width on every raw input, irrespective of the root width. -/
theorem translateBits_width_le (p a g : BitStr) :
    ∀ c ∈ translateBits p a g, c.length ≤ p.length := by
  induction g with
  | nil => simp [translateBits]
  | cons b g ih =>
    apply linearMulCarry_width_le _ _ _ _ _ _ ih
    cases b <;> simp

/-- Correct-width translation preserves the quotient coefficient width. -/
theorem translateBits_width (p a g : BitStr) (ha : a.length = p.length) :
    ∀ c ∈ translateBits p a g, c.length = p.length := by
  induction g with
  | nil => simp [translateBits]
  | cons b g ih =>
    apply linearMulCarry_width _ _ _ _ ha _ ih
    cases b <;> simp

variable {R : Type*} [CommRing R] [CharP R 2] [Algebra (ZMod 2) R]

/-- The translation program substitutes `X+a` in the input binary polynomial. -/
theorem coeffPolynomial_translateBits (z : R) (p a g : BitStr) (hp : p ≠ [])
    (hz : z ^ p.length = evalBits z p) (ha : a.length = p.length) :
    coeffPolynomial z (translateBits p a g) =
      ((polyOfBits g).map (algebraMap (ZMod 2) R)).comp (X + C (evalBits z a)) := by
  induction g with
  | nil => simp [translateBits, polyOfBits]
  | cons b g ih =>
    rw [translateBits, coeffPolynomial_linearMulCarry z p a _ _ hz ha
      (by cases b <;> simp) (translateBits_width p a g ha), ih, polyOfBits_cons]
    cases b <;> simp [ofBool, evalBits_oneBits z p hp, Polynomial.map_add,
      Polynomial.map_mul, add_comp, mul_comp]

private abbrev TranslateState := BitStr × BitStr × List BitStr

private def translateStep (s : TranslateState) (b : Bool) : TranslateState :=
  (s.1, s.2.1, linearMulCarry s.1 s.2.1 (if b then oneBits s.1 else zeroBits s.1) s.2.2)

private theorem fold_translateStep_shape (pre : BitStr) (p a : BitStr) (cs : List BitStr) :
    (pre.foldl translateStep (p, a, cs)).1 = p ∧
      (pre.foldl translateStep (p, a, cs)).2.1 = a ∧
      (pre.foldl translateStep (p, a, cs)).2.2.length = cs.length + pre.length := by
  induction pre generalizing cs with
  | nil => exact ⟨rfl, rfl, by simp⟩
  | cons b pre ih =>
    have h := ih (linearMulCarry p a (if b then oneBits p else zeroBits p) cs)
    refine ⟨h.1, h.2.1, ?_⟩
    simpa only [List.foldl_cons, translateStep, length_linearMulCarry, List.length_cons,
      Nat.add_assoc, Nat.add_comm 1 pre.length] using h.2.2

private theorem fold_translateStep_width (pre : BitStr) (p a : BitStr) (cs : List BitStr) (N : ℕ)
    (hp : p.length ≤ N) (hc : ∀ c ∈ cs, c.length ≤ N) :
    ∀ c ∈ (pre.foldl translateStep (p, a, cs)).2.2, c.length ≤ N := by
  induction pre generalizing cs with
  | nil => exact hc
  | cons b pre ih =>
    apply ih
    apply linearMulCarry_width_le _ _ _ _ N _ hc
    cases b <;> simpa using hp

private theorem fold_translateStep_eq (bs : BitStr) (p a : BitStr) (cs : List BitStr) :
    bs.foldl translateStep (p, a, cs) =
      (p, a, bs.foldl (fun acc b => linearMulCarry p a
        (if b then oneBits p else zeroBits p) acc) cs) := by
  induction bs generalizing cs with
  | nil => rfl
  | cons b bs ih => exact ih _

private def translateStepProg : PolyTimeFun (TranslateState × Bool) TranslateState :=
  let p := fst.comp fst
  let a := fst.comp (snd.comp fst)
  let cs := snd.comp (snd.comp fst)
  congr (p.pair (a.pair (linearMulCarryProg.comp
    (p.pair (a.pair ((ite snd (oneBitsProg.comp p) (zeroBitsProg.comp p)).pair cs))))))
    (fun q => translateStep q.1 q.2) (by
      rintro ⟨⟨p, a, cs⟩, b⟩
      change (p, a, linearMulCarryProg (p, a, if b then oneBits p else zeroBits p, cs)) = _
      rw [linearMulCarryProg_apply]
      rfl)

private theorem translateStep_bounded :
    FoldBounded translateStepProg (20 * X ^ 2 + 20 * X + 20) := by
  intro bs s pre post heq
  rcases s with ⟨p, a, cs⟩
  let N := esize (bs, p, a, cs)
  have hs : N = esize bs + esize p + esize a + esize cs + 3 := by simp [N, esize_prod]; omega
  have hp : p.length ≤ N := by have := length_le_esize_bitStr p; omega
  have hc : cs.length ≤ N := by have := length_le_esize_list cs; omega
  have hpre : pre.length ≤ N := by
    have := length_le_esize_list bs
    have he := congrArg List.length heq
    simp only [List.length_append] at he
    omega
  have hw : ∀ c ∈ cs, c.length ≤ N := by
    intro c hc'
    have h₁ := esize_mem_le hc'
    have h₂ := length_le_esize_bitStr c
    omega
  have hshape := fold_translateStep_shape pre p a cs
  have hsize := esize_coefficients_le _ N (fold_translateStep_width pre p a cs N hp hw)
  have hn : (pre.foldl translateStep (p, a, cs)).2.2.length ≤ 2 * N := by omega
  have hm := Nat.mul_le_mul_right (4 * N + 2) hn
  change esize (pre.foldl translateStep (p, a, cs)) ≤ _
  rw [esize_prod, esize_prod, hshape.1, hshape.2.1]
  simp only [eval_add, eval_mul, eval_pow, eval_X, eval_ofNat]
  change esize p + (esize a + esize (pre.foldl translateStep (p, a, cs)).2.2 + 1) + 1 ≤
    20 * N ^ 2 + 20 * N + 20
  nlinarith

/-- One globally polynomial-time binary polynomial translation program. -/
def translateBitsProg : PolyTimeFun (BitStr × BitStr × BitStr) (List BitStr) :=
  let scan := foldl translateStepProg (20 * X ^ 2 + 20 * X + 20) translateStep_bounded
  congr ((snd.comp snd).comp (scan.comp
    ((PolyTimeFun.reverse.comp (snd.comp snd)).pair (fst.pair ((fst.comp snd).pair (const []))))))
    (fun q => translateBits q.1 q.2.1 q.2.2) (by
      rintro ⟨p, a, bs⟩
      change (bs.reverse.foldl translateStep (p, a, [])).2.2 = _
      rw [fold_translateStep_eq, List.foldl_reverse]
      induction bs with
      | nil => rfl
      | cons b bs ih =>
        dsimp only at ih ⊢
        simp only [List.foldr_cons, translateBits, ih])

@[simp] theorem translateBitsProg_apply (p a g : BitStr) :
    translateBitsProg (p, a, g) = translateBits p a g := rfl

end MIPRE.LowDegree.BinaryQuotient

end

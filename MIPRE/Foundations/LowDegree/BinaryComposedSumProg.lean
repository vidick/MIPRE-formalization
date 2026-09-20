/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryComposedSumPolynomial

/-! # Uniform polynomial-time products of Frobenius translates -/

noncomputable section

namespace MIPRE.LowDegree.BinaryQuotient

open Cost Cost.PolyTimeFun BinaryPolynomial Polynomial

/-- Modulus, binary polynomial to translate, and accumulating coefficient list. -/
abbrev NormState := BitStr × BitStr × List BitStr

/-- Multiply the accumulator by one translated copy of the binary polynomial. -/
def normStep (s : NormState) (a : BitStr) : NormState :=
  (s.1, s.2.1, mulCoeffLists s.1 (translateBits s.1 a s.2.1) s.2.2)

private theorem fold_normStep_shape (pre : List BitStr) (p g : BitStr) (cs : List BitStr) :
    (pre.foldl normStep (p, g, cs)).1 = p ∧ (pre.foldl normStep (p, g, cs)).2.1 = g ∧
      (pre.foldl normStep (p, g, cs)).2.2.length ≤ cs.length + pre.length * g.length := by
  induction pre generalizing cs with
  | nil => exact ⟨rfl, rfl, by simp⟩
  | cons a pre ih =>
    have h := ih (mulCoeffLists p (translateBits p a g) cs)
    have hl := length_mulCoeffLists_le p (translateBits p a g) cs
    rw [length_translateBits] at hl
    refine ⟨h.1, h.2.1, ?_⟩
    change (pre.foldl normStep (p, g, mulCoeffLists p (translateBits p a g) cs)).2.2.length ≤ _
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

private theorem fold_normStep_width_le (pre : List BitStr) (p g : BitStr) (cs : List BitStr) (N : ℕ)
    (hp : p.length ≤ N) (hc : ∀ c ∈ cs, c.length ≤ N) :
    ∀ c ∈ (pre.foldl normStep (p, g, cs)).2.2, c.length ≤ N := by
  induction pre generalizing cs with
  | nil => exact hc
  | cons a pre ih =>
    apply ih
    exact mulCoeffLists_width_le p _ cs N hp
      (fun c hc' => (translateBits_width_le p a g c hc').trans hp)

/-- Valid quotient widths are preserved by the translate-product loop. -/
theorem fold_normStep_width (pre : List BitStr) (p g : BitStr) (cs : List BitStr)
    (ha : ∀ a ∈ pre, a.length = p.length) (hc : ∀ c ∈ cs, c.length = p.length) :
    ∀ c ∈ (pre.foldl normStep (p, g, cs)).2.2, c.length = p.length := by
  induction pre generalizing cs with
  | nil => exact hc
  | cons a pre ih =>
    apply ih _ (fun d hd => ha d (by simp [hd]))
    exact mulCoeffLists_width p _ cs (translateBits_width p a g (ha a (by simp)))

variable {R : Type*} [CommRing R] [CharP R 2] [Algebra (ZMod 2) R]

/-- The loop computes precisely the product of the specified translated polynomials. -/
theorem coeffPolynomial_fold_normStep (z : R) (pre : List BitStr) (p g : BitStr) (cs : List BitStr)
    (hp : p ≠ []) (hz : z ^ p.length = evalBits z p) (ha : ∀ a ∈ pre, a.length = p.length) :
    coeffPolynomial z (pre.foldl normStep (p, g, cs)).2.2 =
      (pre.map (fun a => translatedPolynomial (polyOfBits g) (evalBits z a))).prod * coeffPolynomial z cs := by
  induction pre generalizing cs with
  | nil => simp
  | cons a pre ih =>
    have ha₀ := ha a (by simp)
    change coeffPolynomial z (pre.foldl normStep (p, g, mulCoeffLists p (translateBits p a g) cs)).2.2 = _
    rw [ih _ (fun d hd => ha d (by simp [hd])),
      coeffPolynomial_mulCoeffLists z p _ cs hz (translateBits_width p a g ha₀),
      coeffPolynomial_translateBits z p a g hp hz ha₀]
    simp only [List.map_cons, List.prod_cons, translatedPolynomial]
    ring

/-- Product of the translates specified by a list of quotient elements. -/
def normProductBits (p g : BitStr) (as : List BitStr) : List BitStr :=
  (as.foldl normStep (p, g, [oneBits p])).2.2

/-- The printed coefficient list represents the prescribed translate product. -/
theorem coeffPolynomial_normProductBits (z : R) (p g : BitStr) (as : List BitStr)
    (hp : p ≠ []) (hz : z ^ p.length = evalBits z p) (ha : ∀ a ∈ as, a.length = p.length) :
    coeffPolynomial z (normProductBits p g as) =
      (as.map (fun a => translatedPolynomial (polyOfBits g) (evalBits z a))).prod := by
  rw [normProductBits, coeffPolynomial_fold_normStep z as p g _ hp hz ha]
  simp [evalBits_oneBits z p hp]

private def normStepProg : PolyTimeFun (NormState × BitStr) NormState :=
  let p := fst.comp fst
  let g := fst.comp (snd.comp fst)
  let cs := snd.comp (snd.comp fst)
  congr (p.pair (g.pair (mulCoeffListsProg.comp
    (p.pair ((translateBitsProg.comp (p.pair (snd.pair g))).pair cs)))))
    (fun q => normStep q.1 q.2) (by rintro ⟨⟨p, g, cs⟩, a⟩; rfl)

private theorem normStep_bounded :
    FoldBounded normStepProg (30 * X ^ 3 + 30 * X ^ 2 + 30 * X + 30) := by
  intro as s pre post heq
  rcases s with ⟨p, g, cs⟩
  let N := esize (as, p, g, cs)
  have hs : N = esize as + esize p + esize g + esize cs + 3 := by simp [N, esize_prod]; omega
  have hp : p.length ≤ N := by have := length_le_esize_bitStr p; omega
  have hg : g.length ≤ N := by have := length_le_esize_bitStr g; omega
  have hc : cs.length ≤ N := by have := length_le_esize_list cs; omega
  have hpre : pre.length ≤ N := by
    have := length_le_esize_list as
    have he := congrArg List.length heq
    simp only [List.length_append] at he
    omega
  have hw : ∀ c ∈ cs, c.length ≤ N := by
    intro c hc'
    have h₁ := esize_mem_le hc'
    have h₂ := length_le_esize_bitStr c
    omega
  have hshape := fold_normStep_shape pre p g cs
  have hsize := esize_coefficients_le _ N (fold_normStep_width_le pre p g cs N hp hw)
  have hpg := Nat.mul_le_mul hpre hg
  have hn : (pre.foldl normStep (p, g, cs)).2.2.length ≤ N + N ^ 2 := by nlinarith
  have hm := Nat.mul_le_mul_right (4 * N + 2) hn
  change esize (pre.foldl normStep (p, g, cs)) ≤ _
  rw [esize_prod, esize_prod, hshape.1, hshape.2.1]
  simp only [eval_add, eval_mul, eval_pow, eval_X, eval_ofNat]
  change esize p + (esize g + esize (pre.foldl normStep (p, g, cs)).2.2 + 1) + 1 ≤
    30 * N ^ 3 + 30 * N ^ 2 + 30 * N + 30
  nlinarith [Nat.zero_le (N ^ 3)]

/-- One globally polynomial-time program for a supplied list of polynomial translates. -/
def normProductBitsProg : PolyTimeFun (BitStr × BitStr × List BitStr) (List BitStr) :=
  (snd.comp snd).comp ((foldl normStepProg (30 * X ^ 3 + 30 * X ^ 2 + 30 * X + 30)
    normStep_bounded).comp ((snd.comp snd).pair
      (fst.pair ((fst.comp snd).pair (cons (oneBitsProg.comp fst) (const []))))))

@[simp] theorem normProductBitsProg_apply (p g : BitStr) (as : List BitStr) :
    normProductBitsProg (p, g, as) = normProductBits p g as := rfl

/-- A fixed-width encoding of the canonical quotient root, also valid in degree one. -/
def rootBits (p : BitStr) : BitStr := shiftReduce p (oneBits p)

@[simp] theorem length_rootBits (p : BitStr) : (rootBits p).length = p.length :=
  length_shiftReduce _ _ (length_oneBits p)

omit [Algebra (ZMod 2) R] in
theorem evalBits_rootBits (z : R) (p : BitStr) (hp : p ≠ []) (hz : z ^ p.length = evalBits z p) :
    evalBits z (rootBits p) = z := by
  rw [rootBits, evalBits_shiftReduce z p _ (length_oneBits p) hz, evalBits_oneBits z p hp, mul_one]

def rootBitsProg : PolyTimeFun BitStr BitStr := shiftReduceProg.comp ((PolyTimeFun.id _).pair oneBitsProg)

@[simp] theorem rootBitsProg_apply (p : BitStr) : rootBitsProg p = rootBits p := rfl

/-- Binary output of the composed-sum construction for the supplied monic modulus and polynomial. -/
def composedSumBits (p g : BitStr) : BitStr :=
  descendBits (normProductBits p g (orbitBits (unary p.length) p (rootBits p)))

/-- The composed-sum constructor is polynomial-time on every pair of raw lists. -/
def composedSumBitsProg : PolyTimeFun (BitStr × BitStr) BitStr :=
  let roots := orbitBitsProg.comp ((length.comp fst).pair (fst.pair (rootBitsProg.comp fst)))
  descendBitsProg.comp (normProductBitsProg.comp (fst.pair (snd.pair roots)))

@[simp] theorem composedSumBitsProg_apply (p g : BitStr) :
    composedSumBitsProg (p, g) = composedSumBits p g := rfl

end MIPRE.LowDegree.BinaryQuotient

end

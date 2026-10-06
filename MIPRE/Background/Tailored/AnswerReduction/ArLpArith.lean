/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.AnswerReduction.ArLpSlots

@[expose] public section

/-!
# Field arithmetic, as programs

Slice P4h of `planning/aldous-lyons-track.md`: combinators for programs computing elements of
`F_{2^t}` in their Shoup bits, with the law that they compute a given field expression when their
arguments do: sums (`fAdd`), products (`fMul`), `0` and `1`, the assignment form `g (1 - g)`
(`fCert`), indexed sums (`fSum`, by folding `xorBits`) and comparisons (`fEq`). The proof check
of the answer-reduced game is written with them.
-/

noncomputable section

namespace MIPRE.Tailored.AnsRed.Typed

open Cost Cost.PolyTimeFun MIPRE.CL MIPRE.SAT MIPRE.LowDegree MIPRE.LowDegree.BinaryPolynomial

/-! ## Summing bit strings -/

theorem esize_xorBits_le (a b : BitStr) : esize (xorBits a b) ≤ 4 * esize b + 1 := by
  have h1 := esize_bitStr_le (xorBits a b)
  have h2 : (xorBits a b).length ≤ b.length := by simp [xorBits]
  have h3 := length_le_esize_list b
  omega

/-- The sum of a list of bit strings, from an initial one, by folding `xorBits`. -/
def xorSumF : PolyTimeFun (List BitStr × BitStr) BitStr :=
  foldlAdd xorBitsProg (4 * Polynomial.X + 1) (by
    intro s a
    simp only [xorBitsProg_apply, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_ofNat, Polynomial.eval_one]
    have := esize_xorBits_le s a
    omega)

@[simp] theorem xorSumF_apply (l : List BitStr) (s : BitStr) :
    xorSumF (l, s) = l.foldl xorBits s := by
  simp [xorSumF]

variable {t : ℕ} {ht : 1 ≤ t}

/-- **The sum of field elements**, in their bits. -/
theorem foldl_xorBits_toBits (l : List (Fq t ht)) (s : Fq t ht) :
    (l.map (shoupBinField t ht).toBits).foldl xorBits ((shoupBinField t ht).toBits s) =
      (shoupBinField t ht).toBits (s + l.sum) := by
  induction l generalizing s with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.foldl_cons, shoupXorBits_correct, ih, List.sum_cons, add_assoc]

/-! ## Combinators -/

section Comb

variable {I : Type} [SizedEncoding I] (uT : PolyTimeFun I Unary)

/-- The sum of two field elements. -/
def fAdd (a b : PolyTimeFun I BitStr) : PolyTimeFun I BitStr := xorBitsProg.comp (a.pair b)

/-- The product of two field elements. -/
def fMul (a b : PolyTimeFun I BitStr) : PolyTimeFun I BitStr :=
  shoupMulProg.comp (uT.pair (a.pair b))

/-- The field element `0`. -/
def fZero : PolyTimeFun I BitStr := replicate.comp (uT.pair (const false))

/-- The field element `1`. -/
def fOne : PolyTimeFun I BitStr := oneBitsProg.comp (fZero uT)

/-- `g (1 - g)`, as `g (1 + g)` in characteristic `2`. -/
def fCert (a : PolyTimeFun I BitStr) : PolyTimeFun I BitStr := fMul uT a (fAdd (fOne uT) a)

/-- The sum of `f i` over `i < n`. -/
def fSum (f : PolyTimeFun (Unary × I) BitStr) (n : PolyTimeFun I Unary) : PolyTimeFun I BitStr :=
  xorSumF.comp ((mapR f (rangeU.comp n)).pair (fZero uT))

/-- Whether two field elements are equal. -/
def fEq (a b : PolyTimeFun I BitStr) : PolyTimeFun I Bool := ArrayProg.eqBits.comp (a.pair b)

variable {uT} {inp : I}

theorem fAdd_eq {a b : PolyTimeFun I BitStr} {x y : Fq t ht}
    (ha : a inp = (shoupBinField t ht).toBits x) (hb : b inp = (shoupBinField t ht).toBits y) :
    fAdd a b inp = (shoupBinField t ht).toBits (x + y) := by
  simp only [fAdd, comp_apply, pair_apply, xorBitsProg_apply, ha, hb, shoupXorBits_correct]

theorem fMul_eq (hT : uT inp = unary t) {a b : PolyTimeFun I BitStr} {x y : Fq t ht}
    (ha : a inp = (shoupBinField t ht).toBits x) (hb : b inp = (shoupBinField t ht).toBits y) :
    fMul uT a b inp = (shoupBinField t ht).toBits (x * y) := by
  simp only [fMul, comp_apply, pair_apply, hT, ha, hb, shoupMulProg_encoding]

theorem fZero_eq (hT : uT inp = unary t) : fZero uT inp = (shoupBinField t ht).toBits 0 := by
  simp only [fZero, comp_apply, pair_apply, hT, const_apply, replicate_apply, length_unary,
    zeros_eq t ht]

theorem fOne_eq (hT : uT inp = unary t) : fOne uT inp = (shoupBinField t ht).toBits 1 := by
  simp only [fOne, comp_apply, oneBitsProg_apply]
  exact shoupBinField_oneBits t ht _ (by simp [fZero, hT])

theorem fCert_eq (hT : uT inp = unary t) {a : PolyTimeFun I BitStr} {x : Fq t ht}
    (ha : a inp = (shoupBinField t ht).toBits x) :
    fCert uT a inp = (shoupBinField t ht).toBits (x * (1 - x)) := by
  rw [fCert, fMul_eq hT ha (fAdd_eq (fOne_eq hT) ha), CharTwo.sub_eq_add]

theorem fSum_eq (hT : uT inp = unary t) {f : PolyTimeFun (Unary × I) BitStr}
    {n : PolyTimeFun I Unary} {k : ℕ} (hn : n inp = unary k) (g : Fin k → Fq t ht)
    (hf : ∀ i : Fin k, f (unary i, inp) = (shoupBinField t ht).toBits (g i)) :
    fSum uT f n inp = (shoupBinField t ht).toBits (∑ i, g i) := by
  have hl : (mapR f (rangeU.comp n)) inp = (List.ofFn g).map (shoupBinField t ht).toBits := by
    simp only [mapR_apply, comp_apply, hn, rangeU_apply, length_unary, List.map_map]
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn, Function.comp_apply]
    exact hf ⟨i, by simpa using h1⟩
  simp only [fSum, comp_apply, pair_apply, xorSumF_apply, hl]
  rw [fZero_eq (ht := ht) hT, foldl_xorBits_toBits, zero_add, List.sum_ofFn]

theorem fEq_eq {a b : PolyTimeFun I BitStr} {x y : Fq t ht}
    (ha : a inp = (shoupBinField t ht).toBits x) (hb : b inp = (shoupBinField t ht).toBits y) :
    fEq a b inp = decide (x = y) := by
  have hi : Function.Injective (shoupBinField t ht).toBits := by
    intro u v h
    simpa only [(shoupBinField t ht).ofBits_toBits] using congrArg (shoupBinField t ht).ofBits h
  simp only [fEq, comp_apply, pair_apply, ArrayProg.eqBits_apply, ha, hb, hi.eq_iff]

end Comb

end MIPRE.Tailored.AnsRed.Typed

end

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryPower
import Mathlib.FieldTheory.Finite.Trace

/-!
# Effective Frobenius iteration and trace

A fixed-width loop squares its current field element and adds it to a trace
accumulator. The loop count is unary, so `k` Frobenius operations take `poly(k)`
time even though the represented exponent is `2^k`.
-/

namespace MIPRE.LowDegree.BinaryPolynomial

open Cost Cost.PolyTimeFun Polynomial

def traceStep (s : PowerState) (_ : Unit) : PowerState :=
  (s.1, mulReduce s.1 s.2.1 s.2.1, xorBits s.2.2 s.2.1)

theorem traceStep_width (s : PowerState) (u : Unit) :
    (traceStep s u).1 = s.1 ∧
    (traceStep s u).2.1.length ≤ s.2.1.length ∧
    (traceStep s u).2.2.length ≤ s.2.2.length :=
  ⟨rfl, length_mulReduce_le _ _ _, by
    change (xorBits s.2.2 s.2.1).length ≤ _
    rw [length_xorBits]
    exact min_le_left _ _⟩

theorem fold_traceStep_width (u : Unary) (s : PowerState) :
    (u.foldl traceStep s).1 = s.1 ∧
    (u.foldl traceStep s).2.1.length ≤ s.2.1.length ∧
    (u.foldl traceStep s).2.2.length ≤ s.2.2.length := by
  induction u generalizing s with
  | nil => exact ⟨rfl, le_rfl, le_rfl⟩
  | cons b u ih =>
    obtain ⟨hp, ha, hc⟩ := ih (traceStep s b)
    obtain ⟨_, ha', hc'⟩ := traceStep_width s b
    exact ⟨hp, ha.trans ha', hc.trans hc'⟩

theorem fold_traceStep_length (u : Unary) (p a c : BitStr)
    (ha : a.length = p.length) (hc : c.length = p.length) :
    (u.foldl traceStep (p, a, c)).2.1.length = p.length ∧
    (u.foldl traceStep (p, a, c)).2.2.length = p.length := by
  induction u generalizing a c with
  | nil => exact ⟨ha, hc⟩
  | cons b u ih =>
    exact ih _ _ (length_mulReduce _ _ _ ha) (by simp [length_xorBits, ha, hc])

/-- Both the final Frobenius iterate and the sum of the preceding iterates. -/
def frobeniusTrace (p a : BitStr) (u : Unary) : BitStr × BitStr :=
  (u.foldl traceStep (p, a, zeroBits p)).2

theorem length_frobeniusTrace (p a : BitStr) (u : Unary) (ha : a.length = p.length) :
    (frobeniusTrace p a u).1.length = p.length ∧
    (frobeniusTrace p a u).2.length = p.length :=
  fold_traceStep_length u p a _ ha (length_zeroBits p)

variable {R : Type*} [CommRing R] [CharP R 2]

theorem evalBits_fold_traceStep (z : R) (p a c : BitStr) (u : Unary)
    (hroot : z ^ p.length = evalBits z p)
    (ha : a.length = p.length) (hc : c.length = p.length) :
    evalBits z (u.foldl traceStep (p, a, c)).2.1 = evalBits z a ^ (2 ^ u.length) ∧
    evalBits z (u.foldl traceStep (p, a, c)).2.2 =
      evalBits z c + ∑ i ∈ Finset.range u.length, evalBits z a ^ (2 ^ i) := by
  induction u generalizing a c with
  | nil => simp
  | cons b u ih =>
    obtain ⟨hi, hs⟩ := ih (mulReduce p a a) (xorBits c a)
      (length_mulReduce _ _ _ ha) (by simp [length_xorBits, ha, hc])
    change evalBits z (u.foldl traceStep (p, mulReduce p a a, xorBits c a)).2.1 = _ ∧
      evalBits z (u.foldl traceStep (p, mulReduce p a a, xorBits c a)).2.2 = _
    rw [hi, hs, evalBits_mulReduce z p a a ha hroot,
      evalBits_xor z c a (hc.trans ha.symm)]
    have hp (i : ℕ) : (evalBits z a * evalBits z a) ^ (2 ^ i) =
        evalBits z a ^ (2 ^ (i + 1)) := by
      rw [← pow_two, ← pow_mul, pow_succ']
    constructor
    · exact hp u.length
    · simp only [List.length_cons, Finset.sum_range_succ', hp, pow_zero, pow_one]
      ring

/-- Squaring and accumulating computes the Frobenius orbit and its trace sum. -/
theorem evalBits_frobeniusTrace (z : R) (p a : BitStr) (u : Unary)
    (hroot : z ^ p.length = evalBits z p) (ha : a.length = p.length) :
    evalBits z (frobeniusTrace p a u).1 = evalBits z a ^ (2 ^ u.length) ∧
    evalBits z (frobeniusTrace p a u).2 =
      ∑ i ∈ Finset.range u.length, evalBits z a ^ (2 ^ i) := by
  have h := evalBits_fold_traceStep z p a (zeroBits p) u hroot ha (length_zeroBits p)
  simpa only [frobeniusTrace, evalBits_zeroBits, zero_add] using h

/-- The full field-degree iteration returns the original element. -/
theorem evalBits_frobeniusTrace_period {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (z : F) (p a : BitStr) (hcard : Fintype.card F = 2 ^ p.length)
    (hroot : z ^ p.length = evalBits z p) (ha : a.length = p.length) :
    evalBits z (frobeniusTrace p a (unary p.length)).1 = evalBits z a := by
  rw [(evalBits_frobeniusTrace z p a _ hroot ha).1, length_unary, ← hcard]
  exact FiniteField.pow_card _

/-- The accumulated sum is the algebraic trace, embedded into the extension field. -/
theorem evalBits_frobeniusTrace_trace {F : Type*} [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F] (z : F) (p a : BitStr)
    (hdegree : Module.finrank (ZMod 2) F = p.length)
    (hroot : z ^ p.length = evalBits z p) (ha : a.length = p.length) :
    evalBits z (frobeniusTrace p a (unary p.length)).2 =
      algebraMap (ZMod 2) F (Algebra.trace (ZMod 2) F (evalBits z a)) := by
  rw [(evalBits_frobeniusTrace z p a _ hroot ha).2,
    FiniteField.algebraMap_trace_eq_sum_pow, hdegree, length_unary]
  simp

private noncomputable def traceStepProg : PolyTimeFun (PowerState × Unit) PowerState :=
  let p := fst.comp fst
  let a := fst.comp (snd.comp fst)
  let c := snd.comp (snd.comp fst)
  p.pair ((mulReduceProg.comp (p.pair (a.pair a))).pair (xorBitsProg.comp (c.pair a)))

private theorem traceStepProg_apply (s : PowerState) (u : Unit) :
    traceStepProg (s, u) = traceStep s u := rfl

private theorem traceStep_bounded : FoldBounded traceStepProg (9 * X + 9) := by
  intro l s pre post _
  change esize (pre.foldl traceStep s) ≤ _
  obtain ⟨hp, ha, hc⟩ := fold_traceStep_width pre s
  have ha0 := length_le_esize_list s.2.1
  have hc0 := length_le_esize_list s.2.2
  have hsa := esize_bitStr_le (pre.foldl traceStep s).2.1
  have hsc := esize_bitStr_le (pre.foldl traceStep s).2.2
  have hs : esize s = esize s.1 + (esize s.2.1 + esize s.2.2 + 1) + 1 := rfl
  rw [esize_prod, esize_prod, hp]
  grw [hsa, hsc, ha, hc, ha0, hc0]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, esize_prod]
  omega

/-- Uniform computation of Frobenius iteration and the associated trace sum. -/
noncomputable def frobeniusTraceProg :
    PolyTimeFun (BitStr × BitStr × Unary) (BitStr × BitStr) :=
  congr (snd.comp ((foldl traceStepProg (9 * X + 9) traceStep_bounded).comp
    ((snd.comp snd).pair (fst.pair ((fst.comp snd).pair (zeroBitsProg.comp fst))))))
    (fun p => frobeniusTrace p.1 p.2.1 p.2.2) (by intro p; rfl)

@[simp] theorem frobeniusTraceProg_apply (p a : BitStr) (u : Unary) :
    frobeniusTraceProg (p, a, u) = frobeniusTrace p a u := rfl

end MIPRE.LowDegree.BinaryPolynomial

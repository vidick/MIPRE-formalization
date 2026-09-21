/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryQuotientOrbit

/-! # Explicit polynomial-time Frobenius-stride traces -/

noncomputable section

namespace MIPRE.LowDegree.BinaryQuotient

open Cost Cost.PolyTimeFun BinaryPolynomial Polynomial

/-- Repeat squaring once per unary stride bit. -/
def squareFuel (s : SquareState) (_ : Unit) : SquareState := squareStep s

theorem fold_squareFuel (u : Unary) (s : SquareState) :
    u.foldl squareFuel s = squareStep^[u.length] s := by
  induction u generalizing s with
  | nil => rfl
  | cons b u ih => simpa only [List.foldl_cons, List.length_cons,
      Function.iterate_succ_apply, squareFuel] using ih (squareStep s)

private def squareFuelProg : PolyTimeFun (SquareState × Unit) SquareState :=
  (fst.comp fst).pair (squareProg.comp fst)

private theorem squareFuel_bounded : FoldBounded squareFuelProg (5 * X + 5) := by
  intro l s pre post _
  change esize (pre.foldl squareFuel s) ≤ _
  rw [fold_squareFuel]
  obtain ⟨hm, hw⟩ := iterate_squareStep_shape pre.length s
  have ha := esize_bitStr_le (squareStep^[pre.length] s).2
  have hb := length_le_esize_bitStr s.2
  have hs : esize s = esize s.1 + esize s.2 + 1 := rfl
  rw [esize_prod, hm]
  simp only [esize_prod, eval_add, eval_mul, eval_ofNat, eval_X]
  omega

/-- A supplied unary number of squarings in the explicit binary quotient. -/
def frobeniusBits (u : Unary) (p a : BitStr) : BitStr :=
  (squareStep^[u.length] (p, a)).2

/-- The stride Frobenius program is globally polynomially bounded. -/
def frobeniusBitsProg : PolyTimeFun (Unary × BitStr × BitStr) BitStr :=
  snd.comp (foldl squareFuelProg (5 * X + 5) squareFuel_bounded)

@[simp] theorem frobeniusBitsProg_apply (u : Unary) (p a : BitStr) :
    frobeniusBitsProg (u, p, a) = frobeniusBits u p a := by
  change (u.foldl squareFuel (p, a)).2 = _
  rw [fold_squareFuel]
  rfl

/-- Repeated squaring never increases even a malformed coefficient width. -/
theorem frobeniusBits_width_le (u : Unary) (p a : BitStr) :
    (frobeniusBits u p a).length ≤ a.length := (iterate_squareStep_shape u.length (p, a)).2

/-- The modulus width is preserved on valid quotient elements. -/
theorem frobeniusBits_width (u : Unary) (p a : BitStr) (ha : a.length = p.length) :
    (frobeniusBits u p a).length = p.length := iterate_squareStep_width u.length p a ha

/-- The supplied stride is the exponent of the Frobenius iterate. -/
theorem evalBits_frobeniusBits {R : Type*} [CommRing R] [CharP R 2]
    (z : R) (u : Unary) (p a : BitStr) (hz : z ^ p.length = evalBits z p)
    (ha : a.length = p.length) :
    evalBits z (frobeniusBits u p a) = evalBits z a ^ (2 ^ u.length) :=
  evalBits_iterate_squareStep z u.length p a hz ha

/-- Stride, modulus, accumulated sum, and the current Frobenius conjugate. -/
abbrev TraceState := Unary × BitStr × BitStr × BitStr

/-- Add the current conjugate and advance by the fixed Frobenius stride. -/
def traceStep (s : TraceState) (_ : Unit) : TraceState :=
  (s.1, s.2.1, xorBits s.2.2.1 s.2.2.2, frobeniusBits s.1 s.2.1 s.2.2.2)

/-- All runtime state widths stay below their initial widths. -/
theorem fold_traceStep_shape (u : Unary) (s : TraceState) :
    (u.foldl traceStep s).1 = s.1 ∧ (u.foldl traceStep s).2.1 = s.2.1 ∧
    (u.foldl traceStep s).2.2.1.length ≤ s.2.2.1.length ∧
    (u.foldl traceStep s).2.2.2.length ≤ s.2.2.2.length := by
  induction u generalizing s with
  | nil => exact ⟨rfl, rfl, le_rfl, le_rfl⟩
  | cons b u ih =>
    obtain ⟨hr, hp, hc, ha⟩ := ih (traceStep s b)
    refine ⟨hr, hp, hc.trans ?_, ha.trans (frobeniusBits_width_le ..)⟩
    simp only [traceStep, xorBits, List.length_zipWith]
    exact min_le_left _ _

/-- Both active coefficient vectors retain the modulus width. -/
theorem fold_traceStep_width (u r : Unary) (p c a : BitStr)
    (hc : c.length = p.length) (ha : a.length = p.length) :
    (u.foldl traceStep (r, p, c, a)).2.2.1.length = p.length ∧
    (u.foldl traceStep (r, p, c, a)).2.2.2.length = p.length := by
  induction u generalizing c a with
  | nil => exact ⟨hc, ha⟩
  | cons b u ih =>
    exact ih _ _ (by simp [length_xorBits, hc, ha]) (frobeniusBits_width r p a ha)

/-- The loop computes the trace-shaped sum, with the supplied initial accumulator. -/
theorem evalBits_fold_traceStep {R : Type*} [CommRing R] [CharP R 2]
    (z : R) (u r : Unary) (p c a : BitStr) (hz : z ^ p.length = evalBits z p)
    (hc : c.length = p.length) (ha : a.length = p.length) :
    evalBits z (u.foldl traceStep (r, p, c, a)).2.2.1 =
      evalBits z c + ∑ i ∈ Finset.range u.length, evalBits z a ^ (2 ^ (r.length * i)) := by
  induction u generalizing c a with
  | nil => simp
  | cons b u ih =>
    change evalBits z (u.foldl traceStep
      (r, p, xorBits c a, frobeniusBits r p a)).2.2.1 = _
    rw [ih _ _ (by simp [length_xorBits, hc, ha]) (frobeniusBits_width r p a ha),
      evalBits_xor z c a (hc.trans ha.symm), evalBits_frobeniusBits z r p a hz ha]
    have hs : ∑ i ∈ Finset.range u.length,
        (evalBits z a ^ (2 ^ r.length)) ^ (2 ^ (r.length * i)) =
        ∑ i ∈ Finset.range u.length, evalBits z a ^ (2 ^ (r.length * (i + 1))) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← pow_mul, ← pow_add]
      congr 2
      simp only [Nat.mul_add, Nat.mul_one, Nat.add_comm]
    rw [hs, List.length_cons, Finset.sum_range_succ']
    simp only [Nat.mul_zero, pow_zero, pow_one]
    ring

private def traceStepProg : PolyTimeFun (TraceState × Unit) TraceState :=
  let r := fst.comp fst
  let p := fst.comp (snd.comp fst)
  let c := fst.comp (snd.comp (snd.comp fst))
  let a := snd.comp (snd.comp (snd.comp fst))
  congr (r.pair (p.pair ((xorBitsProg.comp (c.pair a)).pair
    (frobeniusBitsProg.comp (r.pair (p.pair a))))))
    (fun s => traceStep s.1 s.2) (by
      intro s
      simp only [r, p, c, a, comp_apply, pair_apply, fst_apply, snd_apply,
        xorBitsProg_apply, frobeniusBitsProg_apply]
      rfl)

private theorem traceStep_bounded : FoldBounded traceStepProg (10 * X + 10) := by
  intro l s pre post _
  change esize (pre.foldl traceStep s) ≤ _
  obtain ⟨hr, hp, hc, ha⟩ := fold_traceStep_shape pre s
  have hce := esize_bitStr_le (pre.foldl traceStep s).2.2.1
  have hae := esize_bitStr_le (pre.foldl traceStep s).2.2.2
  have hc0 := length_le_esize_bitStr s.2.2.1
  have ha0 := length_le_esize_bitStr s.2.2.2
  have hs : esize s = esize s.1 + (esize s.2.1 +
    (esize s.2.2.1 + esize s.2.2.2 + 1) + 1) + 1 := rfl
  change esize (pre.foldl traceStep s).1 + (esize (pre.foldl traceStep s).2.1 +
    (esize (pre.foldl traceStep s).2.2.1 + esize (pre.foldl traceStep s).2.2.2 + 1) + 1) + 1 ≤ _
  rw [hr, hp]
  simp only [esize_prod, eval_add, eval_mul, eval_ofNat, eval_X]
  omega

/-- The binary vector for the sum of the requested Frobenius-stride conjugates. -/
def traceBits (m r : Unary) (p a : BitStr) : BitStr :=
  (m.foldl traceStep (r, p, zeroBits p, a)).2.2.1

/-- One globally polynomial-time program computes every such modular trace sum. -/
def traceBitsProg : PolyTimeFun (Unary × Unary × BitStr × BitStr) BitStr :=
  let m := fst
  let r := fst.comp snd
  let p := fst.comp (snd.comp snd)
  let a := snd.comp (snd.comp snd)
  (fst.comp (snd.comp snd)).comp
    ((foldl traceStepProg (10 * X + 10) traceStep_bounded).comp
      (m.pair (r.pair (p.pair ((zeroBitsProg.comp p).pair a)))))

@[simp] theorem traceBitsProg_apply (m r : Unary) (p a : BitStr) :
    traceBitsProg (m, r, p, a) = traceBits m r p a := by
  simp only [traceBitsProg, comp_apply, pair_apply, fst_apply, snd_apply, zeroBitsProg_apply]
  rfl

/-- The modular trace output has exactly the field representation width. -/
theorem traceBits_width (m r : Unary) (p a : BitStr) (ha : a.length = p.length) :
    (traceBits m r p a).length = p.length :=
  (fold_traceStep_width m r p (zeroBits p) a (length_zeroBits p) ha).1

/-- The program's semantics are the finite sum used in Shoup's trace construction. -/
theorem evalBits_traceBits {R : Type*} [CommRing R] [CharP R 2]
    (z : R) (m r : Unary) (p a : BitStr) (hz : z ^ p.length = evalBits z p)
    (ha : a.length = p.length) :
    evalBits z (traceBits m r p a) =
      ∑ i ∈ Finset.range m.length, evalBits z a ^ (2 ^ (r.length * i)) := by
  simpa only [traceBits, evalBits_zeroBits, zero_add] using
    evalBits_fold_traceStep z m r p (zeroBits p) a hz (length_zeroBits p) ha

end MIPRE.LowDegree.BinaryQuotient

end

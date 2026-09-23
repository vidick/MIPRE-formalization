/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.SAT.NormalElementProg

/-! # Uniform evaluation of field coefficient vectors

Coefficients are listed in increasing degree order. The program constructs the
field modulus once, then uses Horner's rule. Its ambient polynomial bound also
holds on malformed inputs: every step preserves the modulus and evaluation
point, and the accumulator's bit length can only decrease.

This file does not parse answers or claim correctness of the Pauli decider.
It supplies the arithmetic operation needed by its two line tests.
-/

noncomputable section
namespace MIPRE.Introspection.FieldPolynomialProgram
open Cost Cost.PolyTimeFun Polynomial LowDegree.BinaryPolynomial SAT

/-- Evaluation of a coefficient list in increasing degree order. -/
def evalCoeffs {R : Type*} [Semiring R] (x : R) (coeffs : List R) : R :=
  coeffs.foldr (fun c a => a * x + c) 0

@[simp] theorem evalCoeffs_nil {R : Type*} [Semiring R] (x : R) :
    evalCoeffs x [] = 0 := rfl

@[simp] theorem evalCoeffs_cons {R : Type*} [Semiring R] (x c : R) (coeffs : List R) :
    evalCoeffs x (c :: coeffs) = evalCoeffs x coeffs * x + c := rfl

/-- This is the coefficient-vector evaluation used by the line-test semantics. -/
theorem evalCoeffs_ofFn {R : Type*} [CommSemiring R] (x : R) {n : ℕ}
    (f : Fin n → R) : evalCoeffs x (List.ofFn f) = ∑ i, f i * x ^ (i : ℕ) := by
  induction n with
  | zero => simp [evalCoeffs]
  | succ n ih =>
    rw [List.ofFn_succ, evalCoeffs_cons, ih, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ,
      Finset.sum_mul, mul_assoc]
    exact add_comm _ _

private def hornerStep (s : BitStr × BitStr × BitStr) (c : BitStr) :
    BitStr × BitStr × BitStr :=
  (s.1, s.2.1, xorBits (mulReduce s.1 s.2.2 s.2.1) c)

private theorem hornerStep_width (s : BitStr × BitStr × BitStr) (c : BitStr) :
    (hornerStep s c).2.2.length ≤ s.2.2.length := by
  change (xorBits (mulReduce s.1 s.2.2 s.2.1) c).length ≤ _
  rw [length_xorBits]
  exact (min_le_left _ _).trans (length_mulReduce_le _ _ _)

private theorem fold_hornerStep (l : List BitStr) (s : BitStr × BitStr × BitStr) :
    (l.foldl hornerStep s).1 = s.1 ∧
    (l.foldl hornerStep s).2.1 = s.2.1 ∧
    (l.foldl hornerStep s).2.2.length ≤ s.2.2.length := by
  induction l generalizing s with
  | nil => exact ⟨rfl, rfl, le_rfl⟩
  | cons c l ih =>
    obtain ⟨hp, hx, ha⟩ := ih (hornerStep s c)
    exact ⟨hp, hx, ha.trans (hornerStep_width s c)⟩

private theorem fold_hornerStep_acc (l : List BitStr) (p x a : BitStr) :
    (l.foldl hornerStep (p, x, a)).2.2 =
      l.foldl (fun a c => xorBits (mulReduce p a x) c) a := by
  induction l generalizing a with
  | nil => rfl
  | cons c l ih => exact ih _

private def hornerStepProg :
    PolyTimeFun ((BitStr × BitStr × BitStr) × BitStr) (BitStr × BitStr × BitStr) :=
  let p := fst.comp fst
  let x := fst.comp (snd.comp fst)
  let a := snd.comp (snd.comp fst)
  p.pair (x.pair (xorBitsProg.comp
    ((mulReduceProg.comp (p.pair (a.pair x))).pair snd)))

private theorem hornerStep_bounded : FoldBounded hornerStepProg (5 * X + 5) := by
  intro l s pre post _
  change esize (pre.foldl hornerStep s) ≤ _
  obtain ⟨hp, hx, ha⟩ := fold_hornerStep pre s
  have hi := length_le_esize_list s.2.2
  have ho := esize_bitStr_le (pre.foldl hornerStep s).2.2
  have hs : esize s = esize s.1 + (esize s.2.1 + esize s.2.2 + 1) + 1 := rfl
  change esize (pre.foldl hornerStep s).1 +
    (esize (pre.foldl hornerStep s).2.1 + esize (pre.foldl hornerStep s).2.2 + 1) + 1 ≤ _
  rw [hp, hx]
  simp only [esize_prod, hs, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_X]
  omega

/-- Horner evaluation with an explicit modulus, point and initial accumulator.
The initial accumulator is useful for the correctness induction; ordinary
polynomial evaluation initializes it to the field's zero vector. -/
def hornerFoldProg :
    PolyTimeFun (List BitStr × (BitStr × BitStr × BitStr)) BitStr :=
  congr (((snd.comp snd).comp
      (foldl hornerStepProg (5 * X + 5) hornerStep_bounded)).comp
      ((PolyTimeFun.reverse.comp fst).pair snd))
    (fun z => z.1.foldr (fun c a => xorBits (mulReduce z.2.1 a z.2.2.1) c) z.2.2.2)
    (by
      rintro ⟨l, p, x, a⟩
      change (l.reverse.foldl hornerStep (p, x, a)).2.2 = _
      rw [fold_hornerStep_acc]
      exact List.foldr_eq_foldl_reverse.symm)

/-- One ambient program, uniform in both field width and coefficient count. -/
def shoupHornerProg : PolyTimeFun (Unary × BitStr × List BitStr) BitStr :=
  hornerFoldProg.comp ((snd.comp snd).pair
    ((shoupLowerCoeffs.comp fst).pair
      ((fst.comp snd).pair (shoupZeroProg.comp fst))))

theorem shoupHornerProg_correct (k : ℕ) (hk : 1 ≤ k)
    (x : (shoupBinField k hk).carrier) (coeffs : List (shoupBinField k hk).carrier) :
    shoupHornerProg (unary k, (shoupBinField k hk).toBits x,
      coeffs.map (shoupBinField k hk).toBits) =
      (shoupBinField k hk).toBits (evalCoeffs x coeffs) := by
  change (coeffs.map (shoupBinField k hk).toBits).foldr
    (fun c a => xorBits (mulReduce (shoupLowerCoeffs (unary k)) a
      ((shoupBinField k hk).toBits x)) c) (shoupZeroProg (unary k)) = _
  rw [shoupZeroProg_correct k hk]
  induction coeffs with
  | nil => rfl
  | cons c coeffs ih =>
    rw [List.map_cons, List.foldr_cons, ih]
    change xorBits (shoupMulProg (unary k,
      (shoupBinField k hk).toBits (evalCoeffs x coeffs),
      (shoupBinField k hk).toBits x)) ((shoupBinField k hk).toBits c) = _
    rw [shoupMulProg_encoding, shoupXorBits_correct]
    rfl

/-- Canonical fixed-length vectors evaluate to the expected power sum. -/
theorem shoupHornerProg_ofFn (k : ℕ) (hk : 1 ≤ k) {n : ℕ}
    (x : (shoupBinField k hk).carrier) (f : Fin n → (shoupBinField k hk).carrier) :
    shoupHornerProg (unary k, (shoupBinField k hk).toBits x,
      (shoupBinField k hk).vecBits f) =
      (shoupBinField k hk).toBits (∑ i, f i * x ^ (i : ℕ)) := by
  rw [← evalCoeffs_ofFn]
  simpa only [BinField.vecBits, List.map_ofFn] using shoupHornerProg_correct k hk x (List.ofFn f)

/-- A single polynomial bounds every raw input, including malformed vectors. -/
theorem shoupHornerProg_runs (input : Unary × BitStr × List BitStr) :
    ∃ t ≤ shoupHornerProg.timeBound.eval (esize input),
      shoupHornerProg.code.Runs (encode input) (encode (shoupHornerProg input)) t :=
  shoupHornerProg.computes input

end MIPRE.Introspection.FieldPolynomialProgram
end

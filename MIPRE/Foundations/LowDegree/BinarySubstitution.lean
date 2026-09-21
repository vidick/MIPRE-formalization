/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryNormalize
import MIPRE.Foundations.LowDegree.BinaryComponentsProg

/-! # Polynomial-time substitution of a unary-specified positive power -/

namespace MIPRE.LowDegree.BinaryPolynomial

open Cost Cost.PolyTimeFun Polynomial

/-- Substitute `X^(u.length+1)` by inserting the requested number of zero coefficients.
The exponent is positive by construction; an empty unary parameter means substitution by `X`. -/
def substitutePowerBits (a : BitStr) (u : Unary) : BitStr :=
  normalizeBits (a.flatMap (fun b => b :: List.replicate u.length false))

/-- Substitution has the expected Horner semantics in every commutative ring. -/
theorem evalBits_substitutePowerBits {R : Type*} [CommRing R] (z : R) (a : BitStr) (u : Unary) :
    evalBits z (substitutePowerBits a u) = evalBits (z ^ (u.length + 1)) a := by
  rw [substitutePowerBits, evalBits_normalizeBits]
  induction a with
  | nil => rfl
  | cons b a ih =>
    rw [List.flatMap_cons, evalBits_append, ih]
    simp [evalBits_cons]

/-- The executable substitution agrees with Mathlib polynomial composition. -/
theorem polyOfBits_substitutePowerBits (a : BitStr) (u : Unary) :
    polyOfBits (substitutePowerBits a u) = (polyOfBits a).comp (X ^ (u.length + 1)) := by
  rw [polyOfBits_eq_evalBits, evalBits_substitutePowerBits]
  exact (eval₂_polyOfBits Polynomial.C (X ^ (u.length + 1)) a).symm

/-- The intermediate and final coefficient lengths grow by at most the unary exponent. -/
theorem substitutePowerBits_width (a : BitStr) (u : Unary) :
    (substitutePowerBits a u).length ≤ a.length * (u.length + 1) := by
  apply (length_normalizeBits_le _).trans
  have h : (a.flatMap (fun b => b :: List.replicate u.length false)).length =
      a.length * (u.length + 1) := by
    induction a with
    | nil => simp
    | cons b a ih => simp [ih, Nat.add_mul, Nat.add_comm]; omega
  exact h.le

private noncomputable def coefficientBlockProg : PolyTimeFun (Bool × Unary) BitStr :=
  cons fst (replicate.comp (snd.pair (const false)))

private noncomputable def flattenCoefficientsProg : PolyTimeFun (List BitStr) BitStr :=
  congr ((foldlAdd append X (by
    intro l r
    have h := esize_list_append l r
    simp only [append_apply, eval_X]
    omega)).comp ((PolyTimeFun.id _).pair (const []))) List.flatten (by
      intro l
      change l.foldl (fun a b => a ++ b) [] = l.flatten
      simpa using (List.foldl_append_eq_append (l := l) (l' := []) (f := fun b => b)))

/-- A fixed ambient program for positive-power substitution on arbitrary coefficient lists. -/
noncomputable def substitutePowerBitsProg : PolyTimeFun (BitStr × Unary) BitStr :=
  congr (normalizeBitsProg.comp (flattenCoefficientsProg.comp (mapWith coefficientBlockProg)))
    (fun s => substitutePowerBits s.1 s.2) (by
      intro s
      change normalizeBits (List.flatten (s.1.map
        (fun b => b :: List.replicate s.2.length false))) = _
      simp only [substitutePowerBits, List.flatMap_def])

@[simp] theorem substitutePowerBitsProg_apply (a : BitStr) (u : Unary) :
    substitutePowerBitsProg (a, u) = substitutePowerBits a u := rfl

end MIPRE.LowDegree.BinaryPolynomial

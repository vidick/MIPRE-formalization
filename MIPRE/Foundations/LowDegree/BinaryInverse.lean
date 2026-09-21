/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Cost.Reader
import MIPRE.Foundations.LowDegree.BinaryPower
import MIPRE.Foundations.SAT.QuotientField
import Mathlib.FieldTheory.Finite.Basic

/-! # Uniform inversion in the Shoup polynomial-basis field -/

namespace MIPRE.LowDegree.BinaryPolynomial

open Cost Cost.PolyTimeFun

/-- The exponent `2^k - 2`, written directly in `k` bits rather than expanded in unary. -/
def inverseExponent (p : BitStr) : BitStr := false :: p.tail.map (fun _ => true)

theorem bitsVal_ones (n : ℕ) : bitsVal (List.replicate n true) + 1 = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.replicate_succ, bitsVal_cons, Nat.bit, Bool.cond_true, pow_succ]
    omega

theorem bitsVal_inverseExponent (p : BitStr) :
    bitsVal (inverseExponent p) = 2 ^ p.length - 2 := by
  cases p with
  | nil => rfl
  | cons b p =>
    have h := bitsVal_ones p.length
    have hm : p.map (fun _ => true) = List.replicate p.length true := by simp
    simp only [inverseExponent, List.tail_cons, hm, bitsVal_cons, Nat.bit,
      Bool.cond_false, List.length_cons, pow_succ]
    omega

/-- Inversion by binary exponentiation. Its specification requires a nonzero operand. -/
def inverseBits (p a : BitStr) : BitStr := powerBits p a (inverseExponent p)

theorem length_inverseBits (p a : BitStr) (ha : a.length = p.length) :
    (inverseBits p a).length = p.length := length_powerBits _ _ _ ha

/-- Correctness in every finite characteristic-two field of the supplied cardinality. -/
theorem evalBits_inverseBits {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (z : F) (p a : BitStr) (hp : p ≠ [])
    (hcard : Fintype.card F = 2 ^ p.length)
    (hroot : z ^ p.length = evalBits z p)
    (ha : a.length = p.length) (hne : evalBits z a ≠ 0) :
    evalBits z (inverseBits p a) = (evalBits z a)⁻¹ := by
  rw [inverseBits, evalBits_powerBits z p a _ hp hroot ha, bitsVal_inverseExponent, ← hcard]
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_succ]
  have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
  rw [show Fintype.card F - 2 + 1 = Fintype.card F - 1 by omega]
  exact FiniteField.pow_card_sub_one_eq_one _ hne

noncomputable def inverseExponentProg : PolyTimeFun BitStr BitStr :=
  cons (const false) ((map (const true)).comp tail)

@[simp] theorem inverseExponentProg_apply (p : BitStr) :
    inverseExponentProg p = inverseExponent p := rfl

/-- Globally polynomial-time inversion routine, uniform in the supplied modulus. -/
noncomputable def inverseBitsProg : PolyTimeFun (BitStr × BitStr) BitStr :=
  congr (powerBitsProg.comp (fst.pair (snd.pair (inverseExponentProg.comp fst))))
    (fun a => inverseBits a.1 a.2) (by intro a; rfl)

@[simp] theorem inverseBitsProg_apply (p a : BitStr) :
    inverseBitsProg (p, a) = inverseBits p a := rfl

end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.SAT

open Cost LowDegree LowDegree.BinaryPolynomial

/-- Construct the Shoup modulus and invert a nonzero field element in its power basis. -/
noncomputable def shoupInvProg : PolyTimeFun (Unary × BitStr) BitStr :=
  inverseBitsProg.comp ((shoupLowerCoeffs.comp PolyTimeFun.fst).pair PolyTimeFun.snd)

theorem shoupInvProg_correct (k : ℕ) (hk : 1 ≤ k)
    (a : (shoupBinField k hk).carrier) (ha : a ≠ 0) :
    shoupInvProg (unary k, (shoupBinField k hk).toBits a) =
      (shoupBinField k hk).toBits a⁻¹ := by
  have hp : shoupLowerCoeffs (unary k) ≠ [] := by
    intro he
    have := shoupLowerCoeffs_length k hk
    rw [he] at this
    simp only [List.length_nil] at this
    omega
  have hwidth : ((shoupBinField k hk).toBits a).length =
      (shoupLowerCoeffs (unary k)).length := by
    rw [(shoupBinField k hk).length_toBits, shoupLowerCoeffs_length k hk]
  have hi := evalBits_inverseBits (shoupRoot k hk) (shoupLowerCoeffs (unary k))
    ((shoupBinField k hk).toBits a) hp
    (by rw [shoupLowerCoeffs_length k hk]; exact (shoupBinField k hk).card_carrier)
    (shoupRoot_equation k hk) hwidth (by rwa [shoupRoot_eval_toBits])
  apply (shoupRoot_eval_eq_iff k hk _ _
    ((length_inverseBits _ _ hwidth).trans (shoupLowerCoeffs_length k hk))
    ((shoupBinField k hk).length_toBits _)).mp
  rw [shoupRoot_eval_toBits]
  simpa only [shoupRoot_eval_toBits] using hi

/-- Including construction of the modulus, inversion takes polynomial time in the degree. -/
theorem shoupInvProg_time_le : ∃ R : Polynomial ℕ, ∀ k : ℕ, ∀ a : BitStr,
    a.length = k → ∃ t ≤ R.eval k,
      shoupInvProg.code.Runs (encode (unary k, a))
        (encode (shoupInvProg (unary k, a))) t := by
  refine ⟨shoupInvProg.timeBound.comp (6 * Polynomial.X + 3), fun k a ha => ?_⟩
  obtain ⟨t, ht, hr⟩ := shoupInvProg.computes (unary k, a)
  refine ⟨t, ht.trans ?_, hr⟩
  have hsize : esize (unary k, a) ≤ 6 * k + 3 := by
    have h := esize_bitStr_le a
    simp only [esize_prod, esize_unary]
    rw [ha] at h
    omega
  simpa using polynomial_eval_mono shoupInvProg.timeBound hsize

end MIPRE.SAT

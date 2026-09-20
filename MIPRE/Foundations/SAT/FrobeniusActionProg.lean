/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.SAT.FrobeniusAction
import MIPRE.Foundations.SAT.FrobeniusMatrix
import MIPRE.Foundations.LowDegree.BinaryComponentsProg

/-! # Uniform programs for Frobenius orbits and cyclic operators -/

noncomputable section

namespace MIPRE.SAT

open Cost Cost.PolyTimeFun LowDegree LowDegree.BinaryLinear Polynomial

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

def shoupSquareStateProg : PolyTimeFun (Unary × BitStr) (Unary × BitStr) :=
  fst.pair shoupSquareProg

theorem shoupSquareProg_length_le (u : Unary) (v : BitStr) :
    (shoupSquareProg (u, v)).length ≤ v.length :=
  BinaryPolynomial.length_mulReduce_le _ _ _

theorem shoupSquareStateProg_iterate_width (n : ℕ) (s : Unary × BitStr) :
    ((shoupSquareStateProg : (Unary × BitStr) → (Unary × BitStr))^[n] s).1 = s.1 ∧
    ((shoupSquareStateProg : (Unary × BitStr) → (Unary × BitStr))^[n] s).2.length ≤ s.2.length := by
  induction n with
  | zero => exact ⟨rfl, le_rfl⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨ih.1, (shoupSquareProg_length_le _ _).trans ih.2⟩

theorem shoupSquareStateProg_iterate_size (n : ℕ) (s : Unary × BitStr) :
    esize ((shoupSquareStateProg : (Unary × BitStr) → (Unary × BitStr))^[n] s) ≤
      (5 * X + 5 : Polynomial ℕ).eval (esize s) := by
  obtain ⟨hu, hv⟩ := shoupSquareStateProg_iterate_width n s
  have hs := esize_bitStr_le
    ((shoupSquareStateProg : (Unary × BitStr) → (Unary × BitStr))^[n] s).2
  have hi := length_le_esize_bitStr s.2
  have hp : esize s = esize s.1 + esize s.2 + 1 := rfl
  rw [esize_prod, hu]
  simp only [eval_add, eval_mul, eval_ofNat, eval_X, esize_prod]
  omega

theorem shoupSquareStateProg_iterate_correct (k : ℕ) (hk : 1 ≤ k)
    (a : (shoupBinField k hk).carrier) (n : ℕ) :
    ((shoupSquareStateProg : (Unary × BitStr) → (Unary × BitStr))^[n]
      (unary k, (shoupBinField k hk).toBits a)) =
    (unary k, (shoupBinField k hk).toBits (a ^ (2 ^ n))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    change (unary k, shoupSquareProg (unary k, (shoupBinField k hk).toBits (a ^ (2 ^ n)))) = _
    rw [shoupSquareProg_correct, shoupFrobeniusLinear_apply, ← pow_mul, ← pow_succ]

/-- Print exactly `k` successive Frobenius powers of an encoded field element. -/
def shoupOrbitProg : PolyTimeFun (Unary × BitStr) (List BitStr) :=
  (map snd).comp ((recordIteratesProg shoupSquareStateProg (5 * X + 5)
    shoupSquareStateProg_iterate_size).comp (fst.pair (PolyTimeFun.id _)))

theorem shoupOrbitProg_correct (k : ℕ) (hk : 1 ≤ k) (a : (shoupBinField k hk).carrier) :
    shoupOrbitProg (unary k, (shoupBinField k hk).toBits a) =
      List.ofFn (fun i : Fin k => (shoupBinField k hk).toBits (a ^ (2 ^ i.val))) := by
  change (recordIterates (shoupSquareStateProg : (Unary × BitStr) → (Unary × BitStr))
    (unary k) (unary k, (shoupBinField k hk).toBits a)).map Prod.snd = _
  simp only [recordIterates, length_unary, List.map_ofFn, shoupSquareStateProg_iterate_correct]
  rfl

/-- Evaluate a linearized polynomial from its cyclic coefficient vector. -/
def shoupActionProg : PolyTimeFun (Unary × BitStr × BitStr) BitStr :=
  let orbit := shoupOrbitProg.comp (fst.pair (snd.comp snd))
  applyBitsProg.comp ((transposeBitsProg.comp (fst.pair orbit)).pair (fst.comp snd))

theorem shoupActionProg_correct (k : ℕ) (hk : 1 ≤ k) [NeZero k]
    (z : AddMonoidAlgebra (ZMod 2) (Fin k)) (a : (shoupBinField k hk).carrier) :
    shoupActionProg (unary k, vectorBits (groupCoordinates k z), (shoupBinField k hk).toBits a) =
      (shoupBinField k hk).toBits (shoupFrobeniusAction k hk z a) := by
  let A : Matrix (Fin k) (Fin k) (ZMod 2) :=
    fun j i => shoupCoordinateEquiv k hk (a ^ (2 ^ j.val)) i
  have ho : shoupOrbitProg (unary k, (shoupBinField k hk).toBits a) = matrixBits A := by
    rw [shoupOrbitProg_correct]
    unfold matrixBits
    congr 1
    funext j
    exact (shoupCoordinateEquiv_encoding k hk _).symm
  change applyBits (transposeBits (unary k).length
    (shoupOrbitProg (unary k, (shoupBinField k hk).toBits a)))
      (vectorBits (groupCoordinates k z)) = _
  rw [length_unary, ho, transposeBits_matrixBits, applyBits_matrixBits,
    ← shoupCoordinateEquiv_encoding, shoupFrobeniusAction_apply, map_sum]
  congr 1
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.sum_apply,
    map_smul, Pi.smul_apply, smul_eq_mul, A, groupCoordinates_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

end MIPRE.SAT

end

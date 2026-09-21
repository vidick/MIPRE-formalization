/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.SAT.FieldCoordinates
import MIPRE.Foundations.LowDegree.BinaryMatrixInverse

/-! # Effective trace Gram matrices -/

noncomputable section

namespace MIPRE.SAT

open Cost LowDegree LowDegree.BinaryLinear LowDegree.BinaryPolynomial

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- The actual coefficient-vector representation of the unit. -/
theorem shoupBinField_oneBits (k : ℕ) (hk : 1 ≤ k) (v : BitStr) (hv : v.length = k) :
    BinaryPolynomial.oneBits v = (shoupBinField k hk).toBits 1 := by
  apply (shoupRoot_eval_eq_iff k hk _ _ (by simpa using hv)
    ((shoupBinField k hk).length_toBits _)).mp
  rw [shoupRoot_eval_toBits, BinaryPolynomial.evalBits_oneBits]
  intro he
  simp only [he, List.length_nil] at hv
  omega

/-- Output the trace as one base-field bit, rather than an extension-field vector. -/
def shoupTraceBitProg : PolyTimeFun (Unary × BitStr) Bool :=
  ArrayProg.eqBits.comp (shoupTraceProg.pair (BinaryPolynomial.oneBitsProg.comp PolyTimeFun.snd))

theorem shoupTraceBitProg_correct (k : ℕ) (hk : 1 ≤ k)
    (a : (shoupBinField k hk).carrier) :
    shoupTraceBitProg (unary k, (shoupBinField k hk).toBits a) =
      bit (Algebra.trace (ZMod 2) (shoupBinField k hk).carrier a) := by
  change decide (shoupTraceProg (unary k, (shoupBinField k hk).toBits a) =
    BinaryPolynomial.oneBits ((shoupBinField k hk).toBits a)) = _
  rw [shoupTraceProg_correct, shoupBinField_oneBits k hk _ ((shoupBinField k hk).length_toBits a)]
  have hi : Function.Injective (shoupBinField k hk).toBits := by
    intro x y h
    have hh := congrArg (shoupBinField k hk).ofBits h
    simpa only [(shoupBinField k hk).ofBits_toBits] using hh
  unfold bit
  have he : (shoupBinField k hk).toBits
      (algebraMap (ZMod 2) (shoupBinField k hk).carrier
        (Algebra.trace (ZMod 2) (shoupBinField k hk).carrier a)) =
      (shoupBinField k hk).toBits 1 ↔
      Algebra.trace (ZMod 2) (shoupBinField k hk).carrier a = 1 := by
    rw [hi.eq_iff, ← map_one (algebraMap (ZMod 2) (shoupBinField k hk).carrier)]
    exact (algebraMap (ZMod 2) (shoupBinField k hk).carrier).injective.eq_iff
  simp only [he]

/-- The binary trace Gram matrix of any finite field-vector family. -/
def shoupTraceGram (k : ℕ) (hk : 1 ≤ k) {n : ℕ}
    (v : Fin n → (shoupBinField k hk).carrier) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun i j => Algebra.trace (ZMod 2) (shoupBinField k hk).carrier (v i * v j)

/-- Construct the full trace Gram matrix of a supplied family. -/
def shoupTraceGramProg : PolyTimeFun (Unary × List BitStr) (List BitStr) :=
  let pairTrace : PolyTimeFun (Unary × BitStr × BitStr) Bool :=
    shoupTraceBitProg.comp (PolyTimeFun.fst.pair shoupMulProg)
  let entry : PolyTimeFun (BitStr × Unary × BitStr) Bool :=
    pairTrace.comp ((PolyTimeFun.fst.comp PolyTimeFun.snd).pair
      ((PolyTimeFun.snd.comp PolyTimeFun.snd).pair PolyTimeFun.fst))
  let row : PolyTimeFun (BitStr × Unary × List BitStr) BitStr :=
    (PolyTimeFun.mapWith entry).comp ((PolyTimeFun.snd.comp PolyTimeFun.snd).pair
      ((PolyTimeFun.fst.comp PolyTimeFun.snd).pair PolyTimeFun.fst))
  (PolyTimeFun.mapWith row).comp
    (PolyTimeFun.snd.pair (PolyTimeFun.fst.pair PolyTimeFun.snd))

/-- Every printed entry is the algebraic trace of the corresponding product. -/
theorem shoupTraceGramProg_correct (k : ℕ) (hk : 1 ≤ k) {n : ℕ}
    (v : Fin n → (shoupBinField k hk).carrier) :
    shoupTraceGramProg (unary k, List.ofFn (fun i => (shoupBinField k hk).toBits (v i))) =
      matrixBits (shoupTraceGram k hk v) := by
  change (List.ofFn (fun i => (shoupBinField k hk).toBits (v i))).map (fun a =>
    (List.ofFn (fun j => (shoupBinField k hk).toBits (v j))).map (fun b =>
      shoupTraceBitProg (unary k, shoupMulProg (unary k, a, b)))) = _
  simp only [List.map_ofFn, matrixBits]
  apply congrArg List.ofFn
  funext i
  simp only [Function.comp_apply, List.map_ofFn, vectorBits]
  apply congrArg List.ofFn
  funext j
  change shoupTraceBitProg (unary k,
    shoupMulProg (unary k, (shoupBinField k hk).toBits (v i),
      (shoupBinField k hk).toBits (v j))) = _
  rw [shoupMulProg_encoding, shoupTraceBitProg_correct]
  rfl

/-- A basis has a nonsingular trace Gram matrix. -/
theorem shoupTraceGram_surjective (k : ℕ) (hk : 1 ≤ k)
    (b : Module.Basis (Fin k) (ZMod 2) (shoupBinField k hk).carrier) :
    Function.Surjective (shoupTraceGram k hk b).mulVec := by
  change Function.Surjective (shoupTraceGram k hk b).mulVecLin
  apply LinearMap.surjective_of_injective
  intro x y h
  apply sub_eq_zero.mp
  have hh : (shoupTraceGram k hk b).mulVecLin (x - y) = 0 := by
    rw [map_sub, show (shoupTraceGram k hk b).mulVecLin x =
      (shoupTraceGram k hk b).mulVecLin y from h, sub_self]
  let z := ∑ j : Fin k, (x - y) j • b j
  have hz : z = 0 := by
    apply (traceForm_nondegenerate (ZMod 2) (shoupBinField k hk).carrier).1 z
    intro w
    have hpair (i : Fin k) :
        Algebra.trace (ZMod 2) (shoupBinField k hk).carrier (b i * z) = 0 := by
      have hc := congrFun hh i
      simpa only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, shoupTraceGram,
        z, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, smul_eq_mul, mul_comm,
        Pi.zero_apply] using hc
    rw [Algebra.traceForm_apply, ← b.sum_repr w, Finset.mul_sum, map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [mul_smul_comm, map_smul, mul_comm z (b i), hpair, smul_zero]
  funext j
  have hrepr := congrArg (fun a => b.repr a j) hz
  simpa [z, Finsupp.single_apply] using hrepr

/-- Compute the inverse trace Gram matrix of a basis. -/
def shoupInverseGramProg : PolyTimeFun (Unary × List BitStr) (List BitStr) :=
  inverseMatrixProg.comp (PolyTimeFun.fst.pair shoupTraceGramProg)

theorem shoupInverseGramProg_correct (k : ℕ) (hk : 1 ≤ k)
    (b : Module.Basis (Fin k) (ZMod 2) (shoupBinField k hk).carrier) :
    mulBits k (matrixBits (shoupTraceGram k hk b))
        (shoupInverseGramProg (unary k, List.ofFn (fun i => (shoupBinField k hk).toBits (b i)))) =
      identityBits k ∧
    mulBits k (shoupInverseGramProg (unary k, List.ofFn (fun i => (shoupBinField k hk).toBits (b i))))
        (matrixBits (shoupTraceGram k hk b)) = identityBits k := by
  change mulBits k _ (inverseMatrixProg (unary k, shoupTraceGramProg _)) = _ ∧
    mulBits k (inverseMatrixProg (unary k, shoupTraceGramProg _)) _ = _
  rw [shoupTraceGramProg_correct]
  exact inverseMatrixProg_correct _ (shoupTraceGram_surjective k hk b)

end MIPRE.SAT

end

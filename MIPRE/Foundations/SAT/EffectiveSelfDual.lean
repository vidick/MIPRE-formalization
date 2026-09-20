/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.SAT.NormalGram
import MIPRE.Foundations.SAT.BasisTransport
import MIPRE.Foundations.LowDegree.BinaryCirculantProg

/-! # Effective self-dualization of a supplied normal basis -/

noncomputable section

namespace MIPRE.SAT

open Cost LowDegree LowDegree.BinaryLinear

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- Apply a binary matrix to the columns of a supplied field basis. -/
def shoupChangedVectors (k : ℕ) (hk : 1 ≤ k)
    (b : Module.Basis (Fin k) (ZMod 2) (shoupBinField k hk).carrier)
    (H : Matrix (Fin k) (Fin k) (ZMod 2)) : Fin k → (shoupBinField k hk).carrier :=
  fun i => ∑ j, H j i • b j

/-- Basis changes transform the trace Gram matrix by the usual congruence. -/
theorem shoupChangedVectors_gram (k : ℕ) (hk : 1 ≤ k)
    (b : Module.Basis (Fin k) (ZMod 2) (shoupBinField k hk).carrier)
    (H : Matrix (Fin k) (Fin k) (ZMod 2)) :
    shoupTraceGram k hk (shoupChangedVectors k hk b H) =
      H.transpose * shoupTraceGram k hk b * H := by
  ext i j
  simp only [shoupTraceGram, shoupChangedVectors, Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm, map_sum, map_smul, smul_eq_mul,
    Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  ring

/-- An identity trace Gram matrix proves linear independence. -/
theorem shoupTraceGram_one_linearIndependent (k : ℕ) (hk : 1 ≤ k)
    (v : Fin k → (shoupBinField k hk).carrier) (hv : shoupTraceGram k hk v = 1) :
    LinearIndependent (ZMod 2) v := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have h := congrArg (fun a => Algebra.trace (ZMod 2) (shoupBinField k hk).carrier (a * v j)) hc
  simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_smul, smul_eq_mul,
    zero_mul, map_zero] at h
  have hg (i : Fin k) : Algebra.trace (ZMod 2) (shoupBinField k hk).carrier (v i * v j) =
      if i = j then 1 else 0 := congrArg (fun A => A i j) hv
  simpa only [hg, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] using h

/-- A circulant change of coordinates preserves the orbit form of a normal basis. -/
theorem shoupChangedVectors_normal (k : ℕ) (hk : 1 ≤ k) [NeZero k]
    (b : Module.Basis (Fin k) (ZMod 2) (shoupBinField k hk).carrier)
    (hb : IsNormalBasis b) (h : Fin k → ZMod 2) :
    ∃ a, ∀ i : Fin k, shoupChangedVectors k hk b (Matrix.circulant h) i = a ^ (2 ^ i.val) := by
  obtain ⟨a, ha⟩ := hb
  have hb' (j : Fin k) : b j = shoupFrobeniusCycle k hk (Multiplicative.ofAdd j) a := by
    rw [ha, shoupFrobeniusCycle_apply]
    simp
  have hact (i j : Fin k) :
      shoupFrobeniusCycle k hk (Multiplicative.ofAdd i) (b j) = b (j + i) := by
    rw [hb', hb', ← AlgEquiv.mul_apply, ← map_mul]
    have he : Multiplicative.ofAdd i * Multiplicative.ofAdd j =
        Multiplicative.ofAdd (j + i) := congrArg Multiplicative.ofAdd (add_comm i j)
    rw [he]
  refine ⟨shoupChangedVectors k hk b (Matrix.circulant h) 0, fun i => ?_⟩
  rw [← shoupFrobeniusCycle_apply k hk i]
  simp only [shoupChangedVectors, Matrix.circulant_apply, sub_zero, map_sum,
    map_smul, hact]
  symm
  apply Fintype.sum_bijective (fun j : Fin k => j + i) (Equiv.addRight i).bijective
  intro j
  simp

/-- The self-dualizing vectors computed from a supplied normal basis. -/
def shoupSelfDualVectors (k : ℕ) (hk : 1 ≤ k) [NeZero k]
    (b : Module.Basis (Fin k) (ZMod 2) (shoupBinField k hk).carrier) :
    Fin k → (shoupBinField k hk).carrier :=
  shoupChangedVectors k hk b (inverseRootMatrix (shoupTraceGram k hk b))

theorem shoupSelfDualVectors_gram (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (b : Module.Basis (Fin k) (ZMod 2) (shoupBinField k hk).carrier)
    (hb : IsNormalBasis b) : shoupTraceGram k hk (shoupSelfDualVectors k hk b) = 1 := by
  rw [shoupSelfDualVectors, shoupChangedVectors_gram]
  exact shoupNormalGram_selfDualize k hk hodd b hb

/-- Self-dualization gives an actual basis with exactly the computed vectors. -/
def shoupSelfDualBasis (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (b : Module.Basis (Fin k) (ZMod 2) (shoupBinField k hk).carrier)
    (hb : IsNormalBasis b) : Module.Basis (Fin k) (ZMod 2) (shoupBinField k hk).carrier :=
  basisOfLinearIndependentOfCardEqFinrank
    (shoupTraceGram_one_linearIndependent k hk _ (shoupSelfDualVectors_gram k hk hodd b hb))
    (by simp [shoupBinField_finrank k hk])

theorem shoupSelfDualBasis_apply (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (b : Module.Basis (Fin k) (ZMod 2) (shoupBinField k hk).carrier)
    (hb : IsNormalBasis b) (i : Fin k) :
    shoupSelfDualBasis k hk hodd b hb i = shoupSelfDualVectors k hk b i := by
  rw [shoupSelfDualBasis, coe_basisOfLinearIndependentOfCardEqFinrank]

theorem shoupSelfDualBasis_selfDual (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (b : Module.Basis (Fin k) (ZMod 2) (shoupBinField k hk).carrier)
    (hb : IsNormalBasis b) : IsSelfDualBasis (shoupSelfDualBasis k hk hodd b hb) := by
  intro i j
  rw [shoupSelfDualBasis_apply, shoupSelfDualBasis_apply]
  exact congrArg (fun A => A i j) (shoupSelfDualVectors_gram k hk hodd b hb)

theorem shoupSelfDualBasis_normal (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (b : Module.Basis (Fin k) (ZMod 2) (shoupBinField k hk).carrier)
    (hb : IsNormalBasis b) : IsNormalBasis (shoupSelfDualBasis k hk hodd b hb) := by
  obtain ⟨a, ha⟩ := shoupChangedVectors_normal k hk b hb
    (fun i => inverseMatrix (shoupTraceGram k hk b) (i + i) 0)
  refine ⟨a, fun i => ?_⟩
  rw [shoupSelfDualBasis_apply]
  simpa only [shoupSelfDualVectors, inverseRootMatrix, Fintype.card_fin, ZMod.card] using ha i

/-- Polynomial-basis coordinates of the changed family are the matrix product columns. -/
theorem shoupChangedVectors_encoding (k : ℕ) (hk : 1 ≤ k)
    (b : Module.Basis (Fin k) (ZMod 2) (shoupBinField k hk).carrier)
    (H : Matrix (Fin k) (Fin k) (ZMod 2)) (j : Fin k) :
    (shoupBinField k hk).toBits (shoupChangedVectors k hk b H j) =
      vectorBits ((shoupBasisMatrix k hk b * H).col j) := by
  rw [← shoupCoordinateEquiv_encoding]
  congr 1
  funext i
  simp only [shoupChangedVectors, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Matrix.col_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro r _
  rw [shoupBasisMatrix, LinearMap.toMatrix_apply]
  exact mul_comm _ _

/-- Construct and apply the inverse Gram square root, returning the new basis vectors. -/
def shoupSelfDualizeProg : PolyTimeFun (Unary × List BitStr) (List BitStr) :=
  let root := inverseRootMatrixProg.comp (PolyTimeFun.fst.pair shoupTraceGramProg)
  let product := mulBitsProg.comp (PolyTimeFun.fst.pair (transposeBitsProg.pair root))
  transposeBitsProg.comp (PolyTimeFun.fst.pair product)

/-- Every output vector is the canonical encoding of the constructed self-dual normal basis. -/
theorem shoupSelfDualizeProg_correct (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (b : Module.Basis (Fin k) (ZMod 2) (shoupBinField k hk).carrier)
    (hb : IsNormalBasis b) :
    shoupSelfDualizeProg (unary k, List.ofFn (fun i => (shoupBinField k hk).toBits (b i))) =
      List.ofFn (fun i => (shoupBinField k hk).toBits (shoupSelfDualBasis k hk hodd b hb i)) := by
  change transposeBits (unary k).length (mulBits (unary k).length
    (transposeBits (unary k).length (List.ofFn (fun i => (shoupBinField k hk).toBits (b i))))
    (inverseRootMatrixProg (unary k, shoupTraceGramProg
      (unary k, List.ofFn (fun i => (shoupBinField k hk).toBits (b i)))))) = _
  rw [length_unary, shoupBasisMatrix_encoding, shoupTraceGramProg_correct,
    inverseRootMatrixProg_correct hodd, mulBits_matrixBits, transposeBits_matrixBits]
  apply congrArg List.ofFn
  funext i
  rw [shoupSelfDualBasis_apply]
  exact (shoupChangedVectors_encoding k hk b _ i).symm

/-- The complete change of basis, including its Gram inverse, has polynomial runtime. -/
theorem shoupSelfDualizeProg_time_le : ∃ R : Polynomial ℕ, ∀ k : ℕ, ∀ hk : 1 ≤ k,
    ∀ b : Module.Basis (Fin k) (ZMod 2) (shoupBinField k hk).carrier,
    ∃ t ≤ R.eval k, shoupSelfDualizeProg.code.Runs
      (encode (unary k, List.ofFn (fun i => (shoupBinField k hk).toBits (b i))))
      (encode (shoupSelfDualizeProg
        (unary k, List.ofFn (fun i => (shoupBinField k hk).toBits (b i))))) t := by
  refine ⟨shoupSelfDualizeProg.timeBound.comp
    (4 * Polynomial.X ^ 2 + 4 * Polynomial.X + 3), fun k hk b => ?_⟩
  obtain ⟨t, ht, hr⟩ := shoupSelfDualizeProg.computes
    (unary k, List.ofFn (fun i => (shoupBinField k hk).toBits (b i)))
  refine ⟨t, ht.trans ?_, hr⟩
  have hs : esize (unary k, List.ofFn (fun i => (shoupBinField k hk).toBits (b i))) ≤
      4 * k ^ 2 + 4 * k + 3 := by
    rw [esize_prod, esize_unary]
    have h := esize_shoupBasis k hk b
    nlinarith
  simpa using polynomial_eval_mono shoupSelfDualizeProg.timeBound hs

end MIPRE.SAT

end

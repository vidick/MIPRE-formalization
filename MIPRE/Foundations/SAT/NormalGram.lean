/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.SAT.TraceGram
import MIPRE.Foundations.LowDegree.BinaryCirculant
import MIPRE.Foundations.LowDegree.NormalBasis

/-! # The circulant Gram matrix of a supplied normal basis -/

noncomputable section

namespace MIPRE.SAT

open Cost LowDegree LowDegree.BinaryLinear

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- The cyclic Frobenius action with exactly the degree as its index modulus. -/
def shoupFrobeniusCycle (k : ℕ) (hk : 1 ≤ k) [NeZero k] :
    Multiplicative (Fin k) →* ((shoupBinField k hk).carrier ≃ₐ[ZMod 2]
      (shoupBinField k hk).carrier) where
  toFun i := FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2)
    (shoupBinField k hk).carrier ^ (Multiplicative.toAdd i).val
  map_one' := by simp
  map_mul' i j := by
    change _ ^ ((Multiplicative.toAdd i + Multiplicative.toAdd j).val) = _
    rw [Fin.val_add]
    have ho := FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic (ZMod 2)
      (shoupBinField k hk).carrier
    rw [shoupBinField_finrank k hk] at ho
    have hm := pow_mod_orderOf (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2)
      (shoupBinField k hk).carrier) ((Multiplicative.toAdd i).val + (Multiplicative.toAdd j).val)
    rw [ho] at hm
    rw [hm, pow_add]

/-- The finite cyclic action agrees with the Frobenius powers used in normality. -/
theorem shoupFrobeniusCycle_apply (k : ℕ) (hk : 1 ≤ k) [NeZero k]
    (i : Fin k) (a : (shoupBinField k hk).carrier) :
    shoupFrobeniusCycle k hk (Multiplicative.ofAdd i) a = a ^ (2 ^ i.val) := by
  change (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2)
    (shoupBinField k hk).carrier ^ i.val) a = _
  rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
  simp

/-- A normal basis's Gram matrix is the circulant determined by its first column. -/
theorem shoupTraceGram_normal_circulant (k : ℕ) (hk : 1 ≤ k) [NeZero k]
    (b : Module.Basis (Fin k) (ZMod 2) (shoupBinField k hk).carrier)
    (hb : IsNormalBasis b) :
    shoupTraceGram k hk b = Matrix.circulant (fun i => shoupTraceGram k hk b i 0) := by
  obtain ⟨a, ha⟩ := hb
  have hb' (i : Fin k) : b i = shoupFrobeniusCycle k hk (Multiplicative.ofAdd i) a := by
    rw [ha, shoupFrobeniusCycle_apply]
    simp
  have hdiff (i j : Fin k) :
      (shoupFrobeniusCycle k hk (Multiplicative.ofAdd j))⁻¹ *
        shoupFrobeniusCycle k hk (Multiplicative.ofAdd i) =
      shoupFrobeniusCycle k hk (Multiplicative.ofAdd (i - j)) := by
    rw [← map_inv, ← map_mul]
    congr 1
    change Multiplicative.ofAdd (-j + i) = _
    rw [sub_eq_add_neg, add_comm]
  ext i j
  change Algebra.trace (ZMod 2) (shoupBinField k hk).carrier (b i * b j) =
    Algebra.trace (ZMod 2) (shoupBinField k hk).carrier (b (i - j) * b 0)
  rw [mul_comm (b i) (b j), hb', hb', trace_orbit, hdiff, hb', hb']
  simp only [show Multiplicative.ofAdd (0 : Fin k) = 1 from rfl, map_one,
    AlgEquiv.one_apply, mul_comm]

/-- The normal Gram matrix is a concretely identified group-algebra matrix. -/
def shoupNormalGramElement (k : ℕ) (hk : 1 ≤ k) [NeZero k]
    (b : Module.Basis (Fin k) (ZMod 2) (shoupBinField k hk).carrier) :
    AddMonoidAlgebra (ZMod 2) (Fin k) :=
  finGroupOfVector (fun i => shoupTraceGram k hk b i 0)

theorem shoupNormalGramElement_matrix (k : ℕ) (hk : 1 ≤ k) [NeZero k]
    (b : Module.Basis (Fin k) (ZMod 2) (shoupBinField k hk).carrier)
    (hb : IsNormalBasis b) :
    groupMatrix (shoupNormalGramElement k hk b) = shoupTraceGram k hk b := by
  calc
    groupMatrix (shoupNormalGramElement k hk b) =
        Matrix.circulant (fun i => shoupTraceGram k hk b i 0) := by
      ext i j
      simp [groupMatrix, shoupNormalGramElement]
    _ = shoupTraceGram k hk b := (shoupTraceGram_normal_circulant k hk b hb).symm

/-- The doubled-index inverse square root gives the required Gram identity for any normal basis. -/
theorem shoupNormalGram_selfDualize (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (b : Module.Basis (Fin k) (ZMod 2) (shoupBinField k hk).carrier)
    (hb : IsNormalBasis b) :
    (inverseRootMatrix (shoupTraceGram k hk b)).transpose * shoupTraceGram k hk b *
      inverseRootMatrix (shoupTraceGram k hk b) = 1 := by
  have he := shoupNormalGramElement_matrix k hk b hb
  have hs : (shoupTraceGram k hk b).IsSymm := by
    ext i j
    simp [shoupTraceGram, mul_comm]
  rw [← he] at hs ⊢
  apply inverseRootMatrix_gram hodd _ _ hs
  rw [he]
  exact shoupTraceGram_surjective k hk b

end MIPRE.SAT

end

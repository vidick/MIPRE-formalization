/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.SAT.FieldCoordinates

/-! # Computing binary matrices of field maps and of Frobenius -/

noncomputable section

namespace MIPRE.SAT

open Cost LowDegree LowDegree.BinaryLinear LowDegree.BinaryPolynomial

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- Compute a field map on the polynomial basis, then transpose the column list. -/
def fieldMapMatrixProg (f : PolyTimeFun (Unary × BitStr) BitStr) :
    PolyTimeFun Unary (List BitStr) :=
  let columns := (PolyTimeFun.mapWith (f.comp (PolyTimeFun.snd.pair PolyTimeFun.fst))).comp
    (identityBitsProg.pair (PolyTimeFun.id _))
  transposeBitsProg.comp ((PolyTimeFun.id _).pair columns)

/-- A canonically encoded linear map gives its exact matrix in the effective basis. -/
theorem fieldMapMatrixProg_correct (k : ℕ) (hk : 1 ≤ k)
    (L : (shoupBinField k hk).carrier →ₗ[ZMod 2] (shoupBinField k hk).carrier)
    (f : PolyTimeFun (Unary × BitStr) BitStr)
    (hf : ∀ a, f (unary k, (shoupBinField k hk).toBits a) =
      (shoupBinField k hk).toBits (L a)) :
    fieldMapMatrixProg f (unary k) =
      matrixBits (LinearMap.toMatrix (shoupPowerBasis k hk) (shoupPowerBasis k hk) L) := by
  let A := LinearMap.toMatrix (shoupPowerBasis k hk) (shoupPowerBasis k hk) L
  have hc : (identityBits k).map (fun v => f (unary k, v)) = matrixBits A.transpose := by
    apply List.ext_getElem
    · simp [identityBits, matrixBits]
    · intro j hj hj'
      have hjk : j < k := by simpa [identityBits] using hj
      simp only [identityBits, List.getElem_map, List.getElem_range, matrixBits,
        List.getElem_ofFn]
      rw [← shoupPowerBasis_encoding k hk (⟨j, hjk⟩ : Fin k), hf,
        ← shoupCoordinateEquiv_encoding]
      congr 1
      funext i
      exact (LinearMap.toMatrix_apply (shoupPowerBasis k hk) (shoupPowerBasis k hk)
        L i ⟨j, hjk⟩).symm
  change transposeBits (unary k).length
    ((identityBits (unary k).length).map (fun v => f (unary k, v))) = _
  rw [length_unary, hc, transposeBits_matrixBits, Matrix.transpose_transpose]

/-- Frobenius as a binary linear map on the concrete quotient field. -/
def shoupFrobeniusLinear (k : ℕ) (hk : 1 ≤ k) :
    (shoupBinField k hk).carrier →ₗ[ZMod 2] (shoupBinField k hk).carrier :=
  (FiniteField.frobeniusAlgHom (ZMod 2) (shoupBinField k hk).carrier).toLinearMap

@[simp] theorem shoupFrobeniusLinear_apply (k : ℕ) (hk : 1 ≤ k)
    (a : (shoupBinField k hk).carrier) : shoupFrobeniusLinear k hk a = a ^ 2 := by
  simp [shoupFrobeniusLinear, FiniteField.frobeniusAlgHom]

/-- Frobenius in the actual polynomial-basis coordinates. -/
def shoupFrobeniusMatrix (k : ℕ) (hk : 1 ≤ k) : Matrix (Fin k) (Fin k) (ZMod 2) :=
  LinearMap.toMatrix (shoupPowerBasis k hk) (shoupPowerBasis k hk)
    (shoupFrobeniusLinear k hk)

/-- One squaring, including uniform modulus construction. -/
def shoupSquareProg : PolyTimeFun (Unary × BitStr) BitStr :=
  shoupMulProg.comp (PolyTimeFun.fst.pair (PolyTimeFun.snd.pair PolyTimeFun.snd))

theorem shoupSquareProg_correct (k : ℕ) (hk : 1 ≤ k)
    (a : (shoupBinField k hk).carrier) :
    shoupSquareProg (unary k, (shoupBinField k hk).toBits a) =
      (shoupBinField k hk).toBits (shoupFrobeniusLinear k hk a) := by
  change shoupMulProg (unary k, (shoupBinField k hk).toBits a,
    (shoupBinField k hk).toBits a) = _
  rw [shoupMulProg_encoding, shoupFrobeniusLinear_apply, pow_two]

/-- One polynomial-time program constructs the full binary Frobenius matrix. -/
def shoupFrobeniusMatrixProg : PolyTimeFun Unary (List BitStr) :=
  fieldMapMatrixProg shoupSquareProg

theorem shoupFrobeniusMatrixProg_correct (k : ℕ) (hk : 1 ≤ k) :
    shoupFrobeniusMatrixProg (unary k) = matrixBits (shoupFrobeniusMatrix k hk) :=
  fieldMapMatrixProg_correct k hk _ _ (shoupSquareProg_correct k hk)

/-- The full field degree is the degree of Frobenius's minimal polynomial. -/
theorem shoupFrobeniusMatrix_minpoly (k : ℕ) (hk : 1 ≤ k) :
    minpoly (ZMod 2) (shoupFrobeniusMatrix k hk) = Polynomial.X ^ k - 1 := by
  change minpoly (ZMod 2) ((LinearMap.toMatrixAlgEquiv (shoupPowerBasis k hk))
    (shoupFrobeniusLinear k hk)) = _
  rw [minpoly.algEquiv_eq]
  rw [shoupFrobeniusLinear, FiniteField.minpoly_frobeniusAlgHom, shoupBinField_finrank]

/-- The matrix computed by the program has period dividing the field degree. -/
theorem shoupFrobeniusMatrix_period (k : ℕ) (hk : 1 ≤ k) :
    shoupFrobeniusMatrix k hk ^ k = 1 := by
  have h := minpoly.aeval (ZMod 2) (shoupFrobeniusMatrix k hk)
  rw [shoupFrobeniusMatrix_minpoly] at h
  simpa only [map_sub, map_pow, Polynomial.aeval_X, map_one, sub_eq_zero] using h

/-- Odd degree makes the Frobenius minimal polynomial squarefree. -/
theorem shoupFrobeniusMatrix_squarefree (k : ℕ) (hk : 1 ≤ k) (hodd : Odd k) :
    Squarefree (minpoly (ZMod 2) (shoupFrobeniusMatrix k hk)) := by
  rw [shoupFrobeniusMatrix_minpoly]
  have hn : (k : ZMod 2) ≠ 0 := by
    intro hz
    exact hodd.not_two_dvd_nat ((ZMod.natCast_eq_zero_iff k 2).mp hz)
  simpa using (Polynomial.separable_X_pow_sub_C (1 : ZMod 2) hn one_ne_zero).squarefree

/-- On unary degree input the complete matrix construction has polynomial runtime. -/
theorem shoupFrobeniusMatrixProg_time_le : ∃ R : Polynomial ℕ, ∀ k : ℕ,
    ∃ t ≤ R.eval k, shoupFrobeniusMatrixProg.code.Runs (encode (unary k))
      (encode (shoupFrobeniusMatrixProg (unary k))) t := by
  refine ⟨shoupFrobeniusMatrixProg.timeBound.comp (2 * Polynomial.X + 1), fun k => ?_⟩
  obtain ⟨t, ht, hr⟩ := shoupFrobeniusMatrixProg.computes (unary k)
  refine ⟨t, ?_, hr⟩
  simpa [esize_unary] using ht

end MIPRE.SAT

end

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.SAT.FieldTrace
import MIPRE.Foundations.LowDegree.BinaryMatrixSolve

/-! # Canonical binary linear coordinates for the effective field -/

noncomputable section

namespace MIPRE.LowDegree.BinaryLinear

/-- Decoding and re-encoding a vector of the prescribed width is exact. -/
theorem vectorBits_vectorValue (n : ℕ) (v : Cost.BitStr) (hv : v.length = n) :
    vectorBits (vectorValue n v) = v := by
  apply List.ext_getElem
  · simp [vectorBits, hv]
  · intro i hi hj
    simp [vectorBits, vectorValue, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hj]

end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.SAT

open Cost LowDegree LowDegree.BinaryPolynomial LowDegree.BinaryLinear

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- Correct-width decoding in the Shoup model is evaluation at its root. -/
theorem shoupBinField_ofBits (k : ℕ) (hk : 1 ≤ k) (v : BitStr) (hv : v.length = k) :
    (shoupBinField k hk).ofBits v = evalBits (shoupRoot k hk) v := by
  letI : Fact (Irreducible (polyOfBits (shoupIrreducible (unary k)))) :=
    ⟨shoupIrreducible_irreducible k hk⟩
  exact quotientBinField_ofBits _ (shoupIrreducible_monic k hk) v
    (hv.trans (shoupIrreducible_natDegree k hk).symm)

/-- The canonical bit representation is also a binary linear equivalence. -/
def shoupCoordinateEquiv (k : ℕ) (hk : 1 ≤ k) :
    (shoupBinField k hk).carrier ≃ₗ[ZMod 2] (Fin k → ZMod 2) :=
  (show (Fin k → ZMod 2) ≃ₗ[ZMod 2] (shoupBinField k hk).carrier from
    { toFun := fun v => (shoupBinField k hk).ofBits (vectorBits v)
      invFun := fun a => vectorValue k ((shoupBinField k hk).toBits a)
      left_inv := fun v => by
        dsimp only
        rw [shoupBinField_toBits_ofBits k hk (vectorBits v) (by simp [vectorBits]),
          vectorValue_vectorBits]
      right_inv := fun a => by
        dsimp only
        rw [vectorBits_vectorValue k _ ((shoupBinField k hk).length_toBits a)]
        exact (shoupBinField k hk).ofBits_toBits a
      map_add' := fun v w => by
        rw [← xorBits_vectorBits]
        rw [shoupBinField_ofBits k hk _ (by simp [length_xorBits, vectorBits]),
          shoupBinField_ofBits k hk (vectorBits v) (by simp [vectorBits]),
          shoupBinField_ofBits k hk (vectorBits w) (by simp [vectorBits])]
        exact evalBits_xor _ _ _ (by simp [vectorBits])
      map_smul' := fun c v => by
        rcases binary_eq_zero_or_one c with rfl | rfl
        · simp only [zero_smul, RingHom.id_apply]
          rw [shoupBinField_ofBits k hk (vectorBits 0) (by simp [vectorBits])]
          have he : vectorBits (0 : Fin k → ZMod 2) = BinaryPolynomial.zeroBits (vectorBits v) := by
            apply List.ext_getElem
            · simp [vectorBits, BinaryPolynomial.length_zeroBits]
            · intro i hi hj
              simp [vectorBits, bit, BinaryPolynomial.zeroBits]
          rw [he, BinaryPolynomial.evalBits_zeroBits]
        · simp }).symm

@[simp] theorem shoupCoordinateEquiv_apply (k : ℕ) (hk : 1 ≤ k)
    (a : (shoupBinField k hk).carrier) :
    shoupCoordinateEquiv k hk a = vectorValue k ((shoupBinField k hk).toBits a) := rfl

/-- Canonical field encodings and canonical linear coordinates coincide exactly. -/
theorem shoupCoordinateEquiv_encoding (k : ℕ) (hk : 1 ≤ k)
    (a : (shoupBinField k hk).carrier) :
    vectorBits (shoupCoordinateEquiv k hk a) = (shoupBinField k hk).toBits a :=
  vectorBits_vectorValue k _ ((shoupBinField k hk).length_toBits a)

/-- The basis associated to the actual polynomial-time field representation. -/
def shoupPowerBasis (k : ℕ) (hk : 1 ≤ k) :
    Module.Basis (Fin k) (ZMod 2) (shoupBinField k hk).carrier :=
  Module.Basis.ofEquivFun (shoupCoordinateEquiv k hk)

/-- Standard unit vectors encode the corresponding polynomial-basis elements. -/
theorem shoupPowerBasis_encoding (k : ℕ) (hk : 1 ≤ k) (j : Fin k) :
    (shoupBinField k hk).toBits (shoupPowerBasis k hk j) = unitBits k j := by
  rw [← shoupCoordinateEquiv_encoding, shoupPowerBasis, Module.Basis.coe_ofEquivFun,
    LinearEquiv.apply_symm_apply, unitBits_eq_vectorBits]

/-- Multiplication prints the canonical linear coordinates of the product. -/
theorem shoupMulProg_encoding (k : ℕ) (hk : 1 ≤ k)
    (a b : (shoupBinField k hk).carrier) :
    shoupMulProg (unary k, (shoupBinField k hk).toBits a, (shoupBinField k hk).toBits b) =
      (shoupBinField k hk).toBits (a * b) := by
  change mulReduce (shoupLowerCoeffs (unary k)) ((shoupBinField k hk).toBits a)
    ((shoupBinField k hk).toBits b) = _
  apply (shoupRoot_eval_eq_iff k hk _ _
    ((length_mulReduce _ _ _ (by rw [(shoupBinField k hk).length_toBits,
      shoupLowerCoeffs_length k hk])).trans (shoupLowerCoeffs_length k hk))
    ((shoupBinField k hk).length_toBits _)).mp
  rw [shoupRoot_eval_toBits]
  change evalBits (shoupRoot k hk) (mulReduce _ _ _) = _
  rw [evalBits_mulReduce _ _ _ _ (by rw [(shoupBinField k hk).length_toBits,
    shoupLowerCoeffs_length k hk]) (shoupRoot_equation k hk),
    shoupRoot_eval_toBits, shoupRoot_eval_toBits]

end MIPRE.SAT

end

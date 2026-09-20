/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryCirculantProg
import MIPRE.Foundations.LowDegree.BinaryKernel

/-! # Effective binary cyclic group algebra coordinates -/

noncomputable section

namespace MIPRE.LowDegree.BinaryLinear

open Cost Cost.PolyTimeFun

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

instance groupAlgebraCharP (k : ℕ) [NeZero k] :
    CharP (AddMonoidAlgebra (ZMod 2) (Fin k)) 2 :=
  charP_of_injective_algebraMap' (ZMod 2) 2

/-- All cyclic group-algebra coefficients as a binary linear equivalence. -/
def groupCoordinates (k : ℕ) :
    AddMonoidAlgebra (ZMod 2) (Fin k) ≃ₗ[ZMod 2] (Fin k → ZMod 2) :=
  (AddMonoidAlgebra.coeffLinearEquiv (ZMod 2)).trans
    (Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) (Fin k))

@[simp] theorem groupCoordinates_apply (k : ℕ)
    (z : AddMonoidAlgebra (ZMod 2) (Fin k)) (i : Fin k) : groupCoordinates k z i = z.coeff i := rfl

@[simp] theorem groupCoordinates_finGroupOfVector {k : ℕ} [NeZero k] (v : Fin k → ZMod 2) :
    groupCoordinates k (finGroupOfVector v) = v := by
  ext i
  simp

@[simp] theorem groupCoordinates_symm_apply {k : ℕ} [NeZero k] (v : Fin k → ZMod 2) :
    (groupCoordinates k).symm v = finGroupOfVector v := by
  apply (groupCoordinates k).injective
  simp

/-- Cyclic convolution, using the verified circulant printer and matrix application. -/
def groupMulBitsProg : PolyTimeFun (BitStr × BitStr) BitStr :=
  applyBitsProg.comp ((circulantBitsProg.comp fst).pair snd)

theorem groupMulBitsProg_correct {k : ℕ} [NeZero k]
    (z w : AddMonoidAlgebra (ZMod 2) (Fin k)) :
    groupMulBitsProg (vectorBits (groupCoordinates k z), vectorBits (groupCoordinates k w)) =
      vectorBits (groupCoordinates k (z * w)) := by
  change applyBits (circulantBitsProg (vectorBits (groupCoordinates k z)))
    (vectorBits (groupCoordinates k w)) = _
  rw [circulantBitsProg_correct, applyBits_matrixBits]
  congr 1
  funext i
  rw [groupCoordinates_apply, AddMonoidAlgebra.coeff_mul_apply_right,
    Finsupp.sum_fintype _ _ (by intro j; simp)]
  simp only [Matrix.mulVec, dotProduct, Matrix.circulant_apply, groupCoordinates_apply,
    sub_eq_add_neg]

/-- Squaring in a binary commutative group algebra is a linear map. -/
def groupSquareLinear (k : ℕ) [NeZero k] :
    AddMonoidAlgebra (ZMod 2) (Fin k) →ₗ[ZMod 2] AddMonoidAlgebra (ZMod 2) (Fin k) :=
  (FiniteField.frobeniusAlgHom (ZMod 2) (AddMonoidAlgebra (ZMod 2) (Fin k))).toLinearMap

@[simp] theorem groupSquareLinear_apply (k : ℕ) [NeZero k]
    (z : AddMonoidAlgebra (ZMod 2) (Fin k)) : groupSquareLinear k z = z * z := by
  simp [groupSquareLinear, FiniteField.frobeniusAlgHom, pow_two]

def groupSquareCoordinates (k : ℕ) [NeZero k] :
    (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) :=
  (groupCoordinates k).toLinearMap.comp
    ((groupSquareLinear k).comp (groupCoordinates k).symm.toLinearMap)

@[simp] theorem groupSquareCoordinates_apply (k : ℕ) [NeZero k]
    (z : AddMonoidAlgebra (ZMod 2) (Fin k)) :
    groupSquareCoordinates k (groupCoordinates k z) = groupCoordinates k (z * z) := by
  simp [groupSquareCoordinates]

def groupSquareMatrix (k : ℕ) [NeZero k] : Matrix (Fin k) (Fin k) (ZMod 2) :=
  LinearMap.toMatrix' (groupSquareCoordinates k)

/-- Print the squaring matrix by applying cyclic convolution to the coordinate units. -/
def groupSquareMatrixProg : PolyTimeFun Unary (List BitStr) :=
  let square := groupMulBitsProg.comp ((PolyTimeFun.id _).pair (PolyTimeFun.id _))
  transposeBitsProg.comp ((PolyTimeFun.id _).pair ((map square).comp identityBitsProg))

theorem groupSquareMatrixProg_correct (k : ℕ) [NeZero k] :
    groupSquareMatrixProg (unary k) = matrixBits (groupSquareMatrix k) := by
  have hc : (identityBits k).map (fun v => groupMulBitsProg (v, v)) =
      matrixBits (groupSquareMatrix k).transpose := by
    rw [identityBits_eq_matrixBits]
    simp only [matrixBits, List.map_ofFn]
    apply congrArg List.ofFn
    funext j
    have hj : (1 : Matrix (Fin k) (Fin k) (ZMod 2)) j = Pi.single j 1 := by
      funext i
      simp [Pi.single_apply, Matrix.one_apply, eq_comm]
    change groupMulBitsProg (vectorBits ((1 : Matrix (Fin k) (Fin k) (ZMod 2)) j),
      vectorBits ((1 : Matrix (Fin k) (Fin k) (ZMod 2)) j)) = _
    rw [hj, ← groupCoordinates_finGroupOfVector (Pi.single j 1), groupMulBitsProg_correct]
    congr 1
    funext i
    change groupCoordinates k (finGroupOfVector (Pi.single j 1) *
      finGroupOfVector (Pi.single j 1)) i = (LinearMap.toMatrix' (groupSquareCoordinates k)) i j
    rw [LinearMap.toMatrix'_apply]
    simp [groupSquareCoordinates]
  change transposeBits (unary k).length ((identityBits (unary k).length).map
    (fun v => groupMulBitsProg (v, v))) = _
  rw [length_unary, hc, transposeBits_matrixBits, Matrix.transpose_transpose]

/-- The fixed-space equation is squaring plus the identity, in characteristic two. -/
def groupFixedMatrix (k : ℕ) [NeZero k] : Matrix (Fin k) (Fin k) (ZMod 2) :=
  groupSquareMatrix k + 1

theorem groupFixedMatrix_ker (k : ℕ) [NeZero k]
    (z : AddMonoidAlgebra (ZMod 2) (Fin k)) :
    groupCoordinates k z ∈ (groupFixedMatrix k).mulVecLin.ker ↔ z * z = z := by
  rw [LinearMap.mem_ker]
  change (groupSquareMatrix k + 1).mulVec (groupCoordinates k z) = 0 ↔ _
  rw [Matrix.add_mulVec, Matrix.one_mulVec]
  have hs : (groupSquareMatrix k).mulVec (groupCoordinates k z) = groupCoordinates k (z * z) := by
    change (LinearMap.toMatrix' (groupSquareCoordinates k)).mulVec _ = _
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix', groupSquareCoordinates_apply]
  rw [hs, ← map_add, ← (groupCoordinates k).map_zero, (groupCoordinates k).injective.eq_iff]
  exact CharTwo.add_eq_zero

/-- Coordinatewise addition of binary matrices. -/
def addMatrixBitsProg : PolyTimeFun (List BitStr × List BitStr) (List BitStr) :=
  (map BinaryPolynomial.xorBitsProg).comp zip

theorem addMatrixBitsProg_correct {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) (ZMod 2)) :
    addMatrixBitsProg (matrixBits A, matrixBits B) = matrixBits (A + B) := by
  change ((matrixBits A).zip (matrixBits B)).map (fun p => BinaryPolynomial.xorBits p.1 p.2) = _
  apply List.ext_getElem
  · simp [matrixBits]
  · intro i hi hj
    simp only [matrixBits, List.getElem_map, List.getElem_zip, List.getElem_ofFn]
    exact xorBits_vectorBits _ _

/-- Construct the binary fixed-space equation. -/
def groupFixedMatrixProg : PolyTimeFun Unary (List BitStr) :=
  addMatrixBitsProg.comp (groupSquareMatrixProg.pair identityBitsProg)

theorem groupFixedMatrixProg_correct (k : ℕ) [NeZero k] :
    groupFixedMatrixProg (unary k) = matrixBits (groupFixedMatrix k) := by
  change addMatrixBitsProg (groupSquareMatrixProg (unary k), identityBits (unary k).length) = _
  rw [length_unary, groupSquareMatrixProg_correct, identityBits_eq_matrixBits,
    addMatrixBitsProg_correct]
  rfl

/-- At most `k` coefficient vectors generate all idempotents of the binary cyclic algebra. -/
def groupFixedGeneratorsProg : PolyTimeFun Unary (List BitStr) :=
  kernelGeneratorsProg.comp ((PolyTimeFun.id _).pair groupFixedMatrixProg)

def groupFixedGenerator (k : ℕ) [NeZero k] (j : Fin k) :
    AddMonoidAlgebra (ZMod 2) (Fin k) :=
  (groupCoordinates k).symm (kernelMap (groupFixedMatrix k) (Pi.single j 1))

theorem groupFixedGenerator_idempotent (k : ℕ) [NeZero k] (j : Fin k) :
    groupFixedGenerator k j * groupFixedGenerator k j = groupFixedGenerator k j := by
  apply (groupFixedMatrix_ker k _).mp
  rw [groupFixedGenerator, LinearEquiv.apply_symm_apply]
  exact kernelMap_mem_ker _ _

/-- Every idempotent lies in the binary span of the computed generators. -/
theorem groupFixedGenerator_spans (k : ℕ) [NeZero k]
    (z : AddMonoidAlgebra (ZMod 2) (Fin k)) (hz : z * z = z) :
    z ∈ Submodule.span (ZMod 2) (Set.range (groupFixedGenerator k)) := by
  have hc := (groupFixedMatrix_ker k z).mpr hz
  rw [← kernel_generators_span] at hc
  have hm : z ∈ Submodule.map (groupCoordinates k).symm.toLinearMap
      (Submodule.span (ZMod 2) (Set.range (fun j : Fin k =>
        kernelMap (groupFixedMatrix k) (Pi.single j 1)))) :=
    Submodule.mem_map.mpr ⟨groupCoordinates k z, hc, (groupCoordinates k).symm_apply_apply z⟩
  rw [Submodule.map_span, ← Set.range_comp] at hm
  change z ∈ Submodule.span (ZMod 2) (Set.range (groupFixedGenerator k)) at hm
  exact hm

/-- Exact encoding of the computed fixed-space generators; no linear combinations are enumerated. -/
theorem groupFixedGeneratorsProg_correct (k : ℕ) [NeZero k] :
    groupFixedGeneratorsProg (unary k) =
      List.ofFn (fun j => vectorBits (groupCoordinates k (groupFixedGenerator k j))) := by
  change kernelGeneratorsProg (unary k, groupFixedMatrixProg (unary k)) = _
  rw [groupFixedMatrixProg_correct, kernelGeneratorsProg_encoding]
  apply congrArg List.ofFn
  funext j
  rw [groupFixedGenerator, LinearEquiv.apply_symm_apply]

end MIPRE.LowDegree.BinaryLinear

end

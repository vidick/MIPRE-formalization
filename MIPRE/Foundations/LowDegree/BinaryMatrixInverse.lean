/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryMatrixSolve

/-! # Uniform binary matrix inversion -/

namespace MIPRE.LowDegree.BinaryLinear

open Cost Cost.PolyTimeFun

/-- The coefficient vector selected by the deterministic elimination algorithm. -/
def matrixSolution {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (v : Fin m → ZMod 2) : Fin n → ZMod 2 :=
  (typedReduce (typedBasis (columnRows A)) (v, 0)).2

theorem matrixSolveProg_encoding {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) (v : Fin m → ZMod 2) :
    matrixSolveProg (unary n, matrixBits A, vectorBits v) = vectorBits (matrixSolution A v) := by
  change basisSolveProg
    (unary n, coordinateRows (transposeBits (unary n).length (matrixBits A)), vectorBits v) = _
  rw [length_unary, coordinateRows_matrixBits, basisSolveProg_encoding]
  rfl

theorem matrixSolution_correct {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) (v : Fin m → ZMod 2)
    (hv : ∃ x, A.mulVec x = v) : A.mulVec (matrixSolution A v) = v := by
  have h := matrixSolveProg_correct A v hv
  rwa [matrixSolveProg_encoding, vectorValue_vectorBits] at h

/-- The inverse is assembled column by column, solving for each standard basis vector. -/
def inverseMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2)) :
    Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun i j => matrixSolution A (Pi.single j 1) i

/-- For nonsingular matrices, the computed columns form a right inverse. -/
theorem mul_inverseMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2))
    (hA : Function.Surjective A.mulVec) : A * inverseMatrix A = 1 := by
  ext i j
  have h := congrFun (matrixSolution_correct A (Pi.single j 1) (hA _)) i
  change (A.mulVec (matrixSolution A (Pi.single j 1))) i = (1 : Matrix (Fin n) (Fin n) (ZMod 2)) i j
  rw [h]
  simp [Pi.single_apply, Matrix.one_apply, eq_comm]

/-- Over the finite binary field the computed right inverse is also a left inverse. -/
theorem inverseMatrix_mul {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2))
    (hA : Function.Surjective A.mulVec) : inverseMatrix A * A = 1 :=
  mul_eq_one_comm.mp (mul_inverseMatrix A hA)

private noncomputable def inverseColumnsProg : PolyTimeFun (Unary × List BitStr) (List BitStr) :=
  let solve : PolyTimeFun (BitStr × (Unary × List BitStr)) BitStr :=
    matrixSolveProg.comp ((fst.comp snd).pair ((snd.comp snd).pair fst))
  (mapWith solve).comp ((identityBitsProg.comp fst).pair (PolyTimeFun.id _))

private theorem inverseColumnsProg_encoding {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (ZMod 2)) :
    inverseColumnsProg (unary n, matrixBits A) = matrixBits (inverseMatrix A).transpose := by
  change (identityBits (unary n).length).map
    (fun v => matrixSolveProg (unary n, matrixBits A, v)) = _
  rw [length_unary, identityBits_eq_matrixBits]
  simp only [matrixBits, List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  have hj : (1 : Matrix (Fin n) (Fin n) (ZMod 2)) j = Pi.single j 1 := by
    funext i
    simp [Pi.single_apply, Matrix.one_apply, eq_comm]
  change matrixSolveProg (unary n, matrixBits A, vectorBits ((1 : Matrix (Fin n) (Fin n) (ZMod 2)) j)) = _
  rw [hj, matrixSolveProg_encoding]
  rfl

/-- One globally polynomial-time ambient program for binary matrix inversion.
The dimension is explicit and unary; correctness requires a nonsingular matrix. -/
noncomputable def inverseMatrixProg : PolyTimeFun (Unary × List BitStr) (List BitStr) :=
  transposeBitsProg.comp (fst.pair inverseColumnsProg)

/-- The raw program prints canonical coordinates of the constructed inverse matrix. -/
theorem inverseMatrixProg_encoding {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2)) :
    inverseMatrixProg (unary n, matrixBits A) = matrixBits (inverseMatrix A) := by
  change transposeBits (unary n).length (inverseColumnsProg (unary n, matrixBits A)) = _
  rw [length_unary, inverseColumnsProg_encoding, transposeBits_matrixBits, Matrix.transpose_transpose]

/-- The printed matrix passes both executable multiplication checks. -/
theorem inverseMatrixProg_correct {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2))
    (hA : Function.Surjective A.mulVec) :
    mulBits n (matrixBits A) (inverseMatrixProg (unary n, matrixBits A)) = identityBits n ∧
    mulBits n (inverseMatrixProg (unary n, matrixBits A)) (matrixBits A) = identityBits n := by
  rw [inverseMatrixProg_encoding, mulBits_matrixBits, mulBits_matrixBits,
    mul_inverseMatrix A hA, inverseMatrix_mul A hA, identityBits_eq_matrixBits]
  exact ⟨rfl, rfl⟩

end MIPRE.LowDegree.BinaryLinear

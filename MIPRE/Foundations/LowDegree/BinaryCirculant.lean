/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryMatrixInverse
import MIPRE.Foundations.LowDegree.BinarySquareRoot
import Mathlib.LinearAlgebra.Matrix.Circulant

/-! # Binary cyclic group algebras as circulant matrices -/

noncomputable section

namespace MIPRE.LowDegree.BinaryLinear

open Cost

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The regular representation of a finite binary group algebra is circulant. -/
def groupMatrix (z : AddMonoidAlgebra (ZMod 2) G) : Matrix G G (ZMod 2) :=
  Matrix.circulant z.coeff

theorem groupMatrix_mul (z w : AddMonoidAlgebra (ZMod 2) G) :
    groupMatrix (z * w) = groupMatrix z * groupMatrix w := by
  rw [groupMatrix, groupMatrix, groupMatrix, Matrix.circulant_mul]
  congr 1
  funext g
  rw [AddMonoidAlgebra.coeff_mul_apply_right]
  rw [Finsupp.sum_fintype _ _ (by intro j; simp)]
  simp only [Matrix.mulVec, dotProduct, Matrix.circulant_apply, sub_eq_add_neg]

/-- The identity and product laws allow algebraic square roots to be used as matrices. -/
def groupMatrixHom : AddMonoidAlgebra (ZMod 2) G →+* Matrix G G (ZMod 2) where
  toFun := groupMatrix
  map_one' := by
    ext i j
    change (AddMonoidAlgebra.single (0 : G) (1 : ZMod 2)).coeff (i - j) =
      (1 : Matrix G G (ZMod 2)) i j
    simp [Matrix.one_apply, Finsupp.single_apply, sub_eq_zero, eq_comm]
  map_mul' := groupMatrix_mul
  map_zero' := by simp [groupMatrix]
  map_add' := fun z w => by
    ext i j
    simp [groupMatrix]

theorem groupMatrix_injective : Function.Injective (groupMatrix (G := G)) := by
  intro z w h
  apply AddMonoidAlgebra.coeff_injective
  ext g
  simpa [groupMatrix] using congrArg (fun A => A g 0) h

/-- The explicit group-algebra square root gives an exact matrix square root. -/
theorem groupMatrix_binarySquareRoot (hG : Odd (Fintype.card G))
    (z : AddMonoidAlgebra (ZMod 2) G) :
    groupMatrix (binarySquareRoot z) * groupMatrix (binarySquareRoot z) = groupMatrix z := by
  rw [← groupMatrix_mul, binarySquareRoot_mul_self hG]

/-- Coefficient vectors are encoded with the same ordering as binary matrices. -/
def finGroupOfVector {k : ℕ} [NeZero k] (v : Fin k → ZMod 2) :
    AddMonoidAlgebra (ZMod 2) (Fin k) :=
  .ofCoeff (Finsupp.onFinset Finset.univ v (fun i _ => Finset.mem_univ i))

@[simp] theorem coeff_finGroupOfVector {k : ℕ} [NeZero k]
    (v : Fin k → ZMod 2) (i : Fin k) : (finGroupOfVector v).coeff i = v i := by
  simp [finGroupOfVector]

/-- The computed inverse of a nonsingular circulant is again circulant. -/
theorem inverseMatrix_groupMatrix {k : ℕ} [NeZero k]
    (z : AddMonoidAlgebra (ZMod 2) (Fin k))
    (hz : Function.Surjective (groupMatrix z).mulVec) :
    ∃ u : AddMonoidAlgebra (ZMod 2) (Fin k), z * u = 1 ∧
      inverseMatrix (groupMatrix z) = groupMatrix u := by
  haveI : Finite (AddMonoidAlgebra (ZMod 2) (Fin k)) :=
    Finite.of_injective AddMonoidAlgebra.coeff AddMonoidAlgebra.coeff_injective
  have hinj : Function.Injective (fun u => z * u) := by
    intro x y h
    apply groupMatrix_injective
    have hh := congrArg groupMatrix h
    rw [groupMatrix_mul, groupMatrix_mul] at hh
    have hh' := congrArg (fun A => inverseMatrix (groupMatrix z) * A) hh
    simpa only [← Matrix.mul_assoc, inverseMatrix_mul _ hz, Matrix.one_mul] using hh'
  obtain ⟨u, hu⟩ := (Finite.injective_iff_surjective.mp hinj) 1
  change z * u = 1 at hu
  refine ⟨u, hu, ?_⟩
  have hm : groupMatrix z * groupMatrix u = 1 := by
    rw [← groupMatrix_mul, hu]
    exact groupMatrixHom.map_one
  calc
    inverseMatrix (groupMatrix z) = inverseMatrix (groupMatrix z) *
        (groupMatrix z * groupMatrix u) := by rw [hm, Matrix.mul_one]
    _ = groupMatrix u := by rw [← Matrix.mul_assoc, inverseMatrix_mul _ hz, Matrix.one_mul]

/-- The inverse circulant's square root is read from doubled indices of its first column. -/
def inverseRootMatrix {k : ℕ} [NeZero k] (A : Matrix (Fin k) (Fin k) (ZMod 2)) :
    Matrix (Fin k) (Fin k) (ZMod 2) :=
  Matrix.circulant (fun i => inverseMatrix A (i + i) 0)

theorem inverseRootMatrix_square {k : ℕ} [NeZero k] (hk : Odd k)
    (z : AddMonoidAlgebra (ZMod 2) (Fin k))
    (hz : Function.Surjective (groupMatrix z).mulVec) :
    inverseRootMatrix (groupMatrix z) * inverseRootMatrix (groupMatrix z) =
      inverseMatrix (groupMatrix z) := by
  obtain ⟨u, _, hu⟩ := inverseMatrix_groupMatrix z hz
  have hr : inverseRootMatrix (groupMatrix z) = groupMatrix (binarySquareRoot u) := by
    unfold inverseRootMatrix
    rw [hu]
    ext i j
    simp [groupMatrix]
  rw [hr, hu]
  exact groupMatrix_binarySquareRoot (by simpa using hk) u

/-- Transposition preserves the unique inverse of a symmetric matrix. -/
theorem inverseMatrix_isSymm {k : ℕ} (A : Matrix (Fin k) (Fin k) (ZMod 2))
    (hA : Function.Surjective A.mulVec) (hs : A.IsSymm) : (inverseMatrix A).IsSymm := by
  have hleft : (inverseMatrix A).transpose * A = 1 := by
    have h := congrArg Matrix.transpose (mul_inverseMatrix A hA)
    simpa only [Matrix.transpose_mul, hs.eq, Matrix.transpose_one] using h
  change (inverseMatrix A).transpose = inverseMatrix A
  calc
    (inverseMatrix A).transpose = (inverseMatrix A).transpose * (A * inverseMatrix A) := by
      rw [mul_inverseMatrix A hA, Matrix.mul_one]
    _ = inverseMatrix A := by rw [← Matrix.mul_assoc, hleft, Matrix.one_mul]

theorem inverseRootMatrix_isSymm {k : ℕ} [NeZero k]
    (z : AddMonoidAlgebra (ZMod 2) (Fin k))
    (hz : Function.Surjective (groupMatrix z).mulVec) (hs : (groupMatrix z).IsSymm) :
    (inverseRootMatrix (groupMatrix z)).IsSymm := by
  obtain ⟨u, _, hu⟩ := inverseMatrix_groupMatrix z hz
  have hi := inverseMatrix_isSymm (groupMatrix z) hz hs
  rw [hu] at hi
  have hc := Matrix.circulant_isSymm_iff.mp hi
  unfold inverseRootMatrix
  rw [hu]
  apply Matrix.circulant_isSymm_iff.mpr
  intro i
  simpa [groupMatrix, neg_add_rev] using hc (i + i)

/-- The explicit doubled-index square root self-dualizes every nonsingular symmetric circulant. -/
theorem inverseRootMatrix_gram {k : ℕ} [NeZero k] (hk : Odd k)
    (z : AddMonoidAlgebra (ZMod 2) (Fin k))
    (hz : Function.Surjective (groupMatrix z).mulVec) (hs : (groupMatrix z).IsSymm) :
    (inverseRootMatrix (groupMatrix z)).transpose * groupMatrix z *
      inverseRootMatrix (groupMatrix z) = 1 := by
  rw [(inverseRootMatrix_isSymm z hz hs).eq]
  have hc : inverseRootMatrix (groupMatrix z) * groupMatrix z =
      groupMatrix z * inverseRootMatrix (groupMatrix z) :=
    Matrix.circulant_mul_comm _ _
  rw [hc, Matrix.mul_assoc, inverseRootMatrix_square hk z hz, mul_inverseMatrix _ hz]

end MIPRE.LowDegree.BinaryLinear

end

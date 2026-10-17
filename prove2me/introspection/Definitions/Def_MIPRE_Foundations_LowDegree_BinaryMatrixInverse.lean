/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryMatrixInverse.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryLinear
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryElimination
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasisProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasis
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve_B
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_coordinateRows_matrixBits
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_transposeBits_matrixBits
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_basisSolveProg_encoding
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_identityBits_eq_matrixBits

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

/-- The inverse is assembled column by column, solving for each standard basis vector. -/
def inverseMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2)) :
    Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun i j => matrixSolution A (Pi.single j 1) i

noncomputable def inverseColumnsProg : PolyTimeFun (Unary × List BitStr) (List BitStr) :=
  let solve : PolyTimeFun (BitStr × (Unary × List BitStr)) BitStr :=
    matrixSolveProg.comp ((fst.comp snd).pair ((snd.comp snd).pair fst))
  (mapWith solve).comp ((identityBitsProg.comp fst).pair (PolyTimeFun.id _))

theorem inverseColumnsProg_encoding {n : ℕ}
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

end MIPRE.LowDegree.BinaryLinear

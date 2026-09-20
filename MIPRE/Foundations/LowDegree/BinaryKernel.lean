/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryMatrixSolve

/-! # Effective generators for a binary matrix kernel -/

namespace MIPRE.LowDegree.BinaryLinear

open Cost Cost.PolyTimeFun

variable {n t : ℕ}

/-- In characteristic two, conditional row addition is a linear map. -/
theorem typedReduceStep_eq_linear (r : Row n t) (p : Pivot n t) :
    typedReduceStep r p = r + (r.1 p.1) • p.2 := by
  rcases binary_eq_zero_or_one (r.1 p.1) with h | h
  · simp [typedReduceStep, h]
  · simp [typedReduceStep, h]
    rfl

def reduceStepLinear (p : Pivot n t) : Row n t →ₗ[ZMod 2] Row n t :=
  LinearMap.id +
    (((LinearMap.proj p.1 : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2).comp
      (LinearMap.fst (ZMod 2) (Fin n → ZMod 2) (Fin t → ZMod 2))).smulRight p.2)

@[simp] theorem reduceStepLinear_apply (p : Pivot n t) (r : Row n t) :
    reduceStepLinear p r = typedReduceStep r p := (typedReduceStep_eq_linear r p).symm

def reduceLinear : List (Pivot n t) → (Row n t →ₗ[ZMod 2] Row n t)
  | [] => LinearMap.id
  | p :: b => (reduceLinear b).comp (reduceStepLinear p)

@[simp] theorem reduceLinear_apply (b : List (Pivot n t)) (r : Row n t) :
    reduceLinear b r = typedReduce b r := by
  induction b generalizing r with
  | nil => rfl
  | cons p b ih =>
    rw [reduceLinear, LinearMap.comp_apply, ih, reduceStepLinear_apply]
    rfl

/-- A row whose value is zero keeps its entire certificate unchanged. -/
theorem typedReduce_zero_value (b : List (Pivot n t)) (x : Fin t → ZMod 2) :
    typedReduce b (0, x) = (0, x) := by
  induction b with
  | nil => rfl
  | cons p b ih =>
    change typedReduce b (typedReduceStep (0, x) p) = _
    have hs : typedReduceStep (0, x) p = (0, x) := by simp [typedReduceStep]
    rw [hs, ih]

/-- Reduce the graph of the original matrix map and retain the certificate.
This is a projection onto its kernel. -/
def kernelMap {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
  (LinearMap.snd (ZMod 2) (Fin m → ZMod 2) (Fin n → ZMod 2)).comp
    ((reduceLinear (typedBasis (columnRows A))).comp (A.mulVecLin.prod LinearMap.id))

theorem kernelMap_apply {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (x : Fin n → ZMod 2) :
    kernelMap A x = (typedReduce (typedBasis (columnRows A)) (A.mulVec x, x)).2 := by
  simp [kernelMap]

/-- Every output of the computed projection is in the matrix kernel. -/
theorem kernelMap_mem_ker {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (x : Fin n → ZMod 2) : kernelMap A x ∈ A.mulVecLin.ker := by
  have hp := typedBasis_represents A.mulVecLin (columnRows A) (columnRows_represents A)
  have hr : Represents A.mulVecLin (A.mulVec x, x) := rfl
  have hrel := represents_typedReduce A.mulVecLin (typedBasis (columnRows A))
    (A.mulVec x, x) hr hp
  have hz := (typedBasis_isPivotBasis (columnRows A)).reduce_eq_zero (A.mulVec x, x) (by
    rw [typedBasis_span, rowSpan_columnRows]
    exact ⟨x, rfl⟩)
  rw [LinearMap.mem_ker, kernelMap_apply]
  exact hrel.trans hz

/-- The projection fixes every vector already in the kernel. -/
theorem kernelMap_fixed {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (x : Fin n → ZMod 2) (hx : x ∈ A.mulVecLin.ker) : kernelMap A x = x := by
  rw [LinearMap.mem_ker] at hx
  rw [kernelMap_apply, show A.mulVec x = 0 from hx, typedReduce_zero_value]

theorem kernelMap_range {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    (kernelMap A).range = A.mulVecLin.ker := by
  apply le_antisymm
  · rintro v ⟨x, rfl⟩
    exact kernelMap_mem_ker A x
  · intro x hx
    exact ⟨x, kernelMap_fixed A x hx⟩

/-- The images of the standard basis generate exactly the matrix kernel. -/
theorem kernel_generators_span {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    Submodule.span (ZMod 2) (Set.range (fun j : Fin n => kernelMap A (Pi.single j 1))) =
      A.mulVecLin.ker := by
  let K := LinearMap.toMatrix' (kernelMap A)
  have hK : K.mulVecLin = kernelMap A := by
    exact Matrix.toLin'_toMatrix' (kernelMap A)
  have hcols : K.col = fun j : Fin n => kernelMap A (Pi.single j 1) := by
    funext j i
    exact LinearMap.toMatrix'_apply (kernelMap A) i j
  rw [← hcols, ← Matrix.range_mulVecLin, hK, kernelMap_range]

/-- Compute at most `n` generators of an `m`-by-`n` binary matrix kernel.
The explicit unary input is the number of columns. -/
noncomputable def kernelGeneratorsProg : PolyTimeFun (Unary × List BitStr) (List BitStr) :=
  let rows := coordinateRowsProg.comp transposeBitsProg
  let basis := basisRowsProg.comp rows
  let reduce := reduceRowsProg.comp (snd.pair fst)
  (map snd).comp ((mapWith reduce).comp (rows.pair basis))

/-- The raw program prints canonical vectors spanning the full matrix kernel. -/
theorem kernelGeneratorsProg_encoding {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    kernelGeneratorsProg (unary n, matrixBits A) =
      List.ofFn (fun j : Fin n => vectorBits (kernelMap A (Pi.single j 1))) := by
  change ((coordinateRows (transposeBits (unary n).length (matrixBits A))).map
    (fun r => reduceRows (basisRowsProg (coordinateRows
      (transposeBits (unary n).length (matrixBits A)))) r)).map Prod.snd = _
  rw [length_unary, coordinateRows_matrixBits, basisRowsProg_correct, List.map_map,
    List.map_map]
  simp only [columnRows, List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  change (reduceRows ((typedBasis (columnRows A)).map pivotBits)
    (rowBits (A.col j, Pi.single j 1))).2 = _
  rw [reduceRows_rowBits]
  change vectorBits (typedReduce (typedBasis (columnRows A)) (A.col j, Pi.single j 1)).2 = _
  rw [kernelMap_apply, Matrix.mulVec_single_one]

/-- The generated family has polynomial length and every vector lies in the kernel. -/
theorem kernelGeneratorsProg_correct {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    (kernelGeneratorsProg (unary n, matrixBits A)).length = n ∧
    (∀ v ∈ kernelGeneratorsProg (unary n, matrixBits A),
      v.length = n ∧ vectorValue n v ∈ A.mulVecLin.ker) ∧
    Submodule.span (ZMod 2)
      {x | ∃ v ∈ kernelGeneratorsProg (unary n, matrixBits A), vectorValue n v = x} =
      A.mulVecLin.ker := by
  rw [kernelGeneratorsProg_encoding]
  refine ⟨List.length_ofFn, ?_, ?_⟩
  · intro v hv
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hv
    exact ⟨List.length_ofFn, by rw [vectorValue_vectorBits]; exact kernelMap_mem_ker A _⟩
  · convert kernel_generators_span A using 1
    congr 1
    ext x
    simp only [Set.mem_setOf_eq, List.mem_ofFn, Set.mem_range]
    constructor
    · rintro ⟨v, ⟨j, rfl⟩, hj⟩
      exact ⟨j, by simpa using hj⟩
    · rintro ⟨j, hj⟩
      exact ⟨_, ⟨j, rfl⟩, by simpa using hj⟩

end MIPRE.LowDegree.BinaryLinear

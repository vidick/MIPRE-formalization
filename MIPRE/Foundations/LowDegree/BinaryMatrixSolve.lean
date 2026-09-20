/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinarySolve
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # A uniform solver for binary matrices -/

namespace MIPRE.LowDegree.BinaryLinear

open Cost Cost.PolyTimeFun

def unitBits (n j : ℕ) : BitStr := (List.range n).map (fun i => decide (i = j))

def identityBits (n : ℕ) : List BitStr := (List.range n).map (unitBits n)

theorem unitBits_eq_vectorBits {n : ℕ} (j : Fin n) :
    unitBits n j = vectorBits (Pi.single j 1 : Fin n → ZMod 2) := by
  apply List.ext_getElem
  · simp [unitBits, vectorBits]
  · intro i hi hj
    simp only [unitBits, vectorBits, List.getElem_map, List.getElem_range, List.getElem_ofFn]
    by_cases he : i = j
    · simp [bit, Pi.single_apply, Fin.ext_iff, he]
    · simp [bit, Pi.single_apply, Fin.ext_iff, he]

theorem identityBits_eq_matrixBits (n : ℕ) :
    identityBits n = matrixBits (1 : Matrix (Fin n) (Fin n) (ZMod 2)) := by
  apply List.ext_getElem
  · simp [identityBits, matrixBits]
  · intro i hi hj
    have hin : i < n := by simpa [identityBits] using hi
    simp only [identityBits, matrixBits, List.getElem_map, List.getElem_range, List.getElem_ofFn]
    rw [unitBits_eq_vectorBits (⟨i, hin⟩ : Fin n)]
    congr 1
    funext j
    simp [Pi.single_apply, Matrix.one_apply, eq_comm]

noncomputable def unitBitsProg : PolyTimeFun (ℕ × Unary) BitStr :=
  congr ((mapWith SAT.ArrayProg.eqNat).comp
    ((SAT.range'P.comp ((const 0).pair snd)).pair fst))
    (fun p => unitBits p.2.length p.1) (by
      intro p
      simp only [comp_apply, pair_apply, mapWith_apply, SAT.ArrayProg.eqNat_apply,
        SAT.range'P_apply, fst_apply, snd_apply, const_apply, ← List.range_eq_range']
      rfl)

noncomputable def identityBitsProg : PolyTimeFun Unary (List BitStr) :=
  congr ((mapWith unitBitsProg).comp
    ((SAT.range'P.comp ((const 0).pair (PolyTimeFun.id _))).pair (PolyTimeFun.id _)))
    (fun u => identityBits u.length) (by
      intro u
      simp only [comp_apply, pair_apply, mapWith_apply, SAT.range'P_apply,
        fst_apply, snd_apply, id_apply, const_apply, ← List.range_eq_range']
      rfl)

/-- Attach the standard coordinate certificate to each supplied column. -/
def coordinateRows (columns : List BitStr) : List RawRow :=
  columns.zip (identityBits columns.length)

noncomputable def coordinateRowsProg : PolyTimeFun (List BitStr) (List RawRow) :=
  congr (zip.comp ((PolyTimeFun.id _).pair (identityBitsProg.comp length))) coordinateRows
    (by intro columns; change columns.zip (identityBits (unary columns.length).length) = _
        rw [length_unary]; rfl)

def columnRows {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) : List (Row m n) :=
  List.ofFn (fun j => (A.col j, Pi.single j 1))

theorem coordinateRows_matrixBits {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    coordinateRows (transposeBits n (matrixBits A)) = (columnRows A).map rowBits := by
  rw [transposeBits_matrixBits]
  unfold coordinateRows
  have hl : (matrixBits A.transpose).length = n := by simp [matrixBits]
  rw [hl, identityBits_eq_matrixBits]
  apply List.ext_getElem
  · simp [matrixBits, columnRows]
  · intro j hj hj'
    simp only [matrixBits, columnRows, List.getElem_zip, List.getElem_ofFn,
      List.getElem_map, rowBits]
    congr 1
    congr 1
    funext i
    simp [Pi.single_apply, Matrix.one_apply, eq_comm]

theorem columnRows_represents {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    ∀ r ∈ columnRows A, Represents A.mulVecLin r := by
  intro r hr
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hr
  exact Matrix.mulVec_single_one A j

theorem rowSpan_columnRows {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    rowSpan (columnRows A) = A.mulVecLin.range := by
  rw [Matrix.range_mulVecLin]
  unfold rowSpan
  congr 1
  ext v
  simp only [Set.mem_setOf_eq, columnRows, List.mem_ofFn, Set.mem_range]
  constructor
  · rintro ⟨r, ⟨j, rfl⟩, hr⟩
    exact ⟨j, hr⟩
  · rintro ⟨j, hj⟩
    exact ⟨(A.col j, Pi.single j 1), ⟨j, rfl⟩, hj⟩

/-- The output width is unary; matrix rows and the right-hand side are raw bits. -/
noncomputable def matrixSolveProg : PolyTimeFun (Unary × List BitStr × BitStr) BitStr :=
  basisSolveProg.comp (fst.pair
    ((coordinateRowsProg.comp (transposeBitsProg.comp (fst.pair (fst.comp snd)))).pair
      (snd.comp snd)))

/-- A globally polynomial-time solver for every consistent binary matrix system. -/
theorem matrixSolveProg_correct {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) (v : Fin m → ZMod 2)
    (hv : ∃ x, A.mulVec x = v) :
    A.mulVec (vectorValue n (matrixSolveProg (unary n, matrixBits A, vectorBits v))) = v := by
  change A.mulVecLin (vectorValue n (basisSolveProg
    (unary n, coordinateRows (transposeBits (unary n).length (matrixBits A)), vectorBits v))) = v
  rw [length_unary, coordinateRows_matrixBits]
  apply basisSolveProg_correct A.mulVecLin _ (columnRows_represents A) v
  rw [rowSpan_columnRows, LinearMap.mem_range]
  exact hv

end MIPRE.LowDegree.BinaryLinear

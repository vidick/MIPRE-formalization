/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryCirculant
import MIPRE.Foundations.Cost.Iterates
import Mathlib.Data.List.Rotate

/-! # Executable circulant matrices and their inverse square roots -/

namespace MIPRE.LowDegree.BinaryLinear

open Cost Cost.PolyTimeFun

def rotateLeftBits : BitStr → BitStr
  | [] => []
  | a :: l => l ++ [a]

theorem rotateLeftBits_eq_rotate (l : BitStr) : rotateLeftBits l = l.rotate 1 := by
  cases l <;> simp [rotateLeftBits, List.rotate_eq_rotate', List.rotate']

def rotateRightBits (l : BitStr) : BitStr := (rotateLeftBits l.reverse).reverse

theorem esize_rotateLeftBits (l : BitStr) : esize (rotateLeftBits l) = esize l := by
  cases l with
  | nil => rfl
  | cons a l =>
    have h := esize_list_append l [a]
    simp only [rotateLeftBits, esize_list_cons, esize_list_nil] at *
    omega

theorem esize_rotateRightBits (l : BitStr) : esize (rotateRightBits l) = esize l := by
  rw [rotateRightBits, esize_list_reverse, esize_rotateLeftBits, esize_list_reverse]

noncomputable def rotateLeftBitsProg : PolyTimeFun BitStr BitStr :=
  congr ((casesList (const [])
    (append.comp ((snd.comp snd).pair (cons (fst.comp snd) (const []))))).comp
      ((const ()).pair (PolyTimeFun.id _))) rotateLeftBits (by intro l; cases l <;> rfl)

noncomputable def rotateRightBitsProg : PolyTimeFun BitStr BitStr :=
  reverse.comp (rotateLeftBitsProg.comp reverse)

theorem iterate_rotateRightBits (n : ℕ) (l : BitStr) :
    rotateRightBits^[n] l = (l.reverse.rotate n).reverse := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [rotateRightBits, List.reverse_reverse, rotateLeftBits_eq_rotate, List.rotate_rotate]

private theorem rotateRightBitsProg_iterate_size (n : ℕ) (l : BitStr) :
    esize ((rotateRightBitsProg : BitStr → BitStr)^[n] l) ≤ Polynomial.X.eval (esize l) := by
  have hf : (rotateRightBitsProg : BitStr → BitStr) = rotateRightBits := by funext l; rfl
  rw [hf, Polynomial.eval_X]
  induction n with
  | zero => exact le_rfl
  | succ n ih => rw [Function.iterate_succ_apply', esize_rotateRightBits]; exact ih

theorem reverse_vectorBits {k : ℕ} (v : Fin k → ZMod 2) :
    (vectorBits v).reverse = vectorBits (fun i => v i.rev) := by
  apply List.ext_getElem
  · simp [vectorBits]
  · intro i hi hj
    simp [vectorBits, List.getElem_reverse, Fin.rev, Nat.sub_sub, Nat.add_comm]

theorem rotate_vectorBits {k : ℕ} [NeZero k] (v : Fin k → ZMod 2) (j : Fin k) :
    (vectorBits v).rotate j = vectorBits (fun i => v (i + j)) := by
  apply List.ext_getElem
  · simp [vectorBits]
  · intro i hi hj
    simp only [List.getElem_rotate, vectorBits, List.length_ofFn, List.getElem_ofFn]
    rfl

/-- Right rotation is translation by the negative column index. -/
theorem iterate_rotateRightBits_vectorBits {k : ℕ} [NeZero k]
    (v : Fin k → ZMod 2) (j : Fin k) :
    rotateRightBits^[j] (vectorBits v) = vectorBits (fun i => v (i - j)) := by
  rw [iterate_rotateRightBits, reverse_vectorBits, rotate_vectorBits, reverse_vectorBits]
  congr 1
  funext i
  rw [Fin.rev_add, Fin.rev_rev]

/-- Print a circulant from its first column. The size and all iteration counts come from the input. -/
noncomputable def circulantBitsProg : PolyTimeFun BitStr (List BitStr) :=
  let columns := (recordIteratesProg rotateRightBitsProg Polynomial.X
    rotateRightBitsProg_iterate_size).comp (length.pair (PolyTimeFun.id _))
  transposeBitsProg.comp (length.pair columns)

theorem circulantBitsProg_correct {k : ℕ} [NeZero k] (v : Fin k → ZMod 2) :
    circulantBitsProg (vectorBits v) = matrixBits (Matrix.circulant v) := by
  have hc : recordIterates rotateRightBits (unary k) (vectorBits v) =
      matrixBits (Matrix.circulant v).transpose := by
    unfold recordIterates matrixBits
    simp only [length_unary]
    apply congrArg List.ofFn
    funext j
    exact iterate_rotateRightBits_vectorBits v j
  change transposeBits (unary (vectorBits v).length).length
    (recordIterates rotateRightBits (unary (vectorBits v).length) (vectorBits v)) = _
  rw [show (vectorBits v).length = k from List.length_ofFn, length_unary, hc,
    transposeBits_matrixBits, Matrix.transpose_transpose]

/-- The coefficient square-root program uses doubled indices also for `Fin k` coordinates. -/
theorem rootBitsProg_vectorBits {k : ℕ} [NeZero k] (hk : Odd k) (v : Fin k → ZMod 2) :
    rootBitsProg (vectorBits v) = vectorBits (fun i => v (i + i)) := by
  rw [rootBitsProg_apply]
  apply List.ext_getElem
  · simp [vectorBits]
  · intro i hi hj
    have hik : i < k := by simpa [vectorBits] using hj
    have h := getD_rootBits (vectorBits v) false (by simpa [vectorBits] using hk)
      (by simpa [vectorBits] using hik)
    change (rootBits (vectorBits v))[i] = _
    have hir : i < (rootBits (vectorBits v)).length := by
      simpa only [rootBitsProg_apply] using hi
    have hleft : (rootBits (vectorBits v)).getD i false = (rootBits (vectorBits v))[i] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hir]
    rw [hleft] at h
    rw [h]
    simp [vectorBits, List.getD_eq_getElem?_getD, Nat.mod_lt _ (NeZero.pos k)]
    rfl

/-- Compute the inverse matrix, read its first column, permute doubled indices,
then print the circulant square root. -/
noncomputable def inverseRootMatrixProg : PolyTimeFun (Unary × List BitStr) (List BitStr) :=
  let firstColumn : PolyTimeFun (List BitStr) BitStr :=
    map ((SAT.ArrayProg.getD false).comp ((const 0).pair (PolyTimeFun.id _)))
  circulantBitsProg.comp (rootBitsProg.comp (firstColumn.comp inverseMatrixProg))

theorem inverseRootMatrixProg_correct {k : ℕ} [NeZero k] (hk : Odd k)
    (A : Matrix (Fin k) (Fin k) (ZMod 2)) :
    inverseRootMatrixProg (unary k, matrixBits A) = matrixBits (inverseRootMatrix A) := by
  change circulantBitsProg (rootBitsProg
    ((inverseMatrixProg (unary k, matrixBits A)).map (fun r => r.getD 0 false))) = _
  rw [inverseMatrixProg_encoding]
  have hc : (matrixBits (inverseMatrix A)).map (fun r => r.getD 0 false) =
      vectorBits (fun i => inverseMatrix A i 0) := by
    simp only [matrixBits, List.map_ofFn, vectorBits]
    apply congrArg List.ofFn
    funext i
    simp [NeZero.pos k]
  rw [hc, rootBitsProg_vectorBits hk, circulantBitsProg_correct]
  rfl

end MIPRE.LowDegree.BinaryLinear

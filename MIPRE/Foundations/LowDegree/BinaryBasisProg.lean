/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryElimination

/-! # Uniform construction of a binary pivot basis -/

namespace MIPRE.LowDegree.BinaryLinear

open Cost Cost.PolyTimeFun Polynomial

/-- First set bit, or the list length if the vector is zero. -/
def firstOne (v : BitStr) : ℕ := v.findIdx id

theorem firstOne_le (v : BitStr) : firstOne v ≤ v.length := List.findIdx_le_length

theorem firstOne_getD (v : BitStr) (h : firstOne v < v.length) :
    v.getD (firstOne v) false = true := by
  have hbit := List.findIdx_getElem (xs := v) (p := id) (w := h)
  change v[firstOne v]?.getD false = true
  rw [List.getElem?_eq_getElem h]
  exact hbit

theorem firstOne_getD_iff (v : BitStr) :
    v.getD (firstOne v) false = true ↔ firstOne v < v.length := by
  refine ⟨fun h => ?_, firstOne_getD v⟩
  by_contra hn
  have he : firstOne v = v.length := by have := firstOne_le v; omega
  simp [he, List.getD_eq_getElem?_getD] at h

private noncomputable def firstOneStep : PolyTimeFun (ℕ × Bool) ℕ :=
  ite snd (const 0) (inc.comp fst)

private theorem firstOne_fold (v : BitStr) :
    v.reverse.foldl firstOneStep.step 0 = firstOne v := by
  rw [List.foldl_reverse]
  induction v with
  | nil => rfl
  | cons b v ih =>
    change (if b then 0 else v.foldr (fun b n => firstOneStep (n, b)) 0 + 1) = _
    rw [ih]
    cases b <;> simp [firstOne, List.findIdx_cons]

/-- Finding a pivot scans the vector, without enumerating its binary magnitude. -/
noncomputable def firstOneProg : PolyTimeFun BitStr ℕ :=
  let scan := foldlAdd firstOneStep 4 (by
    intro n b
    change esize (if b then 0 else n + 1) ≤ _
    cases b
    · simpa only [Bool.false_eq_true, if_false, Polynomial.eval_ofNat] using esize_succ_le n
    · have hn := esize_pos n
      change 1 ≤ esize n + _
      omega)
  congr (scan.comp (reverse.pair (const 0))) firstOne firstOne_fold

@[simp] theorem firstOneProg_apply (v : BitStr) : firstOneProg v = firstOne v := rfl

/-- Reduce the candidate, then append it only when its remainder has a pivot. -/
def insertRow (b : List RawPivot) (r : RawRow) : List RawPivot :=
  let s := reduceRows b r
  let j := firstOne s.1
  if s.1.getD j false then b ++ [(j, s)] else b

noncomputable def insertRowProg : PolyTimeFun (List RawPivot × RawRow) (List RawPivot) :=
  let prepared : PolyTimeFun (List RawPivot × RawRow) (List RawPivot × RawRow) :=
    fst.pair reduceRowsProg
  let value : PolyTimeFun (List RawPivot × RawRow) BitStr := fst.comp snd
  let j := firstOneProg.comp value
  let test := (SAT.ArrayProg.getD false).comp (j.pair value)
  let row := j.pair snd
  congr ((ite test (append.comp (fst.pair (cons row (const [])))) fst).comp prepared)
    (fun p => insertRow p.1 p.2) (by intro p; rfl)

@[simp] theorem insertRowProg_apply (b : List RawPivot) (r : RawRow) :
    insertRowProg (b, r) = insertRow b r := rfl

/-- The new row's encoded size is bounded by the input row, independent of the
existing basis. This additive bound is the polynomial fold invariant. -/
theorem insertRow_size (b : List RawPivot) (r : RawRow) :
    esize (insertRow b r) ≤ esize b + 20 * esize r + 20 := by
  obtain ⟨hv, hw⟩ := reduceRows_width b r
  have hj := firstOne_le (reduceRows b r).1
  have hjn : Nat.size (firstOne (reduceRows b r).1) ≤ firstOne (reduceRows b r).1 :=
    Nat.size_le.mpr (Nat.lt_two_pow_self)
  have hjc := esize_nat_le (firstOne (reduceRows b r).1)
  have hvc := esize_bitStr_le (reduceRows b r).1
  have hwc := esize_bitStr_le (reduceRows b r).2
  have hv0 := length_le_esize_list r.1
  have hw0 := length_le_esize_list r.2
  have hr : esize r = esize r.1 + esize r.2 + 1 := rfl
  unfold insertRow
  dsimp only
  split
  · have he := esize_list_append b [(firstOne (reduceRows b r).1, reduceRows b r)]
    simp only [esize_list_cons, esize_list_nil, esize_prod] at he
    have hs : esize (reduceRows b r) =
        esize (reduceRows b r).1 + esize (reduceRows b r).2 + 1 := rfl
    omega
  · omega

/-- The complete forward elimination scan. -/
def basisRows (rows : List RawRow) : List RawPivot := rows.foldl insertRow []

/-- Uniform polynomial-time construction of a pivot basis with coefficient certificates. -/
noncomputable def basisRowsProg : PolyTimeFun (List RawRow) (List RawPivot) :=
  let scan := foldlAdd insertRowProg (20 * X + 20) (by
    intro b r
    simpa only [insertRowProg_apply, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_ofNat, Polynomial.eval_X, Nat.add_assoc] using insertRow_size b r)
  congr (scan.comp ((PolyTimeFun.id _).pair (const []))) basisRows (by intro rows; rfl)

@[simp] theorem basisRowsProg_apply (rows : List RawRow) : basisRowsProg rows = basisRows rows := rfl

end MIPRE.LowDegree.BinaryLinear

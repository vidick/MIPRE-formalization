/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryBasisProg
import MIPRE.Foundations.LowDegree.BinaryEchelon

/-! # Correctness of the effective binary basis construction -/

namespace MIPRE.LowDegree.BinaryLinear

variable {n t : ℕ}

/-- The program's pivot choice, applied to typed coordinate vectors. -/
def typedInsert (b : List (Pivot n t)) (r : Row n t) : List (Pivot n t) :=
  let s := typedReduce b r
  let j := firstOne (vectorBits s.1)
  if h : j < n then b ++ [(⟨j, h⟩, s)] else b

theorem vector_eq_zero_of_firstOne_ge (v : Fin n → ZMod 2)
    (h : ¬ firstOne (vectorBits v) < n) : v = 0 := by
  funext i
  rcases binary_eq_zero_or_one (v i) with hi | hi
  · exact hi
  · have hm : true ∈ vectorBits v := List.mem_ofFn.mpr ⟨i, by simp [bit, hi]⟩
    have hj := List.findIdx_lt_length_of_exists (xs := vectorBits v) (p := id)
      ⟨true, hm, rfl⟩
    exact False.elim (h (by simpa [firstOne, vectorBits] using hj))

theorem firstOne_vectorBits_one (v : Fin n → ZMod 2)
    (h : firstOne (vectorBits v) < n) : v ⟨firstOne (vectorBits v), h⟩ = 1 := by
  have hh := firstOne_getD (vectorBits v) (by simpa [vectorBits] using h)
  change (vectorBits v).getD (⟨firstOne (vectorBits v), h⟩ : Fin n) false = true at hh
  rw [getD_vectorBits] at hh
  simpa [bit] using hh

/-- Raw row insertion uses exactly the verified typed pivot rule. -/
theorem insertRow_pivotBits (b : List (Pivot n t)) (r : Row n t) :
    insertRow (b.map pivotBits) (rowBits r) = (typedInsert b r).map pivotBits := by
  unfold insertRow
  rw [reduceRows_rowBits]
  dsimp only [rowBits]
  by_cases h : firstOne (vectorBits (typedReduce b r).1) < n
  · have hh := firstOne_getD (vectorBits (typedReduce b r).1) (by simpa [vectorBits] using h)
    simp only [hh, if_pos rfl]
    simp only [typedInsert, h, dif_pos, List.map_append, List.map_cons, List.map_nil]
    rfl
  · have hh : (vectorBits (typedReduce b r).1).getD
        (firstOne (vectorBits (typedReduce b r).1)) false = false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      exact h (by simpa [vectorBits] using (firstOne_getD_iff _).mp ht)
    simp only [hh, Bool.false_eq_true, if_false]
    simp [typedInsert, h]

/-- Insertion maintains the triangular pivot invariant. -/
theorem IsPivotBasis.typedInsert {b : List (Pivot n t)} (hb : IsPivotBasis b) (r : Row n t) :
    IsPivotBasis (typedInsert b r) := by
  unfold MIPRE.LowDegree.BinaryLinear.typedInsert
  dsimp only
  split
  · rename_i h
    exact hb.append_reduced r _ (firstOne_vectorBits_one _ h)
  · exact hb

/-- Forward elimination, with its vectors and coefficient certificates retained. -/
def typedBasis (rows : List (Row n t)) : List (Pivot n t) := rows.foldl typedInsert []

theorem fold_insertRow_pivotBits (rows : List (Row n t)) (b : List (Pivot n t)) :
    (rows.map rowBits).foldl insertRow (b.map pivotBits) =
      (rows.foldl typedInsert b).map pivotBits := by
  induction rows generalizing b with
  | nil => rfl
  | cons r rows ih =>
    simp only [List.map_cons, List.foldl_cons, insertRow_pivotBits, ih]

/-- The actual ambient program constructs precisely the typed binary basis. -/
theorem basisRowsProg_correct (rows : List (Row n t)) :
    basisRowsProg (rows.map rowBits) = (typedBasis rows).map pivotBits :=
  fold_insertRow_pivotBits rows []

theorem fold_typedInsert_isPivotBasis (rows : List (Row n t)) (b : List (Pivot n t))
    (hb : IsPivotBasis b) : IsPivotBasis (rows.foldl typedInsert b) := by
  induction rows generalizing b with
  | nil => exact hb
  | cons r rows ih => exact ih _ (hb.typedInsert r)

theorem typedBasis_isPivotBasis (rows : List (Row n t)) : IsPivotBasis (typedBasis rows) :=
  fold_typedInsert_isPivotBasis rows [] trivial

theorem typedBasis_linearIndependent (rows : List (Row n t)) :
    LinearIndependent (ZMod 2) (pivotVectors (typedBasis rows)) :=
  (typedBasis_isPivotBasis rows).linearIndependent

theorem typedBasis_length_le (rows : List (Row n t)) : (typedBasis rows).length ≤ n :=
  (typedBasis_isPivotBasis rows).length_le

/-- Adding a stored vector preserves membership in every subspace containing it. -/
theorem typedReduceStep_mem_iff (S : Submodule (ZMod 2) (Fin n → ZMod 2))
    (r : Row n t) (p : Pivot n t) (hp : p.2.1 ∈ S) :
    (typedReduceStep r p).1 ∈ S ↔ r.1 ∈ S := by
  unfold typedReduceStep
  split
  · constructor
    · intro h
      have hs := S.sub_mem h hp
      simpa using hs
    · intro h
      exact S.add_mem h hp
  · rfl

theorem typedReduce_mem_iff (S : Submodule (ZMod 2) (Fin n → ZMod 2))
    (b : List (Pivot n t)) (r : Row n t) (hb : ∀ p ∈ b, p.2.1 ∈ S) :
    (typedReduce b r).1 ∈ S ↔ r.1 ∈ S := by
  induction b generalizing r with
  | nil => rfl
  | cons p b ih =>
    change (typedReduce b (typedReduceStep r p)).1 ∈ S ↔ _
    rw [ih _ (fun q hq => hb q (by simp [hq])),
      typedReduceStep_mem_iff S r p (hb p (by simp))]

/-- Insertion preserves exactly the subspace generated by the old basis and new row. -/
theorem typedInsert_mem_iff (S : Submodule (ZMod 2) (Fin n → ZMod 2))
    (b : List (Pivot n t)) (r : Row n t) :
    (∀ p ∈ typedInsert b r, p.2.1 ∈ S) ↔ (∀ p ∈ b, p.2.1 ∈ S) ∧ r.1 ∈ S := by
  unfold typedInsert
  dsimp only
  split
  · rename_i hj
    constructor
    · intro h
      have hb : ∀ p ∈ b, p.2.1 ∈ S := fun p hp => h p (List.mem_append_left _ hp)
      refine ⟨hb, (typedReduce_mem_iff S b r hb).mp ?_⟩
      exact h (⟨firstOne (vectorBits (typedReduce b r).1), hj⟩, typedReduce b r)
        (List.mem_append_right _ (List.mem_singleton_self _))
    · rintro ⟨hb, hr⟩ p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hb p hp
      · obtain rfl := List.mem_singleton.mp hp
        exact (typedReduce_mem_iff S b r hb).mpr hr
  · rename_i hn
    have hz := vector_eq_zero_of_firstOne_ge (typedReduce b r).1 hn
    constructor
    · intro hb
      refine ⟨hb, (typedReduce_mem_iff S b r hb).mp ?_⟩
      rw [hz]
      exact S.zero_mem
    · exact fun h => h.1

theorem fold_typedInsert_mem_iff (S : Submodule (ZMod 2) (Fin n → ZMod 2))
    (rows : List (Row n t)) (b : List (Pivot n t)) :
    (∀ p ∈ rows.foldl typedInsert b, p.2.1 ∈ S) ↔
      (∀ p ∈ b, p.2.1 ∈ S) ∧ (∀ r ∈ rows, r.1 ∈ S) := by
  induction rows generalizing b with
  | nil => simp
  | cons r rows ih =>
    rw [List.foldl_cons, ih, typedInsert_mem_iff]
    simp only [List.forall_mem_cons]
    tauto

/-- Output and input generate exactly the same binary subspace. -/
theorem typedBasis_mem_iff (S : Submodule (ZMod 2) (Fin n → ZMod 2))
    (rows : List (Row n t)) :
    (∀ p ∈ typedBasis rows, p.2.1 ∈ S) ↔ ∀ r ∈ rows, r.1 ∈ S := by
  simpa [typedBasis] using fold_typedInsert_mem_iff S rows []

def pivotSpan (b : List (Pivot n t)) : Submodule (ZMod 2) (Fin n → ZMod 2) :=
  Submodule.span (ZMod 2) {v | ∃ p ∈ b, p.2.1 = v}

def rowSpan (rows : List (Row n t)) : Submodule (ZMod 2) (Fin n → ZMod 2) :=
  Submodule.span (ZMod 2) {v | ∃ r ∈ rows, r.1 = v}

/-- The constructed independent vectors span the original family. -/
theorem typedBasis_span (rows : List (Row n t)) : pivotSpan (typedBasis rows) = rowSpan rows := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨p, hp, rfl⟩
    apply (typedBasis_mem_iff (rowSpan rows) rows).mpr _ p hp
    intro r hr
    exact Submodule.subset_span ⟨r, hr, rfl⟩
  · apply Submodule.span_le.mpr
    rintro v ⟨r, hr, rfl⟩
    apply (typedBasis_mem_iff (pivotSpan (typedBasis rows)) rows).mp _ r hr
    intro p hp
    exact Submodule.subset_span ⟨p, hp, rfl⟩

end MIPRE.LowDegree.BinaryLinear

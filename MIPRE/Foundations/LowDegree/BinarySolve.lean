/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryBasis

/-! # Solving binary linear systems with certified elimination -/

namespace MIPRE.LowDegree.BinaryLinear

open Cost Cost.PolyTimeFun

variable {n t : ℕ}

@[simp] theorem pivotSpan_nil : pivotSpan ([] : List (Pivot n t)) = ⊥ := by
  simp [pivotSpan]

theorem pivotSpan_cons (p : Pivot n t) (b : List (Pivot n t)) :
    pivotSpan (p :: b) = Submodule.span (ZMod 2) {p.2.1} ⊔ pivotSpan b := by
  have hs : {v | ∃ q ∈ p :: b, q.2.1 = v} =
      insert p.2.1 {v | ∃ q ∈ b, q.2.1 = v} := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, List.mem_cons]
    aesop
  unfold pivotSpan
  rw [hs, Submodule.span_insert]

/-- Within the span of a triangular basis, its pivot coordinates determine the vector. -/
theorem IsPivotBasis.eq_zero_of_pivots_zero {b : List (Pivot n t)} (hb : IsPivotBasis b)
    (v : Fin n → ZMod 2) (hv : v ∈ pivotSpan b) (hz : ∀ p ∈ b, v p.1 = 0) : v = 0 := by
  induction b generalizing v with
  | nil => simpa using hv
  | cons p b ih =>
    rw [pivotSpan_cons] at hv
    obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.mp hv
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp ha
    let π : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 := LinearMap.proj p.1
    have hs : pivotSpan b ≤ π.ker := by
      apply Submodule.span_le.mpr
      rintro w ⟨q, hq, rfl⟩
      exact hb.2.1 q hq
    have hc0 : c p.1 = 0 := hs hc
    have hr0 : r = 0 := by
      have he := congrFun hac p.1
      rw [← hr] at he
      simpa [hb.1, hc0, hz p (by simp)] using he
    rw [hr0, zero_smul] at hr
    have he : c = v := by simpa [← hr] using hac
    subst c
    exact ih hb.2.2 v hc (fun q hq => hz q (by simp [hq]))

/-- A member of the basis span reduces to zero. -/
theorem IsPivotBasis.reduce_eq_zero {b : List (Pivot n t)} (hb : IsPivotBasis b)
    (r : Row n t) (hr : r.1 ∈ pivotSpan b) : (typedReduce b r).1 = 0 := by
  apply hb.eq_zero_of_pivots_zero _ _ (typedReduce_pivots_zero b hb r)
  apply (typedReduce_mem_iff (pivotSpan b) b r _).mpr hr
  intro p hp
  exact Submodule.subset_span ⟨p, hp, rfl⟩

theorem represents_typedInsert
    (L : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (b : List (Pivot n t)) (r : Row n t)
    (hb : ∀ p ∈ b, Represents L p.2) (hr : Represents L r) :
    ∀ p ∈ typedInsert b r, Represents L p.2 := by
  unfold typedInsert
  dsimp only
  split
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hb p hp
    · obtain rfl := List.mem_singleton.mp hp
      exact represents_typedReduce L b r hr hb
  · exact hb

theorem represents_fold_typedInsert
    (L : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (rows : List (Row n t)) (b : List (Pivot n t))
    (hb : ∀ p ∈ b, Represents L p.2) (hr : ∀ r ∈ rows, Represents L r) :
    ∀ p ∈ rows.foldl typedInsert b, Represents L p.2 := by
  induction rows generalizing b with
  | nil => exact hb
  | cons r rows ih =>
    exact ih _ (represents_typedInsert L b r hb (hr r (by simp)))
      (fun s hs => hr s (by simp [hs]))

/-- Every constructed basis row retains its expression in the original generating family. -/
theorem typedBasis_represents
    (L : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (rows : List (Row n t)) (hr : ∀ r ∈ rows, Represents L r) :
    ∀ p ∈ typedBasis rows, Represents L p.2 :=
  represents_fold_typedInsert L rows [] (by simp) hr

/-- The vector plus the image of its certificate is unchanged by reduction. -/
theorem typedReduceStep_error
    (L : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (r : Row n t) (p : Pivot n t) (hp : Represents L p.2) :
    (typedReduceStep r p).1 + L (typedReduceStep r p).2 = r.1 + L r.2 := by
  unfold typedReduceStep
  split
  · change (r.1 + p.2.1) + L (r.2 + p.2.2) = _
    rw [map_add, hp]
    have hz : p.2.1 + p.2.1 = 0 := by
      funext i
      exact CharTwo.add_self_eq_zero _
    calc
      (r.1 + p.2.1) + (L r.2 + p.2.1) = (r.1 + L r.2) + (p.2.1 + p.2.1) := by abel
      _ = r.1 + L r.2 := by rw [hz, add_zero]
  · rfl

theorem typedReduce_error
    (L : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (b : List (Pivot n t)) (r : Row n t) (hb : ∀ p ∈ b, Represents L p.2) :
    (typedReduce b r).1 + L (typedReduce b r).2 = r.1 + L r.2 := by
  induction b generalizing r with
  | nil => rfl
  | cons p b ih =>
    change (typedReduce b (typedReduceStep r p)).1 + L (typedReduce b (typedReduceStep r p)).2 = _
    rw [ih _ (fun q hq => hb q (by simp [hq])), typedReduceStep_error L r p (hb p (by simp))]

/-- Reducing a target with an initially zero certificate solves the original system. -/
theorem solve_certificate
    (L : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (b : List (Pivot n t)) (hb : IsPivotBasis b) (hrep : ∀ p ∈ b, Represents L p.2)
    (v : Fin n → ZMod 2) (hv : v ∈ pivotSpan b) :
    L (typedReduce b (v, 0)).2 = v := by
  have h := typedReduce_error L b (v, 0) hrep
  rw [hb.reduce_eq_zero (v, 0) hv, zero_add, map_zero, add_zero] at h
  exact h

def vectorValue (n : ℕ) (v : BitStr) : Fin n → ZMod 2 := fun i => ofBool (v.getD i false)

@[simp] theorem vectorValue_vectorBits (v : Fin n → ZMod 2) :
    vectorValue n (vectorBits v) = v := by
  funext i
  rw [vectorValue, getD_vectorBits, ofBool_bit]

/-- Solve using a supplied pivot basis; the certificate width is unary. -/
noncomputable def solveBitsProg : PolyTimeFun (Unary × List RawPivot × BitStr) BitStr :=
  snd.comp (reduceRowsProg.comp ((fst.comp snd).pair
    ((snd.comp snd).pair (replicate.comp (fst.pair (const false))))))

/-- Solver output is the canonical fixed-width encoding of its coefficient vector. -/
theorem solveBitsProg_encoding (b : List (Pivot n t)) (v : Fin n → ZMod 2) :
    solveBitsProg (unary t, b.map pivotBits, vectorBits v) =
      vectorBits (typedReduce b (v, 0)).2 := by
  have hz : List.replicate t false = vectorBits (0 : Fin t → ZMod 2) := by
    simp [vectorBits, bit]
  change (reduceRows (b.map pivotBits)
    (vectorBits v, List.replicate (unary t).length false)).2 = _
  rw [length_unary, hz]
  exact congrArg Prod.snd (reduceRows_rowBits b (v, 0))

/-- Correctness of the actual uniform binary solver on every target in the basis span. -/
theorem solveBitsProg_correct
    (L : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (b : List (Pivot n t)) (hb : IsPivotBasis b) (hrep : ∀ p ∈ b, Represents L p.2)
    (v : Fin n → ZMod 2) (hv : v ∈ pivotSpan b) :
    L (vectorValue t (solveBitsProg (unary t, b.map pivotBits, vectorBits v))) = v := by
  have hz : List.replicate t false = vectorBits (0 : Fin t → ZMod 2) := by
    simp [vectorBits, bit]
  change L (vectorValue t (reduceRows (b.map pivotBits)
    (vectorBits v, List.replicate (unary t).length false)).2) = v
  rw [length_unary, hz]
  change L (vectorValue t (reduceRows (b.map pivotBits) (rowBits (v, 0))).2) = v
  rw [reduceRows_rowBits]
  change L (vectorValue t (vectorBits (typedReduce b (v, 0)).2)) = v
  rw [vectorValue_vectorBits]
  exact solve_certificate L b hb hrep v hv

/-- Construct a basis and solve, all within one ambient polynomial-time program. -/
noncomputable def basisSolveProg : PolyTimeFun (Unary × List RawRow × BitStr) BitStr :=
  solveBitsProg.comp (fst.pair ((basisRowsProg.comp (fst.comp snd)).pair (snd.comp snd)))

theorem basisSolveProg_encoding (rows : List (Row n t)) (v : Fin n → ZMod 2) :
    basisSolveProg (unary t, rows.map rowBits, vectorBits v) =
      vectorBits (typedReduce (typedBasis rows) (v, 0)).2 := by
  change solveBitsProg (unary t, basisRowsProg (rows.map rowBits), vectorBits v) = _
  rw [basisRowsProg_correct, solveBitsProg_encoding]

/-- The program solves any consistent binary linear system with supplied generator coordinates. -/
theorem basisSolveProg_correct
    (L : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (rows : List (Row n t)) (hr : ∀ r ∈ rows, Represents L r)
    (v : Fin n → ZMod 2) (hv : v ∈ rowSpan rows) :
    L (vectorValue t (basisSolveProg (unary t, rows.map rowBits, vectorBits v))) = v := by
  change L (vectorValue t (solveBitsProg (unary t, basisRowsProg (rows.map rowBits), vectorBits v))) = v
  rw [basisRowsProg_correct]
  apply solveBitsProg_correct L _ (typedBasis_isPivotBasis rows) (typedBasis_represents L rows hr) v
  rwa [typedBasis_span]

end MIPRE.LowDegree.BinaryLinear

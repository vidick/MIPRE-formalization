/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryKernel
import MIPRE.Foundations.CL.Canonical

/-! # Verified canonical binary elimination for auxiliary dual checks

The effective elimination library chooses the first nonzero coordinate at
each insertion. Its resulting pivot set is exactly the dimension-defined
canonical pivot set used by `CL.canonLin`. Thus its residual, not merely an
arbitrary equivalent quotient representative, computes that canonical map.
-/

noncomputable section
namespace MIPRE.Introspection.AuxiliaryCanonical
open Cost Cost.PolyTimeFun LowDegree.BinaryLinear
open Finset Submodule Module
variable {n t : ℕ}

private theorem firstOne_before (bs : BitStr) (j : ℕ) (hj : j < firstOne bs) :
    bs.getD j false = false := by
  induction bs generalizing j with
  | nil => simp [firstOne] at hj
  | cons b bs ih =>
    cases b with
    | false =>
      cases j with
      | zero => rfl
      | succ j =>
        apply ih j
        simpa [firstOne,List.findIdx_cons] using hj
    | true => simp [firstOne,List.findIdx_cons] at hj

private theorem firstOne_vector_before (v : Fin n → ZMod 2) (i : Fin n)
    (hi : i.val < firstOne (vectorBits v)) : v i = 0 := by
  have h := firstOne_before (vectorBits v) i hi
  rw [getD_vectorBits] at h
  rcases binary_eq_zero_or_one (v i) with hz | ho
  · exact hz
  · simp [bit,ho] at h

def Leading (b : List (Pivot n t)) : Prop :=
  ∀ p ∈ b, ∀ i : Fin n, i < p.1 → p.2.1 i = 0

theorem leading_insert {b : List (Pivot n t)} (hb : Leading b) (r : Row n t) :
    Leading (typedInsert b r) := by
  unfold typedInsert
  dsimp only
  split
  · intro p hp i hi
    rcases List.mem_append.mp hp with hp | hp
    · exact hb p hp i hi
    · obtain rfl := List.mem_singleton.mp hp
      exact firstOne_vector_before _ i hi
  · exact hb

theorem typedBasis_leading (rows : List (Row n t)) : Leading (typedBasis rows) := by
  suffices h : ∀ b, Leading b → Leading (rows.foldl typedInsert b) from h [] (by simp [Leading])
  induction rows with
  | nil => exact fun _ h => h
  | cons r rows ih => exact fun b hb => ih _ (leading_insert hb r)

theorem pivot_one {b : List (Pivot n t)} (hb : IsPivotBasis b) (p : Pivot n t)
    (hp : p ∈ b) : p.2.1 p.1 = 1 := by
  induction b with
  | nil => simp at hp
  | cons q b ih =>
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hb.1
    · exact ih hb.2.2 hp

theorem pivot_nodup {b : List (Pivot n t)} (hb : IsPivotBasis b) :
    (b.map Prod.fst).Nodup := by
  induction b with
  | nil => simp
  | cons p b ih =>
    rw [List.map_cons,List.nodup_cons]
    refine ⟨?_,ih hb.2.2⟩
    intro hm
    obtain ⟨q,hq,he⟩ := List.mem_map.mp hm
    have hz := hb.2.1 q hq
    have ho := pivot_one hb.2.2 q hq
    rw [he] at ho
    exact zero_ne_one (hz.symm.trans ho)

theorem pivotSpan_range (b : List (Pivot n t)) :
    pivotSpan b = Submodule.span (ZMod 2) (Set.range (pivotVectors b)) := by
  unfold pivotSpan
  congr 1
  ext x
  constructor
  · rintro ⟨p,hp,rfl⟩
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hp
    exact ⟨⟨i,hi⟩,by simpa [pivotVectors] using congrArg (fun p : Pivot n t => p.2.1) he⟩
  · rintro ⟨i,rfl⟩
    exact ⟨b[i],List.getElem_mem i.isLt,rfl⟩

theorem finrank_pivotSpan {b : List (Pivot n t)} (hb : IsPivotBasis b) :
    finrank (ZMod 2) (pivotSpan b) = b.length := by
  rw [pivotSpan_range,finrank_span_eq_card hb.linearIndependent,Fintype.card_fin]

/-- A leading nonzero coordinate of a subspace vector is a canonical pivot. -/
theorem leading_mem_pivots (S : Submodule (ZMod 2) (Fin n → ZMod 2))
    (v : Fin n → ZMod 2) (hv : v ∈ S) (j : Fin n) (hj : v j ≠ 0)
    (hprev : ∀ i : Fin n, i < j → v i = 0) : j ∈ CL.pivots S := by
  have hm : v ∈ S ⊓ CL.tail (F := ZMod 2) n j.val :=
    ⟨hv,CL.mem_tail.mpr hprev⟩
  have hn : v ∉ S ⊓ CL.tail (F := ZMod 2) n (j.val+1) := by
    intro h
    exact hj (CL.mem_tail.mp h.2 j (Nat.lt_succ_self _))
  have hlt : S ⊓ CL.tail (F := ZMod 2) n (j.val+1) < S ⊓ CL.tail n j.val :=
    lt_of_le_of_ne (inf_le_inf_left _ (CL.tail_mono (Nat.le_succ _)))
      (fun he => hn (he ▸ hm))
  exact CL.mem_pivots.mpr (Submodule.finrank_lt_finrank_of_lt hlt)

/-- The program's stored pivot indices equal the source's canonical pivot set. -/
theorem pivot_set_canonical {b : List (Pivot n t)} (hb : IsPivotBasis b) (hl : Leading b) :
    (b.map Prod.fst).toFinset = CL.pivots (pivotSpan b) := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro j hj
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hj)
    exact leading_mem_pivots (pivotSpan b) p.2.1 (Submodule.subset_span ⟨p,hp,rfl⟩)
      p.1 (by rw [pivot_one hb p hp]; exact one_ne_zero) (hl p hp)
  · rw [CL.card_pivots,finrank_pivotSpan hb,List.toFinset_card_of_nodup (pivot_nodup hb),
      List.length_map]

private theorem reduce_sub_mem (S : Submodule (ZMod 2) (Fin n → ZMod 2))
    (b : List (Pivot n t)) (hb : ∀ p ∈ b, p.2.1 ∈ S) (r : Row n t) :
    r.1 - (typedReduce b r).1 ∈ S := by
  induction b generalizing r with
  | nil => change r.1-r.1 ∈ S; simp
  | cons p b ih =>
    have hp : r.1 - (typedReduceStep r p).1 ∈ S := by
      unfold typedReduceStep
      split
      · simpa using S.neg_mem (hb p (by simp))
      · simp
    have hr := ih (fun q hq => hb q (by simp [hq])) (typedReduceStep r p)
    change r.1 - (typedReduce b (typedReduceStep r p)).1 ∈ S
    simpa only [sub_add_sub_cancel] using S.add_mem hp hr

theorem typedReduce_canonLin {b : List (Pivot n t)} (hb : IsPivotBasis b) (hl : Leading b)
    (r : Row n t) : (typedReduce b r).1 = CL.canonLin (pivotSpan b) r.1 := by
  have hm : (typedReduce b r).1 ∈ CL.canonCompl (pivotSpan b) := by
    intro j hj
    rw [← pivot_set_canonical hb hl] at hj
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hj)
    exact typedReduce_pivots_zero b hb r p hp
  have hs := reduce_sub_mem (pivotSpan b) b
    (fun p hp => Submodule.subset_span ⟨p,hp,rfl⟩) r
  have hz : CL.canonLin (pivotSpan b) (r.1-(typedReduce b r).1) = 0 := by
    exact (CL.ker_canonLin (pivotSpan b) ▸ hs : _ ∈ (CL.canonLin (pivotSpan b)).ker)
  rw [map_sub,show CL.canonLin (pivotSpan b) (typedReduce b r).1 = (typedReduce b r).1 from
    Submodule.projection_apply_of_mem_left (CL.isCompl_canonCompl (pivotSpan b)).symm hm] at hz
  exact (sub_eq_zero.mp hz).symm

/-- Canonical reduction for an arbitrary finite generating family. -/
theorem typedBasis_canonLin (rows : List (Row n t)) (v : Fin n → ZMod 2) :
    (typedReduce (typedBasis rows) (v,0)).1 = CL.canonLin (rowSpan rows) v := by
  rw [typedReduce_canonLin (typedBasis_isPivotBasis rows) (typedBasis_leading rows),typedBasis_span]

/-- A single uniform polynomial-time program for the exact canonical quotient
representative. The coefficient width is zero, since no certificate is output. -/
def canonicalProg : PolyTimeFun (List BitStr × BitStr) BitStr :=
  let rows := (map ((PolyTimeFun.id BitStr).pair (const ([] : BitStr)))).comp fst
  fst.comp (reduceRowsProg.comp ((basisRowsProg.comp rows).pair (snd.pair (const ([] : BitStr)))))

theorem canonicalProg_correct (vs : List (Fin n → ZMod 2)) (v : Fin n → ZMod 2) :
    canonicalProg (vs.map vectorBits,vectorBits v) =
      vectorBits (CL.canonLin (Submodule.span (ZMod 2) {x | x ∈ vs}) v) := by
  let rows : List (Row n 0) := vs.map (fun x => (x,0))
  have he : (vs.map vectorBits).map (fun x => (x,([] : BitStr))) = rows.map rowBits := by
    simp [rows,rowBits,vectorBits,List.map_map]
  change (reduceRows (basisRowsProg ((vs.map vectorBits).map (fun x => (x,([] : BitStr)))))
    (vectorBits v,[])).1 = _
  rw [he,basisRowsProg_correct]
  change (reduceRows ((typedBasis rows).map pivotBits) (rowBits (v,(0 : Fin 0 → ZMod 2)))).1 = _
  rw [reduceRows_rowBits]
  change vectorBits (typedReduce (typedBasis rows) (v,0)).1 = _
  rw [typedBasis_canonLin]
  congr 2
  unfold rowSpan rows
  congr 1
  ext x
  simp

end MIPRE.Introspection.AuxiliaryCanonical
end

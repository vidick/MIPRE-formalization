/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Sofic.Measure.Stage

@[expose] public section

/-!
# Locally good patterns

The two directions of the support condition of the polytopes:

* `goodP_map`: the pattern of a good set of words (in particular of a subgroup) on a set of words
  closed under shortening is locally good;
* `extW_not_mem_badSet`: the set of words of a locally good pattern avoids every bad set whose
  words it contains (Lemma I:941 (2): a limit of such patterns is carried by `Good s`).
-/

namespace MIPRE.Tailored.Sofic.Measure

open SubgroupTestValue

/-- The words of a bad set. -/
def badWords : Unit ⊕ (Word × Word × ℕ × Bool) ⊕ (Word × Word) ⊕ (Word × Word × ℕ × Bool) →
    List Word
  | .inl _ => [[]]
  | .inr (.inl (u₁, u₂, i, c)) => [u₁ ++ (i, c) :: (i, !c) :: u₂]
  | .inr (.inr (.inl (u, v))) => [u, v, u ++ invW v]
  | .inr (.inr (.inr (u₁, u₂, i, c))) => [u₁ ++ (i, c) :: u₂]

/-- Deleting letters keeps a word among the words up to a length. -/
theorem mem_wordsUpTo_of_sublist {L n : ℕ} {u v : Word} (hu : u ∈ wordsUpTo L n)
    (h : v.Sublist u) : v ∈ wordsUpTo L n := by
  rw [mem_wordsUpTo] at hu ⊢
  exact ⟨h.length_le.trans hu.1, fun l hl => hu.2 l (h.subset hl)⟩

theorem sublist_take_append_drop (u : Word) (j k : ℕ) (hjk : j ≤ k) :
    (u.take j ++ u.drop k).Sublist u := by
  conv_rhs => rw [← List.take_append_drop j u]
  refine List.Sublist.append (List.Sublist.refl _) ?_
  rw [show k = j + (k - j) by omega, ← List.drop_drop]
  exact List.drop_sublist _ _

/-- The decomposition of a word at a cancelling pair. -/
theorem eq_of_cancel2 {u : Word} {j : ℕ} (h : cancel2 u j = true) :
    u = u.take j ++ (u.getD j (0, false)) :: ((u.getD j (0, false)).1, !(u.getD j (0, false)).2) ::
      u.drop (j + 2) := by
  simp only [cancel2, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨hj, h1⟩, h2⟩ := h
  have hj' : j < u.length := by omega
  rw [List.getD_eq_getElem _ _ hj', List.getD_eq_getElem _ _ hj] at h1 h2
  rw [List.getD_eq_getElem _ _ hj']
  conv_lhs => rw [← List.take_append_drop j u]
  congr 1
  rw [List.drop_eq_getElem_cons hj', List.drop_eq_getElem_cons hj]
  congr 2
  exact Prod.ext h1.symm h2

theorem eq_of_drop1 {s : ℕ} {u : Word} {j : ℕ} (h : drop1 s u j = true) :
    u = u.take j ++ (u.getD j (0, false)) :: u.drop (j + 1) ∧ s ≤ (u.getD j (0, false)).1 := by
  simp only [drop1, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hj, h1⟩ := h
  refine ⟨?_, h1⟩
  rw [List.getD_eq_getElem _ _ hj]
  conv_lhs => rw [← List.take_append_drop j u]
  rw [List.drop_eq_getElem_cons hj]

/-- **The pattern of a good set of words is locally good.** -/
theorem goodP_map {s L n : ℕ} {A : WordSpace} (hA : A ∈ Good s) :
    goodP s (wordsUpTo L n) ((wordsUpTo L n).map A) = true := by
  set W := wordsUpTo L n
  have he : ∀ u ∈ W, extW W (W.map A) u = A u := fun u hu => extW_map A hu
  have hnil : ([] : Word) ∈ W := mem_wordsUpTo.2 ⟨by simp, by simp⟩
  simp only [goodP, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', beq_iff_eq]
  refine ⟨⟨by rw [he _ hnil]; exact hA.1, fun u hu j hj => ⟨?_, ?_⟩⟩, fun u hu v hv => ?_⟩
  · by_cases hc : cancel2 u j = true
    · right
      have hu' := mem_wordsUpTo_of_sublist hu (sublist_take_append_drop u j (j + 2) (by omega))
      rw [he _ hu, he _ hu']
      conv_lhs => rw [eq_of_cancel2 hc]
      exact hA.2.1 _ _ _ _
    · left; simpa using hc
  · by_cases hc : drop1 s u j = true
    · right
      have hu' := mem_wordsUpTo_of_sublist hu (sublist_take_append_drop u j (j + 1) (by omega))
      rw [he _ hu, he _ hu']
      obtain ⟨hdec, hs⟩ := eq_of_drop1 hc
      conv_lhs => rw [hdec]
      exact hA.2.2.2 _ _ _ _ hs
    · left; simpa using hc
  · by_cases hm : (memW W (u ++ invW v) && extW W (W.map A) u && extW W (W.map A) v) = true
    · right
      simp only [Bool.and_eq_true, memW_iff] at hm
      obtain ⟨⟨hm, h1⟩, h2⟩ := hm
      rw [he _ hm]
      rw [he _ hu] at h1; rw [he _ hv] at h2
      exact hA.2.2.1 _ _ h1 h2
    · left; simpa using hm

theorem cancel2_append (u₁ u₂ : Word) (i : ℕ) (c : Bool) :
    cancel2 (u₁ ++ (i, c) :: (i, !c) :: u₂) u₁.length = true := by
  simp [cancel2, List.getD_eq_getElem?_getD]

theorem drop1_append {s : ℕ} (u₁ u₂ : Word) {i : ℕ} (c : Bool) (hi : s ≤ i) :
    drop1 s (u₁ ++ (i, c) :: u₂) u₁.length = true := by
  simp [drop1, List.getD_eq_getElem?_getD, hi]

/-- **A locally good pattern avoids the bad sets within its words.** -/
theorem extW_not_mem_badSet {s L n : ℕ} {p : List Bool}
    (hp : goodP s (wordsUpTo L n) p = true) (b) (hb : ∀ w ∈ badWords b, w ∈ wordsUpTo L n) :
    extW (wordsUpTo L n) p ∉ badSet s b := by
  set W := wordsUpTo L n
  simp only [goodP, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', beq_iff_eq] at hp
  obtain ⟨⟨hnil, hloc⟩, hmul⟩ := hp
  rcases b with _ | ⟨u₁, u₂, i, c⟩ | ⟨u, v⟩ | ⟨u₁, u₂, i, c⟩
  · simp [badSet, hnil]
  · have hu := hb (u₁ ++ (i, c) :: (i, !c) :: u₂) (by simp [badWords])
    have h := (hloc _ hu u₁.length (by simp)).1
    rw [cancel2_append] at h
    replace h := h.resolve_left (by simp)
    simp only [badSet, Set.mem_ofPred_eq, ne_eq, not_not]
    rw [h]
    congr 1
    simp [List.drop_append]
  · have hu := hb u (by simp [badWords])
    have hv := hb v (by simp [badWords])
    have huv := hb (u ++ invW v) (by simp [badWords])
    simp only [badSet, Set.mem_ofPred_eq, not_and]
    intro h1 h2
    have := hmul u hu v hv
    rw [(memW_iff).2 huv, h1, h2] at this
    simpa using this
  · simp only [badSet, Set.mem_ofPred_eq, not_and, ne_eq, not_not]
    intro hi
    have hu := hb (u₁ ++ (i, c) :: u₂) (by simp [badWords])
    have h := (hloc _ hu u₁.length (by simp)).2
    rw [drop1_append _ _ _ hi] at h
    replace h := h.resolve_left (by simp)
    rw [h]
    congr 1
    simp [List.drop_append]

end MIPRE.Tailored.Sofic.Measure

end

/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Prelim/Seed.lean
-/
/-
# Shared-permutation classical sampling (ported fallback seed)

Ported from `QuantumParallelRepetition.lean` (github.com/openai/ten-proofs,
Apache-2.0; see lean/NOTICE), lines 9686-10224, with the outer namespace renamed.
Classical/scalar material only; no quantum layer is imported.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Prelim.FiniteProb

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

noncomputable section

open scoped BigOperators

namespace ClassicalSampling

variable {α : Type*} [Fintype α] [DecidableEq α]

def markedFirst (rank : α ≃ Fin (Fintype.card α))
    (marked : Finset α) (nonempty : marked.Nonempty)
    (permutation : Equiv.Perm α) : α :=
  permutation.symm
    (rank.symm
      ((marked.image (fun a => rank (permutation a))).min'
        (nonempty.image (fun a => rank (permutation a)))))

omit [DecidableEq α] in

theorem markedFirst_mem (rank : α ≃ Fin (Fintype.card α))
    (marked : Finset α) (nonempty : marked.Nonempty)
    (permutation : Equiv.Perm α) :
    markedFirst rank marked nonempty permutation ∈ marked := by
  have hmin := (marked.image (fun a => rank (permutation a))).min'_mem
    (nonempty.image (fun a => rank (permutation a)))
  obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp hmin
  simpa [markedFirst, ← heq] using ha

omit [DecidableEq α] in

theorem markedFirst_rank (rank : α ≃ Fin (Fintype.card α))
    (marked : Finset α) (nonempty : marked.Nonempty)
    (permutation : Equiv.Perm α) :
    rank (permutation (markedFirst rank marked nonempty permutation)) =
      (marked.image (fun a => rank (permutation a))).min'
        (nonempty.image (fun a => rank (permutation a))) := by
  simp [markedFirst]

omit [DecidableEq α] in

theorem markedFirst_rank_le (rank : α ≃ Fin (Fintype.card α))
    (marked : Finset α) (nonempty : marked.Nonempty)
    (permutation : Equiv.Perm α) {a : α} (ha : a ∈ marked) :
    rank (permutation (markedFirst rank marked nonempty permutation)) ≤
      rank (permutation a) := by
  rw [markedFirst_rank]
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩)

omit [DecidableEq α] in

theorem markedFirst_eq_of_mem_of_rank_le
    (rank : α ≃ Fin (Fintype.card α))
    (marked : Finset α) (nonempty : marked.Nonempty)
    (permutation : Equiv.Perm α) {a : α} (ha : a ∈ marked)
    (hle : ∀ b ∈ marked, rank (permutation a) ≤ rank (permutation b)) :
    markedFirst rank marked nonempty permutation = a := by
  apply permutation.injective
  apply rank.injective
  exact le_antisymm
    (markedFirst_rank_le rank marked nonempty permutation ha)
    (hle _ (markedFirst_mem rank marked nonempty permutation))

omit [DecidableEq α] in

theorem markedFirst_subset_eq_of_mem
    (rank : α ≃ Fin (Fintype.card α))
    {small large : Finset α}
    (hsmall : small.Nonempty) (hlarge : large.Nonempty)
    (permutation : Equiv.Perm α)
    (hsub : small ⊆ large)
    (hmem : markedFirst rank large hlarge permutation ∈ small) :
    markedFirst rank small hsmall permutation =
      markedFirst rank large hlarge permutation := by
  apply markedFirst_eq_of_mem_of_rank_le rank small hsmall permutation hmem
  intro a ha
  exact markedFirst_rank_le rank large hlarge permutation (hsub ha)

theorem markedFirst_eq_iff_union_first_mem_inter
    (rank : α ≃ Fin (Fintype.card α))
    (left right : Finset α)
    (hleft : left.Nonempty) (hright : right.Nonempty)
    (permutation : Equiv.Perm α) :
    markedFirst rank left hleft permutation =
        markedFirst rank right hright permutation ↔
      markedFirst rank (left ∪ right) (hleft.mono Finset.subset_union_left)
          permutation ∈ left ∩ right := by
  let hunion : (left ∪ right).Nonempty :=
    hleft.mono Finset.subset_union_left
  constructor
  · intro hagree
    have hfirst :
        markedFirst rank (left ∪ right) hunion permutation =
          markedFirst rank left hleft permutation := by
      apply markedFirst_eq_of_mem_of_rank_le
        rank (left ∪ right) hunion permutation
      · exact Finset.mem_union_left right
          (markedFirst_mem rank left hleft permutation)
      · intro a ha
        rcases Finset.mem_union.mp ha with ha | ha
        · exact markedFirst_rank_le rank left hleft permutation ha
        · rw [hagree]
          exact markedFirst_rank_le rank right hright permutation ha
    apply Finset.mem_inter.mpr
    constructor
    · rw [hfirst]
      exact markedFirst_mem rank left hleft permutation
    · rw [hfirst, hagree]
      exact markedFirst_mem rank right hright permutation
  · intro hcommon
    have hleft' := markedFirst_subset_eq_of_mem
      rank hleft hunion permutation Finset.subset_union_left
      (Finset.mem_inter.mp hcommon).1
    have hright' := markedFirst_subset_eq_of_mem
      rank hright hunion permutation Finset.subset_union_right
      (Finset.mem_inter.mp hcommon).2
    exact hleft'.trans hright'.symm

theorem markedFirst_ne_iff_union_first_mem_symmDiff
    (rank : α ≃ Fin (Fintype.card α))
    (left right : Finset α)
    (hleft : left.Nonempty) (hright : right.Nonempty)
    (permutation : Equiv.Perm α) :
    markedFirst rank left hleft permutation ≠
        markedFirst rank right hright permutation ↔
      markedFirst rank (left ∪ right) (hleft.mono Finset.subset_union_left)
          permutation ∈ (left \ right) ∪ (right \ left) := by
  let hunion : (left ∪ right).Nonempty :=
    hleft.mono Finset.subset_union_left
  let a := markedFirst rank (left ∪ right) hunion permutation
  have ha : a ∈ left ∪ right :=
    markedFirst_mem rank (left ∪ right) hunion permutation
  have hagree := markedFirst_eq_iff_union_first_mem_inter
    rank left right hleft hright permutation
  change markedFirst rank left hleft permutation ≠
      markedFirst rank right hright permutation ↔
    a ∈ (left \ right) ∪ (right \ left)
  constructor
  · intro hne
    have hninter : a ∉ left ∩ right := by
      intro hinter
      exact hne (hagree.mpr hinter)
    rcases Finset.mem_union.mp ha with hla | hra
    · apply Finset.mem_union_left
      exact Finset.mem_sdiff.mpr
        ⟨hla, fun hright' => hninter (Finset.mem_inter.mpr ⟨hla, hright'⟩)⟩
    · apply Finset.mem_union_right
      exact Finset.mem_sdiff.mpr
        ⟨hra, fun hleft' => hninter (Finset.mem_inter.mpr ⟨hleft', hra⟩)⟩
  · intro hdiff heq
    have hinter : a ∈ left ∩ right := hagree.mp heq
    rcases Finset.mem_union.mp hdiff with hdiff | hdiff
    · exact (Finset.mem_sdiff.mp hdiff).2 (Finset.mem_inter.mp hinter).2
    · exact (Finset.mem_sdiff.mp hdiff).2 (Finset.mem_inter.mp hinter).1

omit [Fintype α] in

theorem swap_mem_iff_of_mem {marked : Finset α} {x y : α}
    (hx : x ∈ marked) (hy : y ∈ marked) (a : α) :
    Equiv.swap x y a ∈ marked ↔ a ∈ marked := by
  by_cases hax : a = x
  · subst a
    simp [hx, hy]
  · by_cases hay : a = y
    · subst a
      simp [hx, hy]
    · rw [Equiv.swap_apply_of_ne_of_ne hax hay]

theorem markedFirst_swap_trans
    (rank : α ≃ Fin (Fintype.card α))
    (marked : Finset α) (nonempty : marked.Nonempty)
    {x y : α} (hx : x ∈ marked) (hy : y ∈ marked)
    (permutation : Equiv.Perm α) :
    markedFirst rank marked nonempty ((Equiv.swap x y).trans permutation) =
      Equiv.swap x y (markedFirst rank marked nonempty permutation) := by
  apply markedFirst_eq_of_mem_of_rank_le
    rank marked nonempty ((Equiv.swap x y).trans permutation)
  · exact (swap_mem_iff_of_mem hx hy _).mpr
      (markedFirst_mem rank marked nonempty permutation)
  · intro a ha
    have hminimal := markedFirst_rank_le rank marked nonempty permutation
      ((swap_mem_iff_of_mem hx hy a).mpr ha)
    simpa [Equiv.trans_apply] using hminimal

def firstFiber (rank : α ≃ Fin (Fintype.card α))
    (marked : Finset α) (nonempty : marked.Nonempty)
    (a : α) : Finset (Equiv.Perm α) :=
  Finset.univ.filter fun permutation =>
    markedFirst rank marked nonempty permutation = a

theorem firstFiber_card_eq
    (rank : α ≃ Fin (Fintype.card α))
    (marked : Finset α) (nonempty : marked.Nonempty)
    {x y : α} (hx : x ∈ marked) (hy : y ∈ marked) :
    (firstFiber rank marked nonempty x).card =
      (firstFiber rank marked nonempty y).card := by
  classical
  refine Finset.card_bij'
    (fun permutation _ => (Equiv.swap x y).trans permutation)
    (fun permutation _ => (Equiv.swap x y).trans permutation)
    ?_ ?_ ?_ ?_
  · intro permutation hpermutation
    have hfirst : markedFirst rank marked nonempty permutation = x :=
      (Finset.mem_filter.mp hpermutation).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [markedFirst_swap_trans rank marked nonempty hx hy permutation,
      hfirst, Equiv.swap_apply_left]
  · intro permutation hpermutation
    have hfirst : markedFirst rank marked nonempty permutation = y :=
      (Finset.mem_filter.mp hpermutation).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [markedFirst_swap_trans rank marked nonempty hx hy permutation,
      hfirst, Equiv.swap_apply_right]
  · intro permutation _
    ext a
    simp [Equiv.trans_apply]
  · intro permutation _
    ext a
    simp [Equiv.trans_apply]

theorem markedFirst_event_card_mul
    (rank : α ≃ Fin (Fintype.card α))
    (marked : Finset α) (nonempty : marked.Nonempty)
    (event : Finset α) (hevent : event ⊆ marked) :
    (Finset.univ.filter fun permutation : Equiv.Perm α =>
        markedFirst rank marked nonempty permutation ∈ event).card *
        marked.card =
      event.card * Fintype.card (Equiv.Perm α) := by
  classical
  obtain ⟨base, hbase⟩ := nonempty
  have hevent_card :
      (Finset.univ.filter fun permutation : Equiv.Perm α =>
          markedFirst rank marked ⟨base, hbase⟩ permutation ∈ event).card =
        event.card * (firstFiber rank marked ⟨base, hbase⟩ base).card := by
    calc
      (Finset.univ.filter fun permutation : Equiv.Perm α =>
          markedFirst rank marked ⟨base, hbase⟩ permutation ∈ event).card =
          ∑ a ∈ event,
            (firstFiber rank marked ⟨base, hbase⟩ a).card := by
              symm
              simpa [firstFiber] using
                (Finset.sum_card_fiberwise_eq_card_filter
                  (Finset.univ : Finset (Equiv.Perm α)) event
                  (markedFirst rank marked ⟨base, hbase⟩))
      _ = event.card * (firstFiber rank marked ⟨base, hbase⟩ base).card :=
        Finset.sum_const_nat fun a ha =>
          firstFiber_card_eq rank marked ⟨base, hbase⟩ (hevent ha) hbase
  have htotal_card :
      Fintype.card (Equiv.Perm α) =
        marked.card * (firstFiber rank marked ⟨base, hbase⟩ base).card := by
    calc
      Fintype.card (Equiv.Perm α) =
          (Finset.univ : Finset (Equiv.Perm α)).card := by simp
      _ = ∑ a ∈ marked,
            (firstFiber rank marked ⟨base, hbase⟩ a).card := by
              simpa [firstFiber] using
                (Finset.card_eq_sum_card_fiberwise
                  (f := markedFirst rank marked ⟨base, hbase⟩)
                  (s := (Finset.univ : Finset (Equiv.Perm α)))
                  (t := marked)
                  (fun permutation _ =>
                    markedFirst_mem rank marked ⟨base, hbase⟩ permutation))
      _ = marked.card * (firstFiber rank marked ⟨base, hbase⟩ base).card :=
        Finset.sum_const_nat fun a ha =>
          firstFiber_card_eq rank marked ⟨base, hbase⟩ ha hbase
  change
    (Finset.univ.filter fun permutation : Equiv.Perm α =>
        markedFirst rank marked ⟨base, hbase⟩ permutation ∈ event).card *
        marked.card =
      event.card * Fintype.card (Equiv.Perm α)
  rw [hevent_card, htotal_card]
  ac_rfl

theorem sharedPermutation_disagreement_card_mul
    (rank : α ≃ Fin (Fintype.card α))
    (left right : Finset α)
    (hleft : left.Nonempty) (hright : right.Nonempty) :
    (Finset.univ.filter fun permutation : Equiv.Perm α =>
        markedFirst rank left hleft permutation ≠
          markedFirst rank right hright permutation).card *
        (left ∪ right).card =
      ((left \ right) ∪ (right \ left)).card *
        Fintype.card (Equiv.Perm α) := by
  classical
  let hunion : (left ∪ right).Nonempty :=
    hleft.mono Finset.subset_union_left
  have hsubset : (left \ right) ∪ (right \ left) ⊆ left ∪ right := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact Finset.mem_union_left right (Finset.mem_sdiff.mp ha).1
    · exact Finset.mem_union_right left (Finset.mem_sdiff.mp ha).1
  have hfilter :
      (Finset.univ.filter fun permutation : Equiv.Perm α =>
        markedFirst rank left hleft permutation ≠
          markedFirst rank right hright permutation) =
      (Finset.univ.filter fun permutation : Equiv.Perm α =>
        markedFirst rank (left ∪ right) hunion permutation ∈
          (left \ right) ∪ (right \ left)) := by
    ext permutation
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact markedFirst_ne_iff_union_first_mem_symmDiff
      rank left right hleft hright permutation
  rw [hfilter]
  exact markedFirst_event_card_mul rank (left ∪ right) hunion
    ((left \ right) ∪ (right \ left)) hsubset

def uniformPermutationProbability (event : Equiv.Perm α → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter fun permutation : Equiv.Perm α =>
      event permutation).card : ℝ) / Fintype.card (Equiv.Perm α)

theorem markedFirst_event_probability
    (rank : α ≃ Fin (Fintype.card α))
    (marked : Finset α) (nonempty : marked.Nonempty)
    (event : Finset α) (hevent : event ⊆ marked) :
    uniformPermutationProbability
      (fun permutation : Equiv.Perm α =>
        markedFirst rank marked nonempty permutation ∈ event) =
      (event.card : ℝ) / marked.card := by
  classical
  have hpermutation : 0 < (Fintype.card (Equiv.Perm α) : ℝ) := by
    exact_mod_cast
      (Fintype.card_pos_iff.mpr ⟨Equiv.refl α⟩ :
        0 < Fintype.card (Equiv.Perm α))
  have hmarked : 0 < (marked.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr nonempty : 0 < marked.card)
  unfold uniformPermutationProbability
  apply (div_eq_div_iff hpermutation.ne' hmarked.ne').mpr
  have hcount := markedFirst_event_card_mul
    rank marked nonempty event hevent
  have hreal :
      ((Finset.univ.filter fun permutation : Equiv.Perm α =>
        markedFirst rank marked nonempty permutation ∈ event).card : ℝ) *
          (marked.card : ℝ) =
        (event.card : ℝ) * (Fintype.card (Equiv.Perm α) : ℝ) := by
    exact_mod_cast hcount
  simpa only [] using hreal

theorem sharedPermutation_disagreement_probability
    (rank : α ≃ Fin (Fintype.card α))
    (left right : Finset α)
    (hleft : left.Nonempty) (hright : right.Nonempty) :
    uniformPermutationProbability
      (fun permutation : Equiv.Perm α =>
        markedFirst rank left hleft permutation ≠
          markedFirst rank right hright permutation) =
      (((left \ right) ∪ (right \ left)).card : ℝ) /
        (left ∪ right).card := by
  classical
  have hpermutation : 0 < (Fintype.card (Equiv.Perm α) : ℝ) := by
    exact_mod_cast
      (Fintype.card_pos_iff.mpr ⟨Equiv.refl α⟩ :
        0 < Fintype.card (Equiv.Perm α))
  have hunion : 0 < ((left ∪ right).card : ℝ) := by
    exact_mod_cast
      (Finset.card_pos.mpr
        (hleft.mono Finset.subset_union_left) :
        0 < (left ∪ right).card)
  unfold uniformPermutationProbability
  apply (div_eq_div_iff hpermutation.ne' hunion.ne').mpr
  exact_mod_cast
    sharedPermutation_disagreement_card_mul rank left right hleft hright

theorem sharedPermutation_disagreement_probability_le
    (rank : α ≃ Fin (Fintype.card α))
    (left right : Finset α)
    (hleft : left.Nonempty) (hright : right.Nonempty) :
    uniformPermutationProbability
      (fun permutation : Equiv.Perm α =>
        markedFirst rank left hleft permutation ≠
          markedFirst rank right hright permutation) ≤
      (((left \ right) ∪ (right \ left)).card : ℝ) / left.card := by
  rw [sharedPermutation_disagreement_probability
    rank left right hleft hright]
  apply div_le_div_of_nonneg_left
  · positivity
  · exact_mod_cast (Finset.card_pos.mpr hleft : 0 < left.card)
  · exact_mod_cast (Finset.card_le_card Finset.subset_union_left :
      left.card ≤ (left ∪ right).card)

def markedTotalVariation (left right : Finset α) : ℝ :=
  (((left \ right) ∪ (right \ left)).card : ℝ) /
    (2 * (left.card : ℝ))

theorem sharedPermutation_disagreement_probability_le_two_mul_tv
    (rank : α ≃ Fin (Fintype.card α))
    (left right : Finset α)
    (hleft : left.Nonempty) (hright : right.Nonempty)
    (_equal_card : left.card = right.card) :
    uniformPermutationProbability
      (fun permutation : Equiv.Perm α =>
        markedFirst rank left hleft permutation ≠
          markedFirst rank right hright permutation) ≤
      2 * markedTotalVariation left right := by
  calc
    uniformPermutationProbability
        (fun permutation : Equiv.Perm α =>
          markedFirst rank left hleft permutation ≠
            markedFirst rank right hright permutation) ≤
        (((left \ right) ∪ (right \ left)).card : ℝ) / left.card :=
      sharedPermutation_disagreement_probability_le
        rank left right hleft hright
    _ = 2 * markedTotalVariation left right := by
      unfold markedTotalVariation
      have hcard : (left.card : ℝ) ≠ 0 := by
        exact_mod_cast (Finset.card_ne_zero.mpr hleft)
      field_simp

section RationalMarks

variable {β : Type*} [Fintype β] [DecidableEq β]

def rationalMarked (denominator : ℕ) (numerator : β → ℕ) :
    Finset (β × Fin denominator) := by
  classical
  exact Finset.univ.filter fun point =>
    point.2.val < numerator point.1

theorem rationalMarked_fiber_card
    (denominator : ℕ) (numerator : β → ℕ) (letter : β) :
    ((rationalMarked denominator numerator).filter
      fun point => point.1 = letter).card =
        min denominator (numerator letter) := by
  classical
  calc
    ((rationalMarked denominator numerator).filter
      fun point => point.1 = letter).card =
        (Finset.univ.filter fun copy : Fin denominator =>
          copy.val < numerator letter).card := by
      refine Finset.card_bij'
        (fun point _ => point.2)
        (fun copy _ => (letter, copy))
        ?_ ?_ ?_ ?_
      · intro point hpoint
        have hpoint' :
            point.2.val < numerator point.1 ∧ point.1 = letter := by
          simpa [rationalMarked] using hpoint
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, by simpa [hpoint'.2] using hpoint'.1⟩
      · intro copy hcopy
        have hcopy' : copy.val < numerator letter :=
          (Finset.mem_filter.mp hcopy).2
        simp [rationalMarked, hcopy']
      · intro point hpoint
        have hletter : point.1 = letter :=
          (Finset.mem_filter.mp hpoint).2
        apply Prod.ext
        · exact hletter.symm
        · rfl
      · intro copy _
        rfl
    _ = min denominator (numerator letter) := by
      simpa using
        (Fin.card_filter_val_lt (n := denominator)
          (m := numerator letter))

omit [DecidableEq β] in

theorem rationalNumerator_le_denominator
    (denominator : ℕ) (numerator : β → ℕ)
    (normalized : (∑ letter, numerator letter) = denominator)
    (letter : β) : numerator letter ≤ denominator := by
  rw [← normalized]
  exact Finset.single_le_sum
    (fun a _ => Nat.zero_le (numerator a)) (Finset.mem_univ letter)

theorem rationalMarked_card
    (denominator : ℕ) (numerator : β → ℕ)
    (normalized : (∑ letter, numerator letter) = denominator) :
    (rationalMarked denominator numerator).card = denominator := by
  classical
  calc
    (rationalMarked denominator numerator).card =
        ∑ letter : β,
          ((rationalMarked denominator numerator).filter
            fun point => point.1 = letter).card := by
      simpa using
        (Finset.card_eq_sum_card_fiberwise
          (f := fun point : β × Fin denominator => point.1)
          (s := rationalMarked denominator numerator)
          (t := (Finset.univ : Finset β))
          (fun _ _ => Finset.mem_univ _))
    _ = ∑ letter : β, numerator letter := by
      apply Finset.sum_congr rfl
      intro letter _
      rw [rationalMarked_fiber_card]
      exact min_eq_right
        (rationalNumerator_le_denominator denominator numerator normalized letter)
    _ = denominator := normalized

theorem rationalMarked_nonempty
    (denominator : ℕ) (numerator : β → ℕ)
    (normalized : (∑ letter, numerator letter) = denominator)
    (positive : 0 < denominator) :
    (rationalMarked denominator numerator).Nonempty := by
  apply Finset.card_pos.mp
  rw [rationalMarked_card denominator numerator normalized]
  exact positive

theorem rationalMarked_letter_probability
    (denominator : ℕ) (numerator : β → ℕ)
    (normalized : (∑ letter, numerator letter) = denominator)
    (nonempty : (rationalMarked denominator numerator).Nonempty)
    (rank : (β × Fin denominator) ≃
      Fin (Fintype.card (β × Fin denominator)))
    (letter : β) :
    uniformPermutationProbability
      (fun permutation : Equiv.Perm (β × Fin denominator) =>
        (markedFirst rank (rationalMarked denominator numerator)
          nonempty permutation).1 = letter) =
      (numerator letter : ℝ) / denominator := by
  classical
  let marked := rationalMarked denominator numerator
  let event := marked.filter fun point => point.1 = letter
  have hsub : event ⊆ marked := Finset.filter_subset _ _
  calc
    uniformPermutationProbability
        (fun permutation : Equiv.Perm (β × Fin denominator) =>
          (markedFirst rank marked nonempty permutation).1 = letter) =
        uniformPermutationProbability
          (fun permutation : Equiv.Perm (β × Fin denominator) =>
            markedFirst rank marked nonempty permutation ∈ event) := by
      congr 1
      funext permutation
      apply propext
      simp [event, markedFirst_mem rank marked nonempty permutation]
    _ = (event.card : ℝ) / marked.card :=
      markedFirst_event_probability rank marked nonempty event hsub
    _ = (numerator letter : ℝ) / denominator := by
      change
        (((rationalMarked denominator numerator).filter
          fun point => point.1 = letter).card : ℝ) /
          (rationalMarked denominator numerator).card =
        (numerator letter : ℝ) / denominator
      rw [rationalMarked_fiber_card,
        min_eq_right
          (rationalNumerator_le_denominator
            denominator numerator normalized letter),
        rationalMarked_card denominator numerator normalized]

end RationalMarks

end ClassicalSampling

end

end CommutingRepetition

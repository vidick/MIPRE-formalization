/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.SubgroupTestValue
public import MIPRE.Tailored.Sofic.Hamming
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import MIPRE.Tactics

@[expose] public section

/-!
# Robustness: close actions have close values

Paper I, Claim I:1480: the value of a subgroup test changes by at most the significance-weighted
Hamming distance between two actions on the same set. The *significance* of a generator `k`
(I:1474) is the expected number of occurrences of `k` or `k⁻¹` in the words of a challenge:

`sig T k = E_{challenge} Σ_{w ∈ K} #{letters of w with generator k}`.

The proof is the paper's. A word's permutation differs between the two actions at most at the
points where one of its letters does (`diffCard_mul`, applied letter by letter), an inverse
letter differing exactly as often as the direct one (`diffCard_inv`); the stabilizer decisions
on the words of a challenge, hence the decision itself, agree wherever the words' permutations
do; and a union bound over the words.

The paper states the claim for the edit distance, the minimum over relabellings; only the
Hamming distance on one set is needed here.
-/

namespace MIPRE.Tailored.Sofic

open SubgroupTestValue Finset

/-- The number of letters of `w` whose generator is `k`, direct or inverse (`v_k(w)`, I:1470;
on an unreduced word, which can only increase the count). -/
def wordCount (k : ℕ) (w : Word) : ℕ := w.countP fun l => l.1 = k

/-- The significance of the generator `k` in the test `T` (I:1474): the expected number of
occurrences of `k` in the words of a challenge. -/
noncomputable def sig (T : SubgroupTestData) (k : ℕ) : ℝ :=
  (T.challenges.map fun c => (c.1 : ℝ) * (c.2.1.map fun w => (wordCount k w : ℝ)).sum).sum /
    T.totalWeight

theorem sig_nonneg (T : SubgroupTestData) (k : ℕ) : 0 ≤ sig T k := by
  unfold sig
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply List.sum_nonneg
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨c, _, rfl⟩ := hx
  apply mul_nonneg (Nat.cast_nonneg _)
  apply List.sum_nonneg
  intro y hy
  simp only [List.mem_map] at hy
  obtain ⟨w, _, rfl⟩ := hy
  exact Nat.cast_nonneg _

/-! ## List sums -/

private theorem list_sum_finset_sum {β ι : Type*} (L : List β) (s : Finset ι) (F : β → ι → ℝ) :
    (L.map fun b => ∑ k ∈ s, F b k).sum = ∑ k ∈ s, (L.map fun b => F b k).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih, Finset.sum_add_distrib]

private theorem list_sum_le_sum {β : Type*} (L : List β) (f g : β → ℝ)
    (h : ∀ b ∈ L, f b ≤ g b) : (L.map f).sum ≤ (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

private theorem abs_list_sum_sub_le {β : Type*} (L : List β) (f g : β → ℝ) :
    |(L.map f).sum - (L.map g).sum| ≤ (L.map fun b => |f b - g b|).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    calc |f a + (L.map f).sum - (g a + (L.map g).sum)|
        = |(f a - g a) + ((L.map f).sum - (L.map g).sum)| := by ring_nf
      _ ≤ |f a - g a| + |(L.map f).sum - (L.map g).sum| := abs_add_le _ _
      _ ≤ _ := by linarith

/-- A union bound over a list. -/
private theorem card_le_of_forall_exists {α β : Type*} [DecidableEq α] (L : List β)
    (P : β → α → Prop) [∀ b, DecidablePred (P b)] :
    ∀ D : Finset α, (∀ p ∈ D, ∃ b ∈ L, P b p) →
      D.card ≤ (L.map fun b => (D.filter (P b)).card).sum := by
  induction L with
  | nil =>
    intro D hD
    rcases D.eq_empty_or_nonempty with rfl | ⟨p, hp⟩
    · simp
    · obtain ⟨b, hb, _⟩ := hD p hp; simp at hb
  | cons a L ih =>
    intro D hD
    simp only [List.map_cons, List.sum_cons]
    have h1 : D ⊆ D.filter (P a) ∪ D.filter (fun p => ¬P a p) := by
      intro p hp; by_cases h : P a p <;> simp [hp, h]
    refine (card_le_card h1).trans ((card_union_le _ _).trans (Nat.add_le_add_left ?_ _))
    refine (ih _ ?_).trans (List.sum_le_sum fun b _ =>
      card_le_card (filter_subset_filter _ (filter_subset _ _)))
    intro p hp
    simp only [mem_filter] at hp
    obtain ⟨b, hb, hP⟩ := hD p hp.1
    rcases List.mem_cons.mp hb with rfl | hb
    · exact absurd hP hp.2
    · exact ⟨b, hb, hP⟩

/-! ## Words -/

namespace FiniteActionLemmas

variable {n : ℕ}

theorem wordPerm_nil (σ : FiniteAction n) : σ.wordPerm [] = 1 := by
  simp [FiniteAction.wordPerm]

theorem wordPerm_cons (σ : FiniteAction n) (l : Letter) (w : Word) :
    σ.wordPerm (l :: w) = σ.letterPerm l * σ.wordPerm w := by
  simp [FiniteAction.wordPerm]

theorem wordPerm_append (σ : FiniteAction n) (u v : Word) :
    σ.wordPerm (u ++ v) = σ.wordPerm u * σ.wordPerm v := by
  simp [FiniteAction.wordPerm]

end FiniteActionLemmas

open FiniteActionLemmas

variable {n : ℕ} (σ : FiniteAction n) (ρ' : Fin n → Equiv.Perm (Fin σ.N))

/-- The action `ρ'` on the points of `σ`. -/
abbrev withPerms : FiniteAction n := ⟨σ.N, σ.N_pos, ρ'⟩

theorem diffCard_letterPerm (l : Letter) :
    diffCard (σ.letterPerm l) ((withPerms σ ρ').letterPerm l) =
      if h : l.1 < n then diffCard (σ.σ ⟨l.1, h⟩) (ρ' ⟨l.1, h⟩) else 0 := by
  unfold FiniteAction.letterPerm
  by_cases h : l.1 < n
  · rw [dite_eq_left h, dite_eq_left h, dite_eq_left h]
    split_ifs
    · exact diffCard_inv _ _
    · rfl
  · rw [dite_eq_right h, dite_eq_right h, dite_eq_right h]
    exact diffCard_self _

theorem diffCard_wordPerm (w : Word) :
    diffCard (σ.wordPerm w) ((withPerms σ ρ').wordPerm w) ≤
      (w.map fun l => diffCard (σ.letterPerm l) ((withPerms σ ρ').letterPerm l)).sum := by
  induction w with
  | nil => simp only [wordPerm_nil, List.map_nil, List.sum_nil]; exact (diffCard_self _).le
  | cons l w ih =>
    rw [wordPerm_cons, wordPerm_cons, List.map_cons, List.sum_cons]
    exact (diffCard_mul _ _ _ _).trans (Nat.add_le_add_left ih _)

/-- The letters' distances, summed along a word, are the generators' distances weighted by their
numbers of occurrences. -/
theorem sum_letter_dist (w : Word) :
    (w.map fun l => (diffCard (σ.letterPerm l) ((withPerms σ ρ').letterPerm l) : ℝ) / σ.N).sum =
      ∑ k : Fin n, (wordCount k w : ℝ) * dH (σ.σ k) (ρ' k) := by
  induction w with
  | nil => simp [wordCount]
  | cons l w ih =>
    rw [List.map_cons, List.sum_cons, ih]
    have hc : ∀ k : Fin n, (wordCount k (l :: w) : ℝ) =
        (if l.1 = k then 1 else 0) + wordCount k w := by
      intro k
      simp only [wordCount, List.countP_cons]
      split_ifs <;> simp_all [add_comm]
    simp only [hc, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul]
    congr 1
    rw [diffCard_letterPerm]
    by_cases h : l.1 < n
    · rw [dite_eq_left h]
      rw [Finset.sum_eq_single ⟨l.1, h⟩]
      · simp [dH]
      · intro k _ hk
        rw [ite_eq_right]
        intro e; apply hk; ext; exact e.symm
      · simp
    · rw [dite_eq_right h]
      simp only [Nat.cast_zero, zero_div]
      symm
      apply Finset.sum_eq_zero
      intro k _
      rw [ite_eq_right]
      intro e; apply h; rw [e]; exact k.2

/-- The stabilizer decisions, hence the decision of a challenge, agree where the words'
permutations do. -/
theorem passes_iff_of_agree (K : List Word) (C : List (List (ℕ × Bool))) (p : Fin σ.N)
    (h : ∀ w ∈ K, σ.wordPerm w p = (withPerms σ ρ').wordPerm w p) :
    σ.Passes K C p ↔ (withPerms σ ρ').Passes K C p := by
  have key : ∀ (i : ℕ) (hi : i < K.length),
      decide (σ.InStab p (K[i]'hi)) = decide ((withPerms σ ρ').InStab p (K[i]'hi)) := by
    intro i hi
    apply decide_eq_decide.mpr
    unfold FiniteAction.InStab
    rw [h _ (List.getElem_mem hi)]
  unfold FiniteAction.Passes FiniteAction.LitHolds
  constructor
  · rintro ⟨c, hc, hall⟩
    refine ⟨c, hc, fun lit hl => ?_⟩
    obtain ⟨hi, hd⟩ := hall lit hl
    exact ⟨hi, (key _ hi).symm.trans hd⟩
  · rintro ⟨c, hc, hall⟩
    refine ⟨c, hc, fun lit hl => ?_⟩
    obtain ⟨hi, hd⟩ := hall lit hl
    exact ⟨hi, (key _ hi).trans hd⟩

theorem abs_passProb_sub_le (K : List Word) (C : List (List (ℕ × Bool))) :
    |σ.passProb K C - (withPerms σ ρ').passProb K C| ≤
      (K.map fun w => ∑ k : Fin n, (wordCount k w : ℝ) * dH (σ.σ k) (ρ' k)).sum := by
  classical
  set D := univ.filter fun p : Fin σ.N => ∃ w ∈ K, σ.wordPerm w p ≠ (withPerms σ ρ').wordPerm w p
  set A := univ.filter fun p : Fin σ.N => σ.Passes K C p
  set B := univ.filter fun p : Fin σ.N => (withPerms σ ρ').Passes K C p
  have hAB : A.card ≤ B.card + D.card := by
    refine le_trans (card_le_card ?_) (card_union_le B D)
    intro p
    simp only [A, B, D, mem_filter, mem_univ, true_and, mem_union]
    intro hp
    by_cases hd : ∃ w ∈ K, σ.wordPerm w p ≠ (withPerms σ ρ').wordPerm w p
    · exact Or.inr hd
    · push Not at hd
      exact Or.inl ((passes_iff_of_agree σ ρ' K C p hd).mp hp)
  have hBA : B.card ≤ A.card + D.card := by
    refine le_trans (card_le_card ?_) (card_union_le A D)
    intro p
    simp only [A, B, D, mem_filter, mem_univ, true_and, mem_union]
    intro hp
    by_cases hd : ∃ w ∈ K, σ.wordPerm w p ≠ (withPerms σ ρ').wordPerm w p
    · exact Or.inr hd
    · push Not at hd
      exact Or.inl ((passes_iff_of_agree σ ρ' K C p hd).mpr hp)
  have hD : (D.card : ℝ) / σ.N ≤
      (K.map fun w => ∑ k : Fin n, (wordCount k w : ℝ) * dH (σ.σ k) (ρ' k)).sum := by
    have h1 := card_le_of_forall_exists K
      (fun w (p : Fin σ.N) => σ.wordPerm w p ≠ (withPerms σ ρ').wordPerm w p) D
      (fun p hp => by simpa [D] using hp)
    have h1' : D.card ≤ (K.map fun w =>
        (w.map fun l => diffCard (σ.letterPerm l) ((withPerms σ ρ').letterPerm l)).sum).sum :=
      h1.trans (List.sum_le_sum fun w _ =>
        (card_le_card (filter_subset_filter _ (subset_univ _))).trans (diffCard_wordPerm σ ρ' w))
    have hN : (0 : ℝ) < σ.N := by exact_mod_cast σ.N_pos
    rw [div_le_iff₀ hN]
    refine (Nat.cast_le.mpr h1').trans (le_of_eq ?_)
    rw [Nat.cast_list_sum, List.map_map, ← List.sum_map_mul_right]
    congr 1
    apply List.map_congr_left
    intro w _
    rw [← sum_letter_dist σ ρ' w, ← List.sum_map_mul_right, Function.comp_apply, Nat.cast_list_sum,
      List.map_map]
    congr 1
    apply List.map_congr_left
    intro l _
    rw [Function.comp_apply, div_mul_cancel₀ _ hN.ne']
  unfold FiniteAction.passProb
  have hN : (0 : ℝ) < σ.N := by exact_mod_cast σ.N_pos
  change |(A.card : ℝ) / σ.N - (B.card : ℝ) / σ.N| ≤ _
  rw [← sub_div, abs_div, abs_of_pos hN]
  refine le_trans ?_ hD
  gcongr
  rw [abs_le]
  constructor
  · have : (B.card : ℝ) ≤ A.card + D.card := by exact_mod_cast hBA
    linarith
  · have : (A.card : ℝ) ≤ B.card + D.card := by exact_mod_cast hAB
    linarith

/-- **Robustness** (Claim I:1480): two actions of the free group on the same finite set have test
values within their significance-weighted Hamming distance. -/
theorem abs_value_sub_le (T : SubgroupTestData) (σ : FiniteAction T.nGen)
    (ρ' : Fin T.nGen → Equiv.Perm (Fin σ.N)) :
    |T.value σ - T.value (withPerms σ ρ')| ≤ ∑ k : Fin T.nGen, sig T k * dH (σ.σ k) (ρ' k) := by
  unfold SubgroupTestData.value sig
  rw [← sub_div, abs_div, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) T.totalWeight)]
  simp only [div_mul_eq_mul_div, ← Finset.sum_div]
  gcongr
  refine (abs_list_sum_sub_le _ _ _).trans ?_
  have : ∀ c ∈ T.challenges, |(c.1 : ℝ) * σ.passProb c.2.1 c.2.2 -
      (c.1 : ℝ) * (withPerms σ ρ').passProb c.2.1 c.2.2| ≤
      ∑ k : Fin T.nGen, (c.1 : ℝ) * (c.2.1.map fun w => (wordCount k w : ℝ)).sum *
        dH (σ.σ k) (ρ' k) := by
    intro c _
    rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    refine (mul_le_mul_of_nonneg_left (abs_passProb_sub_le σ ρ' c.2.1 c.2.2)
      (Nat.cast_nonneg _)).trans (le_of_eq ?_)
    rw [list_sum_finset_sum, Finset.mul_sum]
    congr 1
    ext k
    rw [List.sum_map_mul_right, mul_assoc]
  refine (list_sum_le_sum _ _ _ this).trans (le_of_eq ?_)
  rw [list_sum_finset_sum]
  congr 1
  ext k
  rw [List.sum_map_mul_right]

end MIPRE.Tailored.Sofic

end

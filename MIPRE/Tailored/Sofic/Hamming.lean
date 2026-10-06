/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Basic.Real.Basic
public import MIPRE.Tactics

@[expose] public section

/-!
# The normalized Hamming distance on permutations

Paper I (arXiv:2408.00110), I:1351–1370: the normalized Hamming distance
`d_H(a, b) = P_p[a p ≠ b p]` between two permutations of one finite set. We work with the
number `diffCard a b` of points where `a` and `b` differ, and `dH a b = diffCard a b / |α|`.

The facts used by the robustness claim and the stability claims: the triangle inequality, the
product bound `d(a b, a' b') ≤ d(a, a') + d(b, b')` (the paper's "iterated triangle inequality"),
inversion invariance `d(a⁻¹, b⁻¹) = d(a, b)`, and the count of the points a commutator moves.
-/

namespace MIPRE.Tailored.Sofic

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The number of points at which two permutations differ. -/
def diffCard (a b : Equiv.Perm α) : ℕ := (univ.filter fun p => a p ≠ b p).card

/-- The normalized Hamming distance (I:1356): the fraction of points at which two permutations
differ. -/
noncomputable def dH (a b : Equiv.Perm α) : ℝ := (diffCard a b : ℝ) / Fintype.card α

omit [Fintype α] [DecidableEq α] in
@[simp] theorem perm_inv_apply_self' (a : Equiv.Perm α) (x : α) : a⁻¹ (a x) = x :=
  Equiv.Perm.inv_eq_iff_eq.mpr rfl

omit [Fintype α] [DecidableEq α] in
@[simp] theorem perm_apply_inv_self' (a : Equiv.Perm α) (x : α) : a (a⁻¹ x) = x :=
  (Equiv.eq_symm_apply a).mp rfl

omit [DecidableEq α] in
/-- Composing a predicate with a permutation does not change how many points satisfy it. -/
theorem card_filter_comp_perm (e : Equiv.Perm α) (P : α → Prop) [DecidablePred P] :
    (univ.filter fun p => P (e p)).card = (univ.filter P).card :=
  Finset.card_equiv e (by simp)

theorem diffCard_comm (a b : Equiv.Perm α) : diffCard a b = diffCard b a := by
  unfold diffCard; congr 1; ext p; simp [ne_comm]

@[simp] theorem diffCard_self (a : Equiv.Perm α) : diffCard a a = 0 := by
  simp [diffCard]

theorem diffCard_le_card (a b : Equiv.Perm α) : diffCard a b ≤ Fintype.card α :=
  (card_filter_le _ _).trans (by simp)

/-- The triangle inequality. -/
theorem diffCard_triangle (a b c : Equiv.Perm α) : diffCard a c ≤ diffCard a b + diffCard b c := by
  unfold diffCard
  refine (card_le_card ?_).trans (card_union_le _ _)
  intro p
  simp only [mem_filter, mem_univ, true_and, mem_union]
  intro h
  by_contra h'
  rw [not_or, not_not, not_not] at h'
  exact h (h'.1.trans h'.2)

/-- The product bound: `d(a b, a' b') ≤ d(a, a') + d(b, b')`. -/
theorem diffCard_mul (a a' b b' : Equiv.Perm α) :
    diffCard (a * b) (a' * b') ≤ diffCard a a' + diffCard b b' := by
  have h2 : (univ.filter fun p => a (b p) ≠ a' (b p)).card = diffCard a a' :=
    card_filter_comp_perm b (fun q => a q ≠ a' q)
  unfold diffCard at h2 ⊢
  rw [← h2]
  refine (card_le_card ?_).trans (card_union_le _ _)
  intro p
  simp only [mem_filter, mem_univ, true_and, mem_union]
  intro h
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply] at h
  by_cases hb : b p = b' p
  · left; rwa [← hb] at h
  · right; exact hb

/-- Inversion does not change the distance. -/
theorem diffCard_inv (a b : Equiv.Perm α) : diffCard a⁻¹ b⁻¹ = diffCard a b := by
  unfold diffCard
  rw [← card_filter_comp_perm a]
  congr 1
  ext q
  simp only [mem_filter, mem_univ, true_and, perm_inv_apply_self']
  constructor
  · intro h h'; apply h; rw [h']; simp
  · intro h h'; apply h
    have := congrArg b h'
    simp only [perm_apply_inv_self'] at this
    exact this.symm

/-- The points a commutator `a b a⁻¹ b⁻¹` moves are as many as those at which `a` and `b` do not
commute. -/
theorem card_commutator_moves (a b : Equiv.Perm α) :
    (univ.filter fun q => (a * b * a⁻¹ * b⁻¹) q ≠ q).card =
      (univ.filter fun r => a (b r) ≠ b (a r)).card := by
  rw [← card_filter_comp_perm (b * a)]
  congr 1
  ext r
  simp [Equiv.Perm.mul_apply]

theorem dH_nonneg (a b : Equiv.Perm α) : 0 ≤ dH a b := by
  unfold dH; positivity

theorem dH_le_one (a b : Equiv.Perm α) : dH a b ≤ 1 := by
  unfold dH
  rcases (Nat.eq_zero_or_pos (Fintype.card α)) with h | h
  · simp [h]
  · rw [div_le_one (by exact_mod_cast h)]
    exact_mod_cast diffCard_le_card a b

theorem dH_comm (a b : Equiv.Perm α) : dH a b = dH b a := by
  unfold dH; rw [diffCard_comm]

theorem dH_triangle (a b c : Equiv.Perm α) : dH a c ≤ dH a b + dH b c := by
  unfold dH
  rw [← add_div]
  gcongr
  exact_mod_cast diffCard_triangle a b c

theorem dH_mul (a a' b b' : Equiv.Perm α) : dH (a * b) (a' * b') ≤ dH a a' + dH b b' := by
  unfold dH
  rw [← add_div]
  gcongr
  exact_mod_cast diffCard_mul a a' b b'

theorem dH_inv (a b : Equiv.Perm α) : dH a⁻¹ b⁻¹ = dH a b := by
  unfold dH; rw [diffCard_inv]

end MIPRE.Tailored.Sofic

end

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Sofic.Assoc
public import MIPRE.Tailored.Sofic.Robust
public import Mathlib.Algebra.BigOperators.Intervals
public import MIPRE.Tactics

@[expose] public section

/-!
# The value of the associated test, challenge by challenge

For the associated test `assocTest g` of `MIPRE/Tailored/Sofic/Assoc.lean`:

* `qw g x y`, the weight of the challenge at the question pair `(x, y)` (the game's convention
  when every weight vanishes: weight `1` at `(0, 0)`), and `qwTot g > 0` their total; every sum
  over the challenges is the `qw`-weighted sum over the pairs `(x, y)`, `x, y ≤ nV`
  (`sum_challenges`), so the value and the significance are such sums (`value_eq`, `sig_eq`).
* The per-point consequences of passing the challenge at `(x, y)` (Checks 1–3, I:2086): `J` moves
  the point, `J²`, `[J, X]`, `X²`, `[X, X']` fix it for the variables `X, X'` at `x` and at `y`,
  and each readable variable `X` fixes it or `J X` does. Hence the number of points where one
  of these fails is at most the number of points failing the challenge (`card_J_fixed_le` and
  the following).
-/

namespace MIPRE.Tailored.Sofic

open SubgroupTestValue TailoredGameValue Finset FiniteActionLemmas

variable (g : TailoredGameData)

/-! ## Weights -/

/-- The weight of the challenge at `(x, y)`. -/
def qw (x y : ℕ) : ℕ :=
  if (wts g).totalWeight = 0 then (if x = 0 ∧ y = 0 then 1 else 0) else (wts g).questionWeight x y

/-- The total weight of the challenges. -/
def qwTot : ℕ := ∑ x ∈ range (g.nV + 1), ∑ y ∈ range (g.nV + 1), qw g x y

private theorem list_sum_range (n : ℕ) (h : ℕ → ℝ) :
    ((List.range n).map h).sum = ∑ i ∈ range n, h i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

private theorem list_sum_flatMap {α β : Type*} (L : List α) (f : α → List β) (F : β → ℝ) :
    ((L.flatMap f).map F).sum = (L.map fun a => ((f a).map F).sum).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [List.flatMap_cons, ih]

theorem qwTot_eq_of_ne (h : (wts g).totalWeight ≠ 0) : qwTot g = (wts g).totalWeight := by
  unfold qwTot HaltingGameValue.GameData.totalWeight
  simp only [qw, h, ite_false]
  rw [← Fin.sum_univ_eq_sum_range (fun x => ∑ y ∈ range (g.nV + 1),
    (wts g).questionWeight x y)]
  congr 1
  ext x
  rw [← Fin.sum_univ_eq_sum_range (fun y => (wts g).questionWeight x y)]
  rfl

theorem qwTot_pos : 0 < qwTot g := by
  by_cases h : (wts g).totalWeight = 0
  · unfold qwTot
    have : qw g 0 0 = 1 := by simp [qw, h]
    calc 0 < qw g 0 0 := by omega
      _ = ∑ y ∈ range (g.nV + 1), qw g 0 y := by
          rw [sum_eq_single 0 (fun y _ hy => by simp [qw, h, hy]) (by simp)]
      _ ≤ _ := single_le_sum (f := fun x => ∑ y ∈ range (g.nV + 1), qw g x y)
          (fun _ _ => Nat.zero_le _) (by simp)
  · rw [qwTot_eq_of_ne g h]; omega

/-- Every weighted sum over the challenges is the `qw`-weighted sum over the question pairs. -/
theorem sum_challenges (Ψ : List Word × List (List (ℕ × Bool)) → ℝ) :
    ((assocTest g).challenges.map fun c => (c.1 : ℝ) * Ψ c.2).sum =
      ∑ x ∈ range (g.nV + 1), ∑ y ∈ range (g.nV + 1),
        (qw g x y : ℝ) * Ψ (words g x y, clauses g x y) := by
  unfold assocTest
  by_cases h : (wts g).totalWeight = 0
  · simp only [h, ite_true, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, challenge]
    rw [sum_eq_single 0, sum_eq_single 0]
    · simp [qw, h]
    · intro y _ hy; simp [qw, h, hy]
    · simp
    · intro x _ hx; apply sum_eq_zero; intro y _; simp [qw, h, hx]
    · simp
  · simp only [h, ite_false]
    rw [list_sum_flatMap, list_sum_range]
    congr 1
    ext x
    rw [List.map_map, list_sum_range]
    congr 1
    ext y
    simp [challenge, qw, h]

theorem assocTest_totalWeight_eq : ((assocTest g).totalWeight : ℝ) = qwTot g := by
  have h := sum_challenges g (fun _ => 1)
  simp only [mul_one] at h
  unfold SubgroupTestData.totalWeight
  rw [Nat.cast_list_sum, List.map_map]
  refine (Eq.trans ?_ h).trans ?_
  · rfl
  · unfold qwTot; push_cast; rfl

/-- The value of the associated test as a sum over the question pairs. -/
theorem value_eq (σ : FiniteAction (nGen g)) :
    (assocTest g).value σ = (∑ x ∈ range (g.nV + 1), ∑ y ∈ range (g.nV + 1),
      (qw g x y : ℝ) * σ.passProb (words g x y) (clauses g x y)) / qwTot g := by
  unfold SubgroupTestData.value
  rw [assocTest_totalWeight_eq]
  congr 1
  exact sum_challenges g (fun c => σ.passProb c.1 c.2)

/-- The significance in the associated test as a sum over the question pairs. -/
theorem sig_eq (k : ℕ) :
    sig (assocTest g) k = (∑ x ∈ range (g.nV + 1), ∑ y ∈ range (g.nV + 1),
      (qw g x y : ℝ) * ((words g x y).map fun w => (wordCount k w : ℝ)).sum) / qwTot g := by
  unfold sig
  rw [assocTest_totalWeight_eq]
  congr 1
  exact sum_challenges g (fun c => (c.1.map fun w => (wordCount k w : ℝ)).sum)

/-! ## Words and their permutations -/

section Perms

variable {n : ℕ} (σ : FiniteAction n)

theorem letterPerm_flip (l : Letter) : σ.letterPerm (l.1, !l.2) = (σ.letterPerm l)⁻¹ := by
  unfold FiniteAction.letterPerm
  by_cases h : l.1 < n
  · rw [dite_eq_left h, dite_eq_left h]
    cases l.2 <;> simp
  · rw [dite_eq_right h, dite_eq_right h, inv_one]

theorem wordPerm_invW (u : Word) : σ.wordPerm (invW u) = (σ.wordPerm u)⁻¹ := by
  induction u with
  | nil => simp [invW, wordPerm_nil]
  | cons l u ih =>
    have : invW (l :: u) = invW u ++ [(l.1, !l.2)] := by simp [invW]
    rw [this, wordPerm_append, ih, wordPerm_cons, wordPerm_cons, wordPerm_nil, mul_one,
      letterPerm_flip, mul_inv_rev]

theorem wordPerm_commW (u v : Word) : σ.wordPerm (commW u v) =
    σ.wordPerm u * σ.wordPerm v * (σ.wordPerm u)⁻¹ * (σ.wordPerm v)⁻¹ := by
  simp only [commW, wordPerm_append, wordPerm_invW]

theorem wordPerm_genW (k : ℕ) : σ.wordPerm (genW k) = genPerm σ k := by
  simp [genW, genPerm, wordPerm_cons, wordPerm_nil]

end Perms

/-! ## Passing a challenge -/

section Passing

variable {g} {n : ℕ} (σ : FiniteAction n)

private theorem litHolds_of_getElem? {K : List Word} {q : Fin σ.N} {i : ℕ} {b : Bool} {w : Word}
    (h : σ.LitHolds K q (i, b)) (hw : K[i]? = some w) : decide (σ.InStab q w) = b := by
  obtain ⟨hi, hd⟩ := h
  rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hw
  rw [← hw]
  exact hd

private theorem clause_of_passes {x y : ℕ} {q : Fin σ.N}
    (h : σ.Passes (words g x y) (clauses g x y) q) :
    ∃ r, ∀ lit ∈ clause g x y r, σ.LitHolds (words g x y) q lit := by
  obtain ⟨c, hc, hall⟩ := h
  unfold clauses at hc
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hc
  exact ⟨r, hall⟩

/-- Passing a challenge gives every fixed literal (Checks 1 and 2). -/
theorem fixed_of_passes {x y : ℕ} {q : Fin σ.N}
    (h : σ.Passes (words g x y) (clauses g x y) q) {wb : Word × Bool}
    (hwb : wb ∈ fixedLits g x y) : decide (σ.InStab q wb.1) = wb.2 := by
  obtain ⟨r, hr⟩ := clause_of_passes σ h
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hwb
  have hlit : (i, wb.2) ∈ clause g x y r := by
    unfold clause
    simp only [List.mem_append, List.mem_map]
    left; left
    exact ⟨(wb, i), List.mem_zipIdx_iff_getElem?.mpr hi, rfl⟩
  apply litHolds_of_getElem? σ (hr _ hlit)
  have hlt : i < (fixedLits g x y).length := by
    by_contra hge
    rw [List.getElem?_eq_none (by omega)] at hi
    cases hi
  unfold words
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simpa using hlt),
    List.getElem?_map, hi]
  rfl

private theorem flatMap_pair_getElem? {α : Type*} (f : α → α) :
    ∀ (L : List α) (t : ℕ) (ht : t < L.length),
      (L.flatMap fun X => [X, f X])[2 * t]? = some L[t] ∧
        (L.flatMap fun X => [X, f X])[2 * t + 1]? = some (f L[t])
  | [], _, ht => by simp at ht
  | a :: L, 0, _ => by simp
  | a :: L, t + 1, ht => by
    have := flatMap_pair_getElem? f L t (by simp at ht; omega)
    simp only [List.flatMap_cons, List.getElem_cons_succ]
    rw [show 2 * (t + 1) = 2 * t + 2 by ring, show 2 * t + 2 + 1 = 2 * t + 1 + 2 by ring]
    simpa using this

/-- Passing a challenge gives every readable literal (Check 3). -/
theorem read_of_passes {x y : ℕ} {q : Fin σ.N}
    (h : σ.Passes (words g x y) (clauses g x y) q) {X : Word} (hX : X ∈ readVars g x y) :
    σ.InStab q X ∨ σ.InStab q (wJ ++ X) := by
  obtain ⟨r, hr⟩ := clause_of_passes σ h
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hX
  set F := (fixedLits g x y).length
  set b : ℕ := if r.getD t false then 1 else 0
  have hlit : (F + 2 * t + b, true) ∈ clause g x y r := by
    unfold clause
    simp only [List.mem_append, List.mem_map, List.mem_range]
    left; right
    exact ⟨t, ht, rfl⟩
  have hpair := flatMap_pair_getElem? (fun X => wJ ++ X) (readVars g x y) t ht
  have hK : ∀ j, (readWords g x y)[j]? ≠ none → (words g x y)[F + j]? = (readWords g x y)[j]? := by
    intro j hj
    have hj' : j < (readWords g x y).length := by
      by_contra hge; exact hj (List.getElem?_eq_none (by omega))
    unfold words
    rw [List.getElem?_append_left (by simp [F]; omega), List.getElem?_append_right (by simp [F])]
    simp [F]
  have hd := hr _ hlit
  by_cases hb : r.getD t false = true
  · have hb1 : b = 1 := ite_eq_left hb
    right
    have hw : (words g x y)[F + 2 * t + b]? = some (wJ ++ (readVars g x y)[t]) := by
      rw [hb1, add_assoc, hK _ (by unfold readWords; rw [hpair.2]; simp)]
      unfold readWords; exact hpair.2
    have := litHolds_of_getElem? σ hd hw
    simpa using this
  · have hb0 : b = 0 := ite_eq_right hb
    left
    have hw : (words g x y)[F + 2 * t + b]? = some (readVars g x y)[t] := by
      rw [hb0, add_zero, hK _ (by unfold readWords; rw [hpair.1]; simp)]
      unfold readWords; exact hpair.1
    have := litHolds_of_getElem? σ hd hw
    simpa using this

end Passing

end MIPRE.Tailored.Sofic

end

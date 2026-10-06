/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Sofic.Assoc
public import MIPRE.Tactics

@[expose] public section

/-!
# Passing a challenge of the associated test, under Checks 1–3

For an action `σ` passing Checks 1–3 (`Checks g σ`), the decision of the challenge at `(x, y)`
of `assocTest g` reduces to Check 4: the point `p` passes exactly when every constraint word
whose readable part is the readable value `rdv σ x y p` of `p` fixes `p` (`passes_iff`). The
fixed literals then always hold (`fixedLits_holds`), and the readable literal of a readable
variable holds for exactly one of its two words (`inStab_readWord_iff`).

Also: the value of the test as a `μ`-weighted average of pass probabilities (`value_eq_sum`), and
the number of distinct constraint words (`length_consWords_le`).
-/

namespace MIPRE.Tailored.Sofic

open SubgroupTestValue TailoredGameValue

/-! ## Words as permutations -/

section WordPerm

variable {n : ℕ} (σ : FiniteAction n)

@[simp] theorem wordPerm_nil : σ.wordPerm [] = 1 := rfl

@[simp] theorem wordPerm_append (u v : Word) : σ.wordPerm (u ++ v) = σ.wordPerm u * σ.wordPerm v := by
  simp [FiniteAction.wordPerm]

@[simp] theorem wordPerm_cons (l : Letter) (u : Word) :
    σ.wordPerm (l :: u) = σ.letterPerm l * σ.wordPerm u := by
  simp [FiniteAction.wordPerm]

theorem letterPerm_eq (k : ℕ) (b : Bool) :
    σ.letterPerm (k, b) = if b then (genPerm σ k)⁻¹ else genPerm σ k := by
  unfold genPerm FiniteAction.letterPerm
  by_cases hk : k < n
  · simp only [hk, dite_true]
    cases b <;> simp
  · simp [hk]

@[simp] theorem wordPerm_genW (k : ℕ) : σ.wordPerm (genW k) = genPerm σ k := by
  simp [genW, letterPerm_eq]

theorem wordPerm_invW (u : Word) : σ.wordPerm (invW u) = (σ.wordPerm u)⁻¹ := by
  induction u with
  | nil => simp [invW]
  | cons l u ih =>
    have : invW (l :: u) = invW u ++ [(l.1, !l.2)] := by simp [invW]
    rw [this, wordPerm_append, ih, wordPerm_cons σ l u, mul_inv_rev]
    congr 1
    obtain ⟨k, b⟩ := l
    simp only [wordPerm_cons, wordPerm_nil, mul_one, letterPerm_eq]
    cases b <;> simp

theorem wordPerm_commW (u v : Word) :
    σ.wordPerm (commW u v) =
      σ.wordPerm u * σ.wordPerm v * (σ.wordPerm u)⁻¹ * (σ.wordPerm v)⁻¹ := by
  simp [commW, wordPerm_invW, mul_assoc]

theorem wordPerm_commW_of_commute {u v : Word}
    (h : σ.wordPerm u * σ.wordPerm v = σ.wordPerm v * σ.wordPerm u) :
    σ.wordPerm (commW u v) = 1 := by
  rw [wordPerm_commW, h]
  group

end WordPerm

/-! ## The fixed and readable literals under Checks 1–3 -/

variable {g : TailoredGameData} {σ : FiniteAction (nGen g)}

@[simp] theorem wordPerm_wJ : σ.wordPerm wJ = genPerm σ genJ := wordPerm_genW σ _

@[simp] theorem wordPerm_wX (x i : ℕ) : σ.wordPerm (wX g x i) = genPerm σ (genX g x i) :=
  wordPerm_genW σ _

theorem mem_varsAt {x : ℕ} {X : Word} :
    X ∈ varsAt g x ↔ ∃ i < g.lenAt x, X = wX g x i := by
  simp [varsAt, List.mem_map, List.mem_range, eq_comm]

/-- **The fixed literals hold** (Checks 1 and 2). -/
theorem fixedLits_holds (hσ : Checks g σ) {x y : ℕ} (hx : x < g.nV + 1) (hy : y < g.nV + 1)
    (p : Fin σ.N) {wb : Word × Bool} (hwb : wb ∈ fixedLits g x y) :
    decide (σ.InStab p wb.1) = wb.2 := by
  have hvar : ∀ X ∈ varsAt g x ++ varsAt g y, ∃ z i, z < g.nV + 1 ∧ i < g.lenAt z ∧
      X = wX g z i := by
    intro X hX
    rcases List.mem_append.mp hX with h | h
    · obtain ⟨i, hi, rfl⟩ := mem_varsAt.mp h; exact ⟨x, i, hx, hi, rfl⟩
    · obtain ⟨i, hi, rfl⟩ := mem_varsAt.mp h; exact ⟨y, i, hy, hi, rfl⟩
  have hfix : ∀ w : Word, σ.wordPerm w = 1 → decide (σ.InStab p w) = true := fun w hw => by
    simp [FiniteAction.InStab, hw]
  have hcomm : ∀ z, z < g.nV + 1 → ∀ X ∈ varsAt g z, ∀ X' ∈ varsAt g z,
      decide (σ.InStab p (commW X X')) = true := by
    intro z hz X hX X' hX'
    obtain ⟨i, hi, rfl⟩ := mem_varsAt.mp hX
    obtain ⟨i', hi', rfl⟩ := mem_varsAt.mp hX'
    exact hfix _ (wordPerm_commW_of_commute σ (by simpa using hσ.X_comm z i i' hz hi hi'))
  unfold fixedLits at hwb
  simp only [List.mem_append] at hwb
  rcases hwb with (((h | h) | h) | h) | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · simpa [FiniteAction.InStab] using hσ.J_free p
    · simp [FiniteAction.InStab, hσ.J_invol p]
  · obtain ⟨X, hX, rfl⟩ := List.mem_map.mp h
    obtain ⟨z, i, hz, hi, rfl⟩ := hvar X hX
    exact hfix _ (wordPerm_commW_of_commute σ (by simpa using hσ.J_comm z i hz hi))
  · obtain ⟨X, hX, rfl⟩ := List.mem_map.mp h
    obtain ⟨z, i, hz, hi, rfl⟩ := hvar X hX
    simp [FiniteAction.InStab, hσ.X_invol z i hz hi p]
  · obtain ⟨X, hX, h'⟩ := List.mem_flatMap.mp h
    obtain ⟨X', hX', rfl⟩ := List.mem_map.mp h'
    exact hcomm x hx X hX X' hX'
  · obtain ⟨X, hX, h'⟩ := List.mem_flatMap.mp h
    obtain ⟨X', hX', rfl⟩ := List.mem_map.mp h'
    exact hcomm y hy X hX X' hX'

theorem mem_readVars {x y : ℕ} {X : Word} (hX : X ∈ readVars g x y) :
    ∃ z i, (z = x ∨ z = y) ∧ i < g.lenRAt z ∧ X = wX g z i := by
  simp only [readVars, List.mem_append, List.mem_map, List.mem_range] at hX
  rcases hX with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
  · exact ⟨x, i, Or.inl rfl, hi, rfl⟩
  · exact ⟨y, i, Or.inr rfl, hi, rfl⟩

theorem length_readVars (x y : ℕ) :
    (readVars g x y).length = g.lenRAt x + g.lenRAt y := by
  simp [readVars]

/-- The readable value of a point at `(x, y)`: for each readable variable, whether it moves the
point. -/
def rdv (σ : FiniteAction (nGen g)) (x y : ℕ) (p : Fin σ.N) : List Bool :=
  (readVars g x y).map fun X => decide (σ.wordPerm X p ≠ p)

theorem length_rdv (x y : ℕ) (p : Fin σ.N) :
    (rdv σ x y p).length = g.lenRAt x + g.lenRAt y := by
  simp [rdv, length_readVars]

theorem flatMap_pair_length {α β : Type*} (l : List α) (f h : α → β) :
    (l.flatMap fun a => [f a, h a]).length = 2 * l.length := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]; ring

theorem flatMap_pair_getElem {α β : Type*} (l : List α) (f h : α → β) (t : ℕ) (b : Bool)
    (ht : t < l.length) (hlt : 2 * t + (if b then 1 else 0) < (l.flatMap fun a => [f a, h a]).length) :
    (l.flatMap fun a => [f a, h a])[2 * t + (if b then 1 else 0)] =
      if b then h l[t] else f l[t] := by
  induction l generalizing t with
  | nil => simp at ht
  | cons a l ih =>
    cases t with
    | zero => cases b <;> simp [List.flatMap_cons]
    | succ t =>
      have ht' : t < l.length := by simpa using ht
      have hlt' : 2 * t + (if b then 1 else 0) < (l.flatMap fun a => [f a, h a]).length := by
        rw [flatMap_pair_length]; split_ifs <;> omega
      have e : 2 * (t + 1) + (if b then 1 else 0) = 2 * t + (if b then 1 else 0) + 2 := by ring
      simp only [List.flatMap_cons, e]
      rw [List.getElem_append_right (by simp)]
      simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.add_sub_cancel,
        List.getElem_cons_succ]
      exact ih t ht' hlt'

theorem length_readWords (x y : ℕ) :
    (readWords g x y).length = 2 * (g.lenRAt x + g.lenRAt y) := by
  rw [readWords, flatMap_pair_length, length_readVars]

/-- **The readable literal of a readable variable holds for exactly one of its words**: `X` when
`X` fixes the point, `J X` when it moves it (Check 3). -/
theorem inStab_readWord_iff (hσ : Checks g σ) {x y : ℕ} (hx : x < g.nV + 1) (hy : y < g.nV + 1)
    (p : Fin σ.N) (t : ℕ) (ht : t < (readVars g x y).length) (b : Bool)
    (hlt : 2 * t + (if b then 1 else 0) < (readWords g x y).length) :
    σ.InStab p ((readWords g x y)[2 * t + (if b then 1 else 0)]) ↔
      b = (rdv σ x y p)[t]'(by rw [rdv, List.length_map]; exact ht) := by
  simp only [readWords] at hlt ⊢
  rw [flatMap_pair_getElem _ _ _ t b ht hlt]
  simp only [rdv, List.getElem_map]
  obtain ⟨z, i, hz, hi, hX⟩ := mem_readVars (List.getElem_mem ht)
  have hz' : z < g.nV + 1 := by rcases hz with rfl | rfl <;> assumption
  rw [hX]
  have hr := hσ.readable z i hz' hi p
  simp only [FiniteAction.InStab, wordPerm_wX]
  cases b
  · simp
  · simp only [ite_true, wordPerm_append, wordPerm_wX, wordPerm_wJ, Equiv.Perm.mul_apply,
      true_eq_decide_iff]
    rcases hr with h | h
    · rw [h]; simp [hσ.J_free p]
    · rw [h, hσ.J_invol p]
      simpa [eq_comm] using (hσ.J_free p).symm

/-! ## The literals of the words `K` -/

theorem mem_allBits {n : ℕ} {r : List Bool} : r ∈ allBits n ↔ r.length = n := by
  induction n generalizing r with
  | zero => simp [allBits, List.length_eq_zero_iff]
  | succ n ih =>
    simp only [allBits, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨r', hr', rfl | rfl⟩ <;> simp [ih.mp hr']
    · intro h
      cases r with
      | nil => simp at h
      | cons b r' =>
        refine ⟨r', ih.mpr (by simpa using h), ?_⟩
        cases b <;> simp

theorem litHolds_fixed (x y : ℕ) (p : Fin σ.N) (i : ℕ) (hi : i < (fixedLits g x y).length)
    (b : Bool) :
    σ.LitHolds (words g x y) p (i, b) ↔ decide (σ.InStab p ((fixedLits g x y)[i]).1) = b := by
  have hK : i < (words g x y).length := by simp [words]; omega
  have e : (words g x y)[i] = ((fixedLits g x y)[i]).1 := by
    simp only [words]
    rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simpa using hi)]
    simp
  exact ⟨fun ⟨_, h⟩ => by rwa [e] at h, fun h => ⟨hK, by rwa [e]⟩⟩

theorem litHolds_read (x y : ℕ) (p : Fin σ.N) (i : ℕ) (hi : i < (readWords g x y).length)
    (b : Bool) :
    σ.LitHolds (words g x y) p ((fixedLits g x y).length + i, b) ↔
      decide (σ.InStab p ((readWords g x y)[i])) = b := by
  have hK : (fixedLits g x y).length + i < (words g x y).length := by simp [words]; omega
  have e : (words g x y)[(fixedLits g x y).length + i] = (readWords g x y)[i] := by
    simp only [words]
    rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp)]
    simp
  exact ⟨fun ⟨_, h⟩ => by rwa [e] at h, fun h => ⟨hK, by rwa [e]⟩⟩

theorem litHolds_cons (x y : ℕ) (p : Fin σ.N) (i : ℕ) (hi : i < (consWords g x y).length)
    (b : Bool) :
    σ.LitHolds (words g x y) p
        ((fixedLits g x y).length + (readWords g x y).length + i, b) ↔
      decide (σ.InStab p ((consWords g x y)[i])) = b := by
  have hK : (fixedLits g x y).length + (readWords g x y).length + i < (words g x y).length := by
    simp [words]; omega
  have e : (words g x y)[(fixedLits g x y).length + (readWords g x y).length + i] =
      (consWords g x y)[i] := by
    simp only [words]
    rw [List.getElem_append_right (by simp)]
    simp
  exact ⟨fun ⟨_, h⟩ => by rwa [e] at h, fun h => ⟨hK, by rwa [e]⟩⟩

theorem consWord_mem_consWords {x y : ℕ} {e : ℕ × ℕ × List Bool × List Bool}
    (he : e ∈ consAt g x y) : consWord g x y e.2.2.2 ∈ consWords g x y := by
  rw [consWords, List.mem_dedup]
  exact List.mem_map.mpr ⟨e, he, rfl⟩

/-- **Passing a challenge under Checks 1–3 is Check 4**: every constraint word whose readable
part is the point's readable value fixes the point. -/
theorem passes_iff (hσ : Checks g σ) {x y : ℕ} (hx : x < g.nV + 1) (hy : y < g.nV + 1)
    (p : Fin σ.N) :
    σ.Passes (words g x y) (clauses g x y) p ↔
      ∀ e ∈ consAt g x y, e.2.2.1 = rdv σ x y p → σ.InStab p (consWord g x y e.2.2.2) := by
  have hR := length_readVars (g := g) x y
  constructor
  · rintro ⟨c, hc, hlits⟩
    simp only [clauses, List.mem_map] at hc
    obtain ⟨r, hr, rfl⟩ := hc
    have hrlen := mem_allBits.mp hr
    -- the readable literals force `r = rdv p`
    have hrv : r = rdv σ x y p := by
      refine List.ext_getElem (by rw [hrlen, length_rdv]) fun t ht _ => ?_
      have ht' : t < (readVars g x y).length := by rw [hR]; omega
      have hlit := hlits ((fixedLits g x y).length + 2 * t + (if r.getD t false then 1 else 0),
        true) (by
          simp only [clause, List.mem_append, List.mem_map, List.mem_range]
          exact Or.inl (Or.inr ⟨t, ht', rfl⟩))
      have hlt : 2 * t + (if r.getD t false then 1 else 0) < (readWords g x y).length := by
        rw [length_readWords]; split_ifs <;> omega
      rw [Nat.add_assoc, litHolds_read x y p _ hlt, decide_eq_true_iff,
        inStab_readWord_iff hσ hx hy p t ht' _ hlt] at hlit
      rw [← hlit, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]
    intro e he hre
    have hidx := List.idxOf_lt_length_iff.mpr (consWord_mem_consWords he)
    have hlit := hlits ((fixedLits g x y).length + (readWords g x y).length +
      (consWords g x y).idxOf (consWord g x y e.2.2.2), true) (by
        simp only [clause, List.mem_append, List.mem_map, List.mem_filter]
        exact Or.inr ⟨e, ⟨he, by simp [hre, hrv]⟩, rfl⟩)
    rw [litHolds_cons x y p _ hidx, decide_eq_true_iff, List.getElem_idxOf] at hlit
    exact hlit
  · intro hcons
    refine ⟨clause g x y (rdv σ x y p), ?_, ?_⟩
    · simp only [clauses, List.mem_map]
      exact ⟨_, mem_allBits.mpr (length_rdv x y p), rfl⟩
    intro lit hlit
    simp only [clause, List.mem_append, List.mem_map, List.mem_range, List.mem_filter] at hlit
    rcases hlit with (⟨⟨wb, i⟩, hwi, rfl⟩ | ⟨t, ht, rfl⟩) | ⟨e, ⟨he, hre⟩, rfl⟩
    · have hwi' := List.mem_zipIdx_iff_getElem?.mp hwi
      have hi : i < (fixedLits g x y).length := by
        by_contra h
        rw [List.getElem?_eq_none (by omega)] at hwi'
        cases hwi'
      rw [List.getElem?_eq_getElem hi, Option.some_inj] at hwi'
      simp only
      rw [litHolds_fixed x y p i hi, hwi']
      exact fixedLits_holds hσ hx hy p (hwi' ▸ List.getElem_mem hi)
    · have hlt : 2 * t + (if (rdv σ x y p).getD t false then 1 else 0) <
          (readWords g x y).length := by
        rw [length_readWords, ← hR]; split_ifs <;> omega
      rw [Nat.add_assoc, litHolds_read x y p _ hlt, decide_eq_true_iff,
        inStab_readWord_iff hσ hx hy p t ht _ hlt, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [length_rdv, ← hR]; exact ht), Option.getD_some]
    · have hidx := List.idxOf_lt_length_iff.mpr (consWord_mem_consWords he)
      rw [litHolds_cons x y p _ hidx, decide_eq_true_iff, List.getElem_idxOf]
      exact hcons e he (of_decide_eq_true hre)

/-! ## The value of the test -/

theorem list_sum_map_range {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ((List.range n).map f).sum = ∑ i : Fin n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Fin.sum_univ_castSucc]
    simp

theorem list_sum_map_flatMap {α β M : Type*} [AddCommMonoid M] (l : List α) (F : α → List β)
    (h : β → M) : ((l.flatMap F).map h).sum = (l.map fun a => ((F a).map h).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]

theorem list_sum_map_square {β M : Type*} [AddCommMonoid M] (n : ℕ) (F : ℕ → ℕ → β)
    (h : β → M) :
    (((List.range n).flatMap fun x => (List.range n).map fun y => F x y).map h).sum =
      ∑ x : Fin n, ∑ y : Fin n, h (F x y) := by
  rw [list_sum_map_flatMap, list_sum_map_range]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [List.map_map, list_sum_map_range]
  rfl

/-- **The value of the associated test** is the `μ`-average of the pass probabilities of the
challenges, `μ` being the game's question distribution. -/
theorem value_eq_sum (σ : FiniteAction (nGen g)) :
    (assocTest g).value σ = ∑ x : Fin (g.nV + 1), ∑ y : Fin (g.nV + 1),
      g.toGame.μ x y * σ.passProb (words g x.val y.val) (clauses g x.val y.val) := by
  have hμ : ∀ x y : Fin (g.nV + 1), g.toGame.μ x y =
      if (wts g).totalWeight = 0 then (if x = 0 ∧ y = 0 then 1 else 0)
      else ((wts g).questionWeight x.val y.val : ℝ) / ((wts g).totalWeight : ℝ) := fun _ _ => rfl
  simp only [hμ]
  unfold SubgroupTestData.value SubgroupTestData.totalWeight
  by_cases h : (wts g).totalWeight = 0
  · simp only [assocTest, h, ↓reduceIte, challenge, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, Nat.cast_one, div_one, one_mul]
    rw [Finset.sum_eq_single 0 (fun x _ hx => by simp [hx]) (by simp),
      Finset.sum_eq_single 0 (fun y _ hy => by simp [hy]) (by simp)]
    simp
  · simp only [assocTest, h, ↓reduceIte, challenge]
    rw [list_sum_map_square, list_sum_map_square
      (h := fun c : ℕ × List Word × List (List (ℕ × Bool)) => (c.1 : ℕ))]
    have hT : (∑ x : Fin (g.nV + 1), ∑ y : Fin (g.nV + 1), (wts g).questionWeight x.val y.val) =
        (wts g).totalWeight := rfl
    rw [hT, Finset.sum_div]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring

/-! ## Counting the constraint words -/

/-- **There are at most `2^{ℓ(x) + ℓ(y) + 1} + 1` distinct constraint words** at `(x, y)`. -/
theorem length_consWords_le (x y : ℕ) :
    (consWords g x y).length ≤ 2 ^ (g.lenAt x + g.lenAt y + 1) + 1 := by
  classical
  set n := g.lenAt x + g.lenAt y + 1
  rw [← List.toFinset_card_of_nodup (show (consWords g x y).Nodup from List.nodup_dedup _)]
  have hsub : (consWords g x y).toFinset ⊆ insert wJ
      ((Finset.univ : Finset (Fin n → Bool)).image fun f => consWord g x y (List.ofFn f)) := by
    intro w hw
    rw [List.mem_toFinset, consWords, List.mem_dedup, List.mem_map] at hw
    obtain ⟨e, -, rfl⟩ := hw
    by_cases hc : e.2.2.2.length = n
    · refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨fun i => e.2.2.2.getD i.val false,
        Finset.mem_univ _, ?_⟩)
      congr 1
      refine List.ext_getElem (by rw [List.length_ofFn, hc]) fun i _ h2 => ?_
      rw [List.getElem_ofFn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2,
        Option.getD_some]
    · rw [consWord, ite_eq_right hc]
      exact Finset.mem_insert_self _ _
  calc (consWords g x y).toFinset.card
      ≤ (insert wJ ((Finset.univ : Finset (Fin n → Bool)).image
          fun f => consWord g x y (List.ofFn f))).card := Finset.card_le_card hsub
    _ ≤ ((Finset.univ : Finset (Fin n → Bool)).image
          fun f => consWord g x y (List.ofFn f)).card + 1 := Finset.card_insert_le _ _
    _ ≤ (Finset.univ : Finset (Fin n → Bool)).card + 1 := by
        gcongr; exact Finset.card_image_le
    _ = 2 ^ n + 1 := by simp

end MIPRE.Tailored.Sofic

end

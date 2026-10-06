/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Sofic.Measure.Ergodic
public import Mathlib.Data.List.GetD
public import MIPRE.Tactics

@[expose] public section

/-!
# The sofic value is approximable from below (Main Theorem I (1))

Paper I, Main Theorem I clause (1) (I:592) and its proof (I:1148–1168): enumerate the finite
actions and take the running maximum of their values.

A finite action is coded by `(N, P)`, `P` the list of the rows `[σ_i(0), …, σ_i(N − 1)]` of its
permutations (`ActCode`). `ValidC s c` is the decidable condition that a code is one (each row a
list of length `N` with entries below `N` and every point below `N` among them), `decodeAct`
reads off the action, and `codeOf` writes one down. On codes the value is a ratio of naturals
(`value_eq_numC`), the action of a word being computed letter by letter (`applyWord`, the inverse
of a row by `List.idxOf`).

The approximation is dyadic: `lowerSeq T t / 2^t` is the largest value of the actions with code
number at most `t`, rounded down to the grid of step `2^{-t}`. It is primitive recursive
(`primrec_lowerSeq`), non-decreasing, at most the sofic value, and tends to it
(`mainTheoremI_one`).
-/

namespace MIPRE.Tailored.Sofic.Measure

open SubgroupTestValue Filter Topology

/-! ## Codes of finite actions -/

/-- A code of a finite action: the number of points and the rows of the permutations. -/
abbrev ActCode := ℕ × List (List ℕ)

/-- A letter acting on a point through the rows `P`; letters beyond the rows act as the identity,
an inverted letter by the position of the point in its row. -/
def applyLetter (P : List (List ℕ)) (l : Letter) (y : ℕ) : ℕ :=
  if l.1 < P.length then
    (if l.2 then (P.getD l.1 []).idxOf y else (P.getD l.1 []).getD y 0)
  else y

/-- A word acting on a point, its last letter first, as in `FiniteAction.wordPerm`. -/
def applyWord (P : List (List ℕ)) (w : Word) (y : ℕ) : ℕ := w.foldr (applyLetter P) y

/-- The literal `(i, b)` at the point `y`. -/
def litC (P : List (List ℕ)) (K : List Word) (y : ℕ) (lit : ℕ × Bool) : Bool :=
  decide (lit.1 < K.length) && (decide (applyWord P (K.getD lit.1 []) y = y) == lit.2)

/-- The point `y` passes the challenge `(K, cl)`. -/
def passC (P : List (List ℕ)) (K : List Word) (cl : List (List (ℕ × Bool))) (y : ℕ) : Bool :=
  cl.any fun c => c.all fun lit => litC P K y lit

/-- The number of points passing a challenge. -/
def countC (c : ActCode) (K : List Word) (cl : List (List (ℕ × Bool))) : ℕ :=
  ((List.range c.1).filter (passC c.2 K cl)).length

/-- The weighted number of passing points, the numerator of the value. -/
def numC (T : SubgroupTestData) (c : ActCode) : ℕ :=
  (T.challenges.map fun ch => ch.1 * countC c ch.2.1 ch.2.2).sum

/-- A code is the code of a finite action on `s` generators. -/
def ValidC (s : ℕ) (c : ActCode) : Prop :=
  0 < c.1 ∧ c.2.length = s ∧ ∀ p ∈ c.2, p.length = c.1 ∧ (∀ v ∈ p, v < c.1) ∧ ∀ y < c.1, y ∈ p

instance (s : ℕ) : DecidablePred (ValidC s) := fun _ => by unfold ValidC; infer_instance

/-- The code `c` represents the action `σ`. -/
structure Represents {s : ℕ} (σ : FiniteAction s) (c : ActCode) : Prop where
  N_eq : c.1 = σ.N
  len : c.2.length = s
  row_len : ∀ i, i < s → (c.2.getD i []).length = σ.N
  row : ∀ i (hi : i < s) (x : Fin σ.N), (c.2.getD i []).getD x 0 = σ.σ ⟨i, hi⟩ x

section Represents

variable {s : ℕ} {σ : FiniteAction s} {c : ActCode}

theorem Represents.mem_row (h : Represents σ c) {i : ℕ} (hi : i < s) (y : Fin σ.N) :
    (y : ℕ) ∈ c.2.getD i [] := by
  set z := (σ.σ ⟨i, hi⟩)⁻¹ y
  have hz : (c.2.getD i []).getD z 0 = y := by rw [h.row i hi z]; simp [z]
  have hzlen : (z : ℕ) < (c.2.getD i []).length := by rw [h.row_len i hi]; exact z.2
  rw [← hz, List.getD_eq_getElem _ _ hzlen]
  exact List.getElem_mem _

theorem Represents.applyLetter_eq (h : Represents σ c) (l : Letter) (y : Fin σ.N) :
    applyLetter c.2 l y = (σ.letterPerm l y : ℕ) := by
  obtain ⟨i, e⟩ := l
  unfold applyLetter FiniteAction.letterPerm
  simp only [h.len]
  by_cases hi : i < s
  · simp only [hi, dite_true, ite_true]
    cases e
    · simpa [List.getD_eq_getElem?_getD] using h.row i hi y
    · simp only [ite_true]
      have hmem := h.mem_row hi y
      have hj := List.idxOf_lt_length_of_mem hmem
      have hj' : (c.2.getD i []).idxOf (y : ℕ) < σ.N := lt_of_lt_of_eq hj (h.row_len i hi)
      have hpj := List.getElem_idxOf hj
      have hrow := h.row i hi ⟨_, hj'⟩
      rw [List.getD_eq_getElem _ _ hj, hpj] at hrow
      have : (⟨_, hj'⟩ : Fin σ.N) = (σ.σ ⟨i, hi⟩)⁻¹ y := by
        rw [Equiv.Perm.eq_inv_iff_eq]; exact Fin.ext hrow.symm
      exact congrArg Fin.val this
  · simp [hi]

theorem Represents.applyWord_eq (h : Represents σ c) (w : Word) (y : Fin σ.N) :
    applyWord c.2 w y = (σ.wordPerm w y : ℕ) := by
  induction w with
  | nil => simp [applyWord, FiniteAction.wordPerm]
  | cons l w ih =>
    unfold applyWord at ih ⊢
    rw [List.foldr_cons, ih, h.applyLetter_eq]
    simp [FiniteAction.wordPerm]

theorem Represents.litC_eq (h : Represents σ c) (K : List Word) (y : Fin σ.N) (lit : ℕ × Bool) :
    litC c.2 K y lit = decide (σ.LitHolds K y lit) := by
  obtain ⟨i, b⟩ := lit
  unfold litC FiniteAction.LitHolds FiniteAction.InStab
  by_cases hi : i < K.length
  · simp only [hi, decide_true, Bool.true_and, exists_true_left]
    rw [List.getD_eq_getElem _ _ hi, h.applyWord_eq]
    cases b <;> simp [Fin.ext_iff]
  · simp [hi]

theorem Represents.passC_eq (h : Represents σ c) (K : List Word) (cl : List (List (ℕ × Bool)))
    (y : Fin σ.N) : passC c.2 K cl y = decide (σ.Passes K cl y) := by
  unfold passC FiniteAction.Passes
  simp only [h.litC_eq]
  rw [Bool.eq_iff_iff]
  simp

theorem card_filter_fin (N : ℕ) (q : ℕ → Bool) :
    (Finset.univ.filter fun x : Fin N => q x = true).card = ((List.range N).filter q).length := by
  have : (Finset.univ.filter fun x : Fin N => q x = true).map Fin.valEmbedding =
      (Finset.range N).filter fun x => q x = true := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_range]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨y.2, hy⟩
    · rintro ⟨hx, hq⟩; exact ⟨⟨x, hx⟩, hq, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, this, Finset.card_def, Finset.filter_val]
  simp [Finset.range, Multiset.range]

theorem Represents.countC_eq (h : Represents σ c) (K : List Word) (cl : List (List (ℕ × Bool))) :
    countC c K cl = (Finset.univ.filter fun x => σ.Passes K cl x).card := by
  unfold countC
  rw [h.N_eq, ← card_filter_fin]
  congr 1
  ext x
  simp [h.passC_eq]

theorem list_sum_map_div {ι : Type*} (l : List ι) (f : ι → ℝ) (a : ℝ) :
    (l.map fun i => f i / a).sum = (l.map f).sum / a := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih, add_div]

/-- On a code the value is a ratio of naturals. -/
theorem Represents.value_eq (h : Represents σ c) (T : SubgroupTestData) (hs : s = T.nGen) :
    T.value (hs ▸ σ) = (numC T c : ℝ) / ((c.1 * T.totalWeight : ℕ) : ℝ) := by
  subst hs
  unfold SubgroupTestData.value FiniteAction.passProb numC
  rw [Nat.cast_mul, ← div_div, h.N_eq]
  congr 1
  rw [Nat.cast_list_sum, List.map_map, ← list_sum_map_div]
  congr 1
  refine List.map_congr_left fun ch _ => ?_
  simp [h.countC_eq, mul_div_assoc]

end Represents

/-- The row `i` of a valid code. -/
theorem ValidC.row {s : ℕ} {c : ActCode} (h : ValidC s c) {i : ℕ} (hi : i < s) :
    (c.2.getD i []).length = c.1 ∧ (∀ v ∈ c.2.getD i [], v < c.1) ∧
      ∀ y < c.1, y ∈ c.2.getD i [] := by
  have hi' : i < c.2.length := by rw [h.2.1]; exact hi
  rw [List.getD_eq_getElem _ _ hi']
  exact h.2.2 _ (List.getElem_mem hi')

theorem ValidC.getD_lt {s : ℕ} {c : ActCode} (h : ValidC s c) {i : ℕ} (hi : i < s) {x : ℕ}
    (hx : x < c.1) : (c.2.getD i []).getD x 0 < c.1 := by
  have hr := h.row hi
  have hx' : x < (c.2.getD i []).length := by rw [hr.1]; exact hx
  rw [List.getD_eq_getElem _ _ hx']
  exact hr.2.1 _ (List.getElem_mem hx')

/-- The map of the row `i` of a valid code. -/
def rowFun {s : ℕ} {c : ActCode} (h : ValidC s c) (i : Fin s) (x : Fin c.1) : Fin c.1 :=
  ⟨(c.2.getD i []).getD x 0, h.getD_lt i.2 x.2⟩

theorem rowFun_bijective {s : ℕ} {c : ActCode} (h : ValidC s c) (i : Fin s) :
    Function.Bijective (rowFun h i) := by
  have hsurj : Function.Surjective (rowFun h i) := by
    intro y
    have hr := h.row i.2
    obtain ⟨j, hj, hjy⟩ := List.getElem_of_mem (hr.2.2 y y.2)
    refine ⟨⟨j, hr.1 ▸ hj⟩, Fin.ext ?_⟩
    simp only [rowFun]
    rw [List.getD_eq_getElem _ _ hj, hjy]
  exact ⟨Finite.injective_iff_surjective.2 hsurj, hsurj⟩

/-- The action of a valid code. -/
noncomputable def decodeAct (s : ℕ) (c : ActCode) (h : ValidC s c) : FiniteAction s where
  N := c.1
  N_pos := h.1
  σ i := Equiv.ofBijective (rowFun h i) (rowFun_bijective h i)

theorem represents_decodeAct (s : ℕ) (c : ActCode) (h : ValidC s c) :
    Represents (decodeAct s c h) c where
  N_eq := rfl
  len := h.2.1
  row_len _ hi := (h.row hi).1
  row _ _ _ := rfl

/-- The code of a finite action. -/
def codeOf {s : ℕ} (σ : FiniteAction s) : ActCode :=
  (σ.N, List.ofFn fun i => List.ofFn fun x => (σ.σ i x : ℕ))

theorem represents_codeOf {s : ℕ} (σ : FiniteAction s) : Represents σ (codeOf σ) where
  N_eq := rfl
  len := by simp [codeOf]
  row_len i hi := by simp [codeOf, List.getD_eq_getElem?_getD, hi]
  row i hi x := by simp [codeOf, List.getD_eq_getElem?_getD, hi]

theorem Represents.valid {s : ℕ} {σ : FiniteAction s} {c : ActCode} (h : Represents σ c) :
    ValidC s c := by
  refine ⟨h.N_eq ▸ σ.N_pos, h.len, fun p hp => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
  have hi' : i < s := h.len ▸ hi
  have hrow : c.2[i] = c.2.getD i [] := (List.getD_eq_getElem _ _ hi).symm
  rw [hrow, h.N_eq]
  refine ⟨h.row_len i hi', fun v hv => ?_, fun y hy => h.mem_row hi' ⟨y, hy⟩⟩
  obtain ⟨x, hx, rfl⟩ := List.getElem_of_mem hv
  have hx' : x < σ.N := h.row_len i hi' ▸ hx
  rw [← List.getD_eq_getElem _ 0 hx, h.row i hi' ⟨x, hx'⟩]
  exact Fin.isLt _

/-! ## The lower approximation -/

/-- The value of a code rounded down to the grid of step `2^{-t}`, as a numerator; `0` for an
invalid code. -/
def lowerC (T : SubgroupTestData) (c : ActCode) (t : ℕ) : ℕ :=
  if ValidC T.nGen c then 2 ^ t * numC T c / (c.1 * T.totalWeight) else 0

/-- `lowerC` of the code with number `n`. -/
def lowerAt (T : SubgroupTestData) (n t : ℕ) : ℕ :=
  match Encodable.decode (α := ActCode) n with
  | some c => lowerC T c t
  | none => 0

/-- **The lower approximation** at stage `t`: the numerator over `2^t` of the largest rounded
value of the codes numbered at most `t`. -/
def lowerSeq (T : SubgroupTestData) (t : ℕ) : ℕ :=
  ((List.range (t + 1)).map fun n => lowerAt T n t).foldr max 0

/-- The dyadic number `n / 2^t`. -/
noncomputable def dyadic (n t : ℕ) : ℝ := (n : ℝ) / 2 ^ t

theorem dyadic_nonneg (n t : ℕ) : 0 ≤ dyadic n t := by unfold dyadic; positivity

/-- Rounding down to the grid. -/
theorem floor_bounds (a b t : ℕ) :
    dyadic (2 ^ t * a / b) t ≤ (a : ℝ) / b ∧ (a : ℝ) / b - 1 / 2 ^ t ≤ dyadic (2 ^ t * a / b) t := by
  unfold dyadic
  have h2 : (0 : ℝ) < 2 ^ t := by positivity
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb; simp
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  constructor
  · rw [div_le_div_iff₀ h2 hb']
    have := Nat.div_mul_le_self (2 ^ t * a) b
    have h' : ((2 ^ t * a / b : ℕ) : ℝ) * b ≤ 2 ^ t * a := by exact_mod_cast this
    linarith
  · have := Nat.lt_div_mul_add (a := 2 ^ t * a) hb
    have h' : (2 ^ t * a : ℝ) < ((2 ^ t * a / b : ℕ) : ℝ) * b + b := by exact_mod_cast this
    rw [sub_le_iff_le_add, div_add_div _ _ h2.ne' h2.ne', div_le_div_iff₀ hb' (by positivity)]
    nlinarith

theorem lowerC_le {T : SubgroupTestData} {c : ActCode} {σ : FiniteAction T.nGen}
    (h : Represents σ c) (t : ℕ) : dyadic (lowerC T c t) t ≤ T.value σ := by
  simp only [lowerC, h.valid, ↓reduceIte]
  rw [h.value_eq T rfl]
  exact (floor_bounds _ _ t).1

theorem le_lowerC {T : SubgroupTestData} {c : ActCode} {σ : FiniteAction T.nGen}
    (h : Represents σ c) (t : ℕ) : T.value σ - 1 / 2 ^ t ≤ dyadic (lowerC T c t) t := by
  simp only [lowerC, h.valid, ↓reduceIte]
  rw [h.value_eq T rfl]
  exact (floor_bounds _ _ t).2

theorem lowerAt_le (T : SubgroupTestData) (n t : ℕ) : dyadic (lowerAt T n t) t ≤ T.valSof := by
  unfold lowerAt
  cases hd : Encodable.decode (α := ActCode) n with
  | none => simpa [dyadic] using T.valSof_nonneg
  | some c =>
    simp only
    by_cases hv : ValidC T.nGen c
    · exact (lowerC_le (represents_decodeAct _ c hv) t).trans (T.le_valSof _)
    · simpa [lowerC, hv, dyadic] using T.valSof_nonneg

theorem dyadic_mono_succ (n t : ℕ) : dyadic n t = dyadic (2 * n) (t + 1) := by
  unfold dyadic; push_cast; rw [pow_succ]; field_simp

theorem lowerC_mono (T : SubgroupTestData) (c : ActCode) (t : ℕ) :
    dyadic (lowerC T c t) t ≤ dyadic (lowerC T c (t + 1)) (t + 1) := by
  rw [dyadic_mono_succ]
  unfold dyadic
  gcongr
  unfold lowerC
  split_ifs
  · rw [pow_succ, mul_comm (2 ^ t) 2, mul_assoc]
    exact Nat.mul_div_le_mul_div_assoc _ _ _
  · simp

theorem lowerAt_mono (T : SubgroupTestData) (n t : ℕ) :
    dyadic (lowerAt T n t) t ≤ dyadic (lowerAt T n (t + 1)) (t + 1) := by
  unfold lowerAt
  cases Encodable.decode (α := ActCode) n with
  | none => simp [dyadic]
  | some c => exact lowerC_mono T c t

theorem le_foldr_max {l : List ℕ} {a : ℕ} (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem foldr_max_mem_or (l : List ℕ) : l.foldr max 0 = 0 ∨ l.foldr max 0 ∈ l := by
  induction l with
  | nil => simp
  | cons b l ih =>
    rw [List.foldr_cons]
    rcases le_total b (l.foldr max 0) with h | h
    · rw [max_eq_right h]
      rcases ih with h' | h'
      · left; exact h'
      · right; exact List.mem_cons_of_mem _ h'
    · rw [max_eq_left h]; right; exact List.mem_cons_self

theorem le_lowerSeq (T : SubgroupTestData) {n t : ℕ} (hn : n ≤ t) :
    lowerAt T n t ≤ lowerSeq T t :=
  le_foldr_max (List.mem_map.2 ⟨n, List.mem_range.2 (Nat.lt_succ_of_le hn), rfl⟩)

theorem lowerSeq_le (T : SubgroupTestData) (t : ℕ) : dyadic (lowerSeq T t) t ≤ T.valSof := by
  unfold lowerSeq
  rcases foldr_max_mem_or ((List.range (t + 1)).map fun n => lowerAt T n t) with h | h
  · rw [h]; simpa [dyadic] using T.valSof_nonneg
  · obtain ⟨n, -, hn⟩ := List.mem_map.1 h
    rw [← hn]; exact lowerAt_le T n t

theorem lowerSeq_mono_succ (T : SubgroupTestData) (t : ℕ) :
    dyadic (lowerSeq T t) t ≤ dyadic (lowerSeq T (t + 1)) (t + 1) := by
  conv_lhs => unfold lowerSeq
  rcases foldr_max_mem_or ((List.range (t + 1)).map fun n => lowerAt T n t) with h | h
  · rw [h]; simpa [dyadic] using dyadic_nonneg _ _
  · obtain ⟨n, hn, hn'⟩ := List.mem_map.1 h
    rw [← hn']
    refine (lowerAt_mono T n t).trans ?_
    unfold dyadic
    gcongr
    exact_mod_cast le_lowerSeq T (Nat.le_succ_of_le (Nat.lt_succ_iff.1 (List.mem_range.1 hn)))

theorem lowerSeq_monotone (T : SubgroupTestData) : Monotone fun t => dyadic (lowerSeq T t) t :=
  monotone_nat_of_le_succ (lowerSeq_mono_succ T)

theorem tendsto_lowerSeq (T : SubgroupTestData) :
    Tendsto (fun t => dyadic (lowerSeq T t) t) atTop (𝓝 T.valSof) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨σ, hσ⟩ := exists_lt_of_lt_ciSup (f := T.value) (show T.valSof - ε / 2 < T.valSof by linarith)
  obtain ⟨t₀, ht₀⟩ := exists_pow_lt_of_lt_one (show 0 < ε / 2 by linarith)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  set n := Encodable.encode (codeOf σ)
  refine ⟨max n t₀, fun t ht => ?_⟩
  have hn : n ≤ t := (le_max_left _ _).trans ht
  have hlow : T.value σ - 1 / 2 ^ t ≤ dyadic (lowerSeq T t) t := by
    have h1 := le_lowerC (represents_codeOf σ) t (T := T)
    have h2 : lowerAt T n t = lowerC T (codeOf σ) t := by
      unfold lowerAt; rw [Encodable.encodek]
    refine h1.trans ?_
    rw [← h2]
    unfold dyadic
    gcongr
    exact_mod_cast le_lowerSeq T hn
  have hpow : 1 / (2 : ℝ) ^ t < ε / 2 := by
    have : (1 / 2 : ℝ) ^ t ≤ (1 / 2) ^ t₀ :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) ((le_max_right _ _).trans ht)
    rw [one_div_pow, one_div_pow] at this; rw [one_div_pow] at ht₀
    linarith
  rw [Real.dist_eq, abs_lt]
  constructor
  · linarith
  · linarith [lowerSeq_le T t]

end MIPRE.Tailored.Sofic.Measure

end

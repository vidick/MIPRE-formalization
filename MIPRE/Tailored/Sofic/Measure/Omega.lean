/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Sofic.Measure.Ergodic
public import MIPRE.Tailored.Sofic.Assoc
public import Mathlib.GroupTheory.FreeGroup.Reduce
public import MIPRE.Tactics

@[expose] public section

/-!
# Measures on the subsets of the words, and invariant random subgroups

The upper approximation of the ergodic value (Main Theorem I (2), I:1170–1220) works with
probability measures on `{0,1}^B` for finite sets `B` of words; their weak-* limits live on the
compact space `WordSpace = {0,1}^{words}` of all subsets of the words (letters `(i, e)` with any
`i`, unreduced). This file relates `WordSpace` to `Sub(F)`, `F` the free group on `s` generators:

* `wordEval s H`, the words whose element of `F` lies in `H`, maps `Sub(F)` into `WordSpace`; it
  lands in the closed set `Good s` of subsets containing the empty word, invariant under
  cancelling a pair `(i, c)(i, ¬c)` and deleting a letter `i ≥ s`, and closed under `u, v ↦ u v⁻¹`
  (Claim I:794 for words: these conditions are the paper's open cover of the complement);
* `evW s A`, the elements of `F` whose reduced word lies in `A`, maps `Good s` back to `Sub(F)`
  (`isSubgroupIndicator_evW`), as a left inverse of `wordEval`;
* `conjW g` is conjugation by a letter on `WordSpace`, intertwined with `conj` by `wordEval`.

`irs_of_good` is the transfer used at the limit: a probability measure on `WordSpace` carried by
`Good s` and invariant under the `conjW g` (`g` a letter below `s`) is the image of an IRS with the
same value. The value is `valW`, defined like `valGen` for a map to `WordSpace`.
-/

namespace MIPRE.Tailored.Sofic.Measure

open SubgroupTestValue MeasureTheory

/-! ## The value through words -/

/-- The literal `(i, b)` on a set of words. -/
def litW (K : List Word) (A : Word → Bool) (lit : ℕ × Bool) : Bool :=
  match K[lit.1]? with
  | some k => A k == lit.2
  | none => false

/-- A set of words passes the challenge `(K, cl)`. -/
def passW (K : List Word) (cl : List (List (ℕ × Bool))) (A : Word → Bool) : Bool :=
  cl.any fun c => c.all fun lit => litW K A lit

theorem passB_eq_passW (s : ℕ) (K : List Word) (cl : List (List (ℕ × Bool)))
    (G : FreeGroup (Fin s) → Bool) : passB s K cl G = passW K cl fun u => G (wordFG s u) := rfl

/-- `passW` depends only on the words of `K`. -/
theorem passW_congr {K : List Word} (cl : List (List (ℕ × Bool))) {A B : Word → Bool}
    (h : ∀ k ∈ K, A k = B k) : passW K cl A = passW K cl B := by
  unfold passW litW
  congr 1; funext c; congr 1; funext lit
  cases hk : K[lit.1]? with
  | none => rfl
  | some k => simp only [h k (List.mem_of_getElem? hk)]

section ValW

variable {X : Type*} [TopologicalSpace X]

theorem continuous_litW {e : X → Word → Bool} (he : Continuous e) (K : List Word)
    (lit : ℕ × Bool) : Continuous fun x => litW K (e x) lit := by
  unfold litW
  cases K[lit.1]? with
  | none => exact continuous_const
  | some k =>
    exact (continuous_of_discreteTopology (f := fun a : Bool => a == lit.2)).comp
      ((continuous_apply k).comp he)

theorem continuous_passW {e : X → Word → Bool} (he : Continuous e) (K : List Word)
    (cl : List (List (ℕ × Bool))) : Continuous fun x => passW K cl (e x) :=
  continuous_list_any _ _ fun _ _ =>
    continuous_list_all _ _ fun _ _ => continuous_litW he K _

/-- The set of points passing a challenge. -/
def passSetW (e : X → Word → Bool) (K : List Word) (cl : List (List (ℕ × Bool))) : Set X :=
  {x | passW K cl (e x) = true}

theorem isClopen_passSetW {e : X → Word → Bool} (he : Continuous e) (K : List Word)
    (cl : List (List (ℕ × Bool))) : IsClopen (passSetW e K cl) :=
  (isClopen_discrete {true}).preimage (continuous_passW he K cl)

end ValW

/-- The value of a probability measure on a space mapped to sets of words. -/
noncomputable def valW {X : Type*} [MeasurableSpace X] (T : SubgroupTestData)
    (e : X → Word → Bool) (μ : ProbabilityMeasure X) : ℝ :=
  (T.challenges.map fun c => (c.1 : ℝ) * (μ : Measure X).real (passSetW e c.2.1 c.2.2)).sum /
    T.totalWeight

theorem valGen_eq_valW {X : Type*} [MeasurableSpace X] (T : SubgroupTestData)
    (ev : X → FreeGroup (Fin T.nGen) → Bool) (μ : ProbabilityMeasure X) :
    valGen T ev μ = valW T (fun x u => ev x (wordFG T.nGen u)) μ := rfl

theorem continuous_valW {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (T : SubgroupTestData) {e : X → Word → Bool} (he : Continuous e) :
    Continuous (valW T e) := by
  unfold valW
  refine Continuous.div_const (continuous_list_sum_map _ _ fun c _ => ?_) _
  exact continuous_const.mul (continuous_measureReal_of_isClopen (isClopen_passSetW he _ _))

/-- The value is unchanged along a measurable map. -/
theorem valW_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] [TopologicalSpace Y]
    [OpensMeasurableSpace Y] (T : SubgroupTestData) {e : Y → Word → Bool} (he : Continuous e)
    {f : X → Y} (hf : Measurable f) (μ : ProbabilityMeasure X) :
    valW T e (μ.map f) = valW T (e ∘ f) μ := by
  unfold valW
  congr 2
  refine List.map_congr_left fun c _ => ?_
  congr 1
  rw [ProbabilityMeasure.toMeasure_map, map_measureReal_apply hf
    (isClopen_passSetW he _ _).isOpen.measurableSet]
  rfl

/-- The value only sees the passing sets up to null sets. -/
theorem valW_congr_ae {X : Type*} [MeasurableSpace X] (T : SubgroupTestData)
    {e e' : X → Word → Bool} (μ : ProbabilityMeasure X)
    (h : ∀ᵐ x ∂(μ : Measure X), e x = e' x) : valW T e μ = valW T e' μ := by
  unfold valW
  congr 2
  refine List.map_congr_left fun c _ => ?_
  congr 1
  refine measureReal_congr ?_
  filter_upwards [h] with x hx
  show (passW c.2.1 c.2.2 (e x) = true) = (passW c.2.1 c.2.2 (e' x) = true)
  rw [hx]

/-! ## The space of sets of words -/

/-- The sets of words, `{0,1}^{words}` with the product topology. -/
abbrev WordSpace := Word → Bool

/-- The value of a probability measure on sets of words. -/
noncomputable def valΩ (T : SubgroupTestData) (ν : ProbabilityMeasure WordSpace) : ℝ :=
  valW T id ν

theorem continuous_valΩ (T : SubgroupTestData) : Continuous (valΩ T) :=
  continuous_valW T continuous_id

/-! ## Words and the free group -/

theorem wordFG_append (s : ℕ) (u v : Word) : wordFG s (u ++ v) = wordFG s u * wordFG s v := by
  simp [wordFG, List.prod_append]

theorem wordFG_cons (s : ℕ) (l : Letter) (u : Word) :
    wordFG s (l :: u) = letterFG s l * wordFG s u := by
  simp [wordFG]

theorem wordFG_nil (s : ℕ) : wordFG s [] = 1 := rfl

theorem letterFG_flip (s : ℕ) (l : Letter) : letterFG s (l.1, !l.2) = (letterFG s l)⁻¹ := by
  obtain ⟨i, e⟩ := l
  unfold letterFG
  by_cases h : i < s <;> cases e <;> simp [h]

theorem wordFG_invW (s : ℕ) (u : Word) : wordFG s (invW u) = (wordFG s u)⁻¹ := by
  unfold wordFG invW
  rw [List.prod_inv_reverse, List.map_reverse, List.map_map, List.map_map]
  congr 2
  apply List.map_congr_left
  intro l _
  exact letterFG_flip s l

theorem letterFG_of_le {s : ℕ} {l : Letter} (h : s ≤ l.1) : letterFG s l = 1 := by
  unfold letterFG; simp [Nat.not_lt.2 h]

/-- A letter of the free group as a letter of a word (Mathlib's `true` is the generator, the
words' `true` its inverse). -/
def toN (s : ℕ) (x : Fin s × Bool) : Letter := (x.1.val, !x.2)

/-- The letters of a word below `s`, as a word of the free group. -/
def finW (s : ℕ) (w : Word) : List (Fin s × Bool) :=
  w.filterMap fun l => if h : l.1 < s then some (⟨l.1, h⟩, !l.2) else none

theorem wordFG_eq_mk (s : ℕ) (w : Word) : wordFG s w = FreeGroup.mk (finW s w) := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [wordFG_cons, ih]
    obtain ⟨i, e⟩ := l
    unfold finW letterFG
    by_cases h : i < s
    · simp only [List.filterMap_cons, h, dite_true]
      rw [show ∀ L : List (Fin s × Bool), (⟨i, h⟩, !e) :: L = [(⟨i, h⟩, !e)] ++ L from
        fun _ => rfl, ← FreeGroup.mul_mk]
      congr 1
      cases e
      · rfl
      · show (FreeGroup.mk [(_, true)])⁻¹ = _
        rw [FreeGroup.inv_mk]; rfl
    · simp [h]

theorem finW_map_toN (s : ℕ) (L : List (Fin s × Bool)) : finW s (L.map (toN s)) = L := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    simp only [List.map_cons, finW, List.filterMap_cons, toN, x.1.2, dite_true, Bool.not_not] at ih ⊢
    rw [ih]

/-- The word of an element of the free group. -/
def toWordN (s : ℕ) (g : FreeGroup (Fin s)) : Word := (FreeGroup.toWord g).map (toN s)

theorem wordFG_toWordN (s : ℕ) (g : FreeGroup (Fin s)) : wordFG s (toWordN s g) = g := by
  rw [wordFG_eq_mk, toWordN, finW_map_toN, FreeGroup.mk_toWord]

theorem map_toN_invRev (s : ℕ) (L : List (Fin s × Bool)) :
    (FreeGroup.invRev L).map (toN s) = invW (L.map (toN s)) := by
  simp [FreeGroup.invRev, invW, List.map_reverse, toN]

/-! ## Subgroups as sets of words -/

/-- The words whose element of the free group lies in `H`. -/
def wordEval (s : ℕ) (H : SubgroupSpace s) : WordSpace := fun u => H.1 (wordFG s u)

theorem continuous_wordEval (s : ℕ) : Continuous (wordEval s) :=
  continuous_pi fun u => (continuous_apply (wordFG s u)).comp continuous_subtype_val

theorem measurable_wordEval (s : ℕ) : Measurable (wordEval s) :=
  (continuous_wordEval s).measurable

/-- The sets of words that come from subgroups, by local conditions. -/
def Good (s : ℕ) : Set WordSpace :=
  {A | A [] = true ∧ (∀ u₁ u₂ i c, A (u₁ ++ (i, c) :: (i, !c) :: u₂) = A (u₁ ++ u₂)) ∧
    (∀ u v, A u = true → A v = true → A (u ++ invW v) = true) ∧
    (∀ u₁ u₂ i c, s ≤ i → A (u₁ ++ (i, c) :: u₂) = A (u₁ ++ u₂))}

theorem wordEval_mem_good {s : ℕ} (H : SubgroupSpace s) : wordEval s H ∈ Good s := by
  obtain ⟨h1, h2⟩ := H.2
  refine ⟨h1, fun u₁ u₂ i c => ?_, fun u v hu hv => ?_, fun u₁ u₂ i c hi => ?_⟩
  · simp only [wordEval, wordFG_append, wordFG_cons]
    have := letterFG_flip s (i, c)
    simp only at this
    rw [this]; group
  · simp only [wordEval, wordFG_append, wordFG_invW] at hu hv ⊢
    exact h2 _ _ hu hv
  · simp only [wordEval, wordFG_append, wordFG_cons, letterFG_of_le (l := (i, c)) hi, one_mul]

section Good

variable {s : ℕ} {A : WordSpace}

theorem good_red (hA : A ∈ Good s) {L₁ L₂ : List (Fin s × Bool)} (h : FreeGroup.Red L₁ L₂) :
    A (L₁.map (toN s)) = A (L₂.map (toN s)) := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
    rw [ih]
    cases hstep with
    | not =>
      simp only [List.map_append, List.map_cons, toN]
      exact hA.2.1 _ _ _ _

/-- On `Good s`, the value of the element of a word of the free group is the value of the
word. -/
theorem evW_mk (hA : A ∈ Good s) (L : List (Fin s × Bool)) :
    A ((FreeGroup.toWord (FreeGroup.mk L)).map (toN s)) = A (L.map (toN s)) := by
  rw [FreeGroup.toWord_mk]
  exact (good_red hA FreeGroup.reduce.red).symm

theorem good_filter (hA : A ∈ Good s) (u₁ u : Word) :
    A (u₁ ++ u) = A (u₁ ++ (finW s u).map (toN s)) := by
  induction u generalizing u₁ with
  | nil => rfl
  | cons l u ih =>
    obtain ⟨i, e⟩ := l
    by_cases h : i < s
    · have hf : (finW s ((i, e) :: u)).map (toN s) = (i, e) :: (finW s u).map (toN s) := by
        simp [finW, h, toN]
      rw [hf, show u₁ ++ (i, e) :: u = (u₁ ++ [(i, e)]) ++ u by simp, ih]
      simp
    · have hf : finW s ((i, e) :: u) = finW s u := by simp [finW, h]
      rw [hf, hA.2.2.2 u₁ u i e (Nat.le_of_not_lt h), ih]

/-- The elements of the free group whose reduced word lies in `A`. -/
def evW (s : ℕ) (A : WordSpace) : FreeGroup (Fin s) → Bool := fun g => A (toWordN s g)

theorem continuous_evW (s : ℕ) : Continuous (evW s) :=
  continuous_pi fun g => continuous_apply (toWordN s g)

theorem evW_wordFG (hA : A ∈ Good s) (u : Word) : evW s A (wordFG s u) = A u := by
  unfold evW toWordN
  rw [wordFG_eq_mk, evW_mk hA]
  simpa using (good_filter hA [] u).symm

theorem isSubgroupIndicator_evW (hA : A ∈ Good s) : IsSubgroupIndicator (evW s A) := by
  refine ⟨?_, fun v w hv hw => ?_⟩
  · simpa [evW, toWordN] using hA.1
  · have e : v * w⁻¹ =
        FreeGroup.mk (FreeGroup.toWord v ++ FreeGroup.invRev (FreeGroup.toWord w)) := by
      rw [← FreeGroup.mul_mk, ← FreeGroup.inv_mk, FreeGroup.mk_toWord, FreeGroup.mk_toWord]
    show A (toWordN s (v * w⁻¹)) = true
    rw [e, toWordN, evW_mk hA, List.map_append, map_toN_invRev]
    exact hA.2.2.1 _ _ hv hw

theorem evW_wordEval (H : SubgroupSpace s) : evW s (wordEval s H) = H.1 := by
  funext g
  simp [evW, wordEval, wordFG_toWordN]

end Good

/-! ## Conjugation by a letter -/

/-- Conjugation by a letter on sets of words: `u ∈ conjW g A` when `g⁻¹ u g ∈ A`. -/
def conjW (g : Letter) (A : WordSpace) : WordSpace := fun u => A (invW [g] ++ u ++ [g])

theorem continuous_conjW (g : Letter) : Continuous (conjW g) :=
  continuous_pi fun u => continuous_apply (invW [g] ++ u ++ [g])

theorem measurable_conjW (g : Letter) : Measurable (conjW g) :=
  (continuous_conjW g).measurable

theorem wordEval_conj {s : ℕ} (g : Letter) (H : SubgroupSpace s) :
    wordEval s (conj (letterFG s g) H) = conjW g (wordEval s H) := by
  funext u
  simp only [wordEval, conj, conjW, wordFG_append, wordFG_invW]
  simp [wordFG]

theorem evW_conjW {s : ℕ} {A : WordSpace} (hA : A ∈ Good s) (g : Letter) :
    evW s (conjW g A) = fun v => evW s A ((letterFG s g)⁻¹ * v * letterFG s g) := by
  funext v
  have e : (letterFG s g)⁻¹ * v * letterFG s g = wordFG s (invW [g] ++ toWordN s v ++ [g]) := by
    rw [wordFG_append, wordFG_append, wordFG_invW, wordFG_toWordN]
    simp [wordFG]
  rw [e, evW_wordFG hA]
  rfl

/-! ## From measures on words to invariant random subgroups -/

/-- The bad sets: the complement of `Good s` is their union. -/
def badSet (s : ℕ) : Unit ⊕ (Word × Word × ℕ × Bool) ⊕ (Word × Word) ⊕ (Word × Word × ℕ × Bool) →
    Set WordSpace
  | .inl _ => {A | A [] = false}
  | .inr (.inl (u₁, u₂, i, c)) => {A | A (u₁ ++ (i, c) :: (i, !c) :: u₂) ≠ A (u₁ ++ u₂)}
  | .inr (.inr (.inl (u, v))) => {A | A u = true ∧ A v = true ∧ A (u ++ invW v) = false}
  | .inr (.inr (.inr (u₁, u₂, i, c))) => {A | s ≤ i ∧ A (u₁ ++ (i, c) :: u₂) ≠ A (u₁ ++ u₂)}

theorem compl_good (s : ℕ) : (Good s)ᶜ = ⋃ b, badSet s b := by
  ext A
  simp only [Set.mem_compl_iff, Set.mem_iUnion]
  constructor
  · intro h
    by_contra hb
    push Not at hb
    apply h
    refine ⟨?_, fun u₁ u₂ i c => ?_, fun u v hu hv => ?_, fun u₁ u₂ i c hi => ?_⟩
    · have := hb (.inl ()); simp [badSet] at this; exact this
    · have := hb (.inr (.inl (u₁, u₂, i, c))); simpa [badSet] using this
    · have := hb (.inr (.inr (.inl (u, v)))); simp [badSet, hu, hv] at this; exact this
    · have := hb (.inr (.inr (.inr (u₁, u₂, i, c)))); simpa [badSet, hi] using this
  · rintro ⟨b, hb⟩ hA
    rcases b with _ | ⟨u₁, u₂, i, c⟩ | ⟨u, v⟩ | ⟨u₁, u₂, i, c⟩
    · simp [badSet, hA.1] at hb
    · exact hb (hA.2.1 u₁ u₂ i c)
    · simp [badSet, hA.2.2.1 u v hb.1 hb.2.1] at hb
    · exact hb.2 (hA.2.2.2 u₁ u₂ i c hb.1)

theorem isClopen_badSet (s : ℕ) (b) : IsClopen (badSet s b) := by
  have hc : ∀ u : Word, Continuous fun A : WordSpace => A u := fun u => continuous_apply u
  rcases b with _ | ⟨u₁, u₂, i, c⟩ | ⟨u, v⟩ | ⟨u₁, u₂, i, c⟩
  · exact (isClopen_discrete {false}).preimage (hc [])
  · exact (isClopen_discrete {p : Bool × Bool | p.1 ≠ p.2}).preimage ((hc _).prodMk (hc _))
  · exact (isClopen_discrete {p : Bool × Bool × Bool | p.1 = true ∧ p.2.1 = true ∧
      p.2.2 = false}).preimage ((hc u).prodMk ((hc v).prodMk (hc _)))
  · by_cases hi : s ≤ i
    · simpa [badSet, hi] using
        (isClopen_discrete {p : Bool × Bool | p.1 ≠ p.2}).preimage ((hc _).prodMk (hc _))
    · simp only [badSet, hi, false_and, Set.ofPred_false]
      exact isClopen_empty

theorem measurableSet_good (s : ℕ) : MeasurableSet (Good s) := by
  rw [← compl_compl (Good s), compl_good]
  exact (MeasurableSet.iUnion fun b => (isClopen_badSet s b).isOpen.measurableSet).compl

instance (s : ℕ) : Countable (FreeGroup (Fin s)) :=
  Function.Surjective.countable (f := FreeGroup.mk) fun _ => ⟨_, FreeGroup.mk_toWord⟩

/-- The measurable structure of `Sub(F)` is the one induced from the indicators. -/
theorem measurableSpace_subgroupSpace (s : ℕ) :
    instMeasurableSpaceSubgroupSpace s =
      MeasurableSpace.comap (fun H : SubgroupSpace s => H.1)
        (inferInstance : MeasurableSpace (FreeGroup (Fin s) → Bool)) := by
  change borel _ = _
  rw [BorelSpace.measurable_eq (α := FreeGroup (Fin s) → Bool)]
  exact borel_comap

theorem measurable_to_subgroupSpace {X : Type*} [MeasurableSpace X] {s : ℕ}
    {f : X → SubgroupSpace s} (hf : Measurable fun x => (f x).1) : Measurable f := by
  intro E hE
  have h := measurableSpace_subgroupSpace s
  obtain ⟨E', hE', rfl⟩ : MeasurableSet[MeasurableSpace.comap (fun H : SubgroupSpace s => H.1)
      (inferInstance : MeasurableSpace (FreeGroup (Fin s) → Bool))] E := h ▸ hE
  exact hf hE'

/-- The subgroup of a good set of words; the whole group otherwise. -/
noncomputable def toSub (s : ℕ) (A : WordSpace) : SubgroupSpace s := by
  classical
  exact ⟨if A ∈ Good s then evW s A else fun _ => true, by
    split_ifs with h
    · exact isSubgroupIndicator_evW h
    · exact ⟨rfl, fun _ _ _ _ => rfl⟩⟩

theorem toSub_of_good {s : ℕ} {A : WordSpace} (hA : A ∈ Good s) : (toSub s A).1 = evW s A := by
  simp [toSub, hA]

theorem measurable_toSub (s : ℕ) : Measurable (toSub s) := by
  classical
  refine measurable_to_subgroupSpace ?_
  simp only [toSub]
  exact Measurable.ite (measurableSet_good s) (continuous_evW s).measurable measurable_const

theorem conj_mul {s : ℕ} (w₁ w₂ : FreeGroup (Fin s)) (H : SubgroupSpace s) :
    conj (w₁ * w₂) H = conj w₁ (conj w₂ H) := by
  apply Subtype.ext; funext v
  simp only [conj, mul_inv_rev]
  group

theorem conj_one {s : ℕ} (H : SubgroupSpace s) : conj 1 H = H := by
  apply Subtype.ext; funext v; simp [conj]

/-- **The transfer to `Sub(F)`**: a probability measure on sets of words carried by `Good s` and
invariant under conjugation by the letters below `s` is the image of an IRS with the same
value. -/
theorem irs_of_good (T : SubgroupTestData) (ν : ProbabilityMeasure WordSpace)
    (hG : (ν : Measure WordSpace) (Good T.nGen)ᶜ = 0)
    (hinv : ∀ g : Letter, g.1 < T.nGen → (ν : Measure WordSpace).map (conjW g) = ν) :
    ∃ μ ∈ IRS T.nGen, T.valOn μ = valΩ T ν := by
  set s := T.nGen
  have hae : ∀ᵐ A ∂(ν : Measure WordSpace), A ∈ Good s := ae_iff.2 hG
  refine ⟨ν.map (toSub s), ?_, ?_⟩
  · -- invariance under the letters, then under the whole group
    have hletter : ∀ g : Letter, g.1 < s →
        ((ν.map (toSub s) : ProbabilityMeasure _) : Measure (SubgroupSpace s)).map
          (conj (letterFG s g)) = (ν.map (toSub s) : Measure (SubgroupSpace s)) := by
      intro g hg
      have hG' : ∀ᵐ A ∂(ν : Measure WordSpace), conjW g A ∈ Good s := by
        have : (ν : Measure WordSpace) (conjW g ⁻¹' (Good s)ᶜ) = 0 := by
          rw [← Measure.map_apply (measurable_conjW g) (measurableSet_good s).compl, hinv g hg, hG]
        exact ae_iff.2 this
      rw [ProbabilityMeasure.toMeasure_map, Measure.map_map (measurable_conj _) (measurable_toSub s)]
      have hcongr : conj (letterFG s g) ∘ toSub s =ᵐ[(ν : Measure WordSpace)]
          toSub s ∘ conjW g := by
        filter_upwards [hae, hG'] with A hA hA'
        apply Subtype.ext
        simp only [Function.comp_apply, conj, toSub_of_good hA', evW_conjW hA g, toSub_of_good hA]
      rw [Measure.map_congr hcongr, ← Measure.map_map (measurable_toSub s) (measurable_conjW g),
        hinv g hg]
    intro w
    induction w using FreeGroup.induction_on with
    | one =>
      have : (conj (1 : FreeGroup (Fin s)) : SubgroupSpace s → SubgroupSpace s) = id :=
        funext conj_one
      rw [this, Measure.map_id]
    | of x =>
      have := hletter (x.val, false) x.2
      rwa [show letterFG s (x.val, false) = FreeGroup.of x by simp [letterFG, show (x : ℕ) < s from x.2]] at this
    | inv_of x _ =>
      have := hletter (x.val, true) x.2
      rwa [show letterFG s (x.val, true) = (FreeGroup.of x)⁻¹ by simp [letterFG, show (x : ℕ) < s from x.2]] at this
    | mul x y hx hy =>
      have : (conj (x * y) : SubgroupSpace s → SubgroupSpace s) = conj x ∘ conj y :=
        funext (conj_mul x y)
      rw [this, ← Measure.map_map (measurable_conj x) (measurable_conj y), hy, hx]
  · unfold SubgroupTestData.valOn valΩ
    rw [valGen_eq_valW, valW_map T ?_ (measurable_toSub s)]
    · refine valW_congr_ae T ν ?_
      filter_upwards [hae] with A hA
      funext u
      simp only [Function.comp_apply, SubgroupTestData.subVal, toSub_of_good hA, id]
      exact evW_wordFG hA u
    · exact continuous_pi fun u => (continuous_apply (wordFG s u)).comp continuous_subtype_val

/-- The image of an IRS on sets of words is invariant under conjugation by the letters. -/
theorem map_wordEval_conjW {s : ℕ} {μ : ProbabilityMeasure (SubgroupSpace s)} (hμ : μ ∈ IRS s)
    (g : Letter) :
    ((μ : Measure (SubgroupSpace s)).map (wordEval s)).map (conjW g) =
      (μ : Measure (SubgroupSpace s)).map (wordEval s) := by
  rw [Measure.map_map (measurable_conjW g) (measurable_wordEval s)]
  have : conjW g ∘ wordEval s = wordEval s ∘ conj (letterFG s g) :=
    funext fun H => (wordEval_conj g H).symm
  rw [this, ← Measure.map_map (measurable_wordEval s) (measurable_conj _), hμ]

/-- The value of a measure on `Sub(F)` is the value of its image on sets of words. -/
theorem valOn_eq_valΩ (T : SubgroupTestData) (μ : ProbabilityMeasure (SubgroupSpace T.nGen)) :
    T.valOn μ = valΩ T (μ.map (wordEval T.nGen)) := by
  unfold SubgroupTestData.valOn valΩ
  rw [valGen_eq_valW, valW_map T continuous_id (measurable_wordEval _)]
  rfl

end MIPRE.Tailored.Sofic.Measure

end

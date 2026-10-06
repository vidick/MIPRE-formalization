/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.SubgroupTestValue
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import MIPRE.Tactics

@[expose] public section

/-!
# The value of a subgroup test as a weak-* continuous functional

Paper I, I:439–460: the value `val(T, π)` of a test against a probability measure `π` on the
subsets of the free group is the probability that a subset drawn from `π` passes a challenge drawn
with probability proportional to its weight. A challenge depends on finitely many coordinates of
the subset, so its passing set is clopen and the value is weak-* continuous.

The value is defined here for a measure on any space `X` with a continuous map `ev` to the
indicator functions `FreeGroup (Fin s) → Bool` (`valGen`); `SubgroupTestData.valOn` is the case
`X = Sub(F)`, `ev = Subtype.val`, and the upper approximation of the ergodic value uses the case
`X = {0,1}^F`. The main results:

* `wordFG`: the element of the free group of a word, its letters beyond the generators dropped,
  with `FreeGroup.lift σ.σ (wordFG w) = σ.wordPerm w` (`lift_wordFG`);
* `continuous_valGen`, `SubgroupTestData.continuous_valOn`: weak-* continuity;
* `SubgroupTestData.valOn_finDesc`: on the finitely described IRS `Φ(σ)` the value is
  `T.value σ`.
-/

namespace MIPRE.Tailored.Sofic.Measure

open SubgroupTestValue MeasureTheory

/-! ## Words as elements of the free group -/

/-- The element of the free group of a letter; a letter beyond the `s` generators is the
identity, as in `FiniteAction.letterPerm`. -/
def letterFG (s : ℕ) (l : Letter) : FreeGroup (Fin s) :=
  if h : l.1 < s then (if l.2 then (FreeGroup.of ⟨l.1, h⟩)⁻¹ else FreeGroup.of ⟨l.1, h⟩) else 1

/-- The element of the free group of a word, the product of its letters from left to right. -/
def wordFG (s : ℕ) (w : Word) : FreeGroup (Fin s) := (w.map (letterFG s)).prod

theorem lift_letterFG {s : ℕ} (σ : FiniteAction s) (l : Letter) :
    FreeGroup.lift σ.σ (letterFG s l) = σ.letterPerm l := by
  unfold letterFG FiniteAction.letterPerm
  split_ifs <;> simp

/-- A finite action's permutation of a word is the image of the word's element of the free
group. -/
theorem lift_wordFG {s : ℕ} (σ : FiniteAction s) (w : Word) :
    FreeGroup.lift σ.σ (wordFG s w) = σ.wordPerm w := by
  unfold wordFG FiniteAction.wordPerm
  rw [map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun l _ => lift_letterFG σ l

/-- Membership of a word in a stabilizer, through the free group. -/
theorem stab_wordFG {s : ℕ} (σ : FiniteAction s) (x : Fin σ.N) (w : Word) :
    (stab σ x).1 (wordFG s w) = decide (σ.InStab x w) := by
  simp only [stab, FiniteAction.InStab, lift_wordFG]

/-! ## Passing a challenge -/

/-- The literal `(i, b)` on an indicator `A`: the `i`-th word of `K` lies in `A` exactly when
`b`; false when `i` is beyond `K`. -/
def litB (s : ℕ) (K : List Word) (A : FreeGroup (Fin s) → Bool) (lit : ℕ × Bool) : Bool :=
  match K[lit.1]? with
  | some k => A (wordFG s k) == lit.2
  | none => false

/-- The indicator `A` passes the challenge `(K, clauses)`: some clause holds. -/
def passB (s : ℕ) (K : List Word) (cl : List (List (ℕ × Bool))) (A : FreeGroup (Fin s) → Bool) :
    Bool :=
  cl.any fun c => c.all fun lit => litB s K A lit

theorem litB_stab {s : ℕ} (σ : FiniteAction s) (x : Fin σ.N) (K : List Word) (lit : ℕ × Bool) :
    litB s K (stab σ x).1 lit = decide (σ.LitHolds K x lit) := by
  obtain ⟨i, b⟩ := lit
  unfold litB FiniteAction.LitHolds
  by_cases h : i < K.length
  · rw [List.getElem?_eq_getElem h]
    simp only [stab_wordFG, h, exists_true_left]
    cases b <;> simp
  · rw [List.getElem?_eq_none (Nat.le_of_not_lt h)]
    simp [h]

theorem passB_stab {s : ℕ} (σ : FiniteAction s) (x : Fin σ.N) (K : List Word)
    (cl : List (List (ℕ × Bool))) :
    passB s K cl (stab σ x).1 = decide (σ.Passes K cl x) := by
  unfold passB FiniteAction.Passes
  simp only [litB_stab]
  rw [Bool.eq_iff_iff]
  simp

/-! ## Continuity -/

section Continuity

variable {X : Type*} [TopologicalSpace X]

theorem continuous_bool_and {f g : X → Bool} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => f x && g x :=
  (continuous_of_discreteTopology (f := fun p : Bool × Bool => p.1 && p.2)).comp (hf.prodMk hg)

theorem continuous_bool_or {f g : X → Bool} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => f x || g x :=
  (continuous_of_discreteTopology (f := fun p : Bool × Bool => p.1 || p.2)).comp (hf.prodMk hg)

theorem continuous_list_all {ι : Type*} (l : List ι) (f : ι → X → Bool)
    (h : ∀ i ∈ l, Continuous (f i)) : Continuous fun x => l.all fun i => f i x := by
  induction l with
  | nil => simpa using continuous_const
  | cons a l ih =>
    simp only [List.all_cons]
    exact continuous_bool_and (h a (by simp)) (ih fun i hi => h i (by simp [hi]))

theorem continuous_list_any {ι : Type*} (l : List ι) (f : ι → X → Bool)
    (h : ∀ i ∈ l, Continuous (f i)) : Continuous fun x => l.any fun i => f i x := by
  induction l with
  | nil => simpa using continuous_const
  | cons a l ih =>
    simp only [List.any_cons]
    exact continuous_bool_or (h a (by simp)) (ih fun i hi => h i (by simp [hi]))

variable {s : ℕ} {ev : X → FreeGroup (Fin s) → Bool}

theorem continuous_litB (hev : Continuous ev) (K : List Word) (lit : ℕ × Bool) :
    Continuous fun x => litB s K (ev x) lit := by
  unfold litB
  cases K[lit.1]? with
  | none => exact continuous_const
  | some k =>
    exact (continuous_of_discreteTopology (f := fun a : Bool => a == lit.2)).comp
      ((continuous_apply (wordFG s k)).comp hev)

theorem continuous_passB (hev : Continuous ev) (K : List Word) (cl : List (List (ℕ × Bool))) :
    Continuous fun x => passB s K cl (ev x) :=
  continuous_list_any _ _ fun _ _ =>
    continuous_list_all _ _ fun _ _ => continuous_litB hev K _

/-- The set of points passing a challenge. -/
def passSet (s : ℕ) (ev : X → FreeGroup (Fin s) → Bool) (K : List Word)
    (cl : List (List (ℕ × Bool))) : Set X :=
  {x | passB s K cl (ev x) = true}

theorem isClopen_passSet (hev : Continuous ev) (K : List Word) (cl : List (List (ℕ × Bool))) :
    IsClopen (passSet s ev K cl) :=
  (isClopen_discrete {true}).preimage (continuous_passB hev K cl)

variable [MeasurableSpace X] [OpensMeasurableSpace X]

/-- The measure of a clopen set is weak-* continuous. -/
theorem continuous_measureReal_of_isClopen {E : Set X} (hE : IsClopen E) :
    Continuous fun μ : ProbabilityMeasure X => (μ : Measure X).real E := by
  have h := ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (BoundedContinuousFunction.indicator E hE)
  refine h.congr fun μ => ?_
  simp only [BoundedContinuousFunction.indicator_apply]
  exact integral_indicator_one hE.isOpen.measurableSet

end Continuity

/-! ## The value -/

/-- The value `val(T, μ)` (I:455) of a probability measure on a space `X` mapped continuously to
the indicators: the weighted measure of the sets passing each challenge, normalized by the total
weight as in `SubgroupTestData.value`. -/
noncomputable def valGen {X : Type*} [MeasurableSpace X] (T : SubgroupTestData)
    (ev : X → FreeGroup (Fin T.nGen) → Bool) (μ : ProbabilityMeasure X) : ℝ :=
  (T.challenges.map fun c => (c.1 : ℝ) * (μ : Measure X).real (passSet T.nGen ev c.2.1 c.2.2)).sum /
    T.totalWeight

theorem continuous_list_sum_map {X ι : Type*} [TopologicalSpace X] (l : List ι) (f : ι → X → ℝ)
    (h : ∀ i ∈ l, Continuous (f i)) : Continuous fun x => (l.map fun i => f i x).sum := by
  induction l with
  | nil => simpa using continuous_const
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h a (by simp)).add (ih fun i hi => h i (by simp [hi]))

/-- **The value is weak-* continuous.** -/
theorem continuous_valGen {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (T : SubgroupTestData) {ev : X → FreeGroup (Fin T.nGen) → Bool}
    (hev : Continuous ev) : Continuous (valGen T ev) := by
  unfold valGen
  refine Continuous.div_const (continuous_list_sum_map _ _ fun c _ => ?_) _
  exact continuous_const.mul (continuous_measureReal_of_isClopen (isClopen_passSet hev _ _))

theorem valGen_nonneg {X : Type*} [MeasurableSpace X] (T : SubgroupTestData)
    (ev : X → FreeGroup (Fin T.nGen) → Bool) (μ : ProbabilityMeasure X) : 0 ≤ valGen T ev μ := by
  unfold valGen
  refine div_nonneg (List.sum_nonneg fun x hx => ?_) (Nat.cast_nonneg _)
  obtain ⟨_, -, rfl⟩ := List.mem_map.1 hx
  exact mul_nonneg (Nat.cast_nonneg _) measureReal_nonneg

/-- A weighted average of numbers in `[0, 1]` is at most `1`. -/
theorem weighted_le_one {ι : Type*} (l : List (ℕ × ι)) (p : ι → ℝ) (hp : ∀ c ∈ l, p c.2 ≤ 1) :
    (l.map fun c => (c.1 : ℝ) * p c.2).sum ≤ ((l.map (·.1)).sum : ℕ) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, Nat.cast_add]
    have h1 : (a.1 : ℝ) * p a.2 ≤ a.1 :=
      mul_le_of_le_one_right (Nat.cast_nonneg _) (hp a (by simp))
    linarith [ih fun c hc => hp c (by simp [hc])]

theorem valGen_le_one {X : Type*} [MeasurableSpace X] (T : SubgroupTestData)
    (ev : X → FreeGroup (Fin T.nGen) → Bool) (μ : ProbabilityMeasure X) : valGen T ev μ ≤ 1 := by
  unfold valGen
  rcases Nat.eq_zero_or_pos T.totalWeight with h | h
  · simp [h]
  rw [div_le_one (by exact_mod_cast h)]
  exact weighted_le_one T.challenges
    (fun c => (μ : Measure X).real (passSet T.nGen ev c.1 c.2)) fun _ _ => measureReal_le_one

end MIPRE.Tailored.Sofic.Measure

namespace SubgroupTestValue

open MeasureTheory MIPRE.Tailored.Sofic.Measure

/-- The finitely described IRS `Φ(σ)` (I:510) as a probability measure. -/
noncomputable def FiniteAction.finDesc {s : ℕ} (σ : FiniteAction s) :
    ProbabilityMeasure (SubgroupSpace s) :=
  ⟨((σ.N : ENNReal)⁻¹) • ∑ x : Fin σ.N, Measure.dirac (stab σ x), by
    constructor
    simp only [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, measure_univ,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (by exact_mod_cast σ.N_pos.ne') (ENNReal.natCast_ne_top _)⟩

theorem FiniteAction.finDesc_mem {s : ℕ} (σ : FiniteAction s) : σ.finDesc ∈ finDescIRS s :=
  ⟨σ, rfl⟩

open Classical in
/-- The measure of a measurable set under `Φ(σ)`: the fraction of the points whose stabilizer it
contains. -/
theorem FiniteAction.measureReal_eq {s : ℕ} (σ : FiniteAction s) (μ : ProbabilityMeasure (SubgroupSpace s))
    (hμ : (μ : Measure (SubgroupSpace s)) =
      ((σ.N : ENNReal)⁻¹) • ∑ x : Fin σ.N, Measure.dirac (stab σ x))
    {E : Set (SubgroupSpace s)} (hE : MeasurableSet E) :
    (μ : Measure (SubgroupSpace s)).real E =
      ((Finset.univ.filter fun x => stab σ x ∈ E).card : ℝ) / σ.N := by
  rw [measureReal_def, hμ]
  simp only [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.dirac_apply' _ hE, smul_eq_mul]
  rw [Finset.sum_indicator_eq_sum_filter]
  simp only [Pi.one_apply, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv]
  simp [div_eq_inv_mul]

namespace SubgroupTestData

variable (T : SubgroupTestData)

/-- The indicator of a subgroup. -/
def subVal (s : ℕ) (H : SubgroupSpace s) : FreeGroup (Fin s) → Bool := H.1

theorem continuous_subVal (s : ℕ) : Continuous (subVal s) := continuous_subtype_val

/-- **The value of a probability measure on `Sub(F)`** (I:455): the weighted measure of the set
of subgroups passing each challenge, normalized as in `value`. -/
noncomputable def valOn (μ : ProbabilityMeasure (SubgroupSpace T.nGen)) : ℝ :=
  valGen T (subVal T.nGen) μ

/-- **The value is weak-* continuous** (I:458). -/
theorem continuous_valOn : Continuous T.valOn :=
  continuous_valGen T (continuous_subVal _)

theorem valOn_nonneg (μ : ProbabilityMeasure (SubgroupSpace T.nGen)) : 0 ≤ T.valOn μ :=
  valGen_nonneg T _ μ

theorem valOn_le_one (μ : ProbabilityMeasure (SubgroupSpace T.nGen)) : T.valOn μ ≤ 1 :=
  valGen_le_one T _ μ

/-- **The value of a finitely described IRS** `Φ(σ)` is the value of `σ`. -/
theorem valOn_of_eq (σ : FiniteAction T.nGen) (μ : ProbabilityMeasure (SubgroupSpace T.nGen))
    (hμ : (μ : Measure (SubgroupSpace T.nGen)) =
      ((σ.N : ENNReal)⁻¹) • ∑ x : Fin σ.N, Measure.dirac (stab σ x)) :
    T.valOn μ = T.value σ := by
  unfold valOn valGen value
  congr 1
  congr 1
  refine List.map_congr_left fun c _ => ?_
  rw [σ.measureReal_eq μ hμ ((isClopen_passSet (continuous_subVal _) _ _).isOpen.measurableSet)]
  congr 2
  congr 2
  ext x
  simp [passSet, subVal, passB_stab]

theorem valOn_finDesc (σ : FiniteAction T.nGen) : T.valOn σ.finDesc = T.value σ :=
  T.valOn_of_eq σ _ rfl

theorem value_nonneg (σ : FiniteAction T.nGen) : 0 ≤ T.value σ :=
  T.valOn_finDesc σ ▸ T.valOn_nonneg _

theorem value_le_one (σ : FiniteAction T.nGen) : T.value σ ≤ 1 :=
  T.valOn_finDesc σ ▸ T.valOn_le_one _

end SubgroupTestData

end SubgroupTestValue

end

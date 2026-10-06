/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Sofic.Measure.Valid
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import MIPRE.Tactics

@[expose] public section

/-!
# Limits of approximately good, approximately invariant measures

Paper I, the proof of Main Theorem I (2), second half (I:1204–1217): a weak-* limit of points of
the polytopes `Q̃_{B_t}` is an IRS. Here: if probability measures `ν t` on sets of words give
eventually no mass to each bad set and are eventually invariant, up to any `η > 0`, on each
cylinder `restrSet J q` under conjugation by each letter below `s`, then their values are
eventually at most `valErg + ε` (`eventually_valΩ_le`). The probability measures on the compact
space `WordSpace` form a compact space (Prokhorov, in Mathlib), so a frequently bad subsequence
would have a cluster point; it is carried by `Good s` and invariant (the cylinders are a π-system
generating the σ-algebra), so it is the image of an IRS (`irs_of_good`), whose value is at most
the ergodic value.
-/

namespace MIPRE.Tailored.Sofic.Measure

open SubgroupTestValue MeasureTheory Filter Topology

/-- The cylinders. -/
def cylinders : Set (Set WordSpace) := {E | ∃ J q, E = restrSet J q}

theorem isPiSystem_cylinders : IsPiSystem cylinders := by
  rintro _ ⟨J, q, rfl⟩ _ ⟨J', q', rfl⟩ ⟨A, hA, hA'⟩
  refine ⟨J ++ J', q ++ q', ?_⟩
  have hl : J.length = q.length := by rw [← hA]; simp
  ext B
  simp only [restrSet, Set.mem_inter_iff, Set.mem_ofPred_eq, List.map_append]
  constructor
  · rintro ⟨h1, h2⟩; rw [h1, h2]
  · intro h
    exact List.append_inj h (by simp [hl])

theorem generateFrom_cylinders :
    (inferInstance : MeasurableSpace WordSpace) = MeasurableSpace.generateFrom cylinders := by
  apply le_antisymm
  · refine iSup_le fun u => ?_
    have h : @Measurable _ _ (MeasurableSpace.generateFrom cylinders) _ fun A : WordSpace => A u := by
      refine @measurable_to_bool _ (MeasurableSpace.generateFrom cylinders) _ ?_
      refine MeasurableSpace.measurableSet_generateFrom ⟨[u], [true], ?_⟩
      ext A; simp [restrSet]
    exact h.comap_le
  · refine MeasurableSpace.generateFrom_le ?_
    rintro _ ⟨J, q, rfl⟩
    exact measurableSet_restrSet J q

/-- Two probability measures on sets of words agreeing on the cylinders are equal. -/
theorem ext_cylinders {μ ν : Measure WordSpace} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ J q, μ (restrSet J q) = ν (restrSet J q)) : μ = ν :=
  ext_of_generate_finite cylinders generateFrom_cylinders isPiSystem_cylinders
    (by rintro _ ⟨J, q, rfl⟩; exact h J q) (by simp)

theorem isClopen_conjW_restrSet (g : Letter) (J : List Word) (q : List Bool) :
    IsClopen (conjW g ⁻¹' restrSet J q) :=
  (isClopen_restrSet J q).preimage (continuous_conjW g)

/-- A closed set eventually containing a sequence along a filter contains its cluster points. -/
theorem mem_of_clusterPt {X : Type*} [TopologicalSpace X] {F : Filter ℕ} {ν : ℕ → X} {x : X}
    (hx : ClusterPt x (F.map ν)) {S : Set X} (hS : IsClosed S) (h : ∀ᶠ t in F, ν t ∈ S) :
    x ∈ S :=
  hS.closure_eq ▸ hx.mem_closure_of_mem S (Filter.mem_map.2 h)

/-- **Limits of approximately good, approximately invariant measures**: their values are
eventually at most the ergodic value plus any `ε > 0`. -/
theorem eventually_valΩ_le (T : SubgroupTestData) (ν : ℕ → ProbabilityMeasure WordSpace)
    (h1 : ∀ b, ∀ᶠ t in atTop, (ν t : Measure WordSpace) (badSet T.nGen b) = 0)
    (h2 : ∀ g : Letter, g.1 < T.nGen → ∀ J q, ∀ η > 0, ∀ᶠ t in atTop,
      |(ν t : Measure WordSpace).real (restrSet J q) -
        (ν t : Measure WordSpace).real (conjW g ⁻¹' restrSet J q)| ≤ η) :
    ∀ ε > 0, ∀ᶠ t in atTop, valΩ T (ν t) ≤ T.valErg + ε := by
  intro ε hε
  by_contra hne
  rw [Filter.not_eventually, Filter.frequently_iff_neBot] at hne
  set F := atTop ⊓ 𝓟 {t | ¬valΩ T (ν t) ≤ T.valErg + ε}
  have : (F.map ν).NeBot := hne.map ν
  obtain ⟨νL, hcl⟩ := exists_clusterPt_of_compactSpace (F.map ν)
  have hF : ∀ {p : ℕ → Prop}, (∀ᶠ t in atTop, p t) → ∀ᶠ t in F, p t :=
    fun h => h.filter_mono inf_le_left
  -- the value
  have hval : T.valErg + ε ≤ valΩ T νL := by
    have hP : ∀ᶠ t in F, ¬valΩ T (ν t) ≤ T.valErg + ε :=
      (inf_le_right : F ≤ 𝓟 {t | ¬valΩ T (ν t) ≤ T.valErg + ε}) (Filter.mem_principal_self _)
    exact mem_of_clusterPt hcl (isClosed_le continuous_const (continuous_valΩ T))
      (hP.mono fun t ht => le_of_lt (not_le.1 ht))
  -- carried by `Good`
  have hbad : ∀ b, (νL : Measure WordSpace) (badSet T.nGen b) = 0 := by
    intro b
    have hS : IsClosed {μ : ProbabilityMeasure WordSpace |
        (μ : Measure WordSpace).real (badSet T.nGen b) = 0} :=
      isClosed_eq (continuous_measureReal_of_isClopen (isClopen_badSet _ b)) continuous_const
    have := mem_of_clusterPt hcl hS (hF ((h1 b).mono fun t ht => by
      simp [measureReal_def, ht]))
    simpa [measureReal_eq_zero_iff] using this
  have hG : (νL : Measure WordSpace) (Good T.nGen)ᶜ = 0 := by
    rw [compl_good]; exact measure_iUnion_null hbad
  -- invariant
  have hinv : ∀ g : Letter, g.1 < T.nGen →
      (νL : Measure WordSpace).map (conjW g) = νL := by
    intro g hg
    have : IsProbabilityMeasure ((νL : Measure WordSpace).map (conjW g)) := inferInstance
    refine ext_cylinders fun J q => ?_
    rw [Measure.map_apply (measurable_conjW g) (measurableSet_restrSet J q)]
    have hc : Continuous fun μ : ProbabilityMeasure WordSpace =>
        (μ : Measure WordSpace).real (restrSet J q) -
          (μ : Measure WordSpace).real (conjW g ⁻¹' restrSet J q) :=
      (continuous_measureReal_of_isClopen (isClopen_restrSet J q)).sub
        (continuous_measureReal_of_isClopen (isClopen_conjW_restrSet g J q))
    have hzero : |(νL : Measure WordSpace).real (restrSet J q) -
        (νL : Measure WordSpace).real (conjW g ⁻¹' restrSet J q)| = 0 := by
      refine le_antisymm (le_of_forall_pos_le_add fun η hη => ?_) (abs_nonneg _)
      rw [zero_add]
      exact mem_of_clusterPt hcl (isClosed_le (continuous_abs.comp hc) continuous_const)
        (hF (h2 g hg J q η hη))
    rw [abs_eq_zero, sub_eq_zero] at hzero
    rw [measureReal_def, measureReal_def] at hzero
    exact ((ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1
      hzero).symm
  obtain ⟨μ, hμ, hμv⟩ := irs_of_good T νL hG hinv
  have := T.le_valErg hμ
  rw [hμv] at this
  linarith

end MIPRE.Tailored.Sofic.Measure

end

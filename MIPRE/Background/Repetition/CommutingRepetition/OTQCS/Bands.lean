/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/OTQCS/Bands.lean
-/
/-
# OTQCS: the retained bins as a band family (proof layer of node 1.3.9)

The bridge between the grid slab (`OTQCS/Grid.lean`, `OTQCS/GridAverage.lean`:
shifted geometric bins, the rounded masses `a_θ, b_θ, c_θ` and `Γ_θ` as
integrals against the couplings) and the finite band interface consumed by the
trial construction (`OTQCS/Trial.lean`: `IsBandFamily`, `bandMassA/B`,
`bandCross`, `bandZ`). Anchors: 06_otqcs.tex, eq N1-Z "the finite retained bin
set" `J = {j : I_j^θ ∩ [L, H] ≠ ∅}`, eq shifted-bins `t_j^θ = r^{j+1+θ}`, eq
abcGamma, eq c-min, and the tail-cutoff choice "one finite `H` makes the two
high-tail bounds hold for every member".

Contents (all proof-side, no manuscript statements):
* the retained bins `retainedBin r θ L H k = I_{j₀+k}^θ ∩ [L, H]` indexed by
  `Fin (binCount r θ L H)`, their band values `retainedVal`, and the facts that
  they form an `IsBandFamily`, sit inside `[t_k / r, t_k]`, and cover `[L, H]`;
* the bridge identities `gridA/B/C ν r θ L H = ∑_k t_k² · (mass of the k-th
  retained bin)`, so that at the common shift the grid masses ARE the band
  masses;
* the band-mass inequalities `0 ≤ c ≤ min(a, b)`, `a, b ≤ Z`, `a + b − c ≤ Z`;
* the window second-moment lower bound `∫_{[L,H]} b² dμ ≥ 1 − ρ − L²`;
* the tail cutoff: one `H > L` with every high squared tail of a finite family
  of second-moment-one probability measures at most `ρ`.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.OTQCS.Trial
import MIPRE.Background.Repetition.CommutingRepetition.OTQCS.GridAverage

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

open MeasureTheory Set Filter Topology
open scoped BigOperators

universe u v w

/-! ### Retained bins as a band family -/

section RetainedBins

variable (r θ L H : ℝ)

/-- Lowest retained bin index: the bin containing `L`. -/
noncomputable def binLo : ℤ := binIdx r θ L

/-- Highest retained bin index: the bin containing `H`. -/
noncomputable def binHi : ℤ := binIdx r θ H

/-- Number of retained bins (those meeting the window `[L, H]`). -/
noncomputable def binCount : ℕ := (binHi r θ H - binLo r θ L + 1).toNat

/-- The `k`-th retained bin `I_j^θ ∩ [L, H]`, `j = binLo + k`
(06_otqcs.tex, eq N1-Z "the finite retained bin set"). -/
noncomputable def retainedBin (k : Fin (binCount r θ L H)) : Set ℝ :=
  binIdx r θ ⁻¹' {binLo r θ L + ((k : ℕ) : ℤ)} ∩ Icc L H

/-- Its band value: the upper endpoint `t_j^θ = r^(j+1+θ)` (eq shifted-bins). -/
noncomputable def retainedVal (k : Fin (binCount r θ L H)) : ℝ :=
  r ^ (((binLo r θ L + ((k : ℕ) : ℤ) : ℤ) : ℝ) + 1 + θ)

variable {r θ L H}

theorem binIdx_mono (hr : 1 < r) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    binIdx r θ a ≤ binIdx r θ b := by
  have hlr : 0 < Real.log r := Real.log_pos hr
  unfold binIdx
  apply Int.floor_le_floor
  have h := Real.log_le_log ha hab
  have h2 := div_le_div_of_nonneg_right h (le_of_lt hlr)
  linarith

theorem binIdx_mem_range (hr : 1 < r) (hL : 0 < L) {a : ℝ} (ha : a ∈ Icc L H) :
    binLo r θ L ≤ binIdx r θ a ∧ binIdx r θ a ≤ binHi r θ H :=
  ⟨binIdx_mono hr hL ha.1, binIdx_mono hr (lt_of_lt_of_le hL ha.1) ha.2⟩

/-- The retained index of a point of the window. -/
noncomputable def retainedIdx (hr : 1 < r) (hL : 0 < L) {a : ℝ} (ha : a ∈ Icc L H) :
    Fin (binCount r θ L H) :=
  ⟨(binIdx r θ a - binLo r θ L).toNat, by
    have h := binIdx_mem_range (θ := θ) hr hL ha
    unfold binCount
    have h0 : 0 ≤ binIdx r θ a - binLo r θ L := by linarith [h.1]
    have h1 : binIdx r θ a - binLo r θ L < binHi r θ H - binLo r θ L + 1 := by linarith [h.2]
    rw [Int.lt_toNat, Int.toNat_of_nonneg h0]
    exact h1⟩

theorem retainedIdx_spec (hr : 1 < r) (hL : 0 < L) {a : ℝ} (ha : a ∈ Icc L H) :
    binLo r θ L + ((retainedIdx (θ := θ) hr hL ha : ℕ) : ℤ) = binIdx r θ a := by
  unfold retainedIdx
  simp only
  rw [Int.toNat_of_nonneg (by linarith [(binIdx_mem_range (θ := θ) hr hL ha).1])]
  ring

/-- The retained rounded square regroups over the retained bins:
`roundSq a = ∑_k t_k² 1_{B_k}(a)` (eq abcGamma, finite retained-bin form). -/
theorem roundSq_eq_sum_retained (hr : 1 < r) (hL : 0 < L) (a : ℝ) :
    roundSq r θ L H a =
      ∑ k : Fin (binCount r θ L H),
        retainedVal r θ L H k ^ 2 * (retainedBin r θ L H k).indicator 1 a := by
  classical
  by_cases ha : a ∈ Icc L H
  · have hspec := retainedIdx_spec (θ := θ) hr hL ha
    set k₀ := retainedIdx (θ := θ) hr hL ha with hk₀
    rw [Finset.sum_eq_single k₀]
    · have hmem : a ∈ retainedBin r θ L H k₀ := by
        simp only [retainedBin, mem_inter_iff, mem_preimage, mem_singleton_iff]
        exact ⟨hspec.symm, ha⟩
      rw [indicator_of_mem hmem, Pi.one_apply, mul_one, roundSq, if_pos ha, retainedVal,
        hspec, roundVal]
    · intro k _ hk
      have hnot : a ∉ retainedBin r θ L H k := by
        intro hmem
        apply hk
        simp only [retainedBin, mem_inter_iff, mem_preimage, mem_singleton_iff] at hmem
        have : ((k : ℕ) : ℤ) = ((k₀ : ℕ) : ℤ) := by linarith [hmem.1, hspec]
        exact Fin.ext (by exact_mod_cast this)
      rw [indicator_of_notMem hnot, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [roundSq_of_notMem ha]
    symm
    apply Finset.sum_eq_zero
    intro k _
    rw [indicator_of_notMem (fun h => ha h.2), mul_zero]

/-- The same-bin joint rounded square regroups over the retained bins:
`jointRoundSq a b = ∑_k t_k² 1_{B_k × B_k}(a, b)`. -/
theorem jointRoundSq_eq_sum_retained (hr : 1 < r) (hL : 0 < L) (a b : ℝ) :
    jointRoundSq r θ L H a b =
      ∑ k : Fin (binCount r θ L H), retainedVal r θ L H k ^ 2 *
        (retainedBin r θ L H k ×ˢ retainedBin r θ L H k).indicator 1 (a, b) := by
  classical
  by_cases hab : binIdx r θ a = binIdx r θ b ∧ a ∈ Icc L H ∧ b ∈ Icc L H
  · obtain ⟨hidx, ha, hb⟩ := hab
    have hspec := retainedIdx_spec (θ := θ) hr hL ha
    set k₀ := retainedIdx (θ := θ) hr hL ha with hk₀
    rw [Finset.sum_eq_single k₀]
    · have hmem : (a, b) ∈ retainedBin r θ L H k₀ ×ˢ retainedBin r θ L H k₀ := by
        simp only [retainedBin, mem_prod, mem_inter_iff, mem_preimage, mem_singleton_iff]
        exact ⟨⟨hspec.symm, ha⟩, ⟨by rw [← hidx]; exact hspec.symm, hb⟩⟩
      rw [indicator_of_mem hmem, Pi.one_apply, mul_one, jointRoundSq, if_pos ⟨hidx, ha, hb⟩,
        retainedVal, hspec, roundVal]
    · intro k _ hk
      have hnot : (a, b) ∉ retainedBin r θ L H k ×ˢ retainedBin r θ L H k := by
        intro hmem
        apply hk
        simp only [retainedBin, mem_prod, mem_inter_iff, mem_preimage, mem_singleton_iff] at hmem
        have : ((k : ℕ) : ℤ) = ((k₀ : ℕ) : ℤ) := by linarith [hmem.1.1, hspec]
        exact Fin.ext (by exact_mod_cast this)
      rw [indicator_of_notMem hnot, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [jointRoundSq, if_neg hab]
    symm
    apply Finset.sum_eq_zero
    intro k _
    have hnot : (a, b) ∉ retainedBin r θ L H k ×ˢ retainedBin r θ L H k := by
      intro hmem
      apply hab
      simp only [retainedBin, mem_prod, mem_inter_iff, mem_preimage, mem_singleton_iff] at hmem
      exact ⟨by rw [hmem.1.1, hmem.2.1], hmem.1.2, hmem.2.2⟩
    rw [indicator_of_notMem hnot, mul_zero]

/-- The retained bins form a band family. -/
theorem isBandFamily_retained (hr : 1 < r) (hL : 0 < L) :
    IsBandFamily (retainedBin r θ L H) (retainedVal r θ L H) where
  meas k := (measurableSet_binIdx_fiber r θ _).inter measurableSet_Icc
  disj := by
    intro i j hij
    show Disjoint (retainedBin r θ L H i) (retainedBin r θ L H j)
    rw [Set.disjoint_left]
    intro a hai haj
    simp only [retainedBin, mem_inter_iff, mem_preimage, mem_singleton_iff] at hai haj
    apply hij
    have : ((i : ℕ) : ℤ) = ((j : ℕ) : ℤ) := by linarith [hai.1, haj.1]
    exact Fin.ext (by exact_mod_cast this)
  pos k := by
    intro a ha
    simp only [retainedBin, mem_inter_iff, mem_preimage, mem_singleton_iff] at ha
    exact lt_of_lt_of_le hL ha.2.1
  tpos k := Real.rpow_pos_of_pos (lt_trans one_pos hr) _

/-- Each retained bin sits inside `[t_k / r, t_k]` (the shifted-bin geometry,
as consumed by `selSharp_round`). -/
theorem retainedBin_subset (hr : 1 < r) (hL : 0 < L) (k : Fin (binCount r θ L H)) :
    retainedBin r θ L H k ⊆ Icc (retainedVal r θ L H k / r) (retainedVal r θ L H k) := by
  intro a ha
  simp only [retainedBin, mem_inter_iff, mem_preimage, mem_singleton_iff] at ha
  have hapos : 0 < a := lt_of_lt_of_le hL ha.2.1
  have h := (binIdx_eq_iff hr hapos (j := binLo r θ L + ((k : ℕ) : ℤ))).mp ha.1
  have hrpos : 0 < r := lt_trans one_pos hr
  constructor
  · rw [div_le_iff₀ hrpos]
    calc retainedVal r θ L H k
        = r ^ ((((binLo r θ L + ((k : ℕ) : ℤ) : ℤ) : ℝ) + θ) + 1) := by
          rw [retainedVal]; ring_nf
      _ = r ^ (((binLo r θ L + ((k : ℕ) : ℤ) : ℤ) : ℝ) + θ) * r := by
          rw [Real.rpow_add hrpos, Real.rpow_one]
      _ ≤ a * r := mul_le_mul_of_nonneg_right h.1 (le_of_lt hrpos)
  · exact le_of_lt h.2

/-- The retained bins cover exactly the window `[L, H]`. -/
theorem iUnion_retainedBin (hr : 1 < r) (hL : 0 < L) :
    (⋃ k, retainedBin r θ L H k) = Icc L H := by
  ext a
  constructor
  · intro ha
    obtain ⟨k, hk⟩ := mem_iUnion.mp ha
    exact hk.2
  · intro ha
    refine mem_iUnion.mpr ⟨retainedIdx (θ := θ) hr hL ha, ?_⟩
    simp only [retainedBin, mem_inter_iff, mem_preimage, mem_singleton_iff]
    exact ⟨(retainedIdx_spec (θ := θ) hr hL ha).symm, ha⟩

/-- A nondegenerate window retains at least one bin. -/
theorem binCount_pos (hr : 1 < r) (hL : 0 < L) (hLH : L ≤ H) : 0 < binCount r θ L H := by
  unfold binCount
  have h := binIdx_mono (θ := θ) hr hL hLH
  have h' : (0 : ℤ) < binHi r θ H - binLo r θ L + 1 := by
    unfold binHi binLo; linarith
  exact Int.lt_toNat.mpr (by simpa using h')

end RetainedBins

/-! ### The grid functionals as band sums -/

section GridBridge

variable {r θ L H : ℝ}

theorem gridA_eq_sum_retained (hr : 1 < r) (hL : 0 < L) (ν : Measure (ℝ × ℝ))
    [IsProbabilityMeasure ν] :
    gridA ν r θ L H = ∑ k : Fin (binCount r θ L H),
      retainedVal r θ L H k ^ 2 * ((ν.map Prod.fst) (retainedBin r θ L H k)).toReal := by
  classical
  have hmeas := (isBandFamily_retained (θ := θ) (H := H) hr hL).meas
  have hpt : ∀ p : ℝ × ℝ, roundSq r θ L H p.1 = ∑ k : Fin (binCount r θ L H),
      retainedVal r θ L H k ^ 2 * (Prod.fst ⁻¹' retainedBin r θ L H k).indicator 1 p := by
    intro p
    rw [roundSq_eq_sum_retained hr hL]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
  unfold gridA
  simp_rw [hpt]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul, integral_indicator_one (measurable_fst (hmeas k)), measureReal_def,
      Measure.map_apply measurable_fst (hmeas k)]
  · intro k _
    exact ((integrable_const (1 : ℝ)).indicator (measurable_fst (hmeas k))).const_mul _

theorem gridB_eq_sum_retained (hr : 1 < r) (hL : 0 < L) (ν : Measure (ℝ × ℝ))
    [IsProbabilityMeasure ν] :
    gridB ν r θ L H = ∑ k : Fin (binCount r θ L H),
      retainedVal r θ L H k ^ 2 * ((ν.map Prod.snd) (retainedBin r θ L H k)).toReal := by
  classical
  have hmeas := (isBandFamily_retained (θ := θ) (H := H) hr hL).meas
  have hpt : ∀ p : ℝ × ℝ, roundSq r θ L H p.2 = ∑ k : Fin (binCount r θ L H),
      retainedVal r θ L H k ^ 2 * (Prod.snd ⁻¹' retainedBin r θ L H k).indicator 1 p := by
    intro p
    rw [roundSq_eq_sum_retained hr hL]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
  unfold gridB
  simp_rw [hpt]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul, integral_indicator_one (measurable_snd (hmeas k)), measureReal_def,
      Measure.map_apply measurable_snd (hmeas k)]
  · intro k _
    exact ((integrable_const (1 : ℝ)).indicator (measurable_snd (hmeas k))).const_mul _

theorem gridC_eq_sum_retained (hr : 1 < r) (hL : 0 < L) (ν : Measure (ℝ × ℝ))
    [IsProbabilityMeasure ν] :
    gridC ν r θ L H = ∑ k : Fin (binCount r θ L H),
      retainedVal r θ L H k ^ 2 *
        (ν (retainedBin r θ L H k ×ˢ retainedBin r θ L H k)).toReal := by
  classical
  have hmeas := (isBandFamily_retained (θ := θ) (H := H) hr hL).meas
  have hpt : ∀ p : ℝ × ℝ, jointRoundSq r θ L H p.1 p.2 = ∑ k : Fin (binCount r θ L H),
      retainedVal r θ L H k ^ 2 *
        (retainedBin r θ L H k ×ˢ retainedBin r θ L H k).indicator 1 p := by
    intro p
    rw [jointRoundSq_eq_sum_retained hr hL]
  unfold gridC
  simp_rw [hpt]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul, integral_indicator_one ((hmeas k).prod (hmeas k)), measureReal_def]
  · intro k _
    exact ((integrable_const (1 : ℝ)).indicator ((hmeas k).prod (hmeas k))).const_mul _

end GridBridge

/-! ### Band-mass inequalities (eq c-min and `a + b − c ≤ Z`) -/

/-- Per bin: `μ_A(B) + μ_B(B) − ν(B×B) = ν((B×ℝ) ∪ (ℝ×B)) ≤ 1`. -/
theorem marg_add_marg_sub_prod_le_one (ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν]
    {B : Set ℝ} (hB : MeasurableSet B) :
    ((ν.map Prod.fst) B).toReal + ((ν.map Prod.snd) B).toReal - (ν (B ×ˢ B)).toReal ≤ 1 := by
  rw [Measure.map_apply measurable_fst hB, Measure.map_apply measurable_snd hB]
  have hinter : Prod.fst ⁻¹' B ∩ Prod.snd ⁻¹' B = B ×ˢ B := by
    ext p; simp [mem_prod]
  have hunion := measure_union_add_inter (μ := ν) (Prod.fst ⁻¹' B) (measurable_snd hB)
  rw [hinter] at hunion
  have h1 : (ν (Prod.fst ⁻¹' B)).toReal + (ν (Prod.snd ⁻¹' B)).toReal
      = (ν (Prod.fst ⁻¹' B ∪ Prod.snd ⁻¹' B)).toReal + (ν (B ×ˢ B)).toReal := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      ← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), hunion]
  have h2 : (ν (Prod.fst ⁻¹' B ∪ Prod.snd ⁻¹' B)).toReal ≤ 1 := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
  linarith

section BandMass

variable {N : StdTracialAlgebra.{u}} {S : Type v} {T : Type w}
variable {x : S → N.H} {y : T → N.H} (F : ModulusFamily N x y)
variable {m : ℕ} (B : Fin m → Set ℝ) (t : Fin m → ℝ)

theorem bandCross_nonneg (s : S) (t' : T) : 0 ≤ bandCross F B t s t' :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) ENNReal.toReal_nonneg

theorem bandCross_le_bandMassA (hB : IsBandFamily B t) (s : S) (t' : T) :
    bandCross F B t s t' ≤ bandMassA F B t s := by
  have : IsProbabilityMeasure (F.dataA s).μ := (F.dataA s).μ_prob
  unfold bandCross bandMassA
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg (t j))
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  rw [← (F.joint s t').margA, Measure.map_apply measurable_fst (hB.meas j)]
  exact measure_mono fun p hp => hp.1

theorem bandCross_le_bandMassB (hB : IsBandFamily B t) (s : S) (t' : T) :
    bandCross F B t s t' ≤ bandMassB F B t t' := by
  have : IsProbabilityMeasure (F.dataB t').μ := (F.dataB t').μ_prob
  unfold bandCross bandMassB
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg (t j))
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  rw [← (F.joint s t').margB, Measure.map_apply measurable_snd (hB.meas j)]
  exact measure_mono fun p hp => hp.2

theorem bandMassA_le_bandZ (s : S) : bandMassA F B t s ≤ bandZ t := by
  unfold bandMassA bandZ
  apply Finset.sum_le_sum
  intro j _
  have hp : IsProbabilityMeasure (F.dataA s).μ := (F.dataA s).μ_prob
  have h1 : ((F.dataA s).μ (B j)).toReal ≤ 1 := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
  calc t j ^ 2 * ((F.dataA s).μ (B j)).toReal ≤ t j ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    _ = t j ^ 2 := mul_one _

theorem bandMassB_le_bandZ (t' : T) : bandMassB F B t t' ≤ bandZ t := by
  unfold bandMassB bandZ
  apply Finset.sum_le_sum
  intro j _
  have hp : IsProbabilityMeasure (F.dataB t').μ := (F.dataB t').μ_prob
  have h1 : ((F.dataB t').μ (B j)).toReal ≤ 1 := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
  calc t j ^ 2 * ((F.dataB t').μ (B j)).toReal ≤ t j ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    _ = t j ^ 2 := mul_one _

/-- `a_s + b_t − c_{st} ≤ Z` (the per-trial progress is a probability). -/
theorem bandMass_add_sub_cross_le_bandZ (hB : IsBandFamily B t) (s : S) (t' : T) :
    bandMassA F B t s + bandMassB F B t t' - bandCross F B t s t' ≤ bandZ t := by
  have : IsProbabilityMeasure (F.joint s t').ν := (F.joint s t').ν_prob
  unfold bandMassA bandMassB bandCross bandZ
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro j _
  have hper := marg_add_marg_sub_prod_le_one (F.joint s t').ν (hB.meas j)
  rw [(F.joint s t').margA, (F.joint s t').margB] at hper
  calc t j ^ 2 * ((F.dataA s).μ (B j)).toReal + t j ^ 2 * ((F.dataB t').μ (B j)).toReal
        - t j ^ 2 * ((F.joint s t').ν (B j ×ˢ B j)).toReal
      = t j ^ 2 * (((F.dataA s).μ (B j)).toReal + ((F.dataB t').μ (B j)).toReal
          - ((F.joint s t').ν (B j ×ˢ B j)).toReal) := by ring
    _ ≤ t j ^ 2 * 1 := mul_le_mul_of_nonneg_left hper (sq_nonneg _)
    _ = t j ^ 2 := mul_one _

end BandMass

/-- `Z = ∑ t_j² > 0` for a nonempty band family with positive values. -/
theorem bandZ_pos_of_pos {m : ℕ} (hm : 0 < m) {t : Fin m → ℝ} (ht : ∀ j, 0 < t j) :
    0 < bandZ t := by
  unfold bandZ
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  exact Finset.sum_pos (fun j _ => pow_pos (ht j) 2) Finset.univ_nonempty

/-! ### Second-moment facts for the spectral distributions -/

theorem integrable_sq_of_integral_eq_one {μ : Measure ℝ}
    (h : (∫ b, b ^ 2 ∂μ) = 1) : Integrable (fun b : ℝ => b ^ 2) μ := by
  by_contra hn
  rw [integral_undef hn] at h
  norm_num at h

/-- The retained-window second moment of a spectral distribution supported on
`[0, ∞)` with unit second moment and high tail at most `ρ` is at least
`1 − ρ − L²` (06_otqcs.tex, eq rounding-tails: the omitted region is the low
window `[0, L)` of mass at most `L²` and the high tail). -/
theorem setIntegral_sq_Icc_ge (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hnn : μ (Iio 0) = 0) (h1 : (∫ b, b ^ 2 ∂μ) = 1) {L H ρ : ℝ} (hL : 0 < L) (hLH : L < H)
    (htail : (∫ b in Ioi H, b ^ 2 ∂μ) ≤ ρ) :
    1 - ρ - L ^ 2 ≤ ∫ b in Icc L H, b ^ 2 ∂μ := by
  have hint : Integrable (fun b : ℝ => b ^ 2) μ := integrable_sq_of_integral_eq_one h1
  have hcompl : (Icc L H)ᶜ = Iio L ∪ Ioi H := by
    ext b
    simp only [mem_compl_iff, mem_Icc, mem_union, mem_Iio, mem_Ioi, not_and_or, not_le]
  have hsplit : (1 : ℝ) = (∫ b in Icc L H, b ^ 2 ∂μ) +
      ((∫ b in Iio L, b ^ 2 ∂μ) + ∫ b in Ioi H, b ^ 2 ∂μ) := by
    rw [← h1, ← integral_add_compl measurableSet_Icc hint, hcompl]
    congr 1
    rw [setIntegral_union _ measurableSet_Ioi hint.integrableOn hint.integrableOn]
    rw [Set.disjoint_left]
    intro b hb1 hb2
    simp only [mem_Iio, mem_Ioi] at hb1 hb2
    linarith
  have hlow : (∫ b in Iio L, b ^ 2 ∂μ) ≤ L ^ 2 := by
    have hae : ∀ᵐ b ∂μ, 0 ≤ b := by
      rw [ae_iff]
      have : {b : ℝ | ¬ 0 ≤ b} = Iio 0 := by ext b; simp [not_le]
      rw [this]; exact hnn
    have hb : ∀ᵐ b ∂(μ.restrict (Iio L)), b ^ 2 ≤ L ^ 2 := by
      filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem measurableSet_Iio] with b hb hbL
      exact pow_le_pow_left₀ hb (le_of_lt hbL) 2
    have hmle : (μ (Iio L)).toReal ≤ 1 := by
      have := ENNReal.toReal_mono (b := 1) (by norm_num) (prob_le_one (μ := μ) (s := Iio L))
      rwa [ENNReal.toReal_one] at this
    calc (∫ b in Iio L, b ^ 2 ∂μ) ≤ ∫ _ in Iio L, L ^ 2 ∂μ :=
          integral_mono_ae hint.integrableOn (integrable_const _).integrableOn hb
      _ = L ^ 2 * (μ (Iio L)).toReal := by
          rw [setIntegral_const, smul_eq_mul, mul_comm]
          rfl
      _ ≤ L ^ 2 := by nlinarith [sq_nonneg L]
  linarith

/-- One finite cutoff `H > L` makes every high squared tail of a finite family of
probability measures with finite second moment at most `ρ` (06_otqcs.tex, "for each
`ρ > 0` one finite `H` makes the two high-tail bounds hold for every member"). -/
theorem exists_tail_cutoff {ι : Type*} [Fintype ι] (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)]
    (hint : ∀ i, Integrable (fun b : ℝ => b ^ 2) (μ i)) {ρ : ℝ} (hρ : 0 < ρ) (L : ℝ) :
    ∃ H : ℝ, L < H ∧ ∀ i, (∫ b in Ioi H, b ^ 2 ∂(μ i)) ≤ ρ := by
  classical
  have htend : ∀ i, Tendsto (fun n : ℕ => ∫ b in Ioi (n : ℝ), b ^ 2 ∂(μ i)) atTop (𝓝 0) := by
    intro i
    have h := tendsto_setIntegral_of_antitone (μ := μ i) (f := fun b : ℝ => b ^ 2)
      (s := fun n : ℕ => Ioi (n : ℝ)) (fun n => measurableSet_Ioi)
      (fun m n hmn => Ioi_subset_Ioi (by exact_mod_cast hmn)) ⟨0, (hint i).integrableOn⟩
    have hempty : (⋂ n : ℕ, Ioi (n : ℝ)) = ∅ := by
      ext b
      simp only [mem_iInter, mem_Ioi, mem_empty_iff_false, iff_false, not_forall, not_lt]
      obtain ⟨n, hn⟩ := exists_nat_ge b
      exact ⟨n, hn⟩
    rwa [hempty, Measure.restrict_empty, integral_zero_measure] at h
  have hev : ∀ᶠ n : ℕ in atTop, ∀ i, (∫ b in Ioi (n : ℝ), b ^ 2 ∂(μ i)) ≤ ρ := by
    rw [Filter.eventually_all]
    intro i
    exact ((htend i).eventually (gt_mem_nhds hρ)).mono fun n hn => le_of_lt hn
  have hev2 : ∀ᶠ n : ℕ in atTop, L < (n : ℝ) := by
    obtain ⟨M, hM⟩ := exists_nat_gt L
    exact Filter.eventually_atTop.mpr ⟨M, fun n hn => lt_of_lt_of_le hM (by exact_mod_cast hn)⟩
  obtain ⟨n, hn1, hn2⟩ := (hev2.and hev).exists
  exact ⟨n, hn1, hn2⟩

end CommutingRepetition

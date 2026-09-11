/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/OTQCS/Grid.lean
-/
/-
# OTQCS: shifted logarithmic grid (nodes 1.3.3, 1.3.4)

Scalar/measure half of Section 6: the shifted-bin disagreement lemma
and the common-shift selection. Anchors: 06_otqcs.tex, eqs
shifted-bins, abcGamma, c-min, ab-mass, grid-disagreement,
separation-probability, common-shift.

Encoding (consumed form): everything is phrased over an abstract
coupling `ν` — a probability measure on `ℝ × ℝ` with almost surely
nonnegative coordinates — with the joint spectral measure's moment
identities (eq joint-moments) taken as hypotheses. At consumption
(node 1.3.5) `ν` is the joint left–right spectral measure `ν_{h,k}` of
eq joint-measure, whose `JointSpectralData` fields provide exactly
these hypotheses, and the grid functionals below match the manuscript's
`a_θ, b_θ, c_θ` by countable disjoint-bin regrouping (the finite
retained-bin operator forms are bridged there, not here).
-/
import Mathlib

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

open MeasureTheory
open scoped BigOperators

/-- Bin index of `a` on the shifted logarithmic grid with ratio `r` and
shift `θ`: for `1 < r` and `0 < a`, `binIdx r θ a = j` exactly when
`a ∈ I_j^θ = [r^(j+θ), r^(j+1+θ))`. Junk value at `a ≤ 0` (the log is
junk there), harmless: every consumer guards by the retained window
`[L, H]` with `0 < L`. [06_otqcs.tex, eq shifted-bins] -/
noncomputable def binIdx (r θ a : ℝ) : ℤ :=
  ⌊Real.log a / Real.log r - θ⌋

/-- The upper endpoint `t_j^θ = r^(j+1+θ)` of the shifted bin containing
`a` — the upward-rounded value of `a` (real exponent, `Real.rpow`).
[06_otqcs.tex, eq shifted-bins] -/
noncomputable def roundVal (r θ a : ℝ) : ℝ :=
  r ^ ((binIdx r θ a : ℝ) + 1 + θ)

open Classical in
/-- Retained rounded square: the integrand realizing `a_θ(h)` (and
`b_θ(k)`) against the spectral distribution — `(t_j^θ)²` on the bin of
`a` when `a` lies in the retained window `[L, H]`, zero otherwise, so
that `∑_j (t_j^θ)² τ(1_{I_j^θ ∩ [L,H]}(h)) = ∫ roundSq r θ L H a dμ(a)`.
[06_otqcs.tex, eq abcGamma, first two lines] -/
noncomputable def roundSq (r θ L H a : ℝ) : ℝ :=
  if a ∈ Set.Icc L H then roundVal r θ a ^ 2 else 0

open Classical in
/-- Same-bin retained joint rounded square: the integrand realizing
`c_θ(h,k)` against the joint spectral measure — `(t_j^θ)²` when both
coordinates land in the same shifted bin and both are retained, zero
otherwise. [06_otqcs.tex, eq abcGamma, third line] -/
noncomputable def jointRoundSq (r θ L H a b : ℝ) : ℝ :=
  if binIdx r θ a = binIdx r θ b ∧ a ∈ Set.Icc L H ∧ b ∈ Set.Icc L H
  then roundVal r θ a ^ 2 else 0

/-- `a_θ` of eq abcGamma, read through the coupling: the retained
rounded squared mass of the first coordinate. -/
noncomputable def gridA (ν : Measure (ℝ × ℝ)) (r θ L H : ℝ) : ℝ :=
  ∫ p, roundSq r θ L H p.1 ∂ν

/-- `b_θ` of eq abcGamma: the retained rounded squared mass of the
second coordinate. -/
noncomputable def gridB (ν : Measure (ℝ × ℝ)) (r θ L H : ℝ) : ℝ :=
  ∫ p, roundSq r θ L H p.2 ∂ν

/-- `c_θ` of eq abcGamma: the same-bin retained joint rounded mass. -/
noncomputable def gridC (ν : Measure (ℝ × ℝ)) (r θ L H : ℝ) : ℝ :=
  ∫ p, jointRoundSq r θ L H p.1 p.2 ∂ν

/-- `Γ_θ = a_θ + b_θ − 2 c_θ` of eq abcGamma: the grid disagreement
functional. -/
noncomputable def gridGamma (ν : Measure (ℝ × ℝ)) (r θ L H : ℝ) : ℝ :=
  gridA ν r θ L H + gridB ν r θ L H - 2 * gridC ν r θ L H


/-! ### Bin geometry (proof layer) -/

section BinGeometry

variable {r θ a : ℝ}

/-- Characterization of the bin index for positive arguments. -/
theorem binIdx_eq_iff (hr : 1 < r) (ha : 0 < a) {j : ℤ} :
    binIdx r θ a = j ↔
      r ^ ((j : ℝ) + θ) ≤ a ∧ a < r ^ ((j : ℝ) + 1 + θ) := by
  have hlr : 0 < Real.log r := Real.log_pos hr
  have hrpos : 0 < r := lt_trans one_pos hr
  rw [binIdx, Int.floor_eq_iff]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · rw [Real.rpow_def_of_pos hrpos, ← Real.exp_log ha]
      apply Real.exp_le_exp.mpr
      have := (le_div_iff₀ hlr).mp (by linarith [h1] : (j : ℝ) + θ ≤ Real.log a / Real.log r)
      linarith [this]
    · rw [Real.rpow_def_of_pos hrpos, ← Real.exp_log ha]
      apply Real.exp_lt_exp.mpr
      have := (div_lt_iff₀ hlr).mp (by linarith [h2] : Real.log a / Real.log r < (j : ℝ) + 1 + θ)
      linarith [this]
  · rintro ⟨h1, h2⟩
    have hl1 : ((j : ℝ) + θ) * Real.log r ≤ Real.log a := by
      have := Real.log_le_log (Real.rpow_pos_of_pos hrpos _) h1
      rwa [Real.log_rpow hrpos] at this
    have hl2 : Real.log a < ((j : ℝ) + 1 + θ) * Real.log r := by
      have := Real.log_lt_log ha h2
      rwa [Real.log_rpow hrpos] at this
    constructor
    · have h := (le_div_iff₀ hlr).mpr hl1
      linarith
    · have h := (div_lt_iff₀ hlr).mpr hl2
      linarith

theorem le_roundVal (hr : 1 < r) (ha : 0 < a) : a ≤ roundVal r θ a := by
  have h := (binIdx_eq_iff hr ha (j := binIdx r θ a)).mp rfl
  exact le_of_lt h.2

theorem roundVal_le (hr : 1 < r) (ha : 0 < a) : roundVal r θ a ≤ r * a := by
  have hrpos : 0 < r := lt_trans one_pos hr
  have h := (binIdx_eq_iff hr ha (j := binIdx r θ a)).mp rfl
  calc roundVal r θ a = r ^ (((binIdx r θ a : ℝ) + θ) + 1) := by
        rw [roundVal]; ring_nf
    _ = r ^ ((binIdx r θ a : ℝ) + θ) * r := by
        rw [Real.rpow_add hrpos, Real.rpow_one]
    _ ≤ a * r := by
        exact mul_le_mul_of_nonneg_right h.1 (le_of_lt hrpos)
    _ = r * a := mul_comm _ _

theorem roundVal_pos (hr : 1 < r) : 0 < roundVal r θ a :=
  Real.rpow_pos_of_pos (lt_trans one_pos hr) _

theorem roundSq_nonneg {L H : ℝ} : 0 ≤ roundSq r θ L H a := by
  rw [roundSq]
  split
  · exact sq_nonneg _
  · exact le_refl 0

theorem jointRoundSq_nonneg {L H b : ℝ} :
    0 ≤ jointRoundSq r θ L H a b := by
  rw [jointRoundSq]
  split
  · exact sq_nonneg _
  · exact le_refl 0

/-- On the retained window, the rounded square is between `a²` and
`r² a²`. -/
theorem roundSq_bounds (hr : 1 < r) {L H : ℝ} (hL : 0 < L)
    (hmem : a ∈ Set.Icc L H) :
    a ^ 2 ≤ roundSq r θ L H a ∧ roundSq r θ L H a ≤ r ^ 2 * a ^ 2 := by
  have ha : 0 < a := lt_of_lt_of_le hL hmem.1
  rw [roundSq, if_pos hmem]
  constructor
  · exact pow_le_pow_left₀ (le_of_lt ha) (le_roundVal hr ha) 2
  · calc roundVal r θ a ^ 2 ≤ (r * a) ^ 2 :=
        pow_le_pow_left₀ (le_of_lt (roundVal_pos hr)) (roundVal_le hr ha) 2
      _ = r ^ 2 * a ^ 2 := by ring

theorem roundSq_of_notMem {L H : ℝ}
    (hmem : a ∉ Set.Icc L H) : roundSq r θ L H a = 0 := by
  rw [roundSq, if_neg hmem]

/-- The joint rounded square is dominated by each slot's rounded
square (`roundVal` factors through `binIdx`). -/
theorem jointRoundSq_le_left {L H b : ℝ} :
    jointRoundSq r θ L H a b ≤ roundSq r θ L H a := by
  rw [jointRoundSq]
  split
  · next h => rw [roundSq, if_pos h.2.1]
  · next h => exact roundSq_nonneg

theorem jointRoundSq_le_right {L H b : ℝ} :
    jointRoundSq r θ L H a b ≤ roundSq r θ L H b := by
  rw [jointRoundSq]
  split
  · next h =>
    rw [roundSq, if_pos h.2.2]
    have hval : roundVal r θ a = roundVal r θ b := by
      rw [roundVal, roundVal, h.1]
    rw [hval]
  · next h => exact roundSq_nonneg

end BinGeometry


/-! ### Measurability (proof layer) -/

section GridMeasurability

variable {r θ L H : ℝ}

theorem measurableSet_binIdx_fiber (r θ : ℝ) (j : ℤ) :
    MeasurableSet (binIdx r θ ⁻¹' {j}) := by
  have hset : binIdx r θ ⁻¹' {j} =
      {a : ℝ | (j : ℝ) ≤ Real.log a / Real.log r - θ} ∩
        {a : ℝ | Real.log a / Real.log r - θ < (j : ℝ) + 1} := by
    ext a
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff,
      Set.mem_setOf_eq, binIdx]
    rw [Int.floor_eq_iff]
  rw [hset]
  exact (measurableSet_le measurable_const
      ((Real.measurable_log.div_const _).sub_const _)).inter
    (measurableSet_lt
      ((Real.measurable_log.div_const _).sub_const _) measurable_const)

theorem measurable_binIdx (r θ : ℝ) : Measurable (binIdx r θ) :=
  measurable_to_countable fun a =>
    measurableSet_binIdx_fiber r θ (binIdx r θ a)

/-- Any function out of the (discrete) bin index is measurable, so any
real function factoring through it is. -/
theorem measurable_comp_binIdx (r θ : ℝ) (g : ℤ → ℝ) :
    Measurable fun a => g (binIdx r θ a) :=
  (measurable_from_top (f := g)).comp (measurable_binIdx r θ)

theorem measurable_roundVal (r θ : ℝ) : Measurable (roundVal r θ) :=
  measurable_comp_binIdx r θ (fun j => r ^ ((j : ℝ) + 1 + θ))

theorem roundSq_eq_mul_indicator (a : ℝ) :
    roundSq r θ L H a =
      roundVal r θ a ^ 2 * Set.indicator (Set.Icc L H) 1 a := by
  rw [roundSq, Set.indicator_apply]
  by_cases h : a ∈ Set.Icc L H
  · rw [if_pos h, if_pos h, Pi.one_apply, mul_one]
  · rw [if_neg h, if_neg h, mul_zero]

theorem measurable_roundSq (r θ L H : ℝ) :
    Measurable (roundSq r θ L H) := by
  have h : roundSq r θ L H = fun a =>
      roundVal r θ a ^ 2 * Set.indicator (Set.Icc L H) 1 a := by
    funext a
    exact roundSq_eq_mul_indicator a
  rw [h]
  exact ((measurable_roundVal r θ).pow_const 2).mul
    (measurable_one.indicator measurableSet_Icc)

theorem measurableSet_sameBin (r θ : ℝ) :
    MeasurableSet {p : ℝ × ℝ | binIdx r θ p.1 = binIdx r θ p.2} := by
  have hset : {p : ℝ × ℝ | binIdx r θ p.1 = binIdx r θ p.2} =
      ⋃ j : ℤ, (binIdx r θ ⁻¹' {j}) ×ˢ (binIdx r θ ⁻¹' {j}) := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_prod,
      Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h; exact ⟨binIdx r θ p.2, h, rfl⟩
    · rintro ⟨j, h1, h2⟩; rw [h1, h2]
  rw [hset]
  exact MeasurableSet.iUnion fun j =>
    (measurableSet_binIdx_fiber r θ j).prod
      (measurableSet_binIdx_fiber r θ j)

theorem jointRoundSq_eq_mul_indicator (p : ℝ × ℝ) :
    jointRoundSq r θ L H p.1 p.2 =
      roundSq r θ L H p.1 *
        Set.indicator {q : ℝ × ℝ | binIdx r θ q.1 = binIdx r θ q.2}
          1 p * Set.indicator (Set.Icc L H) 1 p.2 := by
  rw [jointRoundSq, roundSq, Set.indicator_apply, Set.indicator_apply]
  by_cases h1 : binIdx r θ p.1 = binIdx r θ p.2
  · by_cases h2 : p.1 ∈ Set.Icc L H
    · by_cases h3 : p.2 ∈ Set.Icc L H
      · rw [if_pos ⟨h1, h2, h3⟩, if_pos h2,
          if_pos (show p ∈ {q : ℝ × ℝ |
            binIdx r θ q.1 = binIdx r θ q.2} from h1),
          if_pos h3, Pi.one_apply, Pi.one_apply, mul_one, mul_one]
      · rw [if_neg (by tauto), if_neg h3, mul_zero]
    · rw [if_neg (by tauto), if_neg h2, zero_mul, zero_mul]
  · rw [if_neg (by tauto),
      if_neg (show p ∉ {q : ℝ × ℝ |
        binIdx r θ q.1 = binIdx r θ q.2} from h1),
      mul_zero, zero_mul]

theorem measurable_jointRoundSq (r θ L H : ℝ) :
    Measurable fun p : ℝ × ℝ => jointRoundSq r θ L H p.1 p.2 := by
  have h : (fun p : ℝ × ℝ => jointRoundSq r θ L H p.1 p.2) = fun p =>
      roundSq r θ L H p.1 *
        Set.indicator {q : ℝ × ℝ | binIdx r θ q.1 = binIdx r θ q.2}
          1 p * Set.indicator (Set.Icc L H) 1 p.2 := by
    funext p
    exact jointRoundSq_eq_mul_indicator p
  rw [h]
  exact ((((measurable_roundSq r θ L H).comp measurable_fst).mul
    (measurable_one.indicator (measurableSet_sameBin r θ)))).mul
    ((measurable_one.indicator measurableSet_Icc).comp measurable_snd)

end GridMeasurability


/-! ### Integrability and the fixed-shift mass bounds (proof layer) -/

section GridMass

variable {ν : Measure (ℝ × ℝ)} [IsProbabilityMeasure ν]
variable {r θ L H ρ : ℝ}

theorem roundSq_le_sq (hr : 1 < r) (hL : 0 < L) (a : ℝ) :
    roundSq r θ L H a ≤ r ^ 2 * a ^ 2 := by
  by_cases h : a ∈ Set.Icc L H
  · exact (roundSq_bounds hr hL h).2
  · rw [roundSq_of_notMem h]
    positivity

theorem integrable_of_integral_eq_one {f : ℝ × ℝ → ℝ}
    (h : (∫ p, f p ∂ν) = 1) : Integrable f ν := by
  by_contra hn
  rw [integral_undef hn] at h
  norm_num at h

theorem integrable_roundSq_fst (hr : 1 < r) (hL : 0 < L)
    (h1 : Integrable (fun p : ℝ × ℝ => p.1 ^ 2) ν) :
    Integrable (fun p : ℝ × ℝ => roundSq r θ L H p.1) ν := by
  apply Integrable.mono' (h1.const_mul (r ^ 2))
  · exact ((measurable_roundSq r θ L H).comp
      measurable_fst).aestronglyMeasurable
  · filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg roundSq_nonneg]
    exact roundSq_le_sq hr hL p.1

theorem integrable_roundSq_snd (hr : 1 < r) (hL : 0 < L)
    (h2 : Integrable (fun p : ℝ × ℝ => p.2 ^ 2) ν) :
    Integrable (fun p : ℝ × ℝ => roundSq r θ L H p.2) ν := by
  apply Integrable.mono' (h2.const_mul (r ^ 2))
  · exact ((measurable_roundSq r θ L H).comp
      measurable_snd).aestronglyMeasurable
  · filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg roundSq_nonneg]
    exact roundSq_le_sq hr hL p.2

theorem integrable_jointRoundSq (hr : 1 < r) (hL : 0 < L)
    (h1 : Integrable (fun p : ℝ × ℝ => p.1 ^ 2) ν) :
    Integrable (fun p : ℝ × ℝ => jointRoundSq r θ L H p.1 p.2) ν := by
  apply Integrable.mono' (integrable_roundSq_fst hr hL h1)
  · exact (measurable_jointRoundSq r θ L H).aestronglyMeasurable
  · filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg jointRoundSq_nonneg]
    exact jointRoundSq_le_left

/-- Upper half of eq ab-mass for the first coordinate. -/
theorem gridA_le (hr : 1 < r) (hL : 0 < L)
    (h1 : (∫ p : ℝ × ℝ, p.1 ^ 2 ∂ν) = 1) :
    gridA ν r θ L H ≤ r ^ 2 := by
  have hint := integrable_of_integral_eq_one h1
  calc gridA ν r θ L H ≤ ∫ p : ℝ × ℝ, r ^ 2 * p.1 ^ 2 ∂ν := by
        apply integral_mono (integrable_roundSq_fst hr hL hint)
          (hint.const_mul _)
        intro p
        exact roundSq_le_sq hr hL p.1
    _ = r ^ 2 := by rw [integral_const_mul, h1, mul_one]

/-- Lower half of eq ab-mass for the first coordinate. -/
theorem gridA_ge (hr : 1 < r) (hL : 0 < L) (hLH : L < H)
    (hnn : ∀ᵐ p ∂ν, 0 ≤ p.1 ∧ 0 ≤ p.2)
    (h1 : (∫ p : ℝ × ℝ, p.1 ^ 2 ∂ν) = 1)
    (htail : (∫ p in {q : ℝ × ℝ | H < q.1}, p.1 ^ 2 ∂ν) ≤ ρ) :
    1 - ρ - L ^ 2 ≤ gridA ν r θ L H := by
  have hint := integrable_of_integral_eq_one h1
  set S : Set (ℝ × ℝ) := {q : ℝ × ℝ | q.1 ∈ Set.Icc L H} with hS
  have hSmeas : MeasurableSet S := measurable_fst measurableSet_Icc
  have hlow : MeasurableSet {q : ℝ × ℝ | q.1 < L} :=
    measurableSet_lt measurable_fst measurable_const
  have hhigh : MeasurableSet {q : ℝ × ℝ | H < q.1} :=
    measurableSet_lt measurable_const measurable_fst
  -- the retained window mass is below gridA
  have hstep1 : (∫ p in S, p.1 ^ 2 ∂ν) ≤ gridA ν r θ L H := by
    rw [← integral_indicator hSmeas]
    apply integral_mono (hint.indicator hSmeas)
      (integrable_roundSq_fst hr hL hint)
    intro p
    rw [Set.indicator_apply]
    by_cases h : p ∈ S
    · rw [if_pos h]
      exact (roundSq_bounds hr hL h).1
    · rw [if_neg h]
      exact roundSq_nonneg
  -- split the total mass
  have hcompl : Sᶜ = {q : ℝ × ℝ | q.1 < L} ∪ {q : ℝ × ℝ | H < q.1} := by
    ext q
    simp only [hS, Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_Icc,
      Set.mem_union, not_and_or, not_le]
  have hsplit : (1 : ℝ) = (∫ p in S, p.1 ^ 2 ∂ν) +
      ((∫ p in {q : ℝ × ℝ | q.1 < L}, p.1 ^ 2 ∂ν) +
        (∫ p in {q : ℝ × ℝ | H < q.1}, p.1 ^ 2 ∂ν)) := by
    rw [← h1, ← integral_add_compl hSmeas hint, hcompl]
    congr 1
    rw [setIntegral_union _ hhigh hint.integrableOn hint.integrableOn]
    · rw [Set.disjoint_left]
      intro q hq1 hq2
      simp only [Set.mem_setOf_eq] at hq1 hq2
      linarith
  -- low-window mass at most L²
  have hlowmass : (∫ p in {q : ℝ × ℝ | q.1 < L}, p.1 ^ 2 ∂ν) ≤
      L ^ 2 := by
    have hb : ∀ᵐ p ∂(ν.restrict {q : ℝ × ℝ | q.1 < L}),
        p.1 ^ 2 ≤ L ^ 2 := by
      filter_upwards [ae_restrict_of_ae hnn, ae_restrict_mem hlow]
        with p hp hpT
      exact pow_le_pow_left₀ hp.1 (le_of_lt hpT) 2
    have hmle : (ν {q : ℝ × ℝ | q.1 < L}).toReal ≤ 1 := by
      have h1t : ν {q : ℝ × ℝ | q.1 < L} ≤ 1 := prob_le_one
      have := ENNReal.toReal_mono (b := 1) (by norm_num) h1t
      rwa [ENNReal.toReal_one] at this
    calc (∫ p in {q : ℝ × ℝ | q.1 < L}, p.1 ^ 2 ∂ν) ≤
          ∫ _ in {q : ℝ × ℝ | q.1 < L}, L ^ 2 ∂ν :=
        integral_mono_ae hint.integrableOn
          ((integrable_const (L ^ 2)).integrableOn) hb
      _ = L ^ 2 * (ν {q : ℝ × ℝ | q.1 < L}).toReal := by
          rw [setIntegral_const, smul_eq_mul, mul_comm]
          rfl
      _ ≤ L ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hmle (sq_nonneg L)
      _ = L ^ 2 := mul_one _
  linarith [hstep1, htail, hlowmass, hsplit.symm.le, hsplit.le]

/-- Upper half of eq ab-mass for the second coordinate. -/
theorem gridB_le (hr : 1 < r) (hL : 0 < L)
    (h2 : (∫ p : ℝ × ℝ, p.2 ^ 2 ∂ν) = 1) :
    gridB ν r θ L H ≤ r ^ 2 := by
  have hint := integrable_of_integral_eq_one h2
  calc gridB ν r θ L H ≤ ∫ p : ℝ × ℝ, r ^ 2 * p.2 ^ 2 ∂ν := by
        apply integral_mono (integrable_roundSq_snd hr hL hint)
          (hint.const_mul _)
        intro p
        exact roundSq_le_sq hr hL p.2
    _ = r ^ 2 := by rw [integral_const_mul, h2, mul_one]

/-- Lower half of eq ab-mass for the second coordinate. -/
theorem gridB_ge (hr : 1 < r) (hL : 0 < L) (hLH : L < H)
    (hnn : ∀ᵐ p ∂ν, 0 ≤ p.1 ∧ 0 ≤ p.2)
    (h2 : (∫ p : ℝ × ℝ, p.2 ^ 2 ∂ν) = 1)
    (htail : (∫ p in {q : ℝ × ℝ | H < q.2}, p.2 ^ 2 ∂ν) ≤ ρ) :
    1 - ρ - L ^ 2 ≤ gridB ν r θ L H := by
  have hint := integrable_of_integral_eq_one h2
  set S : Set (ℝ × ℝ) := {q : ℝ × ℝ | q.2 ∈ Set.Icc L H} with hS
  have hSmeas : MeasurableSet S := measurable_snd measurableSet_Icc
  have hlow : MeasurableSet {q : ℝ × ℝ | q.2 < L} :=
    measurableSet_lt measurable_snd measurable_const
  have hhigh : MeasurableSet {q : ℝ × ℝ | H < q.2} :=
    measurableSet_lt measurable_const measurable_snd
  have hstep1 : (∫ p in S, p.2 ^ 2 ∂ν) ≤ gridB ν r θ L H := by
    rw [← integral_indicator hSmeas]
    apply integral_mono (hint.indicator hSmeas)
      (integrable_roundSq_snd hr hL hint)
    intro p
    rw [Set.indicator_apply]
    by_cases h : p ∈ S
    · rw [if_pos h]
      exact (roundSq_bounds hr hL h).1
    · rw [if_neg h]
      exact roundSq_nonneg
  have hcompl : Sᶜ = {q : ℝ × ℝ | q.2 < L} ∪ {q : ℝ × ℝ | H < q.2} := by
    ext q
    simp only [hS, Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_Icc,
      Set.mem_union, not_and_or, not_le]
  have hsplit : (1 : ℝ) = (∫ p in S, p.2 ^ 2 ∂ν) +
      ((∫ p in {q : ℝ × ℝ | q.2 < L}, p.2 ^ 2 ∂ν) +
        (∫ p in {q : ℝ × ℝ | H < q.2}, p.2 ^ 2 ∂ν)) := by
    rw [← h2, ← integral_add_compl hSmeas hint, hcompl]
    congr 1
    rw [setIntegral_union _ hhigh hint.integrableOn hint.integrableOn]
    · rw [Set.disjoint_left]
      intro q hq1 hq2
      simp only [Set.mem_setOf_eq] at hq1 hq2
      linarith
  have hlowmass : (∫ p in {q : ℝ × ℝ | q.2 < L}, p.2 ^ 2 ∂ν) ≤
      L ^ 2 := by
    have hb : ∀ᵐ p ∂(ν.restrict {q : ℝ × ℝ | q.2 < L}),
        p.2 ^ 2 ≤ L ^ 2 := by
      filter_upwards [ae_restrict_of_ae hnn, ae_restrict_mem hlow]
        with p hp hpT
      exact pow_le_pow_left₀ hp.2 (le_of_lt hpT) 2
    have hmle : (ν {q : ℝ × ℝ | q.2 < L}).toReal ≤ 1 := by
      have h1t : ν {q : ℝ × ℝ | q.2 < L} ≤ 1 := prob_le_one
      have := ENNReal.toReal_mono (b := 1) (by norm_num) h1t
      rwa [ENNReal.toReal_one] at this
    calc (∫ p in {q : ℝ × ℝ | q.2 < L}, p.2 ^ 2 ∂ν) ≤
          ∫ _ in {q : ℝ × ℝ | q.2 < L}, L ^ 2 ∂ν :=
        integral_mono_ae hint.integrableOn
          ((integrable_const (L ^ 2)).integrableOn) hb
      _ = L ^ 2 * (ν {q : ℝ × ℝ | q.2 < L}).toReal := by
          rw [setIntegral_const, smul_eq_mul, mul_comm]
          rfl
      _ ≤ L ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hmle (sq_nonneg L)
      _ = L ^ 2 := mul_one _
  linarith [hstep1, htail, hlowmass, hsplit.symm.le, hsplit.le]

end GridMass


/-! ### The separation probability (proof layer; eq
separation-probability via a two-interval cover) -/

section Separation

/-- A uniformly shifted unit grid separates two reals with probability
at most twice their distance (eq separation-probability, weakened by a
factor of 2 — absorbed by the universal constant): every separating
shift lies in one of two translates of `Ioc u v`. -/
theorem volume_sep_le {u v : ℝ} (huv : u ≤ v) :
    volume {θ : ℝ | θ ∈ Set.Ico (0 : ℝ) 1 ∧ ⌊u - θ⌋ ≠ ⌊v - θ⌋} ≤
      ENNReal.ofReal (2 * (v - u)) := by
  by_cases hgap : 1 < v - u
  · calc volume {θ : ℝ | θ ∈ Set.Ico (0 : ℝ) 1 ∧ ⌊u - θ⌋ ≠ ⌊v - θ⌋} ≤
          volume (Set.Ico (0 : ℝ) 1) :=
        measure_mono fun θ hθ => hθ.1
      _ = 1 := by rw [Real.volume_Ico]; norm_num
      _ ≤ ENNReal.ofReal (2 * (v - u)) := by
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (by linarith)
  · push_neg at hgap
    have hsub : {θ : ℝ | θ ∈ Set.Ico (0 : ℝ) 1 ∧ ⌊u - θ⌋ ≠ ⌊v - θ⌋} ⊆
        Set.Ioc (u - (⌊v⌋ : ℝ)) (v - (⌊v⌋ : ℝ)) ∪
          Set.Ioc (u - ((⌊v⌋ : ℝ) - 1)) (v - ((⌊v⌋ : ℝ) - 1)) := by
      rintro θ ⟨hθ, hne⟩
      have hlt : ⌊u - θ⌋ < ⌊v - θ⌋ :=
        lt_of_le_of_ne (Int.floor_le_floor (by linarith)) hne
      set n : ℤ := ⌊v - θ⌋ with hn
      have h1 : (n : ℝ) ≤ v - θ := Int.floor_le _
      have h2 : u - θ < (n : ℝ) := by
        have hfl := Int.lt_floor_add_one (u - θ)
        have hle : (⌊u - θ⌋ : ℝ) + 1 ≤ (n : ℝ) := by
          exact_mod_cast Int.add_one_le_of_lt hlt
        linarith
      have hmemθ : θ ∈ Set.Ioc (u - (n : ℝ)) (v - (n : ℝ)) :=
        ⟨by linarith, by linarith⟩
      have hnv : n ≤ ⌊v⌋ := by
        apply Int.le_floor.mpr
        have hθ0 : (0 : ℝ) ≤ θ := hθ.1
        linarith
      have hnv' : ⌊v⌋ - 1 ≤ n := by
        have hgt : v - 2 < (n : ℝ) := by
          have hθ2 : θ < 1 := hθ.2
          linarith
        have hfv : (⌊v⌋ : ℝ) ≤ v := Int.floor_le v
        have : (⌊v⌋ : ℝ) < (n : ℝ) + 2 := by linarith
        have hz : ⌊v⌋ < n + 2 := by exact_mod_cast this
        omega
      have hcase : n = ⌊v⌋ ∨ n = ⌊v⌋ - 1 := by omega
      rcases hcase with h | h
      · left
        have hcast : ((⌊v⌋ : ℤ) : ℝ) = (n : ℝ) := by
          rw [h]
        rw [hcast]
        exact hmemθ
      · right
        have hcast : ((⌊v⌋ : ℝ) - 1) = (n : ℝ) := by
          rw [h]
          push_cast
          ring
        rw [hcast]
        exact hmemθ
    calc volume {θ : ℝ | θ ∈ Set.Ico (0 : ℝ) 1 ∧ ⌊u - θ⌋ ≠ ⌊v - θ⌋} ≤
          volume (Set.Ioc (u - (⌊v⌋ : ℝ)) (v - (⌊v⌋ : ℝ)) ∪
            Set.Ioc (u - ((⌊v⌋ : ℝ) - 1)) (v - ((⌊v⌋ : ℝ) - 1))) :=
        measure_mono hsub
      _ ≤ volume (Set.Ioc (u - (⌊v⌋ : ℝ)) (v - (⌊v⌋ : ℝ))) +
          volume (Set.Ioc (u - ((⌊v⌋ : ℝ) - 1))
            (v - ((⌊v⌋ : ℝ) - 1))) := measure_union_le _ _
      _ = ENNReal.ofReal (v - u) + ENNReal.ofReal (v - u) := by
          rw [Real.volume_Ioc, Real.volume_Ioc]
          have e1 : v - (⌊v⌋ : ℝ) - (u - (⌊v⌋ : ℝ)) = v - u := by ring
          have e2 : v - ((⌊v⌋ : ℝ) - 1) - (u - ((⌊v⌋ : ℝ) - 1)) =
              v - u := by ring
          rw [e1, e2]
      _ = ENNReal.ofReal (2 * (v - u)) := by
          rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
          congr 1
          ring

end Separation


/-! ### The pointwise θ-averaged disagreement bound (proof layer) -/

section Pointwise

variable {r α L H a b : ℝ}

/-- The disagreement integrand. -/
noncomputable def gridF (r θ L H a b : ℝ) : ℝ :=
  roundSq r θ L H a + roundSq r θ L H b - 2 * jointRoundSq r θ L H a b

theorem gridF_nonneg (θ : ℝ) : 0 ≤ gridF r θ L H a b := by
  rw [gridF, jointRoundSq]
  by_cases h : binIdx r θ a = binIdx r θ b ∧ a ∈ Set.Icc L H ∧
      b ∈ Set.Icc L H
  · rw [if_pos h, roundSq, if_pos h.2.1, roundSq, if_pos h.2.2]
    have hval : roundVal r θ a = roundVal r θ b := by
      rw [roundVal, roundVal, h.1]
    rw [hval]
    ring_nf
    exact le_refl _
  · rw [if_neg h]
    have h1 : (0:ℝ) ≤ roundSq r θ L H a := roundSq_nonneg
    have h2 : (0:ℝ) ≤ roundSq r θ L H b := roundSq_nonneg
    linarith

/-- Both coordinates off the window: the integrand vanishes. -/
theorem gridF_of_notMem_notMem (θ : ℝ) (haw : a ∉ Set.Icc L H)
    (hbw : b ∉ Set.Icc L H) : gridF r θ L H a b = 0 := by
  rw [gridF, roundSq_of_notMem haw, roundSq_of_notMem hbw, jointRoundSq,
    if_neg (by tauto)]
  ring

/-- One coordinate off the window: the integrand is the other slot's
rounded square. -/
theorem gridF_of_mem_notMem (θ : ℝ) (hbw : b ∉ Set.Icc L H) :
    gridF r θ L H a b = roundSq r θ L H a := by
  rw [gridF, roundSq_of_notMem hbw, jointRoundSq, if_neg (by tauto)]
  ring

theorem gridF_of_notMem_mem (θ : ℝ) (haw : a ∉ Set.Icc L H) :
    gridF r θ L H a b = roundSq r θ L H b := by
  rw [gridF, roundSq_of_notMem haw, jointRoundSq, if_neg (by tauto)]
  ring

/-- Both on the window: the integrand is bounded by `4(a² + b²)` and
vanishes off the separation event. -/
theorem gridF_of_mem_mem (hr1 : 1 < r) (hr2 : r ≤ 2) (hL : 0 < L)
    (θ : ℝ) (haw : a ∈ Set.Icc L H) (hbw : b ∈ Set.Icc L H) :
    gridF r θ L H a b ≤
      Set.indicator {θ' : ℝ | binIdx r θ' a ≠ binIdx r θ' b}
        (fun _ => 4 * (a ^ 2 + b ^ 2)) θ := by
  rw [Set.indicator_apply]
  by_cases hsep : binIdx r θ a = binIdx r θ b
  · rw [if_neg (by simpa using hsep)]
    have h0 : gridF r θ L H a b = 0 := by
      rw [gridF, jointRoundSq, if_pos ⟨hsep, haw, hbw⟩, roundSq,
        if_pos haw, roundSq, if_pos hbw]
      have hval : roundVal r θ a = roundVal r θ b := by
        rw [roundVal, roundVal, hsep]
      rw [hval]
      ring
    rw [h0]
  · rw [if_pos (by simpa using hsep)]
    have hja : (0:ℝ) ≤ jointRoundSq r θ L H a b := jointRoundSq_nonneg
    have hba := (roundSq_bounds (θ := θ) hr1 hL haw).2
    have hbb := (roundSq_bounds (θ := θ) hr1 hL hbw).2
    have hr4 : r ^ 2 ≤ 4 := by nlinarith
    have ha0 : 0 ≤ a ^ 2 := sq_nonneg a
    have hb0 : 0 ≤ b ^ 2 := sq_nonneg b
    rw [gridF]
    nlinarith

end Pointwise


/-! ### The scalar majorant and the θ-averaged bound (proof layer) -/

section Majorant

variable {r α L H a b : ℝ}

open Classical in
/-- The scalar majorant of the θ-averaged disagreement integrand. -/
noncomputable def gridG (α L H a b : ℝ) : ℝ :=
  32 * (a - b) ^ 2 + 48 / α * (max a b * |a - b|) +
    8 * ((if H < a then a ^ 2 else 0) + (if H < b then b ^ 2 else 0)) +
    16 * L ^ 2

theorem gridG_nonneg (hα0 : 0 < α) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ gridG α L H a b := by
  rw [gridG]
  have h1 : (0:ℝ) ≤ 32 * (a - b) ^ 2 := by positivity
  have h2 : (0:ℝ) ≤ 48 / α * (max a b * |a - b|) := by
    apply mul_nonneg (by positivity)
    exact mul_nonneg (le_max_of_le_left ha) (abs_nonneg _)
  have h3 : (0:ℝ) ≤ (if H < a then a ^ 2 else 0) := by
    split <;> positivity
  have h4 : (0:ℝ) ≤ (if H < b then b ^ 2 else 0) := by
    split <;> positivity
  have h5 : (0:ℝ) ≤ 16 * L ^ 2 := by positivity
  linarith

theorem gridF_comm (θ : ℝ) : gridF r θ L H a b = gridF r θ L H b a := by
  rw [gridF, gridF, jointRoundSq, jointRoundSq]
  by_cases h : binIdx r θ a = binIdx r θ b ∧ a ∈ Set.Icc L H ∧
      b ∈ Set.Icc L H
  · rw [if_pos h, if_pos ⟨h.1.symm, h.2.2, h.2.1⟩]
    have hval : roundVal r θ a = roundVal r θ b := by
      rw [roundVal, roundVal, h.1]
    rw [hval]
    ring
  · rw [if_neg h, if_neg (by tauto)]
    ring

theorem gridG_comm : gridG α L H a b = gridG α L H b a := by
  rw [gridG, gridG, max_comm, abs_sub_comm]
  ring_nf

theorem measurableSet_sepTheta (r a b : ℝ) :
    MeasurableSet {θ : ℝ | binIdx r θ a ≠ binIdx r θ b} := by
  have heq : {θ : ℝ | binIdx r θ a = binIdx r θ b} =
      ⋃ j : ℤ, {θ : ℝ | binIdx r θ a = j} ∩ {θ : ℝ | binIdx r θ b = j} := by
    ext θ
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h; exact ⟨binIdx r θ b, h, rfl⟩
    · rintro ⟨j, h1, h2⟩; rw [h1, h2]
  have hone : ∀ c : ℝ, ∀ j : ℤ,
      MeasurableSet {θ : ℝ | binIdx r θ c = j} := by
    intro c j
    have hset : {θ : ℝ | binIdx r θ c = j} =
        {θ : ℝ | (j : ℝ) ≤ Real.log c / Real.log r - θ} ∩
          {θ : ℝ | Real.log c / Real.log r - θ < (j : ℝ) + 1} := by
      ext θ
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, binIdx]
      rw [Int.floor_eq_iff]
    rw [hset]
    exact (measurableSet_le measurable_const
        ((measurable_const.sub measurable_id))).inter
      (measurableSet_lt (measurable_const.sub measurable_id)
        measurable_const)
  have : {θ : ℝ | binIdx r θ a ≠ binIdx r θ b} =
      {θ : ℝ | binIdx r θ a = binIdx r θ b}ᶜ := rfl
  rw [this, heq]
  exact (MeasurableSet.iUnion fun j => (hone a j).inter (hone b j)).compl

end Majorant


/-! ### The θ-averaged master bound (proof layer) -/

section ThetaAverage

variable {α L H a b : ℝ}

/-- Grid-coordinate distance against the scaled value distance in the
comparable case. -/
theorem shift_dist_le (hα0 : 0 < α) (hα2 : α ≤ 1 / 2) (hL : 0 < L)
    (haL : L ≤ a) (hab : a ≤ b) (hnear : b < 2 * a) :
    Real.log b / Real.log (1 + α) - Real.log a / Real.log (1 + α) ≤
      3 * (b - a) / (α * b) := by
  have ha0 : 0 < a := lt_of_lt_of_le hL haL
  have hb0 : 0 < b := lt_of_lt_of_le ha0 hab
  have hlogr23 : 2 * α / 3 ≤ Real.log (1 + α) := by
    have h1 := Real.one_sub_inv_le_log_of_pos
      (show (0:ℝ) < 1 + α by linarith)
    have h2 : 1 - (1 + α)⁻¹ = α / (1 + α) := by
      field_simp
      ring
    rw [h2] at h1
    have h3 : 2 * α / 3 ≤ α / (1 + α) := by
      rw [div_le_div_iff₀ (by norm_num) (by linarith)]
      nlinarith
    linarith
  have hlogdiff : Real.log b - Real.log a ≤ (b - a) / a := by
    have h4 := Real.log_le_sub_one_of_pos
      (show (0:ℝ) < b / a by positivity)
    rw [Real.log_div hb0.ne' ha0.ne'] at h4
    have h5 : b / a - 1 = (b - a) / a := by field_simp
    linarith [h5 ▸ h4]
  have hlogdiff0 : 0 ≤ Real.log b - Real.log a := by
    have := Real.log_le_log ha0 hab
    linarith
  calc Real.log b / Real.log (1 + α) -
        Real.log a / Real.log (1 + α) =
        (Real.log b - Real.log a) / Real.log (1 + α) := by ring
    _ ≤ ((b - a) / a) / (2 * α / 3) := by
        apply div_le_div₀ (by positivity) hlogdiff (by positivity) hlogr23
    _ = 3 * (b - a) / (2 * α * a) := by
        rw [div_div_eq_mul_div]
        ring_nf
    _ ≤ 3 * (b - a) / (α * b) := by
        apply div_le_div_of_nonneg_left (by nlinarith) (by positivity)
        nlinarith

/-- The θ-averaged pointwise bound, oriented `a ≤ b`. -/
theorem lintegral_gridF_le_core (hα0 : 0 < α) (hα2 : α ≤ 1 / 2)
    (hL : 0 < L) (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫⁻ θ in Set.Ico (0 : ℝ) 1,
        ENNReal.ofReal (gridF (1 + α) θ L H a b)) ≤
      ENNReal.ofReal (gridG α L H a b) := by
  have hr1 : (1:ℝ) < 1 + α := by linarith
  have hr2 : (1:ℝ) + α ≤ 2 := by linarith
  have hb : 0 ≤ b := le_trans ha hab
  have hIco : volume (Set.Ico (0:ℝ) 1) = 1 := by
    rw [Real.volume_Ico]; norm_num
  have hGpos := gridG_nonneg (L := L) (H := H) (a := a) (b := b) hα0 ha hb
  have hterm2 : (0:ℝ) ≤ 48 / α * (max a b * |a - b|) := by
    apply mul_nonneg (by positivity)
    exact mul_nonneg (le_max_of_le_left ha) (abs_nonneg _)
  have htail_a : (0:ℝ) ≤ (if H < a then a ^ 2 else 0) := by
    split <;> positivity
  have htail_b : (0:ℝ) ≤ (if H < b then b ^ 2 else 0) := by
    split <;> positivity
  -- constant-dominated integrand bound
  have hconst : ∀ c : ℝ, (∀ θ : ℝ, gridF (1 + α) θ L H a b ≤ c) →
      (∫⁻ θ in Set.Ico (0 : ℝ) 1,
        ENNReal.ofReal (gridF (1 + α) θ L H a b)) ≤
        ENNReal.ofReal c := by
    intro c hbound
    calc (∫⁻ θ in Set.Ico (0 : ℝ) 1,
        ENNReal.ofReal (gridF (1 + α) θ L H a b)) ≤
        ∫⁻ _ in Set.Ico (0 : ℝ) 1, ENNReal.ofReal c :=
      lintegral_mono fun θ => ENNReal.ofReal_le_ofReal (hbound θ)
      _ = ENNReal.ofReal c := by
          rw [setLIntegral_const, hIco, mul_one]
  by_cases haw : a ∈ Set.Icc L H
  · by_cases hbw : b ∈ Set.Icc L H
    · -- both retained: bound through the separation event
      have ha0 : 0 < a := lt_of_lt_of_le hL haw.1
      have hb0 : 0 < b := lt_of_lt_of_le ha0 hab
      have hstep : (∫⁻ θ in Set.Ico (0 : ℝ) 1,
          ENNReal.ofReal (gridF (1 + α) θ L H a b)) ≤
          ENNReal.ofReal (4 * (a ^ 2 + b ^ 2)) *
            volume ({θ : ℝ | binIdx (1 + α) θ a ≠ binIdx (1 + α) θ b} ∩
              Set.Ico (0:ℝ) 1) := by
        have hs1 : (∫⁻ θ in Set.Ico (0 : ℝ) 1,
            ENNReal.ofReal (gridF (1 + α) θ L H a b)) ≤
            ∫⁻ θ in Set.Ico (0 : ℝ) 1,
              Set.indicator {θ' : ℝ |
                  binIdx (1 + α) θ' a ≠ binIdx (1 + α) θ' b}
                (fun _ => ENNReal.ofReal (4 * (a ^ 2 + b ^ 2))) θ := by
          apply lintegral_mono
          intro θ
          have hpt := gridF_of_mem_mem hr1 hr2 hL θ haw hbw
          rw [Set.indicator_apply] at hpt ⊢
          by_cases hθ : θ ∈ {θ' : ℝ |
              binIdx (1 + α) θ' a ≠ binIdx (1 + α) θ' b}
          · rw [if_pos hθ] at hpt ⊢
            exact ENNReal.ofReal_le_ofReal hpt
          · rw [if_neg hθ] at hpt ⊢
            have h0 : gridF (1 + α) θ L H a b = 0 :=
              le_antisymm hpt (gridF_nonneg θ)
            simp only [h0, ENNReal.ofReal_zero, le_refl]
        have hs2 : (∫⁻ θ in Set.Ico (0 : ℝ) 1,
            Set.indicator {θ' : ℝ |
                binIdx (1 + α) θ' a ≠ binIdx (1 + α) θ' b}
              (fun _ => ENNReal.ofReal (4 * (a ^ 2 + b ^ 2))) θ) =
            ENNReal.ofReal (4 * (a ^ 2 + b ^ 2)) *
              volume ({θ : ℝ | binIdx (1 + α) θ a ≠
                binIdx (1 + α) θ b} ∩ Set.Ico (0:ℝ) 1) := by
          rw [lintegral_indicator (measurableSet_sepTheta _ a b),
            setLIntegral_const, Measure.restrict_apply
              (measurableSet_sepTheta _ a b)]
        exact hs1.trans_eq hs2
      by_cases hfar : 2 * a ≤ b
      · -- far: bound the shift mass by 1
        have hvol : volume ({θ : ℝ | binIdx (1 + α) θ a ≠
            binIdx (1 + α) θ b} ∩ Set.Ico (0:ℝ) 1) ≤ 1 := by
          calc volume _ ≤ volume (Set.Ico (0:ℝ) 1) :=
              measure_mono Set.inter_subset_right
            _ = 1 := hIco
        have hscal : 4 * (a ^ 2 + b ^ 2) ≤ gridG α L H a b := by
          rw [gridG]
          nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ b - 2 * a)
            (by linarith : (0:ℝ) ≤ 16 * b - 8 * a)]
        calc (∫⁻ θ in Set.Ico (0 : ℝ) 1,
            ENNReal.ofReal (gridF (1 + α) θ L H a b)) ≤
            ENNReal.ofReal (4 * (a ^ 2 + b ^ 2)) * volume _ := hstep
          _ ≤ ENNReal.ofReal (4 * (a ^ 2 + b ^ 2)) * 1 := by
              gcongr
          _ = ENNReal.ofReal (4 * (a ^ 2 + b ^ 2)) := mul_one _
          _ ≤ ENNReal.ofReal (gridG α L H a b) :=
              ENNReal.ofReal_le_ofReal hscal
      · -- near: bound the shift mass by the separation cover
        push_neg at hfar
        have hlogr0 : (0:ℝ) < Real.log (1 + α) := Real.log_pos hr1
        have hlog : Real.log a ≤ Real.log b := Real.log_le_log ha0 hab
        have huv : Real.log a / Real.log (1 + α) ≤
            Real.log b / Real.log (1 + α) := by
          have hmul := mul_le_mul_of_nonneg_right hlog
            (le_of_lt (inv_pos.mpr hlogr0))
          simpa [div_eq_mul_inv] using hmul
        have hsetEq : {θ' : ℝ | binIdx (1 + α) θ' a ≠
            binIdx (1 + α) θ' b} ∩ Set.Ico (0:ℝ) 1 =
            {θ : ℝ | θ ∈ Set.Ico (0 : ℝ) 1 ∧
              ⌊Real.log a / Real.log (1 + α) - θ⌋ ≠
                ⌊Real.log b / Real.log (1 + α) - θ⌋} := by
          ext θ
          simp only [Set.mem_inter_iff, Set.mem_setOf_eq, binIdx]
          tauto
        have hvol : volume ({θ' : ℝ | binIdx (1 + α) θ' a ≠
            binIdx (1 + α) θ' b} ∩ Set.Ico (0:ℝ) 1) ≤
            ENNReal.ofReal (2 * (Real.log b / Real.log (1 + α) -
              Real.log a / Real.log (1 + α))) := by
          rw [hsetEq]
          exact volume_sep_le huv
        have hdist := shift_dist_le hα0 hα2 hL haw.1 hab hfar
        have hbBound : 4 * (a ^ 2 + b ^ 2) ≤ 8 * b ^ 2 := by nlinarith
        have hmax : max a b = b := max_eq_right hab
        have habs : |a - b| = b - a := by
          rw [abs_sub_comm]
          exact abs_of_nonneg (by linarith)
        have hscal : 4 * (a ^ 2 + b ^ 2) *
            (2 * (Real.log b / Real.log (1 + α) -
              Real.log a / Real.log (1 + α))) ≤ gridG α L H a b := by
          have hst : 4 * (a ^ 2 + b ^ 2) *
              (2 * (Real.log b / Real.log (1 + α) -
                Real.log a / Real.log (1 + α))) ≤
              8 * b ^ 2 * (2 * (3 * (b - a) / (α * b))) := by
            apply mul_le_mul hbBound (by linarith) (by linarith)
              (by positivity)
          have heq : 8 * b ^ 2 * (2 * (3 * (b - a) / (α * b))) =
              48 / α * (max a b * |a - b|) := by
            rw [hmax, habs]
            field_simp
            ring
          rw [gridG]
          rw [heq] at hst
          linarith [sq_nonneg (a - b), sq_nonneg L]
        calc (∫⁻ θ in Set.Ico (0 : ℝ) 1,
            ENNReal.ofReal (gridF (1 + α) θ L H a b)) ≤
            ENNReal.ofReal (4 * (a ^ 2 + b ^ 2)) * volume _ := hstep
          _ ≤ ENNReal.ofReal (4 * (a ^ 2 + b ^ 2)) *
              ENNReal.ofReal (2 * (Real.log b / Real.log (1 + α) -
                Real.log a / Real.log (1 + α))) := by
              gcongr
          _ = ENNReal.ofReal (4 * (a ^ 2 + b ^ 2) *
              (2 * (Real.log b / Real.log (1 + α) -
                Real.log a / Real.log (1 + α)))) :=
              (ENNReal.ofReal_mul (by positivity)).symm
          _ ≤ ENNReal.ofReal (gridG α L H a b) :=
              ENNReal.ofReal_le_ofReal hscal
    · -- `a` retained, `b` off the window: since `a ≤ b`, `H < b`
      have hHb : H < b := by
        by_contra hcon
        push_neg at hcon
        exact hbw ⟨le_trans haw.1 hab, hcon⟩
      have hbnd : ∀ θ : ℝ, gridF (1 + α) θ L H a b ≤ 4 * a ^ 2 := by
        intro θ
        rw [gridF_of_mem_notMem θ hbw]
        calc roundSq (1 + α) θ L H a ≤ (1 + α) ^ 2 * a ^ 2 :=
            roundSq_le_sq hr1 hL a
          _ ≤ 4 * a ^ 2 := by
            nlinarith [mul_nonneg (mul_nonneg
              (by linarith : (0:ℝ) ≤ 2 - (1 + α))
              (by linarith : (0:ℝ) ≤ 2 + (1 + α))) (sq_nonneg a)]
      have hscal : 4 * a ^ 2 ≤ gridG α L H a b := by
        rw [gridG, if_pos hHb]
        nlinarith [sq_nonneg (a - b)]
      exact (hconst _ hbnd).trans (ENNReal.ofReal_le_ofReal hscal)
  · by_cases hbw : b ∈ Set.Icc L H
    · -- `a` off the window, `b` retained: since `a ≤ b ≤ H`, `a < L`
      have haL : a < L := by
        by_contra hcon
        push_neg at hcon
        exact haw ⟨hcon, le_trans hab hbw.2⟩
      have hbnd : ∀ θ : ℝ, gridF (1 + α) θ L H a b ≤ 4 * b ^ 2 := by
        intro θ
        rw [gridF_of_notMem_mem θ haw]
        calc roundSq (1 + α) θ L H b ≤ (1 + α) ^ 2 * b ^ 2 :=
            roundSq_le_sq hr1 hL b
          _ ≤ 4 * b ^ 2 := by
            nlinarith [mul_nonneg (mul_nonneg
              (by linarith : (0:ℝ) ≤ 2 - (1 + α))
              (by linarith : (0:ℝ) ≤ 2 + (1 + α))) (sq_nonneg b)]
      by_cases hfar2 : 2 * a ≤ b
      · have hscal : 4 * b ^ 2 ≤ gridG α L H a b := by
          rw [gridG]
          nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ b - 2 * a)
            (by linarith : (0:ℝ) ≤ 28 * b - 8 * a)]
        exact (hconst _ hbnd).trans (ENNReal.ofReal_le_ofReal hscal)
      · push_neg at hfar2
        have hscal : 4 * b ^ 2 ≤ gridG α L H a b := by
          rw [gridG]
          nlinarith [sq_nonneg (a - b)]
        exact (hconst _ hbnd).trans (ENNReal.ofReal_le_ofReal hscal)
    · -- both off the window: the integrand vanishes
      have hbnd : ∀ θ : ℝ, gridF (1 + α) θ L H a b ≤ 0 := fun θ =>
        le_of_eq (gridF_of_notMem_notMem θ haw hbw)
      calc (∫⁻ θ in Set.Ico (0 : ℝ) 1,
          ENNReal.ofReal (gridF (1 + α) θ L H a b)) ≤
          ENNReal.ofReal 0 := hconst 0 hbnd
        _ ≤ ENNReal.ofReal (gridG α L H a b) :=
            ENNReal.ofReal_le_ofReal hGpos

/-- The θ-averaged pointwise bound, symmetric form. -/
theorem lintegral_gridF_le (hα0 : 0 < α) (hα2 : α ≤ 1 / 2)
    (hL : 0 < L) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫⁻ θ in Set.Ico (0 : ℝ) 1,
        ENNReal.ofReal (gridF (1 + α) θ L H a b)) ≤
      ENNReal.ofReal (gridG α L H a b) := by
  rcases le_total a b with hab | hba
  · exact lintegral_gridF_le_core hα0 hα2 hL ha hab
  · have h := lintegral_gridF_le_core (H := H) hα0 hα2 hL hb hba
    have heq : (∫⁻ θ in Set.Ico (0 : ℝ) 1,
        ENNReal.ofReal (gridF (1 + α) θ L H a b)) =
        (∫⁻ θ in Set.Ico (0 : ℝ) 1,
          ENNReal.ofReal (gridF (1 + α) θ L H b a)) := by
      congr 1
      funext θ
      rw [gridF_comm θ]
    rw [heq, gridG_comm]
    exact h

end ThetaAverage

end CommutingRepetition

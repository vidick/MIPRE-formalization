/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/OTQCS/GridAverage.lean
-/
/-
# OTQCS: θ-averaged grid disagreement and common-shift selection
  (nodes 1.3.3, 1.3.4 — assembly)

The assembly half of the shifted-grid layer: joint (shift, coupling)
measurability, the `gridGamma = ∫ gridF` identity, the scalar-majorant
integral bound (`C = 100`), the Tonelli swap giving the θ-averaged
master bound, and the two signed statements `grid_disagreement` (node
1.3.3) and `exists_common_shift` (node 1.3.4). Split out of
`OTQCS/Grid.lean` for the per-file line cap; the signed definitions and
the fixed-shift proof layers live there.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.OTQCS.Grid

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

open MeasureTheory
open scoped BigOperators

/-! ### Assembly: joint measurability, the integral identity, and the
majorant integral (proof layer) -/

section GridAssembly

variable {ν : Measure (ℝ × ℝ)} [IsProbabilityMeasure ν]
variable {r α L H ρ : ℝ}

/-- Joint measurability of the bin index in the (shift, value) pair. -/
theorem measurable_binIdx_pair (r : ℝ) {β : Type*} [MeasurableSpace β]
    {f : β → ℝ} {g : β → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun q => binIdx r (f q) (g q) := by
  apply measurable_to_countable
  intro q0
  set j : ℤ := binIdx r (f q0) (g q0) with hj
  have hset : (fun q => binIdx r (f q) (g q)) ⁻¹' {j} =
      {q : β | (j : ℝ) ≤ Real.log (g q) / Real.log r - f q} ∩
        {q : β | Real.log (g q) / Real.log r - f q < (j : ℝ) + 1} := by
    ext q
    simp only [Set.mem_preimage, Set.mem_singleton_iff,
      Set.mem_inter_iff, Set.mem_setOf_eq, binIdx]
    rw [Int.floor_eq_iff]
  rw [hset]
  exact (measurableSet_le measurable_const
      (((Real.measurable_log.comp hg).div_const _).sub hf)).inter
    (measurableSet_lt
      (((Real.measurable_log.comp hg).div_const _).sub hf)
      measurable_const)

/-- Joint measurability of the disagreement integrand in the
(shift, pair) variable. -/
theorem measurable_gridF_pair {r : ℝ} (hr : 1 < r) (L H : ℝ) :
    Measurable fun q : ℝ × (ℝ × ℝ) =>
      gridF r q.1 L H q.2.1 q.2.2 := by
  have hrpos : (0:ℝ) < r := lt_trans one_pos hr
  have hbin1 : Measurable fun q : ℝ × (ℝ × ℝ) =>
      binIdx r q.1 q.2.1 :=
    measurable_binIdx_pair r measurable_fst
      (measurable_fst.comp measurable_snd)
  have hbin2 : Measurable fun q : ℝ × (ℝ × ℝ) =>
      binIdx r q.1 q.2.2 :=
    measurable_binIdx_pair r measurable_fst
      (measurable_snd.comp measurable_snd)
  have hrv : ∀ {h : ℝ × (ℝ × ℝ) → ℤ}, Measurable h →
      Measurable fun q : ℝ × (ℝ × ℝ) =>
        r ^ ((h q : ℝ) + 1 + q.1) := by
    intro h hh
    have hexp : Measurable fun q : ℝ × (ℝ × ℝ) =>
        ((h q : ℝ) + 1 + q.1) :=
      (((measurable_from_top (f := (Int.cast : ℤ → ℝ))).comp
        hh).add_const 1).add measurable_fst
    have heq : (fun q : ℝ × (ℝ × ℝ) =>
        r ^ ((h q : ℝ) + 1 + q.1)) = fun q =>
        Real.exp (Real.log r * ((h q : ℝ) + 1 + q.1)) := by
      funext q
      rw [Real.rpow_def_of_pos hrpos]
    rw [heq]
    exact Real.measurable_exp.comp (measurable_const.mul hexp)
  have hrv1 : Measurable fun q : ℝ × (ℝ × ℝ) =>
      roundVal r q.1 q.2.1 := hrv hbin1
  have hrv2 : Measurable fun q : ℝ × (ℝ × ℝ) =>
      roundVal r q.1 q.2.2 := hrv hbin2
  have hindIcc : Measurable (Set.indicator (Set.Icc L H) (1 : ℝ → ℝ)) :=
    measurable_one.indicator measurableSet_Icc
  have hrs1 : Measurable fun q : ℝ × (ℝ × ℝ) =>
      roundSq r q.1 L H q.2.1 := by
    have heq : (fun q : ℝ × (ℝ × ℝ) => roundSq r q.1 L H q.2.1) =
        fun q => roundVal r q.1 q.2.1 ^ 2 *
          Set.indicator (Set.Icc L H) 1 q.2.1 := by
      funext q
      exact roundSq_eq_mul_indicator _
    rw [heq]
    exact (hrv1.pow_const 2).mul
      (hindIcc.comp (measurable_fst.comp measurable_snd))
  have hrs2 : Measurable fun q : ℝ × (ℝ × ℝ) =>
      roundSq r q.1 L H q.2.2 := by
    have heq : (fun q : ℝ × (ℝ × ℝ) => roundSq r q.1 L H q.2.2) =
        fun q => roundVal r q.1 q.2.2 ^ 2 *
          Set.indicator (Set.Icc L H) 1 q.2.2 := by
      funext q
      exact roundSq_eq_mul_indicator _
    rw [heq]
    exact (hrv2.pow_const 2).mul
      (hindIcc.comp (measurable_snd.comp measurable_snd))
  have hsame : MeasurableSet {q : ℝ × (ℝ × ℝ) |
      binIdx r q.1 q.2.1 = binIdx r q.1 q.2.2} := by
    have hset : {q : ℝ × (ℝ × ℝ) |
        binIdx r q.1 q.2.1 = binIdx r q.1 q.2.2} =
        ⋃ j : ℤ,
          ((fun q : ℝ × (ℝ × ℝ) => binIdx r q.1 q.2.1) ⁻¹' {j}) ∩
            ((fun q : ℝ × (ℝ × ℝ) => binIdx r q.1 q.2.2) ⁻¹' {j}) := by
      ext q
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff,
        Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro h; exact ⟨binIdx r q.1 q.2.2, h, rfl⟩
      · rintro ⟨j, h1, h2⟩; rw [h1, h2]
    rw [hset]
    exact MeasurableSet.iUnion fun j =>
      (hbin1 (measurableSet_singleton j)).inter
        (hbin2 (measurableSet_singleton j))
  have hjrs : Measurable fun q : ℝ × (ℝ × ℝ) =>
      jointRoundSq r q.1 L H q.2.1 q.2.2 := by
    have heq : (fun q : ℝ × (ℝ × ℝ) =>
        jointRoundSq r q.1 L H q.2.1 q.2.2) = fun q =>
        roundSq r q.1 L H q.2.1 *
          Set.indicator {q' : ℝ × (ℝ × ℝ) |
            binIdx r q'.1 q'.2.1 = binIdx r q'.1 q'.2.2} 1 q *
          Set.indicator (Set.Icc L H) 1 q.2.2 := by
      funext q
      rw [jointRoundSq, roundSq, Set.indicator_apply,
        Set.indicator_apply]
      by_cases h1 : binIdx r q.1 q.2.1 = binIdx r q.1 q.2.2
      · by_cases h2 : q.2.1 ∈ Set.Icc L H
        · by_cases h3 : q.2.2 ∈ Set.Icc L H
          · rw [if_pos ⟨h1, h2, h3⟩, if_pos h2,
              if_pos (show q ∈ {q' : ℝ × (ℝ × ℝ) |
                binIdx r q'.1 q'.2.1 = binIdx r q'.1 q'.2.2} from h1),
              if_pos h3, Pi.one_apply, Pi.one_apply, mul_one, mul_one]
          · rw [if_neg (by tauto), if_neg h3, mul_zero]
        · rw [if_neg (by tauto), if_neg h2, zero_mul, zero_mul]
      · rw [if_neg (by tauto),
          if_neg (show q ∉ {q' : ℝ × (ℝ × ℝ) |
            binIdx r q'.1 q'.2.1 = binIdx r q'.1 q'.2.2} from h1),
          mul_zero, zero_mul]
    rw [heq]
    exact (hrs1.mul (measurable_one.indicator hsame)).mul
      (hindIcc.comp (measurable_snd.comp measurable_snd))
  have heqF : (fun q : ℝ × (ℝ × ℝ) =>
      gridF r q.1 L H q.2.1 q.2.2) = fun q =>
      roundSq r q.1 L H q.2.1 + roundSq r q.1 L H q.2.2 -
        2 * jointRoundSq r q.1 L H q.2.1 q.2.2 := by
    funext q
    rw [gridF]
  rw [heqF]
  exact (hrs1.add hrs2).sub (hjrs.const_mul 2)


theorem gridGamma_eq_integral (hr : 1 < r) (hL : 0 < L) (θ : ℝ)
    (h1 : Integrable (fun p : ℝ × ℝ => p.1 ^ 2) ν)
    (h2 : Integrable (fun p : ℝ × ℝ => p.2 ^ 2) ν) :
    gridGamma ν r θ L H = ∫ p, gridF r θ L H p.1 p.2 ∂ν := by
  have hA := integrable_roundSq_fst (θ := θ) (H := H) hr hL h1
  have hB := integrable_roundSq_snd (θ := θ) (H := H) hr hL h2
  have hC := integrable_jointRoundSq (θ := θ) (H := H) hr hL h1
  have hAB : Integrable (fun p : ℝ × ℝ =>
      roundSq r θ L H p.1 + roundSq r θ L H p.2) ν := hA.add hB
  rw [gridGamma, gridA, gridB, gridC, ← integral_add hA hB,
    ← integral_const_mul, ← integral_sub hAB (hC.const_mul 2)]
  congr 1

theorem measurable_gridF_slice (hr : 1 < r) (θ : ℝ) :
    Measurable fun p : ℝ × ℝ => gridF r θ L H p.1 p.2 := by
  have h := (measurable_gridF_pair (r := r) hr L H).comp
    (measurable_const.prodMk measurable_id :
      Measurable fun p : ℝ × ℝ => ((θ, p) : ℝ × (ℝ × ℝ)))
  exact h

theorem integral_gridF_eq_toReal (hr : 1 < r) (θ : ℝ) :
    (∫ p, gridF r θ L H p.1 p.2 ∂ν) =
      (∫⁻ p, ENNReal.ofReal (gridF r θ L H p.1 p.2) ∂ν).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ fun p => gridF_nonneg θ)
    (measurable_gridF_slice hr θ).aestronglyMeasurable]

/-- Integrability of the fixed-shift disagreement integrand. -/
theorem integrable_gridF_slice (hr : 1 < r) (hL : 0 < L) (θ : ℝ)
    (h1 : Integrable (fun p : ℝ × ℝ => p.1 ^ 2) ν)
    (h2 : Integrable (fun p : ℝ × ℝ => p.2 ^ 2) ν) :
    Integrable (fun p : ℝ × ℝ => gridF r θ L H p.1 p.2) ν := by
  have hA := integrable_roundSq_fst (θ := θ) (H := H) hr hL h1
  have hB := integrable_roundSq_snd (θ := θ) (H := H) hr hL h2
  have hC := integrable_jointRoundSq (θ := θ) (H := H) hr hL h1
  have hAB : Integrable (fun p : ℝ × ℝ =>
      roundSq r θ L H p.1 + roundSq r θ L H p.2) ν := hA.add hB
  have heq : (fun p : ℝ × ℝ => gridF r θ L H p.1 p.2) = fun p =>
      (roundSq r θ L H p.1 + roundSq r θ L H p.2) -
        2 * jointRoundSq r θ L H p.1 p.2 := by
    funext p
    rw [gridF]
  rw [heq]
  exact hAB.sub (hC.const_mul 2)

/-- Integrability of the scalar majorant. -/
theorem integrable_gridG (h1 : (∫ p : ℝ × ℝ, p.1 ^ 2 ∂ν) = 1)
    (h2 : (∫ p : ℝ × ℝ, p.2 ^ 2 ∂ν) = 1) :
    Integrable (fun p : ℝ × ℝ => gridG α L H p.1 p.2) ν := by
  have h1int := integrable_of_integral_eq_one (ν := ν) h1
  have h2int := integrable_of_integral_eq_one (ν := ν) h2
  have hDint : Integrable (fun p : ℝ × ℝ => (p.1 - p.2) ^ 2) ν := by
    apply Integrable.mono' ((h1int.const_mul 2).add (h2int.const_mul 2))
    · exact ((measurable_fst.sub measurable_snd).pow_const
        2).aestronglyMeasurable
    · filter_upwards with p
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      simp only [Pi.add_apply]
      nlinarith [sq_nonneg (p.1 + p.2)]
  have hMdom : ∀ p : ℝ × ℝ, max p.1 p.2 ^ 2 ≤ p.1 ^ 2 + p.2 ^ 2 := by
    intro p
    rcases max_cases p.1 p.2 with ⟨hm, _⟩ | ⟨hm, _⟩ <;>
      rw [hm] <;> nlinarith [sq_nonneg p.1, sq_nonneg p.2]
  have hMint : Integrable
      (fun p : ℝ × ℝ => max p.1 p.2 * |p.1 - p.2|) ν := by
    apply Integrable.mono' ((h1int.add h2int).add hDint)
    · exact ((measurable_fst.max measurable_snd).mul
        (measurable_fst.sub measurable_snd).abs).aestronglyMeasurable
    · filter_upwards with p
      rw [Real.norm_eq_abs, abs_mul, abs_abs]
      simp only [Pi.add_apply]
      nlinarith [sq_nonneg (|max p.1 p.2| - |p.1 - p.2|),
        sq_abs (max p.1 p.2), sq_abs (p.1 - p.2), hMdom p]
  have hset1 : MeasurableSet {q : ℝ × ℝ | H < q.1} :=
    measurableSet_lt measurable_const measurable_fst
  have hset2 : MeasurableSet {q : ℝ × ℝ | H < q.2} :=
    measurableSet_lt measurable_const measurable_snd
  have htint1 : Integrable
      (fun p : ℝ × ℝ => if H < p.1 then p.1 ^ 2 else 0) ν := by
    have hind1 : (fun p : ℝ × ℝ => if H < p.1 then p.1 ^ 2 else 0) =
        fun p : ℝ × ℝ =>
          Set.indicator {q : ℝ × ℝ | H < q.1} (fun q => q.1 ^ 2) p := by
      funext p
      by_cases hp : H < p.1
      · rw [if_pos hp,
          Set.indicator_of_mem (show p ∈ {q : ℝ × ℝ | H < q.1} from hp)]
      · rw [if_neg hp,
          Set.indicator_of_notMem
            (show p ∉ {q : ℝ × ℝ | H < q.1} from hp)]
    rw [hind1]
    exact h1int.indicator hset1
  have htint2 : Integrable
      (fun p : ℝ × ℝ => if H < p.2 then p.2 ^ 2 else 0) ν := by
    have hind2 : (fun p : ℝ × ℝ => if H < p.2 then p.2 ^ 2 else 0) =
        fun p : ℝ × ℝ =>
          Set.indicator {q : ℝ × ℝ | H < q.2} (fun q => q.2 ^ 2) p := by
      funext p
      by_cases hp : H < p.2
      · rw [if_pos hp,
          Set.indicator_of_mem (show p ∈ {q : ℝ × ℝ | H < q.2} from hp)]
      · rw [if_neg hp,
          Set.indicator_of_notMem
            (show p ∉ {q : ℝ × ℝ | H < q.2} from hp)]
    rw [hind2]
    exact h2int.indicator hset2
  have hgeq : (fun p : ℝ × ℝ => gridG α L H p.1 p.2) = fun p =>
      32 * (p.1 - p.2) ^ 2 + 48 / α * (max p.1 p.2 * |p.1 - p.2|) +
        8 * ((if H < p.1 then p.1 ^ 2 else 0) +
          (if H < p.2 then p.2 ^ 2 else 0)) + 16 * L ^ 2 := by
    funext p
    rw [gridG]
  rw [hgeq]
  exact (((hDint.const_mul 32).add (hMint.const_mul (48 / α))).add
    ((htint1.add htint2).const_mul 8)).add (integrable_const _)

/-- The majorant integrates to the manuscript bound with `C = 100`. -/
theorem integral_gridG_le (hα0 : 0 < α) (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hnn : ∀ᵐ p ∂ν, 0 ≤ p.1 ∧ 0 ≤ p.2)
    (h1 : (∫ p : ℝ × ℝ, p.1 ^ 2 ∂ν) = 1)
    (h2 : (∫ p : ℝ × ℝ, p.2 ^ 2 ∂ν) = 1)
    (ht1 : (∫ p in {q : ℝ × ℝ | H < q.1}, p.1 ^ 2 ∂ν) ≤ ρ)
    (ht2 : (∫ p in {q : ℝ × ℝ | H < q.2}, p.2 ^ 2 ∂ν) ≤ ρ) :
    (∫ p, gridG α L H p.1 p.2 ∂ν) ≤
      100 * ((∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂ν) +
        Real.sqrt (∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂ν) / α + ρ + L ^ 2) := by
  have h1int := integrable_of_integral_eq_one (ν := ν) h1
  have h2int := integrable_of_integral_eq_one (ν := ν) h2
  set D := ∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂ν with hD
  have hmeasD : Measurable fun p : ℝ × ℝ => (p.1 - p.2) ^ 2 :=
    (measurable_fst.sub measurable_snd).pow_const 2
  have hDint : Integrable (fun p : ℝ × ℝ => (p.1 - p.2) ^ 2) ν := by
    apply Integrable.mono' ((h1int.const_mul 2).add (h2int.const_mul 2))
    · exact hmeasD.aestronglyMeasurable
    · filter_upwards with p
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      simp only [Pi.add_apply]
      nlinarith [sq_nonneg (p.1 + p.2)]
  have hD0 : 0 ≤ D := integral_nonneg fun p => sq_nonneg _
  have hmeasM : Measurable fun p : ℝ × ℝ => max p.1 p.2 * |p.1 - p.2| :=
    (measurable_fst.max measurable_snd).mul
      (measurable_fst.sub measurable_snd).abs
  have hMdom : ∀ p : ℝ × ℝ, max p.1 p.2 ^ 2 ≤ p.1 ^ 2 + p.2 ^ 2 := by
    intro p
    rcases max_cases p.1 p.2 with ⟨hm, _⟩ | ⟨hm, _⟩ <;>
      rw [hm] <;> nlinarith [sq_nonneg p.1, sq_nonneg p.2]
  have hMint : Integrable
      (fun p : ℝ × ℝ => max p.1 p.2 * |p.1 - p.2|) ν := by
    apply Integrable.mono' ((h1int.add h2int).add hDint)
    · exact hmeasM.aestronglyMeasurable
    · filter_upwards with p
      rw [Real.norm_eq_abs, abs_mul, abs_abs]
      simp only [Pi.add_apply]
      nlinarith [sq_nonneg (|max p.1 p.2| - |p.1 - p.2|),
        sq_abs (max p.1 p.2), sq_abs (p.1 - p.2), hMdom p]
  -- second moment of the max
  have hmaxsq_int : Integrable (fun p : ℝ × ℝ => max p.1 p.2 ^ 2) ν := by
    apply Integrable.mono' (h1int.add h2int)
    · exact ((measurable_fst.max measurable_snd).pow_const
        2).aestronglyMeasurable
    · filter_upwards with p
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hMdom p
  have hmaxsq_le : (∫ p : ℝ × ℝ, max p.1 p.2 ^ 2 ∂ν) ≤ 2 := by
    have hmono : (∫ p : ℝ × ℝ, max p.1 p.2 ^ 2 ∂ν) ≤
        ∫ p : ℝ × ℝ, p.1 ^ 2 + p.2 ^ 2 ∂ν :=
      integral_mono hmaxsq_int (h1int.add h2int) hMdom
    rw [integral_add h1int h2int, h1, h2] at hmono
    linarith
  set M := ∫ p : ℝ × ℝ, max p.1 p.2 * |p.1 - p.2| ∂ν with hM
  have hM0 : 0 ≤ M := by
    rw [hM]
    apply integral_nonneg_of_ae
    filter_upwards [hnn] with p hp
    exact mul_nonneg (le_max_of_le_left hp.1) (abs_nonneg _)
  -- scale-t arithmetic-geometric bound on the cross term
  have hMs : ∀ s : ℝ, 0 < s → 2 * s * M ≤ 2 * s ^ 2 + D := by
    intro s hs
    have hle : (∫ p : ℝ × ℝ,
        2 * s * (max p.1 p.2 * |p.1 - p.2|) ∂ν) ≤
        ∫ p : ℝ × ℝ, s ^ 2 * max p.1 p.2 ^ 2 + (p.1 - p.2) ^ 2 ∂ν := by
      apply integral_mono (hMint.const_mul _)
        ((hmaxsq_int.const_mul _).add hDint)
      intro p
      simp only [Pi.add_apply]
      nlinarith [sq_nonneg (s * max p.1 p.2 - |p.1 - p.2|),
        sq_abs (p.1 - p.2)]
    rw [integral_const_mul,
      integral_add (hmaxsq_int.const_mul _) hDint, integral_const_mul,
      ← hM, ← hD] at hle
    linarith [mul_le_mul_of_nonneg_left hmaxsq_le (sq_nonneg s)]
  -- optimize the scale: M ≤ √2·√D
  have hMD : M ≤ Real.sqrt 2 * Real.sqrt D := by
    rcases eq_or_lt_of_le hD0 with hD0' | hDpos
    · have hMle : M ≤ 0 := by
        by_contra hcon
        push_neg at hcon
        have h := hMs (M / 2) (by linarith)
        nlinarith
      have hnn2 : (0:ℝ) ≤ Real.sqrt 2 * Real.sqrt D :=
        mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      linarith
    · set s := Real.sqrt (D / 2) with hsdef
      have hs : 0 < s := Real.sqrt_pos.mpr (by linarith)
      have hs2 : s ^ 2 = D / 2 := by
        rw [hsdef]
        exact Real.sq_sqrt (by linarith)
      have h := hMs s hs
      have hsM : s * M ≤ D := by nlinarith
      have hprod : Real.sqrt 2 * Real.sqrt D * s = D := by
        rw [hsdef, ← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2),
          ← Real.sqrt_mul (by linarith : (0:ℝ) ≤ 2 * D),
          show 2 * D * (D / 2) = D ^ 2 by ring, Real.sqrt_sq hD0]
      have hfin : M * s ≤ Real.sqrt 2 * Real.sqrt D * s := by
        rw [hprod]
        nlinarith
      exact le_of_mul_le_mul_right hfin hs
  -- tail terms as set integrals
  have hset1 : MeasurableSet {q : ℝ × ℝ | H < q.1} :=
    measurableSet_lt measurable_const measurable_fst
  have hset2 : MeasurableSet {q : ℝ × ℝ | H < q.2} :=
    measurableSet_lt measurable_const measurable_snd
  have hind1 : (fun p : ℝ × ℝ => if H < p.1 then p.1 ^ 2 else 0) =
      fun p : ℝ × ℝ =>
        Set.indicator {q : ℝ × ℝ | H < q.1} (fun q => q.1 ^ 2) p := by
    funext p
    by_cases hp : H < p.1
    · rw [if_pos hp,
        Set.indicator_of_mem (show p ∈ {q : ℝ × ℝ | H < q.1} from hp)]
    · rw [if_neg hp,
        Set.indicator_of_notMem
          (show p ∉ {q : ℝ × ℝ | H < q.1} from hp)]
  have hind2 : (fun p : ℝ × ℝ => if H < p.2 then p.2 ^ 2 else 0) =
      fun p : ℝ × ℝ =>
        Set.indicator {q : ℝ × ℝ | H < q.2} (fun q => q.2 ^ 2) p := by
    funext p
    by_cases hp : H < p.2
    · rw [if_pos hp,
        Set.indicator_of_mem (show p ∈ {q : ℝ × ℝ | H < q.2} from hp)]
    · rw [if_neg hp,
        Set.indicator_of_notMem
          (show p ∉ {q : ℝ × ℝ | H < q.2} from hp)]
  have htint1 : Integrable
      (fun p : ℝ × ℝ => if H < p.1 then p.1 ^ 2 else 0) ν := by
    rw [hind1]
    exact h1int.indicator hset1
  have htint2 : Integrable
      (fun p : ℝ × ℝ => if H < p.2 then p.2 ^ 2 else 0) ν := by
    rw [hind2]
    exact h2int.indicator hset2
  have htail1 :
      (∫ p : ℝ × ℝ, (if H < p.1 then p.1 ^ 2 else 0) ∂ν) ≤ ρ := by
    rw [hind1, integral_indicator hset1]
    exact ht1
  have htail2 :
      (∫ p : ℝ × ℝ, (if H < p.2 then p.2 ^ 2 else 0) ∂ν) ≤ ρ := by
    rw [hind2, integral_indicator hset2]
    exact ht2
  -- split the majorant integral
  have hsplit : (∫ p, gridG α L H p.1 p.2 ∂ν) =
      32 * D + 48 / α * M +
        8 * ((∫ p : ℝ × ℝ, (if H < p.1 then p.1 ^ 2 else 0) ∂ν) +
          (∫ p : ℝ × ℝ, (if H < p.2 then p.2 ^ 2 else 0) ∂ν)) +
        16 * L ^ 2 := by
    have hgeq : (fun p : ℝ × ℝ => gridG α L H p.1 p.2) = fun p =>
        32 * (p.1 - p.2) ^ 2 + 48 / α * (max p.1 p.2 * |p.1 - p.2|) +
          8 * ((if H < p.1 then p.1 ^ 2 else 0) +
            (if H < p.2 then p.2 ^ 2 else 0)) + 16 * L ^ 2 := by
      funext p
      rw [gridG]
    have hI1 : Integrable (fun p : ℝ × ℝ => 32 * (p.1 - p.2) ^ 2) ν :=
      hDint.const_mul 32
    have hI2 : Integrable (fun p : ℝ × ℝ =>
        48 / α * (max p.1 p.2 * |p.1 - p.2|)) ν :=
      hMint.const_mul (48 / α)
    have hI3 : Integrable (fun p : ℝ × ℝ =>
        8 * ((if H < p.1 then p.1 ^ 2 else 0) +
          (if H < p.2 then p.2 ^ 2 else 0))) ν :=
      (htint1.add htint2).const_mul 8
    have hI12 : Integrable (fun p : ℝ × ℝ =>
        32 * (p.1 - p.2) ^ 2 +
          48 / α * (max p.1 p.2 * |p.1 - p.2|)) ν := hI1.add hI2
    have hI123 : Integrable (fun p : ℝ × ℝ =>
        32 * (p.1 - p.2) ^ 2 +
          48 / α * (max p.1 p.2 * |p.1 - p.2|) +
          8 * ((if H < p.1 then p.1 ^ 2 else 0) +
            (if H < p.2 then p.2 ^ 2 else 0))) ν := hI12.add hI3
    rw [hgeq, integral_add hI123 (integrable_const _),
      integral_add hI12 hI3, integral_add hI1 hI2,
      integral_const_mul, integral_const_mul, integral_const_mul,
      integral_add htint1 htint2, integral_const, ← hD, ← hM]
    simp
  rw [hsplit]
  -- final scalar assembly with C = 100
  have hsqrt2 : Real.sqrt 2 ≤ 25 / 12 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),
      Real.sqrt_nonneg 2]
  have h48 : 48 * M ≤ 100 * Real.sqrt D := by
    nlinarith [hMD, hsqrt2, Real.sqrt_nonneg D]
  have hMbound : 48 / α * M ≤ 100 * (Real.sqrt D / α) := by
    have hrw1 : 48 / α * M = 1 / α * (48 * M) := by ring
    have hrw2 : 100 * (Real.sqrt D / α) =
        1 / α * (100 * Real.sqrt D) := by ring
    rw [hrw1, hrw2]
    exact mul_le_mul_of_nonneg_left h48 (by positivity)
  linarith [htail1, htail2, sq_nonneg L, hMbound, hD0, hρ]

/-- The θ-averaged disagreement bound (eq grid-disagreement, `C = 100`):
swap the θ- and coupling-integrals by Tonelli, apply the pointwise
θ-average master bound, and integrate the majorant. -/
theorem setIntegral_gridGamma_le (hα0 : 0 < α) (hα2 : α ≤ 1 / 2)
    (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hnn : ∀ᵐ p ∂ν, 0 ≤ p.1 ∧ 0 ≤ p.2)
    (h1 : (∫ p : ℝ × ℝ, p.1 ^ 2 ∂ν) = 1)
    (h2 : (∫ p : ℝ × ℝ, p.2 ^ 2 ∂ν) = 1)
    (ht1 : (∫ p in {q : ℝ × ℝ | H < q.1}, p.1 ^ 2 ∂ν) ≤ ρ)
    (ht2 : (∫ p in {q : ℝ × ℝ | H < q.2}, p.2 ^ 2 ∂ν) ≤ ρ) :
    (∫ θ in Set.Ico (0 : ℝ) 1, gridGamma ν (1 + α) θ L H) ≤
      100 * ((∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂ν) +
        Real.sqrt (∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂ν) / α + ρ + L ^ 2) := by
  have hr : 1 < 1 + α := by linarith
  have h1int := integrable_of_integral_eq_one (ν := ν) h1
  have h2int := integrable_of_integral_eq_one (ν := ν) h2
  set I : ℝ → ENNReal := fun θ =>
    ∫⁻ p, ENNReal.ofReal (gridF (1 + α) θ L H p.1 p.2) ∂ν with hIdef
  have hIeq : ∀ θ : ℝ, gridGamma ν (1 + α) θ L H = (I θ).toReal := by
    intro θ
    rw [gridGamma_eq_integral hr hL θ h1int h2int,
      integral_gridF_eq_toReal hr θ, hIdef]
  have hImeas : Measurable I := by
    rw [hIdef]
    exact Measurable.lintegral_prod_right'
      (ENNReal.measurable_ofReal.comp (measurable_gridF_pair hr L H))
  have hIfin : ∀ θ : ℝ, I θ < ⊤ := by
    intro θ
    have hval : I θ = ENNReal.ofReal
        (∫ p, gridF (1 + α) θ L H p.1 p.2 ∂ν) := by
      rw [hIdef]
      exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (integrable_gridF_slice hr hL θ h1int h2int)
        (ae_of_all _ fun p => gridF_nonneg θ)).symm
    rw [hval]
    exact ENNReal.ofReal_lt_top
  have hGnn : 0 ≤ᵐ[ν] fun p : ℝ × ℝ => gridG α L H p.1 p.2 := by
    filter_upwards [hnn] with p hp
    exact gridG_nonneg hα0 hp.1 hp.2
  -- the swapped and majorized lintegral
  have hkey : (∫⁻ θ in Set.Ico (0 : ℝ) 1, I θ) ≤
      ENNReal.ofReal (∫ p, gridG α L H p.1 p.2 ∂ν) := by
    have hswap : (∫⁻ θ in Set.Ico (0 : ℝ) 1, I θ) =
        ∫⁻ p, (∫⁻ θ in Set.Ico (0 : ℝ) 1,
          ENNReal.ofReal (gridF (1 + α) θ L H p.1 p.2)) ∂ν := by
      rw [hIdef]
      exact lintegral_lintegral_swap
        ((ENNReal.measurable_ofReal.comp
          (measurable_gridF_pair hr L H)).aemeasurable)
    rw [hswap]
    have hstep : (∫⁻ p, (∫⁻ θ in Set.Ico (0 : ℝ) 1,
        ENNReal.ofReal (gridF (1 + α) θ L H p.1 p.2)) ∂ν) ≤
        ∫⁻ p, ENNReal.ofReal (gridG α L H p.1 p.2) ∂ν := by
      apply lintegral_mono_ae
      filter_upwards [hnn] with p hp
      exact lintegral_gridF_le hα0 hα2 hL hp.1 hp.2
    have heqG : (∫⁻ p, ENNReal.ofReal (gridG α L H p.1 p.2) ∂ν) =
        ENNReal.ofReal (∫ p, gridG α L H p.1 p.2 ∂ν) :=
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (integrable_gridG h1 h2) hGnn).symm
    rw [← heqG]
    exact hstep
  -- convert back to the Bochner integral
  have hGint_nn : (0:ℝ) ≤ ∫ p, gridG α L H p.1 p.2 ∂ν :=
    integral_nonneg_of_ae hGnn
  calc (∫ θ in Set.Ico (0 : ℝ) 1, gridGamma ν (1 + α) θ L H)
      = ∫ θ in Set.Ico (0 : ℝ) 1, (I θ).toReal := by
        simp only [hIeq]
    _ = (∫⁻ θ in Set.Ico (0 : ℝ) 1, I θ).toReal :=
        integral_toReal (hImeas.aemeasurable)
          (ae_of_all _ fun θ => hIfin θ)
    _ ≤ (ENNReal.ofReal (∫ p, gridG α L H p.1 p.2 ∂ν)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hkey
    _ = ∫ p, gridG α L H p.1 p.2 ∂ν := ENNReal.toReal_ofReal hGint_nn
    _ ≤ 100 * ((∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂ν) +
          Real.sqrt (∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂ν) / α + ρ + L ^ 2) :=
        integral_gridG_le hα0 hL hρ hnn h1 h2 ht1 ht2

/-- Shift-measurability of the disagreement functional. -/
theorem measurable_gridGamma (hr : 1 < r) (hL : 0 < L)
    (h1 : Integrable (fun p : ℝ × ℝ => p.1 ^ 2) ν)
    (h2 : Integrable (fun p : ℝ × ℝ => p.2 ^ 2) ν) :
    Measurable fun θ : ℝ => gridGamma ν r θ L H := by
  have heq : (fun θ : ℝ => gridGamma ν r θ L H) = fun θ =>
      (∫⁻ p, ENNReal.ofReal (gridF r θ L H p.1 p.2) ∂ν).toReal := by
    funext θ
    rw [gridGamma_eq_integral hr hL θ h1 h2,
      integral_gridF_eq_toReal hr θ]
  rw [heq]
  exact (Measurable.lintegral_prod_right'
    (ENNReal.measurable_ofReal.comp
      (measurable_gridF_pair hr L H))).ennreal_toReal

/-- The disagreement functional is nonnegative. -/
theorem gridGamma_nonneg (hr : 1 < r) (hL : 0 < L) (θ : ℝ)
    (h1 : Integrable (fun p : ℝ × ℝ => p.1 ^ 2) ν)
    (h2 : Integrable (fun p : ℝ × ℝ => p.2 ^ 2) ν) :
    0 ≤ gridGamma ν r θ L H := by
  rw [gridGamma_eq_integral hr hL θ h1 h2]
  exact integral_nonneg fun p => gridF_nonneg θ

/-- Crude uniform bound: `Γ_θ ≤ 2 r²`. -/
theorem gridGamma_le_two_sq (hr : 1 < r) (hL : 0 < L) (θ : ℝ)
    (h1 : (∫ p : ℝ × ℝ, p.1 ^ 2 ∂ν) = 1)
    (h2 : (∫ p : ℝ × ℝ, p.2 ^ 2 ∂ν) = 1) :
    gridGamma ν r θ L H ≤ 2 * r ^ 2 := by
  have hC : (0:ℝ) ≤ gridC ν r θ L H :=
    integral_nonneg fun p => jointRoundSq_nonneg
  have hA := gridA_le (θ := θ) (H := H) hr hL h1
  have hB := gridB_le (θ := θ) (H := H) hr hL h2
  rw [gridGamma]
  linarith

end GridAssembly

/-- **Shifted-bin disagreement with cutoffs** (node 1.3.3;
06_otqcs.tex, lem otqcs-grid, eqs ab-mass + grid-disagreement). Over an
abstract coupling `ν` — probability measure on `ℝ × ℝ`, almost surely
nonnegative coordinates, unit coordinate second moments (eq
joint-moments), both high squared tails beyond `H` at most `ρ` — with
ratio `r = 1 + α`, `0 < α ≤ 1/2`, window `0 < L < H`, and
`D = ∫ (a − b)² dν` (`= ‖h−k‖₂²` at consumption, eq joint-moments):
(i) for every shift `θ ∈ [0,1)` the retained rounded masses satisfy
`1 − ρ − L² ≤ a_θ, b_θ ≤ r²` (eq ab-mass); (ii) the average over
`θ ∼ Unif [0,1)` of `Γ_θ` is at most `C (D + √D / α + ρ + L²)` for a
universal numerical constant `C` (eq grid-disagreement). -/
theorem grid_disagreement :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν] (α L H ρ : ℝ),
        0 < α → α ≤ 1 / 2 → 0 < L → L < H → 0 ≤ ρ →
        (∀ᵐ p ∂ν, 0 ≤ p.1 ∧ 0 ≤ p.2) →
        (∫ p : ℝ × ℝ, p.1 ^ 2 ∂ν) = 1 →
        (∫ p : ℝ × ℝ, p.2 ^ 2 ∂ν) = 1 →
        (∫ p in {q : ℝ × ℝ | H < q.1}, p.1 ^ 2 ∂ν) ≤ ρ →
        (∫ p in {q : ℝ × ℝ | H < q.2}, p.2 ^ 2 ∂ν) ≤ ρ →
        (∀ θ ∈ Set.Ico (0 : ℝ) 1,
          1 - ρ - L ^ 2 ≤ gridA ν (1 + α) θ L H ∧
          gridA ν (1 + α) θ L H ≤ (1 + α) ^ 2 ∧
          1 - ρ - L ^ 2 ≤ gridB ν (1 + α) θ L H ∧
          gridB ν (1 + α) θ L H ≤ (1 + α) ^ 2) ∧
        (∫ θ in Set.Ico (0 : ℝ) 1, gridGamma ν (1 + α) θ L H) ≤
          C * ((∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂ν) +
            Real.sqrt (∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂ν) / α +
            ρ + L ^ 2) := by
  refine ⟨100, by norm_num, ?_⟩
  intro ν hprob α L H ρ hα0 hα2 hL hLH hρ hnn h1 h2 ht1 ht2
  have hr : 1 < 1 + α := by linarith
  refine ⟨fun θ _ => ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact gridA_ge hr hL hLH hnn h1 ht1
  · exact gridA_le hr hL h1
  · exact gridB_ge hr hL hLH hnn h2 ht2
  · exact gridB_le hr hL h2
  · exact setIntegral_gridGamma_le hα0 hα2 hL hρ hnn h1 h2 ht1 ht2

/-- **Common shift selection** (node 1.3.4; 06_otqcs.tex, eq
common-shift): for a finite family of couplings satisfying the
`grid_disagreement` hypotheses uniformly — one `α, L, H` and one tail
bound `ρ` for every member — and a probability weight `π` on the
family, there is one deterministic shift `θ₀ ∈ [0,1)` for which the
`π`-average of `Γ_{θ₀}` is at most `C (D̄ + √D̄ / α + ρ + L²)`, where
`D̄` is the `π`-average of the cross second moments (`= E_π D_{st}` at
consumption). Average selection: no union bound, no division by `π`.
Instantiated at the pair family `ι = S × T`. -/
theorem exists_common_shift :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ι : Type) [Fintype ι] (π : ι → ℝ) (ν : ι → Measure (ℝ × ℝ))
        [∀ i, IsProbabilityMeasure (ν i)] (α L H ρ : ℝ),
        0 < α → α ≤ 1 / 2 → 0 < L → L < H → 0 ≤ ρ →
        (∀ i, 0 ≤ π i) → (∑ i, π i) = 1 →
        (∀ i, ∀ᵐ p ∂(ν i), 0 ≤ p.1 ∧ 0 ≤ p.2) →
        (∀ i, (∫ p : ℝ × ℝ, p.1 ^ 2 ∂(ν i)) = 1) →
        (∀ i, (∫ p : ℝ × ℝ, p.2 ^ 2 ∂(ν i)) = 1) →
        (∀ i, (∫ p in {q : ℝ × ℝ | H < q.1}, p.1 ^ 2 ∂(ν i)) ≤ ρ) →
        (∀ i, (∫ p in {q : ℝ × ℝ | H < q.2}, p.2 ^ 2 ∂(ν i)) ≤ ρ) →
        ∃ θ₀ ∈ Set.Ico (0 : ℝ) 1,
          (∑ i, π i * gridGamma (ν i) (1 + α) θ₀ L H) ≤
            C * ((∑ i, π i * ∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂(ν i)) +
              Real.sqrt
                (∑ i, π i * ∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂(ν i)) / α +
              ρ + L ^ 2) := by
  refine ⟨100, by norm_num, ?_⟩
  intro ι _ π ν _ α L H ρ hα0 hα2 hL hLH hρ hπ hπ1 hnn h1 h2 ht1 ht2
  have hr : 1 < 1 + α := by linarith
  have h1int : ∀ i, Integrable (fun p : ℝ × ℝ => p.1 ^ 2) (ν i) :=
    fun i => integrable_of_integral_eq_one (ν := ν i) (h1 i)
  have h2int : ∀ i, Integrable (fun p : ℝ × ℝ => p.2 ^ 2) (ν i) :=
    fun i => integrable_of_integral_eq_one (ν := ν i) (h2 i)
  -- integrability of the θ-slices on the shift window
  haveI hfinres : IsFiniteMeasure (volume.restrict (Set.Ico (0:ℝ) 1)) := by
    constructor
    rw [Measure.restrict_apply_univ, Real.volume_Ico]
    exact ENNReal.ofReal_lt_top
  have hΓint : ∀ i, IntegrableOn
      (fun θ => gridGamma (ν i) (1 + α) θ L H) (Set.Ico (0:ℝ) 1) := by
    intro i
    apply Integrable.mono'
      (integrable_const (2 * (1 + α) ^ 2 : ℝ))
      ((measurable_gridGamma hr hL (h1int i)
        (h2int i)).aestronglyMeasurable)
    filter_upwards with θ
    rw [Real.norm_eq_abs,
      abs_of_nonneg (gridGamma_nonneg hr hL θ (h1int i) (h2int i))]
    exact gridGamma_le_two_sq hr hL θ (h1 i) (h2 i)
  have hbar_int : IntegrableOn
      (fun θ => ∑ i, π i * gridGamma (ν i) (1 + α) θ L H)
      (Set.Ico (0:ℝ) 1) :=
    integrable_finsetSum _ fun i _ => (hΓint i).const_mul (π i)
  -- window measure facts
  have hIco0 : volume (Set.Ico (0:ℝ) 1) ≠ 0 := by
    rw [Real.volume_Ico]
    simp [ENNReal.ofReal_eq_zero]
  have hIcoT : volume (Set.Ico (0:ℝ) 1) ≠ ⊤ := by
    rw [Real.volume_Ico]
    exact ENNReal.ofReal_ne_top
  have hIcoReal : volume.real (Set.Ico (0:ℝ) 1) = 1 := by
    rw [measureReal_def, Real.volume_Ico, ENNReal.toReal_ofReal] <;>
      norm_num
  -- average selection of the common shift
  obtain ⟨θ₀, hθ₀, hle⟩ := exists_le_setAverage hIco0 hIcoT hbar_int
  refine ⟨θ₀, hθ₀, ?_⟩
  have hle' : (∑ i, π i * gridGamma (ν i) (1 + α) θ₀ L H) ≤
      ∫ θ in Set.Ico (0:ℝ) 1,
        ∑ i, π i * gridGamma (ν i) (1 + α) θ L H := by
    calc (∑ i, π i * gridGamma (ν i) (1 + α) θ₀ L H) ≤ _ := hle
      _ = _ := by rw [setAverage_eq, hIcoReal, inv_one, one_smul]
  -- exchange the weighted sum and the shift integral
  have hswap : (∫ θ in Set.Ico (0:ℝ) 1,
      ∑ i, π i * gridGamma (ν i) (1 + α) θ L H) =
      ∑ i, π i * ∫ θ in Set.Ico (0:ℝ) 1,
        gridGamma (ν i) (1 + α) θ L H := by
    rw [integral_finsetSum _ fun i _ => (hΓint i).const_mul (π i)]
    exact Finset.sum_congr rfl fun i _ => by rw [integral_const_mul]
  -- the per-member disagreement bound, weighted
  have hwsum : (∑ i, π i * ∫ θ in Set.Ico (0:ℝ) 1,
      gridGamma (ν i) (1 + α) θ L H) ≤
      ∑ i, π i * (100 * ((∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂(ν i)) +
        Real.sqrt (∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂(ν i)) / α +
        ρ + L ^ 2)) :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
      (setIntegral_gridGamma_le hα0 hα2 hL hρ (hnn i) (h1 i) (h2 i)
        (ht1 i) (ht2 i)) (hπ i)
  -- concavity of the square root: weighted roots below the root of
  -- the weighted average
  have hDnn : ∀ i, (0:ℝ) ≤ ∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂(ν i) :=
    fun i => integral_nonneg fun p => sq_nonneg _
  have hCSsq : (∑ i, π i *
      Real.sqrt (∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂(ν i))) ^ 2 ≤
      ∑ i, π i * ∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂(ν i) := by
    have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (r := fun i => π i *
        Real.sqrt (∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂(ν i)))
      (f := π)
      (g := fun i => π i * ∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂(ν i))
      (fun i _ => hπ i) (fun i _ => mul_nonneg (hπ i) (hDnn i))
      (fun i _ => by
        rw [mul_pow, Real.sq_sqrt (hDnn i)]
        exact le_of_eq (by ring))
    rwa [hπ1, one_mul] at h
  have hCS : (∑ i, π i *
      Real.sqrt (∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂(ν i))) ≤
      Real.sqrt (∑ i, π i * ∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂(ν i)) := by
    have hnnsum : (0:ℝ) ≤ ∑ i, π i *
        Real.sqrt (∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂(ν i)) :=
      Finset.sum_nonneg fun i _ =>
        mul_nonneg (hπ i) (Real.sqrt_nonneg _)
    calc (∑ i, π i *
        Real.sqrt (∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂(ν i)))
        = Real.sqrt ((∑ i, π i *
            Real.sqrt (∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂(ν i))) ^ 2) :=
          (Real.sqrt_sq hnnsum).symm
      _ ≤ Real.sqrt (∑ i, π i *
            ∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂(ν i)) :=
          Real.sqrt_le_sqrt hCSsq
  -- expand the weighted bound and close
  have hexp : (∑ i, π i * (100 *
      ((∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂(ν i)) +
        Real.sqrt (∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂(ν i)) / α +
        ρ + L ^ 2))) =
      100 * (∑ i, π i * ∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂(ν i)) +
        100 / α * (∑ i, π i *
          Real.sqrt (∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂(ν i))) +
        100 * ρ * (∑ i, π i) + 100 * L ^ 2 * (∑ i, π i) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hfinal : (∑ i, π i * (100 *
      ((∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂(ν i)) +
        Real.sqrt (∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂(ν i)) / α +
        ρ + L ^ 2))) ≤
      100 * ((∑ i, π i * ∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂(ν i)) +
        Real.sqrt
          (∑ i, π i * ∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂(ν i)) / α +
        ρ + L ^ 2) := by
    rw [hexp, hπ1]
    have hmul2 : 100 / α * (∑ i, π i *
        Real.sqrt (∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂(ν i))) ≤
        100 * (Real.sqrt
          (∑ i, π i * ∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂(ν i)) / α) := by
      calc 100 / α * (∑ i, π i *
            Real.sqrt (∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂(ν i)))
          ≤ 100 / α * Real.sqrt
              (∑ i, π i * ∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂(ν i)) :=
            mul_le_mul_of_nonneg_left hCS
              (by positivity : (0:ℝ) ≤ 100 / α)
        _ = 100 * (Real.sqrt
              (∑ i, π i * ∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂(ν i)) / α) :=
            by ring
    linarith [hmul2]
  calc (∑ i, π i * gridGamma (ν i) (1 + α) θ₀ L H)
      ≤ ∫ θ in Set.Ico (0:ℝ) 1,
          ∑ i, π i * gridGamma (ν i) (1 + α) θ L H := hle'
    _ = ∑ i, π i * ∫ θ in Set.Ico (0:ℝ) 1,
          gridGamma (ν i) (1 + α) θ L H := hswap
    _ ≤ ∑ i, π i * (100 *
          ((∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂(ν i)) +
            Real.sqrt (∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂(ν i)) / α +
            ρ + L ^ 2)) := hwsum
    _ ≤ 100 * ((∑ i, π i * ∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂(ν i)) +
          Real.sqrt
            (∑ i, π i * ∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂(ν i)) / α +
          ρ + L ^ 2) := hfinal


end CommutingRepetition

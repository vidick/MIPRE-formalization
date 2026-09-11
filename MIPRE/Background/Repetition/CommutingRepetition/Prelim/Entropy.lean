/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Prelim/Entropy.lean
-/
/-
# Entropy helpers and finite Pinsker

Ported from `QuantumParallelRepetition.lean` (github.com/openai/ten-proofs,
Apache-2.0; see lean/NOTICE), lines 1183-1388 and 10226-10613, with the outer namespace renamed.
Classical/scalar material only; no quantum layer is imported.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Prelim.FiniteProb

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

noncomputable section

open scoped BigOperators

variable {ι : Type*}

theorem negMulLog_rescale
    {W p : ℝ} (hW : 0 < W) (hp : 0 < p) :
    W * Real.negMulLog (p / W) = p * Real.log (W / p) := by
  unfold Real.negMulLog
  rw [Real.log_div hp.ne' hW.ne', Real.log_div hW.ne' hp.ne']
  field_simp
  ring

theorem finite_weighted_entropy_le
    (s : Finset ι) (w h : ι → ℝ) {W p : ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hh : ∀ i ∈ s, 0 ≤ h i)
    (hW : 0 < W)
    (hp : 0 < p)
    (hw_sum : (∑ i ∈ s, w i) = W)
    (hp_sum : (∑ i ∈ s, w i * h i) = p) :
    (∑ i ∈ s, w i * Real.negMulLog (h i))
      ≤ p * Real.log (W / p) := by
  classical
  have h_normalized :
      (∑ i ∈ s, w i / W) = 1 := by
    calc
      (∑ i ∈ s, w i / W) = (∑ i ∈ s, w i) / W := by
        rw [Finset.sum_div]
      _ = W / W := by rw [hw_sum]
      _ = 1 := div_self hW.ne'
  have h_mean :
      (∑ i ∈ s, (w i / W) * h i) = p / W := by
    calc
      (∑ i ∈ s, (w i / W) * h i) =
          ∑ i ∈ s, (w i * h i) / W := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = (∑ i ∈ s, w i * h i) / W := by
            rw [Finset.sum_div]
      _ = p / W := by rw [hp_sum]
  have h_jensen :
      (∑ i ∈ s, (w i / W) * Real.negMulLog (h i))
        ≤ Real.negMulLog (∑ i ∈ s, (w i / W) * h i) := by
    simpa only [smul_eq_mul] using
      (Real.concaveOn_negMulLog.le_map_sum
        (t := s) (w := fun i => w i / W) (p := h)
        (fun i hi => div_nonneg (hw i hi) hW.le)
        h_normalized
        (fun i hi => show h i ∈ Set.Ici (0 : ℝ) from hh i hi))
  calc
    (∑ i ∈ s, w i * Real.negMulLog (h i)) =
        W * (∑ i ∈ s, (w i / W) * Real.negMulLog (h i)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          field_simp
    _ ≤ W * Real.negMulLog (∑ i ∈ s, (w i / W) * h i) :=
          mul_le_mul_of_nonneg_left h_jensen hW.le
    _ = W * Real.negMulLog (p / W) := by rw [h_mean]
    _ = p * Real.log (W / p) := negMulLog_rescale hW hp

theorem finite_weighted_entropy_le_of_weight_bound
    (s : Finset ι) (w h : ι → ℝ) {W N p : ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hh : ∀ i ∈ s, 0 ≤ h i)
    (hW : 0 < W)
    (hp : 0 < p)
    (hw_sum : (∑ i ∈ s, w i) = W)
    (hp_sum : (∑ i ∈ s, w i * h i) = p)
    (hWN : W ≤ N) :
    (∑ i ∈ s, w i * Real.negMulLog (h i))
      ≤ p * Real.log (N / p) := by
  have hquot : W / p ≤ N / p := by
    exact (div_le_div_iff_of_pos_right hp).mpr hWN
  have hlog : Real.log (W / p) ≤ Real.log (N / p) :=
    Real.log_le_log (div_pos hW hp) hquot
  exact
    (finite_weighted_entropy_le s w h hw hh hW hp hw_sum hp_sum).trans
      (mul_le_mul_of_nonneg_left hlog hp.le)

end

noncomputable section

open scoped BigOperators

theorem noncommutative_resolvent_identity
    {R : Type*} [Ring R]
    (F M S RF RM : R)
    (hF : RF * (F + S) = 1)
    (hM : (M + S) * RM = 1) :
    RF - RM = RF * (M - F) * RM := by
  calc
    RF - RM = RF * ((M + S) * RM) - (RF * (F + S)) * RM := by
      rw [hM, hF]
      simp
    _ = RF * (M - F) * RM := by
      noncomm_ring

theorem noncommutative_filtered_resolvent_identity
    {R : Type*} [Ring R]
    (F M S RF RM : R)
    (hF_left : (F + S) * RF = 1)
    (hF_right : RF * (F + S) = 1)
    (hM_left : (M + S) * RM = 1) :
    F * RF - M * RM = S * (RF * (F - M) * RM) := by
  have hFR : F * RF = 1 - S * RF := by
    have h : F * RF + S * RF = 1 := by
      simpa [add_mul] using hF_left
    exact eq_sub_of_add_eq h
  have hMR : M * RM = 1 - S * RM := by
    have h : M * RM + S * RM = 1 := by
      simpa [add_mul] using hM_left
    exact eq_sub_of_add_eq h
  have hdiff : RM - RF = RF * (F - M) * RM := by
    calc
      RM - RF = -(RF - RM) := by noncomm_ring
      _ = -(RF * (M - F) * RM) := by
        rw [noncommutative_resolvent_identity F M S RF RM hF_right hM_left]
      _ = RF * (F - M) * RM := by noncomm_ring
  rw [hFR, hMR]
  calc
    (1 - S * RF) - (1 - S * RM) = S * (RM - RF) := by
      noncomm_ring
    _ = S * (RF * (F - M) * RM) := by rw [hdiff]

theorem noncommutative_resolvent_second_order
    {R : Type*} [Ring R]
    (F M S RF RM : R)
    (hF_left : (F + S) * RF = 1)
    (hF_right : RF * (F + S) = 1)
    (hM_left : (M + S) * RM = 1)
    (hM_right : RM * (M + S) = 1) :
    RF = RM - RM * (F - M) * RM +
      RM * (F - M) * RF * (F - M) * RM := by
  have hleft : RM - RF = RM * (F - M) * RF :=
    noncommutative_resolvent_identity M F S RM RF hM_right hF_left
  have hright : RF - RM = RF * (M - F) * RM :=
    noncommutative_resolvent_identity F M S RF RM hF_right hM_left
  have hfirst : RF = RM - RM * (F - M) * RF := by
    calc
      RF = RM - (RM - RF) := by noncomm_ring
      _ = RM - RM * (F - M) * RF := by rw [hleft]
  have hsecond : RF = RM - RF * (F - M) * RM := by
    calc
      RF = RM + (RF - RM) := by noncomm_ring
      _ = RM + RF * (M - F) * RM := by rw [hright]
      _ = RM - RF * (F - M) * RM := by noncomm_ring
  calc
    RF = RM - RM * (F - M) * RF := hfirst
    _ = RM - RM * (F - M) *
      (RM - RF * (F - M) * RM) := by rw [← hsecond]
    _ = RM - RM * (F - M) * RM +
      RM * (F - M) * RF * (F - M) * RM := by noncomm_ring

theorem noncommutative_weighted_resolvent_second_order
    {ι R : Type*} [Fintype ι] [Ring R]
    (weight : ι → R) (F : ι → R) (M S : R)
    (RF : ι → R) (RM : R)
    (normalized : (∑ i : ι, weight i) = 1)
    (centered : (∑ i : ι, weight i * (F i - M)) = 0)
    (commute_mean : ∀ i, weight i * RM = RM * weight i)
    (hF_left : ∀ i, (F i + S) * RF i = 1)
    (hF_right : ∀ i, RF i * (F i + S) = 1)
    (hM_left : (M + S) * RM = 1)
    (hM_right : RM * (M + S) = 1) :
    (∑ i : ι, weight i * RF i) - RM =
      RM * (∑ i : ι,
        weight i * ((F i - M) * RF i * (F i - M))) * RM := by
  have hterm (i : ι) :
      weight i * RF i =
        weight i * RM - RM * (weight i * (F i - M)) * RM +
          RM * (weight i * ((F i - M) * RF i * (F i - M))) * RM := by
    nth_rewrite 1 [noncommutative_resolvent_second_order
      (F i) M S (RF i) RM (hF_left i) (hF_right i) hM_left hM_right]
    have hw := commute_mean i
    calc
      weight i *
        (RM - RM * (F i - M) * RM +
          RM * (F i - M) * RF i * (F i - M) * RM) =
        weight i * RM -
          (weight i * RM) * (F i - M) * RM +
          (weight i * RM) * ((F i - M) * RF i * (F i - M)) * RM := by
            noncomm_ring
      _ = weight i * RM -
          (RM * weight i) * (F i - M) * RM +
          (RM * weight i) * ((F i - M) * RF i * (F i - M)) * RM := by
            rw [hw]
      _ = weight i * RM - RM * (weight i * (F i - M)) * RM +
          RM * (weight i * ((F i - M) * RF i * (F i - M))) * RM := by
            noncomm_ring
  calc
    (∑ i : ι, weight i * RF i) - RM =
        (∑ i : ι,
          (weight i * RM - RM * (weight i * (F i - M)) * RM +
            RM * (weight i * ((F i - M) * RF i * (F i - M))) * RM)) - RM := by
              congr 1
              exact Finset.sum_congr rfl (fun i _ => hterm i)
    _ = (∑ i : ι, weight i) * RM -
          RM * (∑ i : ι, weight i * (F i - M)) * RM +
          RM * (∑ i : ι,
            weight i * ((F i - M) * RF i * (F i - M))) * RM - RM := by
              simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
                ← Finset.sum_mul, ← Finset.mul_sum]
    _ = RM * (∑ i : ι,
          weight i * ((F i - M) * RF i * (F i - M))) * RM := by
            rw [normalized, centered]
            noncomm_ring


namespace Pinsker

theorem centered_log_lower_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    2 * (x - 1) / (x + 1) ≤ Real.log x := by
  have hden : 0 < x + 1 := by linarith
  let t : ℝ := (x - 1) / (x + 1)
  have ht0 : 0 ≤ t := by
    exact div_nonneg (sub_nonneg.mpr hx) hden.le
  have ht1 : t < 1 := by
    apply (div_lt_one hden).mpr
    linarith
  have hratio : (1 + t) / (1 - t) = x := by
    dsimp [t]
    field_simp
    ring
  have hseries :
      t ≤ (1 / 2 : ℝ) * Real.log ((1 + t) / (1 - t)) := by
    simpa using (Real.sum_range_le_log_div ht0 ht1 1)
  rw [hratio] at hseries
  dsimp [t] at hseries
  calc
    2 * (x - 1) / (x + 1) = 2 * ((x - 1) / (x + 1)) := by ring
    _ ≤ Real.log x := by linarith

theorem centered_log_upper_of_le_one
    {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    Real.log x ≤ 2 * (x - 1) / (x + 1) := by
  have hinv : 1 ≤ (1 : ℝ) / x := by
    apply (le_div_iff₀ hx0).mpr
    simpa using hx1
  have h := centered_log_lower_of_one_le hinv
  have hratio :
      2 * ((1 : ℝ) / x - 1) / ((1 : ℝ) / x + 1) =
        -(2 * (x - 1) / (x + 1)) := by
    field_simp
    ring
  rw [hratio, Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hx0.ne',
    Real.log_one] at h
  linarith

def pinskerScalarGap (x : ℝ) : ℝ :=
  InformationTheory.klFun x - 3 * (x - 1) ^ 2 / (2 * (x + 2))

theorem hasDerivAt_pinskerScalarGap {x : ℝ} (hx : 0 < x) :
    HasDerivAt pinskerScalarGap
      (Real.log x - 3 * (x - 1) * (x + 5) / (2 * (x + 2) ^ 2)) x := by
  have hden : 2 * (x + 2) ≠ 0 := by positivity
  have hnumerator :=
    (((hasDerivAt_id x).sub_const 1).pow 2).const_mul 3
  have hdenominator :=
    ((hasDerivAt_id x).add_const 2).const_mul 2
  have hquotient := hnumerator.div hdenominator hden
  have hgap := (InformationTheory.hasDerivAt_klFun hx.ne').sub hquotient
  have hfunction :
      (InformationTheory.klFun -
        (fun y => 3 * ((fun z => id z - 1) ^ 2) y) /
          (fun y => 2 * (id y + 2))) = pinskerScalarGap := by
    funext y
    change
      InformationTheory.klFun y - 3 * (y - 1) ^ 2 / (2 * (y + 2)) =
        InformationTheory.klFun y - 3 * (y - 1) ^ 2 / (2 * (y + 2))
    rfl
  rw [hfunction] at hgap
  apply hgap.congr_deriv
  dsimp
  field_simp
  ring

theorem pinsker_rational_coefficient_le {x : ℝ} (hx : 0 < x) :
    3 * (x + 5) / (2 * (x + 2) ^ 2) ≤ 2 / (x + 1) := by
  have hleft : 0 < 2 * (x + 2) ^ 2 := by positivity
  have hright : 0 < x + 1 := by linarith
  apply (div_le_div_iff₀ hleft hright).mpr
  nlinarith [sq_nonneg (x - 1)]

theorem pinskerScalarGap_derivative_nonneg
    {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ Real.log x -
      3 * (x - 1) * (x + 5) / (2 * (x + 2) ^ 2) := by
  have hx0 : 0 < x := by linarith
  have hcoefficient := pinsker_rational_coefficient_le hx0
  have hscaled := mul_le_mul_of_nonneg_left
    hcoefficient (sub_nonneg.mpr hx)
  have hrational :
      3 * (x - 1) * (x + 5) / (2 * (x + 2) ^ 2) ≤
        2 * (x - 1) / (x + 1) := by
    calc
      3 * (x - 1) * (x + 5) / (2 * (x + 2) ^ 2) =
          (x - 1) * (3 * (x + 5) / (2 * (x + 2) ^ 2)) := by ring
      _ ≤ (x - 1) * (2 / (x + 1)) := hscaled
      _ = 2 * (x - 1) / (x + 1) := by ring
  have hlog := centered_log_lower_of_one_le hx
  linarith

theorem pinskerScalarGap_derivative_nonpos
    {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    Real.log x -
      3 * (x - 1) * (x + 5) / (2 * (x + 2) ^ 2) ≤ 0 := by
  have hcoefficient := pinsker_rational_coefficient_le hx0
  have hscaled := mul_le_mul_of_nonpos_left
    hcoefficient (sub_nonpos.mpr hx1)
  have hrational :
      2 * (x - 1) / (x + 1) ≤
        3 * (x - 1) * (x + 5) / (2 * (x + 2) ^ 2) := by
    calc
      2 * (x - 1) / (x + 1) = (x - 1) * (2 / (x + 1)) := by ring
      _ ≤ (x - 1) * (3 * (x + 5) / (2 * (x + 2) ^ 2)) := hscaled
      _ = 3 * (x - 1) * (x + 5) / (2 * (x + 2) ^ 2) := by ring
  have hlog := centered_log_upper_of_le_one hx0 hx1
  linarith

theorem pinskerScalarGap_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ pinskerScalarGap x := by
  by_cases hzero : x = 0
  · subst x
    norm_num [pinskerScalarGap, InformationTheory.klFun]
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hzero)
  by_cases hone : 1 ≤ x
  · let derivative : ℝ → ℝ := fun y =>
      Real.log y - 3 * (y - 1) * (y + 5) / (2 * (y + 2) ^ 2)
    have hcontinuous : ContinuousOn pinskerScalarGap (Set.Icc 1 x) := by
      intro y hy
      have hypos : 0 < y := by
        have hyone := (Set.mem_Icc.mp hy).1
        linarith
      exact (hasDerivAt_pinskerScalarGap hypos).continuousAt.continuousWithinAt
    have hmonotone : MonotoneOn pinskerScalarGap (Set.Icc 1 x) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg
        (f' := derivative) (convex_Icc 1 x) hcontinuous
      · intro y hy
        have hymem : y ∈ Set.Icc (1 : ℝ) x := interior_subset hy
        have hypos : 0 < y := by
          have hyone := (Set.mem_Icc.mp hymem).1
          linarith
        exact (hasDerivAt_pinskerScalarGap hypos).hasDerivWithinAt
      · intro y hy
        have hymem : y ∈ Set.Icc (1 : ℝ) x := interior_subset hy
        exact pinskerScalarGap_derivative_nonneg (Set.mem_Icc.mp hymem).1
    have hbound := hmonotone
      (show (1 : ℝ) ∈ Set.Icc 1 x from ⟨le_rfl, hone⟩)
      (show x ∈ Set.Icc (1 : ℝ) x from ⟨hone, le_rfl⟩) hone
    simpa [pinskerScalarGap, InformationTheory.klFun] using hbound
  · have hxone : x ≤ 1 := le_of_not_ge hone
    let derivative : ℝ → ℝ := fun y =>
      Real.log y - 3 * (y - 1) * (y + 5) / (2 * (y + 2) ^ 2)
    have hcontinuous : ContinuousOn pinskerScalarGap (Set.Icc x 1) := by
      intro y hy
      have hypos : 0 < y :=
        hxpos.trans_le (Set.mem_Icc.mp hy).1
      exact (hasDerivAt_pinskerScalarGap hypos).continuousAt.continuousWithinAt
    have hantitone : AntitoneOn pinskerScalarGap (Set.Icc x 1) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos
        (f' := derivative) (convex_Icc x 1) hcontinuous
      · intro y hy
        have hymem : y ∈ Set.Icc x (1 : ℝ) := interior_subset hy
        have hypos : 0 < y := hxpos.trans_le (Set.mem_Icc.mp hymem).1
        exact (hasDerivAt_pinskerScalarGap hypos).hasDerivWithinAt
      · intro y hy
        have hymem : y ∈ Set.Icc x (1 : ℝ) := interior_subset hy
        have hypos : 0 < y := hxpos.trans_le (Set.mem_Icc.mp hymem).1
        exact pinskerScalarGap_derivative_nonpos
          hypos (Set.mem_Icc.mp hymem).2
    have hbound := hantitone
      (show x ∈ Set.Icc x (1 : ℝ) from ⟨le_rfl, hxone⟩)
      (show (1 : ℝ) ∈ Set.Icc x 1 from ⟨hxone, le_rfl⟩) hxone
    simpa [pinskerScalarGap, InformationTheory.klFun] using hbound

theorem quadratic_le_klFun {x : ℝ} (hx : 0 ≤ x) :
    3 * (x - 1) ^ 2 / (2 * (x + 2)) ≤ InformationTheory.klFun x := by
  have h := pinskerScalarGap_nonneg hx
  dsimp [pinskerScalarGap] at h
  linarith

def finiteRelativeEntropy {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) : ℝ :=
  ∑ i, q i * InformationTheory.klFun (p i / q i)

def finiteTotalVariation {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) : ℝ :=
  (∑ i, |p i - q i|) / 2

theorem quadratic_density_le_weighted_kl
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    3 * (p - q) ^ 2 / (2 * (p + 2 * q)) ≤
      q * InformationTheory.klFun (p / q) := by
  have hscalar := quadratic_le_klFun (div_nonneg hp hq.le)
  have hweighted := mul_le_mul_of_nonneg_left hscalar hq.le
  calc
    3 * (p - q) ^ 2 / (2 * (p + 2 * q)) =
        q * (3 * (p / q - 1) ^ 2 / (2 * (p / q + 2))) := by
      field_simp [hq.ne']
    _ ≤ q * InformationTheory.klFun (p / q) := hweighted

theorem finiteRelativeEntropy_eq_log_sum
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ)
    (hq : ∀ i, 0 < q i)
    (hp_normalized : (∑ i, p i) = 1)
    (hq_normalized : (∑ i, q i) = 1) :
    finiteRelativeEntropy p q =
      ∑ i, p i * Real.log (p i / q i) := by
  unfold finiteRelativeEntropy
  calc
    (∑ i, q i * InformationTheory.klFun (p i / q i)) =
        ∑ i, (p i * Real.log (p i / q i) + q i - p i) := by
      apply Finset.sum_congr rfl
      intro i _
      unfold InformationTheory.klFun
      field_simp [(hq i).ne']
    _ = ∑ i, p i * Real.log (p i / q i) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        hp_normalized, hq_normalized]
      ring

theorem finite_pinsker
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hq : ∀ i, 0 < q i)
    (hp_normalized : (∑ i, p i) = 1)
    (hq_normalized : (∑ i, q i) = 1) :
    2 * (finiteTotalVariation p q) ^ 2 ≤ finiteRelativeEntropy p q := by
  classical
  let weight : ι → ℝ := fun i => (p i + 2 * q i) / 3
  have hweight : ∀ i, 0 < weight i := by
    intro i
    dsimp [weight]
    have hpi := hp i
    have hqi := hq i
    positivity
  have hweight_sum : (∑ i, weight i) = 1 := by
    dsimp [weight]
    calc
      (∑ i, (p i + 2 * q i) / 3) =
          ((∑ i, p i) + 2 * (∑ i, q i)) / 3 := by
        rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = 1 := by rw [hp_normalized, hq_normalized]; norm_num
  have hcauchy :
      (∑ i, |p i - q i|) ^ 2 ≤
        ∑ i, |p i - q i| ^ 2 / weight i := by
    have h := Finset.sq_sum_div_le_sum_sq_div
      (Finset.univ : Finset ι)
      (fun i => |p i - q i|)
      (g := weight)
      (fun i _ => hweight i)
    simpa [hweight_sum] using h
  have hpoint : ∀ i,
      |p i - q i| ^ 2 / weight i ≤
        2 * (q i * InformationTheory.klFun (p i / q i)) := by
    intro i
    have hdensity := quadratic_density_le_weighted_kl (hp i) (hq i)
    calc
      |p i - q i| ^ 2 / weight i =
          2 * (3 * (p i - q i) ^ 2 /
            (2 * (p i + 2 * q i))) := by
        dsimp [weight]
        rw [sq_abs]
        have hden : p i + 2 * q i ≠ 0 := by
          have hpi := hp i
          have hqi := hq i
          positivity
        field_simp [hden]
      _ ≤ 2 * (q i * InformationTheory.klFun (p i / q i)) :=
        mul_le_mul_of_nonneg_left hdensity (by norm_num)
  have hsum :
      (∑ i, |p i - q i| ^ 2 / weight i) ≤
        2 * finiteRelativeEntropy p q := by
    calc
      (∑ i, |p i - q i| ^ 2 / weight i) ≤
          ∑ i, 2 * (q i * InformationTheory.klFun (p i / q i)) :=
        Finset.sum_le_sum fun i _ => hpoint i
      _ = 2 * finiteRelativeEntropy p q := by
        unfold finiteRelativeEntropy
        rw [Finset.mul_sum]
  have hmain :
      (∑ i, |p i - q i|) ^ 2 ≤ 2 * finiteRelativeEntropy p q :=
    hcauchy.trans hsum
  unfold finiteTotalVariation
  nlinarith

theorem sum_over_positive_reference_support
    {ι : Type*} [Fintype ι]
    (q f : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i)
    (hzero : ∀ i, q i = 0 → f i = 0) :
    (∑ i : {i : ι // 0 < q i}, f i) = ∑ i, f i := by
  classical
  calc
    (∑ i : {i : ι // 0 < q i}, f i) =
        ∑ i ∈ (Finset.univ.filter fun i : ι => 0 < q i), f i := by
      simpa using
        (Finset.sum_subtype_eq_sum_filter
          (s := (Finset.univ : Finset ι))
          (p := fun i : ι => 0 < q i) f)
    _ = ∑ i, f i := by
      apply Finset.sum_filter_of_ne
      intro i _ hfi
      have hqi : q i ≠ 0 := by
        intro hqi
        exact hfi (hzero i hqi)
      exact lt_of_le_of_ne (hq i) hqi.symm

theorem finite_pinsker_of_absolute_continuity
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hq : ∀ i, 0 ≤ q i)
    (absolute_continuity : ∀ i, q i = 0 → p i = 0)
    (hp_normalized : (∑ i, p i) = 1)
    (hq_normalized : (∑ i, q i) = 1) :
    2 * (finiteTotalVariation p q) ^ 2 ≤ finiteRelativeEntropy p q := by
  classical
  let p' : {i : ι // 0 < q i} → ℝ := fun i => p i
  let q' : {i : ι // 0 < q i} → ℝ := fun i => q i
  have hp'_nonnegative : ∀ i, 0 ≤ p' i := fun i => hp i
  have hq'_positive : ∀ i, 0 < q' i := fun i => i.property
  have hp'_normalized : (∑ i, p' i) = 1 := by
    change (∑ i : {i : ι // 0 < q i}, p i) = 1
    rw [sum_over_positive_reference_support q p hq absolute_continuity,
      hp_normalized]
  have hq'_normalized : (∑ i, q' i) = 1 := by
    change (∑ i : {i : ι // 0 < q i}, q i) = 1
    rw [sum_over_positive_reference_support q q hq (fun _ h => h),
      hq_normalized]
  have htv : finiteTotalVariation p' q' = finiteTotalVariation p q := by
    unfold finiteTotalVariation
    change
      (∑ i : {i : ι // 0 < q i}, |p i - q i|) / 2 =
        (∑ i, |p i - q i|) / 2
    rw [sum_over_positive_reference_support
      q (fun i => |p i - q i|) hq]
    intro i hqi
    simp [hqi, absolute_continuity i hqi]
  have hkl : finiteRelativeEntropy p' q' = finiteRelativeEntropy p q := by
    unfold finiteRelativeEntropy
    change
      (∑ i : {i : ι // 0 < q i},
        q i * InformationTheory.klFun (p i / q i)) =
      ∑ i, q i * InformationTheory.klFun (p i / q i)
    apply sum_over_positive_reference_support
      q (fun i => q i * InformationTheory.klFun (p i / q i)) hq
    intro i hqi
    simp [hqi]
  have h := finite_pinsker p' q'
    hp'_nonnegative hq'_positive hp'_normalized hq'_normalized
  rwa [htv, hkl] at h

theorem finiteRelativeEntropy_eq_log_sum_of_absolute_continuity
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i)
    (absolute_continuity : ∀ i, q i = 0 → p i = 0)
    (hp_normalized : (∑ i, p i) = 1)
    (hq_normalized : (∑ i, q i) = 1) :
    finiteRelativeEntropy p q =
      ∑ i, p i * Real.log (p i / q i) := by
  unfold finiteRelativeEntropy
  calc
    (∑ i, q i * InformationTheory.klFun (p i / q i)) =
        ∑ i, (p i * Real.log (p i / q i) + q i - p i) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hqi : q i = 0
      · simp [hqi, absolute_continuity i hqi]
      · unfold InformationTheory.klFun
        have hqpos : 0 < q i := lt_of_le_of_ne (hq i) (Ne.symm hqi)
        field_simp [hqpos.ne']
    _ = ∑ i, p i * Real.log (p i / q i) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        hp_normalized, hq_normalized]
      ring

theorem finite_pinsker_sqrt_of_absolute_continuity
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hq : ∀ i, 0 ≤ q i)
    (absolute_continuity : ∀ i, q i = 0 → p i = 0)
    (hp_normalized : (∑ i, p i) = 1)
    (hq_normalized : (∑ i, q i) = 1) :
    finiteTotalVariation p q ≤
      Real.sqrt (finiteRelativeEntropy p q / 2) := by
  apply Real.le_sqrt_of_sq_le
  have h := finite_pinsker_of_absolute_continuity
    p q hp hq absolute_continuity hp_normalized hq_normalized
  nlinarith

end Pinsker

end

end CommutingRepetition

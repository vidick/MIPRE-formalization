/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Resolver/ResolverKernel.lean
-/
/-
# The resolver Gram kernel (node 1.2.6.3, kernel level)

For positive contractions `F, G` in a C*-algebra the **Gram kernel** of the
manuscript's resolver columns `u ↦ F(F+u)⁻¹` is the Bochner integral

    kern F G := ∫ u in (0,∞), fib F u * fib G u,     fib F u = F (F+u)⁻¹.

This file proves what the entropic arena (node 1.2.6) needs from it:

* integrability, and the two-cutoff limit
  `∫ u in αₙ..Tₙ, fib F u * fib G u → kern F G` (`αₙ = 1/(n+1)`, `Tₙ = n+1`);
* `kern_self : kern F F = F` and `kern_star : star (kern F G) = kern G F`;
* positivity of operator-valued (interval) integrals with positive integrand
  (the positive cone is closed and convex);
* the **kernel entropy inequality** (`kern_entropy_le`): for weights `wₖ ≥ 0`
  with `∑ wₖ Fₖ = W F̄`,

      ∑ₖ wₖ (K(Fₖ,Fₖ) − K(Fₖ,F̄) − K(F̄,Fₖ) + K(F̄,F̄))
        ≤ W • negMulLog(F̄) − ∑ₖ wₖ • negMulLog(Fₖ),

  by integrating the pointwise bound of node 1.2.6.2 over `[αₙ, Tₙ]`,
  evaluating the right side through `Resolver/CfcIntegral.lean`, and passing
  to the limit (the Loewner order is closed).

Nothing here is a manuscript statement (proof-side helpers for node 1.2.6).
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Resolver.CfcIntegral

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace Resolver

open scoped BigOperators Topology
open MeasureTheory intervalIntegral Filter Set

set_option linter.unusedSectionVars false

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-! ## Cutoff sequences -/

/-- Lower cutoff `αₙ = 1/(n+1)`. -/
noncomputable def αseq (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

/-- Upper cutoff `Tₙ = n + 1`. -/
noncomputable def Tseq (n : ℕ) : ℝ := (n : ℝ) + 1

theorem αseq_pos (n : ℕ) : 0 < αseq n := by unfold αseq; positivity

theorem Tseq_pos (n : ℕ) : 0 < Tseq n := by unfold Tseq; positivity

theorem αseq_le_Tseq (n : ℕ) : αseq n ≤ Tseq n := by
  unfold αseq Tseq
  have h : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  calc 1 / ((n : ℝ) + 1) ≤ 1 / 1 := one_div_le_one_div_of_le one_pos h
    _ = 1 := by norm_num
    _ ≤ (n : ℝ) + 1 := h

theorem inv_Tseq (n : ℕ) : (Tseq n)⁻¹ = αseq n := by
  unfold αseq Tseq; rw [one_div]

theorem uIcc_subset_Ioi (n : ℕ) : Set.uIcc (αseq n) (Tseq n) ⊆ Set.Ioi 0 := fun _ hu =>
  lt_of_lt_of_le (lt_min (αseq_pos n) (Tseq_pos n)) hu.1

theorem tendsto_αseq : Tendsto αseq atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat

theorem tendsto_Tseq : Tendsto Tseq atTop atTop :=
  tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds

theorem tendsto_αseq_add_inv_Tseq : Tendsto (fun n => αseq n + (Tseq n)⁻¹) atTop (𝓝 0) := by
  simp_rw [inv_Tseq]
  simpa using tendsto_αseq.add tendsto_αseq

/-! ## Improper integrals as cutoff limits -/

/-- For `f` integrable on `(0, ∞)`, the interval integrals over `[αₙ, Tₙ]` converge to the
integral over `(0, ∞)`. -/
theorem tendsto_intervalIntegral_cutoff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : IntegrableOn f (Set.Ioi 0)) :
    Tendsto (fun n => ∫ u in αseq n..Tseq n, f u) atTop (𝓝 (∫ u in Set.Ioi 0, f u)) := by
  have hcov : AECover (volume.restrict (Set.Ioi 0)) atTop
      (fun n => Set.Ioc (αseq n) (Tseq n)) := by
    refine ⟨?_, fun n => measurableSet_Ioc⟩
    refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_
    have h1 : ∀ᶠ n in atTop, αseq n < x := tendsto_αseq.eventually (eventually_lt_nhds hx)
    have h2 : ∀ᶠ n in atTop, x ≤ Tseq n := tendsto_Tseq.eventually_ge_atTop x
    exact h1.and h2
  have h := hcov.integral_tendsto_of_countably_generated hf
  refine h.congr fun n => ?_
  rw [Measure.restrict_restrict measurableSet_Ioc,
    Set.inter_eq_left.mpr (Set.Ioc_subset_Ioi_self.trans (Set.Ioi_subset_Ioi (αseq_pos n).le)),
    intervalIntegral.integral_of_le (αseq_le_Tseq n)]

/-! ## Positivity of operator-valued integrals -/

theorem convex_nonneg : Convex ℝ (Set.Ici (0 : A)) := by
  intro x hx y hy a b ha hb _
  exact add_nonneg (smul_nonneg_of_nonneg ha hx) (smul_nonneg_of_nonneg hb hy)

/-- A set integral of a positive integrand over a set of finite measure is positive. -/
theorem setIntegral_nonneg_of_nonneg {f : ℝ → A} {s : Set ℝ} (hs : MeasurableSet s)
    (hfin : volume s ≠ ⊤) (hf : IntegrableOn f s) (hpos : ∀ u ∈ s, 0 ≤ f u) :
    0 ≤ ∫ u in s, f u := by
  by_cases h0 : volume s = 0
  · rw [Measure.restrict_eq_zero.mpr h0, integral_zero_measure]
  · have hav := convex_nonneg.set_average_mem isClosed_Ici h0 hfin
      (ae_restrict_of_forall_mem hs hpos) hf
    rw [setAverage_eq] at hav
    have hne : volume.real s ≠ 0 := by
      rw [measureReal_def]; exact ENNReal.toReal_ne_zero.mpr ⟨h0, hfin⟩
    have : ∫ u in s, f u = volume.real s • ((volume.real s)⁻¹ • ∫ u in s, f u) := by
      rw [smul_smul, mul_inv_cancel₀ hne, one_smul]
    rw [this]
    exact smul_nonneg_of_nonneg measureReal_nonneg hav

theorem intervalIntegral_nonneg_of_nonneg {f : ℝ → A} {a b : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b) (hpos : ∀ u ∈ Set.Ioc a b, 0 ≤ f u) :
    0 ≤ ∫ u in a..b, f u := by
  rw [intervalIntegral.integral_of_le hab]
  refine setIntegral_nonneg_of_nonneg measurableSet_Ioc ?_
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hf) hpos
  rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top

theorem intervalIntegral_mono_of_le {f g : ℝ → A} {a b : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b)
    (h : ∀ u ∈ Set.Ioc a b, f u ≤ g u) : ∫ u in a..b, f u ≤ ∫ u in a..b, g u := by
  rw [← sub_nonneg, ← intervalIntegral.integral_sub hg hf]
  exact intervalIntegral_nonneg_of_nonneg hab (hg.sub hf) fun u hu => sub_nonneg.mpr (h u hu)

/-! ## The Gram kernel -/

/-- The resolver Gram kernel `∫₀^∞ F(F+u)⁻¹ G(G+u)⁻¹ du`. -/
noncomputable def kern (F G : A) : A := ∫ u in Set.Ioi 0, fib F u * fib G u

theorem continuousOn_fib_mul_fib {F G : A} (hF0 : 0 ≤ F) (hG0 : 0 ≤ G) :
    ContinuousOn (fun u => fib F u * fib G u) (Set.Ioi 0) :=
  (continuousOn_fib_param hF0).mul (continuousOn_fib_param hG0)

theorem intervalIntegrable_fib_mul_fib {F G : A} (hF0 : 0 ≤ F) (hG0 : 0 ≤ G) (n : ℕ) :
    IntervalIntegrable (fun u => fib F u * fib G u) volume (αseq n) (Tseq n) :=
  ((continuousOn_fib_mul_fib hF0 hG0).mono (uIcc_subset_Ioi n)).intervalIntegrable

/-- Integrability of the kernel integrand on `(0, ∞)`: bounded by `1` near `0` and by
`‖F‖ ‖G‖ / u²` at infinity. -/
theorem integrableOn_fib_mul_fib {F G : A} (hF0 : 0 ≤ F) (hG0 : 0 ≤ G) :
    IntegrableOn (fun u => fib F u * fib G u) (Set.Ioi 0) := by
  have hcont := continuousOn_fib_mul_fib hF0 hG0
  rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ)]
  refine IntegrableOn.union ?_ ?_
  · -- on `(0, 1]`: bounded by `1`
    have hmeas : AEStronglyMeasurable (fun u => fib F u * fib G u)
        (volume.restrict (Set.Ioc 0 1)) :=
      (hcont.mono Set.Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc
    refine ⟨hmeas, HasFiniteIntegral.of_bounded (C := 1) ?_⟩
    refine (ae_restrict_mem measurableSet_Ioc).mono fun u hu => ?_
    calc ‖fib F u * fib G u‖ ≤ ‖fib F u‖ * ‖fib G u‖ := norm_mul_le _ _
      _ ≤ 1 * 1 := mul_le_mul (norm_fib_le_one hF0 hu.1) (norm_fib_le_one hG0 hu.1)
            (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · -- on `(1, ∞)`: bounded by `‖F‖ ‖G‖ u⁻²`
    have hmeas : AEStronglyMeasurable (fun u => fib F u * fib G u)
        (volume.restrict (Set.Ioi 1)) :=
      (hcont.mono (Set.Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi
    have hg : IntegrableOn (fun u : ℝ => ‖F‖ * ‖G‖ * u ^ (-2 : ℝ)) (Set.Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul _
    refine Integrable.mono' hg hmeas ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono fun u hu => ?_
    have hu0 : (0 : ℝ) < u := lt_trans zero_lt_one hu
    calc ‖fib F u * fib G u‖ ≤ ‖fib F u‖ * ‖fib G u‖ := norm_mul_le _ _
      _ ≤ (‖F‖ / u) * (‖G‖ / u) := mul_le_mul (norm_fib_le hF0 hu0) (norm_fib_le hG0 hu0)
            (norm_nonneg _) (by positivity)
      _ = ‖F‖ * ‖G‖ * u ^ (-2 : ℝ) := by
            rw [Real.rpow_neg hu0.le, Real.rpow_two]
            field_simp

/-- The cutoff integrals converge to the kernel. -/
theorem tendsto_intervalIntegral_kern {F G : A} (hF0 : 0 ≤ F) (hG0 : 0 ≤ G) :
    Tendsto (fun n => ∫ u in αseq n..Tseq n, fib F u * fib G u) atTop (𝓝 (kern F G)) :=
  tendsto_intervalIntegral_cutoff (integrableOn_fib_mul_fib hF0 hG0)

/-- `K(F, F) = F`. -/
theorem kern_self {F : A} (hF0 : 0 ≤ F) (hF1 : F ≤ 1) : kern F F = F := by
  have h1 := tendsto_intervalIntegral_kern hF0 hF0
  have h2 : Tendsto (fun n => ∫ u in αseq n..Tseq n, fib F u * fib F u) atTop (𝓝 F) := by
    have he : ∀ n, ∫ u in αseq n..Tseq n, fib F u * fib F u
        = cfc (gfun (αseq n) (Tseq n)) F := fun n =>
      integral_fib_mul_fib hF0 (αseq_pos n) (Tseq_pos n)
    simp_rw [he]
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _)
      (fun n => norm_cfc_gfun_sub_le hF0 hF1 (αseq_pos n) (Tseq_pos n))
      tendsto_αseq_add_inv_Tseq
  exact tendsto_nhds_unique h1 h2

/-- `K(F, G)* = K(G, F)`. -/
theorem kern_star (F G : A) : star (kern F G) = kern G F := by
  unfold kern
  have h := ((starL' ℝ : A ≃L[ℝ] A).integral_comp_comm (fun u => fib F u * fib G u)
    (μ := volume.restrict (Set.Ioi 0))).symm
  simp only [starL'_apply] at h
  rw [h]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  show star (fib F u * fib G u) = fib G u * fib F u
  rw [star_mul, (fib_isSelfAdjoint (F := F) (u := u)).star_eq,
    (fib_isSelfAdjoint (F := G) (u := u)).star_eq]

/-! ## The kernel entropy inequality -/

section Entropy

variable {ι : Type*} [Fintype ι]

/-- The entropic correction converges to `−negMulLog(F)` along the cutoffs. -/
theorem tendsto_Ecorr {F : A} (hF0 : 0 ≤ F) (hF1 : F ≤ 1) :
    Tendsto (fun n => Ecorr (αseq n) (Tseq n) F) atTop (𝓝 (-cfc Real.negMulLog F)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) tendsto_αseq_add_inv_Tseq
  rw [sub_neg_eq_add]
  exact norm_Ecorr_add_le hF0 hF1 (αseq_pos n) (Tseq_pos n)

/-- Continuity on `[αₙ, Tₙ]` of the weighted difference-square integrand. -/
theorem continuousOn_diffsq (w : ι → ℝ) (Fs : ι → A) (Fb : A) (hF0 : ∀ i, 0 ≤ Fs i)
    (hFb0 : 0 ≤ Fb) (n : ℕ) :
    ContinuousOn (fun u => ∑ i, w i • ((fib (Fs i) u - fib Fb u) * (fib (Fs i) u - fib Fb u)))
      (Set.uIcc (αseq n) (Tseq n)) := by
  refine continuousOn_finsetSum _ fun i _ => ContinuousOn.const_smul ?_ _
  have hd : ContinuousOn (fun u => fib (Fs i) u - fib Fb u) (Set.uIcc (αseq n) (Tseq n)) :=
    ((continuousOn_fib_param (hF0 i)).sub (continuousOn_fib_param hFb0)).mono
      (uIcc_subset_Ioi n)
  exact hd.mul hd

/-- Continuity on `[αₙ, Tₙ]` of the weighted resolvent integrand. -/
theorem continuousOn_wres (w : ι → ℝ) (Fs : ι → A) (Fb : A) (hF0 : ∀ i, 0 ≤ Fs i)
    (hFb0 : 0 ≤ Fb) (n : ℕ) :
    ContinuousOn (fun u => u • ((∑ i, w i • res (Fs i) u) - (∑ i, w i) • res Fb u))
      (Set.uIcc (αseq n) (Tseq n)) := by
  refine (continuousOn_id' _).smul (ContinuousOn.sub ?_ (ContinuousOn.const_smul ?_ _))
  · exact continuousOn_finsetSum _ fun i _ =>
      ((continuousOn_res_param (hF0 i)).mono (uIcc_subset_Ioi n)).const_smul _
  · exact (continuousOn_res_param hFb0).mono (uIcc_subset_Ioi n)

/-- The integrated pointwise bound (node 1.2.6.2 over `[αₙ, Tₙ]`). -/
theorem integrated_bound (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (Fs : ι → A) (Fb : A)
    (hF0 : ∀ i, 0 ≤ Fs i) (hFb0 : 0 ≤ Fb)
    (hmean : (∑ i, w i • Fs i) = (∑ i, w i) • Fb) (n : ℕ) :
    ∫ u in αseq n..Tseq n, ∑ i, w i • ((fib (Fs i) u - fib Fb u) * (fib (Fs i) u - fib Fb u))
      ≤ ∫ u in αseq n..Tseq n, u • ((∑ i, w i • res (Fs i) u) - (∑ i, w i) • res Fb u) := by
  refine intervalIntegral_mono_of_le (αseq_le_Tseq n)
    (continuousOn_diffsq w Fs Fb hF0 hFb0 n).intervalIntegrable
    (continuousOn_wres w Fs Fb hF0 hFb0 n).intervalIntegrable fun u hu => ?_
  exact pointwise_expectation_bound w hw Fs Fb hF0 hFb0 (lt_trans (αseq_pos n) hu.1) hmean

/-- Evaluation of the right side: `∑ wᵢ hfun(Fᵢ) − W hfun(F̄)`. -/
theorem integral_wres (w : ι → ℝ) (Fs : ι → A) (Fb : A) (hF0 : ∀ i, 0 ≤ Fs i) (hFb0 : 0 ≤ Fb)
    (n : ℕ) :
    ∫ u in αseq n..Tseq n, u • ((∑ i, w i • res (Fs i) u) - (∑ i, w i) • res Fb u)
      = ∑ i, w i • cfc (hfun (αseq n) (Tseq n)) (Fs i)
        - (∑ i, w i) • cfc (hfun (αseq n) (Tseq n)) Fb := by
  have hres : ∀ (F : A), 0 ≤ F →
      IntervalIntegrable (fun u => u • res F u) volume (αseq n) (Tseq n) := fun F hF =>
    (((continuousOn_id' _).smul (continuousOn_res_param hF)).mono (uIcc_subset_Ioi n)).intervalIntegrable
  have h1 : (fun u => u • ((∑ i, w i • res (Fs i) u) - (∑ i, w i) • res Fb u))
      = fun u => (∑ i, w i • (u • res (Fs i) u)) - (∑ i, w i) • (u • res Fb u) := by
    funext u
    rw [smul_sub, Finset.smul_sum, smul_comm u (∑ i, w i)]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_comm]
  rw [h1, intervalIntegral.integral_sub, intervalIntegral.integral_finsetSum,
    intervalIntegral.integral_smul, integral_smul_res hFb0 (αseq_pos n) (Tseq_pos n)]
  · congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_smul, integral_smul_res (hF0 i) (αseq_pos n) (Tseq_pos n)]
  · exact fun i _ => (hres _ (hF0 i)).smul _
  · exact (continuousOn_finsetSum _ fun i _ =>
      (((continuousOn_id' _).smul (continuousOn_res_param (hF0 i))).mono
        (uIcc_subset_Ioi n)).const_smul _).intervalIntegrable
  · exact (hres _ hFb0).smul _

/-- Evaluation of the left side as a combination of cutoff kernel integrals. -/
theorem integral_diffsq (w : ι → ℝ) (Fs : ι → A) (Fb : A) (hF0 : ∀ i, 0 ≤ Fs i) (hFb0 : 0 ≤ Fb)
    (n : ℕ) :
    ∫ u in αseq n..Tseq n, ∑ i, w i • ((fib (Fs i) u - fib Fb u) * (fib (Fs i) u - fib Fb u))
      = ∑ i, w i • ((∫ u in αseq n..Tseq n, fib (Fs i) u * fib (Fs i) u)
          - (∫ u in αseq n..Tseq n, fib (Fs i) u * fib Fb u)
          - (∫ u in αseq n..Tseq n, fib Fb u * fib (Fs i) u)
          + (∫ u in αseq n..Tseq n, fib Fb u * fib Fb u)) := by
  have hii := fun i => intervalIntegrable_fib_mul_fib (hF0 i) (hF0 i) n
  have hib := fun i => intervalIntegrable_fib_mul_fib (hF0 i) hFb0 n
  have hbi := fun i => intervalIntegrable_fib_mul_fib hFb0 (hF0 i) n
  have hbb := intervalIntegrable_fib_mul_fib hFb0 hFb0 n
  have h1 : (fun u => ∑ i, w i • ((fib (Fs i) u - fib Fb u) * (fib (Fs i) u - fib Fb u)))
      = fun u => ∑ i, w i • (fib (Fs i) u * fib (Fs i) u - fib (Fs i) u * fib Fb u
          - fib Fb u * fib (Fs i) u + fib Fb u * fib Fb u) := by
    funext u
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    noncomm_ring
  rw [h1, intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_smul, intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_sub]
    · exact hii i
    · exact hib i
    · exact (hii i).sub (hib i)
    · exact hbi i
    · exact ((hii i).sub (hib i)).sub (hbi i)
    · exact hbb
  · intro i _
    exact ((((hii i).sub (hib i)).sub (hbi i)).add hbb).smul _

/-- Algebra of the right side: the constant and linear parts cancel by `∑ wᵢ Fᵢ = W F̄`. -/
theorem wsum_cancel (w : ι → ℝ) (Fs : ι → A) (Fb : A)
    (hmean : (∑ i, w i • Fs i) = (∑ i, w i) • Fb) (c : A) (r : ℝ) (E : ι → A) (Eb : A) :
    ∑ i, w i • (c - r • Fs i + E i) - (∑ i, w i) • (c - r • Fb + Eb)
      = ∑ i, w i • E i - (∑ i, w i) • Eb := by
  have hr : ∑ i, w i • (r • Fs i) = (∑ i, w i) • (r • Fb) := by
    simp_rw [smul_comm (w _) r]
    rw [← Finset.smul_sum, hmean, smul_comm]
  simp only [smul_sub, smul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, hr,
    ← Finset.sum_smul]
  abel

/-- **Kernel entropy inequality.** -/
theorem kern_entropy_le (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (Fs : ι → A) (Fb : A)
    (hF0 : ∀ i, 0 ≤ Fs i) (hF1 : ∀ i, Fs i ≤ 1) (hFb0 : 0 ≤ Fb) (hFb1 : Fb ≤ 1)
    (hmean : (∑ i, w i • Fs i) = (∑ i, w i) • Fb) :
    ∑ i, w i • (kern (Fs i) (Fs i) - kern (Fs i) Fb - kern Fb (Fs i) + kern Fb Fb)
      ≤ (∑ i, w i) • cfc Real.negMulLog Fb - ∑ i, w i • cfc Real.negMulLog (Fs i) := by
  -- left side
  have hL : Tendsto (fun n => ∫ u in αseq n..Tseq n,
      ∑ i, w i • ((fib (Fs i) u - fib Fb u) * (fib (Fs i) u - fib Fb u))) atTop
      (𝓝 (∑ i, w i • (kern (Fs i) (Fs i) - kern (Fs i) Fb - kern Fb (Fs i) + kern Fb Fb))) := by
    simp_rw [integral_diffsq w Fs Fb hF0 hFb0]
    refine tendsto_finsetSum _ fun i _ => Tendsto.const_smul ?_ _
    exact (((tendsto_intervalIntegral_kern (hF0 i) (hF0 i)).sub
      (tendsto_intervalIntegral_kern (hF0 i) hFb0)).sub
      (tendsto_intervalIntegral_kern hFb0 (hF0 i))).add (tendsto_intervalIntegral_kern hFb0 hFb0)
  -- right side
  have hR : Tendsto (fun n => ∫ u in αseq n..Tseq n,
      u • ((∑ i, w i • res (Fs i) u) - (∑ i, w i) • res Fb u)) atTop
      (𝓝 ((∑ i, w i) • cfc Real.negMulLog Fb - ∑ i, w i • cfc Real.negMulLog (Fs i))) := by
    simp_rw [integral_wres w Fs Fb hF0 hFb0]
    have he : ∀ n, ∑ i, w i • cfc (hfun (αseq n) (Tseq n)) (Fs i)
        - (∑ i, w i) • cfc (hfun (αseq n) (Tseq n)) Fb
        = ∑ i, w i • Ecorr (αseq n) (Tseq n) (Fs i) - (∑ i, w i) • Ecorr (αseq n) (Tseq n) Fb := by
      intro n
      simp_rw [cfc_hfun_eq (hF0 _) (αseq_pos n) (Tseq_pos n),
        cfc_hfun_eq hFb0 (αseq_pos n) (Tseq_pos n)]
      exact wsum_cancel w Fs Fb hmean _ _ _ _
    simp_rw [he]
    have hlim : Tendsto (fun n => ∑ i, w i • Ecorr (αseq n) (Tseq n) (Fs i)
        - (∑ i, w i) • Ecorr (αseq n) (Tseq n) Fb) atTop
        (𝓝 (∑ i, w i • (-cfc Real.negMulLog (Fs i))
          - (∑ i, w i) • (-cfc Real.negMulLog Fb))) :=
      (tendsto_finsetSum _ fun i _ => (tendsto_Ecorr (hF0 i) (hF1 i)).const_smul _).sub
        ((tendsto_Ecorr hFb0 hFb1).const_smul _)
    convert hlim using 1
    simp only [smul_neg, Finset.sum_neg_distrib]
    abel_nf
  exact le_of_tendsto_of_tendsto' hL hR (integrated_bound w hw Fs Fb hF0 hFb0 hmean)

end Entropy

/-! ## Membership of the kernel in closed star subalgebras -/

theorem setIntegral_mem_of_closed {C : Set A} (hconv : Convex ℝ C) (hcl : IsClosed C)
    (h0 : (0 : A) ∈ C) (hscale : ∀ r : ℝ, 0 ≤ r → ∀ x ∈ C, r • x ∈ C)
    {f : ℝ → A} {s : Set ℝ} (hs : MeasurableSet s) (hfin : volume s ≠ ⊤)
    (hf : IntegrableOn f s) (hmem : ∀ u ∈ s, f u ∈ C) : ∫ u in s, f u ∈ C := by
  by_cases hz : volume s = 0
  · rw [Measure.restrict_eq_zero.mpr hz, integral_zero_measure]
    exact h0
  · have hav := hconv.set_average_mem hcl hz hfin (ae_restrict_of_forall_mem hs hmem) hf
    rw [setAverage_eq] at hav
    have hne : volume.real s ≠ 0 := by
      rw [measureReal_def]; exact ENNReal.toReal_ne_zero.mpr ⟨hz, hfin⟩
    have : ∫ u in s, f u = volume.real s • ((volume.real s)⁻¹ • ∫ u in s, f u) := by
      rw [smul_smul, mul_inv_cancel₀ hne, one_smul]
    rw [this]
    exact hscale _ measureReal_nonneg _ hav

theorem intervalIntegral_mem_of_closed {C : Set A} (hconv : Convex ℝ C) (hcl : IsClosed C)
    (h0 : (0 : A) ∈ C) (hscale : ∀ r : ℝ, 0 ≤ r → ∀ x ∈ C, r • x ∈ C)
    {f : ℝ → A} {a b : ℝ} (hab : a ≤ b) (hf : IntervalIntegrable f volume a b)
    (hmem : ∀ u ∈ Set.Ioc a b, f u ∈ C) : ∫ u in a..b, f u ∈ C := by
  rw [intervalIntegral.integral_of_le hab]
  refine setIntegral_mem_of_closed hconv hcl h0 hscale measurableSet_Ioc ?_
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hf) hmem
  rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top

theorem real_smul_mem (S : StarSubalgebra ℂ A) (r : ℝ) {x : A} (hx : x ∈ S) : r • x ∈ S := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact SMulMemClass.smul_mem _ hx

theorem convex_starSubalgebra (S : StarSubalgebra ℂ A) : Convex ℝ (S : Set A) := by
  intro x hx y hy a b _ _ _
  exact S.add_mem (real_smul_mem S a hx) (real_smul_mem S b hy)

theorem fib_mem {S : StarSubalgebra ℂ A} (hS : IsClosed (S : Set A)) {F : A} (hF : F ∈ S)
    (u : ℝ) : fib F u ∈ S := by
  unfold fib
  exact cfc_mem (𝕜' := ℂ) (hs := hS) _ hF

theorem res_mem {S : StarSubalgebra ℂ A} (hS : IsClosed (S : Set A)) {F : A} (hF : F ∈ S)
    (u : ℝ) : res F u ∈ S := by
  unfold res
  exact cfc_mem (𝕜' := ℂ) (hs := hS) _ hF

/-- The kernel of two elements of a closed star subalgebra lies in it. -/
theorem kern_mem {S : StarSubalgebra ℂ A} (hS : IsClosed (S : Set A)) {F G : A}
    (hF0 : 0 ≤ F) (hG0 : 0 ≤ G) (hF : F ∈ S) (hG : G ∈ S) : kern F G ∈ S := by
  refine hS.mem_of_tendsto (tendsto_intervalIntegral_kern hF0 hG0)
    (Eventually.of_forall fun n => ?_)
  refine intervalIntegral_mem_of_closed (convex_starSubalgebra S) hS (zero_mem S)
    (fun r _ x hx => real_smul_mem S r hx) (αseq_le_Tseq n)
    (intervalIntegrable_fib_mul_fib hF0 hG0 n) fun u _ => ?_
  exact mul_mem (fib_mem hS hF u) (fib_mem hS hG u)

end Resolver

end CommutingRepetition

/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/MonotoneLimit.lean
-/
/-
# Strong limits of bounded monotone operator sequences (WP-B7, stage B)

A pointwise-convergent sequence of uniformly bounded operators has a bounded
pointwise limit (`pointwiseLimit`, no Banach–Steinhaus needed), and a
monotone sequence of positive contractions `0 ≤ Tₙ ≤ Tₙ₊₁ ≤ 1` converges
strongly: `‖(Tₙ − Tₘ)ξ‖² ≤ ⟪ξ, (Tₙ − Tₘ)ξ⟫` because `0 ≤ Tₙ − Tₘ ≤ 1`, and the
real sequence `⟪ξ, Tₙξ⟫` is monotone and bounded. The limit is a positive
contraction dominating every `Tₙ`. This is the analytic engine of the Borel
functional calculus (stage C). Infrastructure only; no manuscript statement.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Resolver.Resolvent
import MIPRE.Background.Repetition.CommutingRepetition.Resolver.Douglas

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace StrongLimit

open scoped InnerProductSpace Topology
open Filter

set_option linter.unusedSectionVars false

variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗] [CompleteSpace 𝓗]

/-! ## Pointwise limits of uniformly bounded sequences -/

section Pointwise

variable (T : ℕ → 𝓗 →L[ℂ] 𝓗) (C : ℝ) (hC : ∀ n, ‖T n‖ ≤ C)
  (hex : ∀ ξ, ∃ l, Tendsto (fun n => T n ξ) atTop (𝓝 l))

/-- The pointwise limit of a uniformly bounded, pointwise convergent sequence. -/
noncomputable def pointwiseLimit : 𝓗 →L[ℂ] 𝓗 :=
  LinearMap.mkContinuous
    { toFun := fun ξ => Classical.choose (hex ξ)
      map_add' := fun ξ η => by
        have h1 := Classical.choose_spec (hex (ξ + η))
        have h2 : Tendsto (fun n => T n (ξ + η)) atTop
            (𝓝 (Classical.choose (hex ξ) + Classical.choose (hex η))) := by
          simp only [map_add]
          exact (Classical.choose_spec (hex ξ)).add (Classical.choose_spec (hex η))
        exact tendsto_nhds_unique h1 h2
      map_smul' := fun c ξ => by
        have h1 := Classical.choose_spec (hex (c • ξ))
        have h2 : Tendsto (fun n => T n (c • ξ)) atTop (𝓝 (c • Classical.choose (hex ξ))) := by
          simp only [map_smul]
          exact (Classical.choose_spec (hex ξ)).const_smul c
        exact tendsto_nhds_unique h1 h2 } (max C 0) fun ξ => by
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    have h := (Classical.choose_spec (hex ξ)).norm
    refine le_of_tendsto' h fun n => ?_
    calc ‖T n ξ‖ ≤ ‖T n‖ * ‖ξ‖ := (T n).le_opNorm ξ
      _ ≤ max C 0 * ‖ξ‖ := by
          exact mul_le_mul_of_nonneg_right ((hC n).trans (le_max_left _ _)) (norm_nonneg _)

theorem pointwiseLimit_tendsto (ξ : 𝓗) :
    Tendsto (fun n => T n ξ) atTop (𝓝 (pointwiseLimit T C hC hex ξ)) :=
  Classical.choose_spec (hex ξ)

end Pointwise

/-! ## Positive contractions -/

theorem re_inner_apply_le {T : 𝓗 →L[ℂ] 𝓗} (h0 : 0 ≤ T) (h1 : T ≤ 1) (ξ : 𝓗) :
    ‖T ξ‖ ^ 2 ≤ (⟪ξ, T ξ⟫_ℂ).re := by
  have hsa : IsSelfAdjoint T := IsSelfAdjoint.of_nonneg h0
  -- T * T ≤ T
  have hsq : T * T ≤ T := by
    have e1 : T * T = cfc (fun t : ℝ => t * t) T := by
      rw [cfc_mul (fun t : ℝ => t) (fun t : ℝ => t) T (continuousOn_id' _) (continuousOn_id' _),
        cfc_id' ℝ T hsa]
    have e2 : T = cfc (fun t : ℝ => t) T := (cfc_id' ℝ T hsa).symm
    rw [e1]
    conv_rhs => rw [e2]
    refine cfc_mono (fun t ht => ?_) ((continuousOn_id' _).mul (continuousOn_id' _))
      (continuousOn_id' _)
    have ht0 := Resolver.spectrum_nonneg h0 ht
    have ht1 := Resolver.spectrum_le_one h1 ht
    nlinarith
  have h := Resolver.Douglas.re_inner_nonneg_of_nonneg (sub_nonneg.mpr hsq) ξ
  rw [ContinuousLinearMap.sub_apply, inner_sub_right, Complex.sub_re] at h
  have e3 : (⟪ξ, (T * T) ξ⟫_ℂ).re = ‖T ξ‖ ^ 2 := by
    have := Resolver.Douglas.re_inner_star_mul T ξ
    rwa [hsa.star_eq] at this
  linarith

theorem norm_le_one_of_nonneg_le_one {T : 𝓗 →L[ℂ] 𝓗} (h0 : 0 ≤ T) (h1 : T ≤ 1) : ‖T‖ ≤ 1 :=
  (CStarAlgebra.norm_le_one_iff_of_nonneg T h0).mpr h1

/-! ## Monotone sequences -/

variable (T : ℕ → 𝓗 →L[ℂ] 𝓗) (hmono : Monotone T) (h0 : 0 ≤ T 0) (h1 : ∀ n, T n ≤ 1)
include hmono h0 h1

theorem nonneg_of_monotone (n : ℕ) : 0 ≤ T n := h0.trans (hmono (Nat.zero_le n))

/-- The quadratic forms `⟪ξ, Tₙ ξ⟫` converge. -/
theorem tendsto_re_inner (ξ : 𝓗) :
    ∃ a : ℝ, Tendsto (fun n => (⟪ξ, T n ξ⟫_ℂ).re) atTop (𝓝 a) := by
  refine ⟨_, tendsto_atTop_ciSup (fun m n hmn => ?_) ⟨‖ξ‖ ^ 2, ?_⟩⟩
  · have h := Resolver.Douglas.re_inner_nonneg_of_nonneg (sub_nonneg.mpr (hmono hmn)) ξ
    rw [ContinuousLinearMap.sub_apply, inner_sub_right, Complex.sub_re] at h
    linarith
  · rintro _ ⟨n, rfl⟩
    have h := Resolver.Douglas.re_inner_nonneg_of_nonneg (sub_nonneg.mpr (h1 n)) ξ
    rw [ContinuousLinearMap.sub_apply, inner_sub_right, Complex.sub_re,
      ContinuousLinearMap.one_apply, ← RCLike.re_to_complex, inner_self_eq_norm_sq] at h
    linarith

/-- Cauchy property of the orbit `Tₙ ξ`. -/
theorem cauchySeq_apply (ξ : 𝓗) : CauchySeq fun n => T n ξ := by
  obtain ⟨a, ha⟩ := tendsto_re_inner T hmono h0 h1 ξ
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp ha.cauchySeq (ε ^ 2) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  -- order the indices
  wlog hle : n ≤ m generalizing m n
  · rw [dist_comm]; exact this n hn m hm (le_of_not_ge hle)
  have hdiff0 : 0 ≤ T m - T n := sub_nonneg.mpr (hmono hle)
  have hdiff1 : T m - T n ≤ 1 :=
    (sub_le_self _ (nonneg_of_monotone T hmono h0 h1 n)).trans (h1 m)
  have hb := re_inner_apply_le hdiff0 hdiff1 ξ
  rw [ContinuousLinearMap.sub_apply, inner_sub_right, Complex.sub_re] at hb
  have hd := hN m hm n hn
  rw [Real.dist_eq] at hd
  rw [dist_eq_norm]
  have : ‖T m ξ - T n ξ‖ ^ 2 < ε ^ 2 := by
    calc ‖T m ξ - T n ξ‖ ^ 2 ≤ (⟪ξ, T m ξ⟫_ℂ).re - (⟪ξ, T n ξ⟫_ℂ).re := hb
      _ ≤ |(⟪ξ, T m ξ⟫_ℂ).re - (⟪ξ, T n ξ⟫_ℂ).re| := le_abs_self _
      _ < ε ^ 2 := hd
  exact lt_of_pow_lt_pow_left₀ 2 hε.le this

theorem exists_tendsto_apply (ξ : 𝓗) : ∃ l, Tendsto (fun n => T n ξ) atTop (𝓝 l) :=
  cauchySeq_tendsto_of_complete (cauchySeq_apply T hmono h0 h1 ξ)

/-- **The strong limit of a monotone sequence of positive contractions.** -/
noncomputable def monotoneLimit : 𝓗 →L[ℂ] 𝓗 :=
  pointwiseLimit T 1 (fun n => norm_le_one_of_nonneg_le_one (nonneg_of_monotone T hmono h0 h1 n)
    (h1 n)) (exists_tendsto_apply T hmono h0 h1)

theorem monotoneLimit_tendsto (ξ : 𝓗) :
    Tendsto (fun n => T n ξ) atTop (𝓝 (monotoneLimit T hmono h0 h1 ξ)) :=
  pointwiseLimit_tendsto _ _ _ _ ξ

theorem monotoneLimit_inner (ξ η : 𝓗) :
    Tendsto (fun n => ⟪ξ, T n η⟫_ℂ) atTop (𝓝 ⟪ξ, monotoneLimit T hmono h0 h1 η⟫_ℂ) :=
  (Continuous.inner continuous_const continuous_id).tendsto _ |>.comp
    (monotoneLimit_tendsto T hmono h0 h1 η)

theorem monotoneLimit_isSelfAdjoint : IsSelfAdjoint (monotoneLimit T hmono h0 h1) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro ξ η
  have hsa : ∀ n, IsSelfAdjoint (T n) := fun n =>
    IsSelfAdjoint.of_nonneg (nonneg_of_monotone T hmono h0 h1 n)
  have h1' : Tendsto (fun n => ⟪T n ξ, η⟫_ℂ) atTop (𝓝 ⟪monotoneLimit T hmono h0 h1 ξ, η⟫_ℂ) :=
    (Continuous.inner continuous_id continuous_const).tendsto _ |>.comp
      (monotoneLimit_tendsto T hmono h0 h1 ξ)
  have h2 : Tendsto (fun n => ⟪T n ξ, η⟫_ℂ) atTop (𝓝 ⟪ξ, monotoneLimit T hmono h0 h1 η⟫_ℂ) := by
    refine (monotoneLimit_inner T hmono h0 h1 ξ η).congr fun n => ?_
    rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
      (hsa n).star_eq]
  exact tendsto_nhds_unique h1' h2

theorem le_monotoneLimit (n : ℕ) : T n ≤ monotoneLimit T hmono h0 h1 := by
  rw [← sub_nonneg]
  refine Resolver.Douglas.nonneg_of_re_inner ((monotoneLimit_isSelfAdjoint T hmono h0 h1).sub
    (IsSelfAdjoint.of_nonneg (nonneg_of_monotone T hmono h0 h1 n))) fun ξ => ?_
  rw [ContinuousLinearMap.sub_apply, inner_sub_left, Complex.sub_re]
  have hlim : Tendsto (fun m => (⟪T m ξ, ξ⟫_ℂ).re) atTop
      (𝓝 (⟪monotoneLimit T hmono h0 h1 ξ, ξ⟫_ℂ).re) :=
    (Complex.continuous_re.tendsto _).comp
      (((Continuous.inner continuous_id continuous_const).tendsto _).comp
        (monotoneLimit_tendsto T hmono h0 h1 ξ))
  have hge : ∀ m, n ≤ m → (⟪T n ξ, ξ⟫_ℂ).re ≤ (⟪T m ξ, ξ⟫_ℂ).re := by
    intro m hm
    have h := Resolver.Douglas.re_inner_nonneg_of_nonneg (sub_nonneg.mpr (hmono hm)) ξ
    rw [ContinuousLinearMap.sub_apply, inner_sub_right, Complex.sub_re, ← inner_conj_symm,
      ← inner_conj_symm ξ (T n ξ), Complex.conj_re, Complex.conj_re] at h
    linarith
  have hev : ∀ᶠ m in atTop, (⟪T n ξ, ξ⟫_ℂ).re ≤ (⟪T m ξ, ξ⟫_ℂ).re :=
    eventually_atTop.mpr ⟨n, hge⟩
  have := ge_of_tendsto hlim hev
  linarith

theorem monotoneLimit_nonneg : 0 ≤ monotoneLimit T hmono h0 h1 :=
  h0.trans (le_monotoneLimit T hmono h0 h1 0)

theorem monotoneLimit_le_one : monotoneLimit T hmono h0 h1 ≤ 1 := by
  rw [← sub_nonneg]
  have h1sa : IsSelfAdjoint (1 : 𝓗 →L[ℂ] 𝓗) := by rw [IsSelfAdjoint, star_one]
  refine Resolver.Douglas.nonneg_of_re_inner (h1sa.sub
    (monotoneLimit_isSelfAdjoint T hmono h0 h1)) fun ξ => ?_
  rw [ContinuousLinearMap.sub_apply, inner_sub_left, Complex.sub_re]
  have hlim : Tendsto (fun m => (⟪T m ξ, ξ⟫_ℂ).re) atTop
      (𝓝 (⟪monotoneLimit T hmono h0 h1 ξ, ξ⟫_ℂ).re) :=
    (Complex.continuous_re.tendsto _).comp
      (((Continuous.inner continuous_id continuous_const).tendsto _).comp
        (monotoneLimit_tendsto T hmono h0 h1 ξ))
  have hle : ∀ m, (⟪T m ξ, ξ⟫_ℂ).re ≤ (⟪(1 : 𝓗 →L[ℂ] 𝓗) ξ, ξ⟫_ℂ).re := fun m => by
    have h := Resolver.Douglas.re_inner_nonneg_of_nonneg (sub_nonneg.mpr (h1 m)) ξ
    rw [ContinuousLinearMap.sub_apply, inner_sub_right, Complex.sub_re, ← inner_conj_symm,
      ← inner_conj_symm ξ (T m ξ), Complex.conj_re, Complex.conj_re] at h
    linarith
  linarith [le_of_tendsto' hlim hle]

end StrongLimit

end CommutingRepetition

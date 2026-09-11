/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/Modular/FourierConverse.lean
-/
/-
# The Fourier converse (density stage E6.1)

If a bounded operator commutes with every `Δ^{it} = e^{itθ(R)}` then it commutes with `R`.

The spectral measures of `R` live on `(0,2)`, where `θ = log((2−λ)/λ)` is a Borel isomorphism
onto `ℝ`. Pushing the (finitely many) spectral measures of the commutator functional forward by
`θ`, the hypothesis says their characteristic functions agree, so they agree
(`Measure.ext_of_charFun`), so the commutator functional vanishes on every bounded Borel
function of `R`, in particular on `R` itself.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.Modular.Centralizer
import MIPRE.Background.Repetition.CommutingRepetition.VN.SpectralProjection

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace VN

namespace Modular

open scoped InnerProductSpace ComplexConjugate
open Filter Topology MeasureTheory BorelCalc

set_option linter.unusedSectionVars false

/-! ## The inverse of `θ` on `(0,2)` -/

/-- `θinv u = 2 / (1 + e^u)`, the inverse of `θ` on `(0,2)`. -/
noncomputable def θinv (u : ℝ) : ℝ := 2 / (1 + Real.exp u)

theorem continuous_θinv : Continuous θinv := by
  unfold θinv
  exact continuous_const.div (continuous_const.add Real.continuous_exp) fun u =>
    (add_pos one_pos (Real.exp_pos u)).ne'

theorem measurable_θinv : Measurable θinv := continuous_θinv.measurable

theorem θinv_θ {l : ℝ} (hl : l ∈ Set.Ioo (0 : ℝ) 2) : θinv (θ l) = l := by
  unfold θinv θ
  rw [if_pos hl, Real.exp_log (div_pos (by linarith [hl.2]) hl.1)]
  have h0 : l ≠ 0 := hl.1.ne'
  field_simp
  ring

/-! ## Measures on `(0,2)` are determined by their `θ`-Fourier transforms -/

theorem ae_mem_Ioo_of_compl_eq_zero {μ : Measure ℝ} (hμ : μ (Set.Ioo (0 : ℝ) 2)ᶜ = 0) :
    ∀ᵐ l ∂μ, l ∈ Set.Ioo (0 : ℝ) 2 := by
  rw [ae_iff]
  exact hμ

theorem integral_eq_integral_map_θ {μ : Measure ℝ} (hμ : μ (Set.Ioo (0 : ℝ) 2)ᶜ = 0)
    {g : ℝ → ℝ} (hg : Measurable g) :
    ∫ l, g l ∂μ = ∫ u, g (θinv u) ∂(μ.map θ) := by
  rw [integral_map (f := fun u => g (θinv u)) measurable_θ.aemeasurable
    (hg.comp measurable_θinv).aestronglyMeasurable]
  refine integral_congr_ae ?_
  filter_upwards [ae_mem_Ioo_of_compl_eq_zero hμ] with l hl
  rw [θinv_θ hl]

theorem bdd_cos_θ (t : ℝ) : Bdd fun l => Real.cos (t * θ l) :=
  ⟨Real.measurable_cos.comp (measurable_const.mul measurable_θ), 1,
    fun _ => Real.abs_cos_le_one _⟩

theorem bdd_sin_θ (t : ℝ) : Bdd fun l => Real.sin (t * θ l) :=
  ⟨Real.measurable_sin.comp (measurable_const.mul measurable_θ), 1,
    fun _ => Real.abs_sin_le_one _⟩

/-- Two finite measures concentrated on `(0,2)` with the same integrals of `cos(tθ)` and
`sin(tθ)` for all `t` have the same integrals of every bounded Borel function. -/
theorem integral_eq_of_cos_sin {μ μ' : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure μ']
    (hμ : μ (Set.Ioo (0 : ℝ) 2)ᶜ = 0) (hμ' : μ' (Set.Ioo (0 : ℝ) 2)ᶜ = 0)
    (hcos : ∀ t : ℝ, ∫ l, Real.cos (t * θ l) ∂μ = ∫ l, Real.cos (t * θ l) ∂μ')
    (hsin : ∀ t : ℝ, ∫ l, Real.sin (t * θ l) ∂μ = ∫ l, Real.sin (t * θ l) ∂μ')
    {g : ℝ → ℝ} (hg : Measurable g) : ∫ l, g l ∂μ = ∫ l, g l ∂μ' := by
  have hmap : μ.map θ = μ'.map θ := by
    refine Measure.ext_of_charFun (funext fun t => ?_)
    have key : ∀ (ν : Measure ℝ) [IsFiniteMeasure ν], charFun (ν.map θ) t =
        ((∫ l, Real.cos (t * θ l) ∂ν : ℝ) : ℂ) + Complex.I * ((∫ l, Real.sin (t * θ l) ∂ν : ℝ) : ℂ) := by
      intro ν _
      rw [charFun_apply_real, integral_map measurable_θ.aemeasurable
        (by fun_prop : Continuous fun x : ℝ => Complex.exp (t * x * Complex.I)).aestronglyMeasurable]
      have e : (fun x : ℝ => Complex.exp (↑t * ↑(θ x) * Complex.I)) =
          fun x => ((Real.cos (t * θ x) : ℝ) : ℂ) + ((Real.sin (t * θ x) : ℝ) : ℂ) * Complex.I := by
        funext x
        rw [← Complex.ofReal_mul, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      rw [e, integral_add ((CBdd.ofReal (bdd_cos_θ t)).integrable ν)
        (((CBdd.ofReal (bdd_sin_θ t)).integrable ν).mul_const _), integral_complex_ofReal,
        integral_mul_const, integral_complex_ofReal, mul_comm]
    rw [key μ, key μ', hcos t, hsin t]
  rw [integral_eq_integral_map_θ hμ hg, integral_eq_integral_map_θ hμ' hg, hmap]

/-! ## Transfer to combinations of finite measures -/

theorem isFiniteMeasure_restrict_Ioo (μ : Measure ℝ) [IsFiniteMeasure μ] :
    IsFiniteMeasure (μ.restrict (Set.Ioo (0 : ℝ) 2)) := inferInstance

theorem restrict_Ioo_compl (μ : Measure ℝ) :
    μ.restrict (Set.Ioo (0 : ℝ) 2) (Set.Ioo (0 : ℝ) 2)ᶜ = 0 := by
  rw [Measure.restrict_apply measurableSet_Ioo.compl, Set.compl_inter_self, measure_empty]

theorem Bdd.indicator_of_bdd {s : Set ℝ} (hs : MeasurableSet s) {g : ℝ → ℝ} (hg : Bdd g) :
    Bdd (s.indicator g) := by
  refine ⟨hg.1.indicator hs, ?_⟩
  obtain ⟨C, hC⟩ := hg.2
  refine ⟨C, fun t => ?_⟩
  by_cases ht : t ∈ s
  · rw [Set.indicator_of_mem ht]; exact hC t
  · rw [Set.indicator_of_notMem ht, abs_zero]; exact (abs_nonneg _).trans (hC t)

/-- A combination of finite measures that vanishes on everything supported off `(0,2)` and on
`cos(tθ)`, `sin(tθ)` for all `t` vanishes on every bounded Borel function. -/
theorem IsCombo.eq_zero_of_cos_sin {Φ : (ℝ → ℝ) → ℂ} (hΦ : IsCombo Φ)
    (h0 : ∀ g : ℝ → ℝ, Bdd g → Φ ((Set.Ioo (0 : ℝ) 2)ᶜ.indicator g) = 0)
    (hcos : ∀ t : ℝ, Φ (fun l => Real.cos (t * θ l)) = 0)
    (hsin : ∀ t : ℝ, Φ (fun l => Real.sin (t * θ l)) = 0)
    {g : ℝ → ℝ} (hg : Bdd g) : Φ g = 0 := by
  obtain ⟨μ₁, μ₂, μ₃, μ₄, h1, h2, h3, h4, hF⟩ := hΦ
  set s : Set ℝ := Set.Ioo 0 2 with hs
  have hsm : MeasurableSet s := measurableSet_Ioo
  -- the formula with the restricted measures
  have hF' : ∀ g : ℝ → ℝ, Bdd g → Φ g =
      (((∫ t, g t ∂(μ₁.restrict s)) - ∫ t, g t ∂(μ₂.restrict s) : ℝ) : ℂ) +
        Complex.I * (((∫ t, g t ∂(μ₃.restrict s)) - ∫ t, g t ∂(μ₄.restrict s) : ℝ) : ℂ) := by
    intro g hg
    have hind : ∀ (μ : Measure ℝ) [IsFiniteMeasure μ],
        ∫ t, g t ∂μ = ∫ t, g t ∂(μ.restrict s) + ∫ t, sᶜ.indicator g t ∂μ := by
      intro μ _
      rw [← integral_indicator hsm, ← integral_add ((Bdd.indicator_of_bdd hsm hg).integrable μ)
        ((Bdd.indicator_of_bdd hsm.compl hg).integrable μ)]
      congr 1
      funext t
      exact (Set.indicator_self_add_compl_apply s g t).symm
    have e' := hF _ (Bdd.indicator_of_bdd hsm.compl hg)
    rw [h0 g hg] at e'
    have hre := congrArg Complex.re e'
    have him := congrArg Complex.im e'
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero, Complex.zero_re, Complex.add_im,
      Complex.mul_im, one_mul, zero_add, Complex.zero_im] at hre him
    rw [hF g hg, hind μ₁, hind μ₂, hind μ₃, hind μ₄]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
      linarith
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, zero_mul, one_mul, zero_add]
      linarith
  -- separate real and imaginary parts of the hypotheses
  have split : ∀ g : ℝ → ℝ, Bdd g → Φ g = 0 →
      ∫ t, g t ∂(μ₁.restrict s) = ∫ t, g t ∂(μ₂.restrict s) ∧
      ∫ t, g t ∂(μ₃.restrict s) = ∫ t, g t ∂(μ₄.restrict s) := by
    intro g hg h
    rw [hF' g hg] at h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero, Complex.zero_re, Complex.add_im,
      Complex.mul_im, one_mul, zero_add, Complex.zero_im] at hre him
    exact ⟨sub_eq_zero.mp hre, sub_eq_zero.mp him⟩
  have e12 := integral_eq_of_cos_sin (restrict_Ioo_compl μ₁) (restrict_Ioo_compl μ₂)
    (fun t => (split _ (bdd_cos_θ t) (hcos t)).1) (fun t => (split _ (bdd_sin_θ t) (hsin t)).1) hg.1
  have e34 := integral_eq_of_cos_sin (restrict_Ioo_compl μ₃) (restrict_Ioo_compl μ₄)
    (fun t => (split _ (bdd_cos_θ t) (hcos t)).2) (fun t => (split _ (bdd_sin_θ t) (hsin t)).2) hg.1
  rw [hF' g hg, hs, e12, e34]
  simp

/-! ## Operators: spectral projections at the endpoints -/

variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗] [CompleteSpace 𝓗]
variable (E : 𝓗 →L[ℂ] 𝓗) (hE : IsSelfAdjoint E)

/-- The truncation of the identity to `[-‖E‖, ‖E‖]`; equal to `id` on the spectrum. -/
noncomputable def trunc (E : 𝓗 →L[ℂ] 𝓗) (l : ℝ) : ℝ := max (-‖E‖) (min l ‖E‖)

theorem continuous_trunc : Continuous (trunc E) := by unfold trunc; fun_prop

theorem bdd_trunc : Bdd (trunc E) :=
  Bdd.of_continuous (continuous_trunc E) (C := ‖E‖) fun l => by
    unfold trunc
    rw [abs_le]
    constructor
    · exact le_max_left _ _
    · exact max_le ((neg_nonpos.mpr (norm_nonneg E)).trans (norm_nonneg E)) (min_le_right _ _)

theorem trunc_of_mem {l : ℝ} (hl : l ∈ Set.Icc (-‖E‖) ‖E‖) : trunc E l = l := by
  unfold trunc
  rw [min_eq_left hl.2, max_eq_right hl.1]

theorem bfc_trunc : bfc E hE (trunc E) = E := by
  rw [bfc_cfc E hE (bdd_trunc E) (continuous_trunc E)]
  have : (spectrum ℝ E).EqOn (trunc E) id := fun l hl =>
    trunc_of_mem E (spectrum_subset_Icc_norm E hl)
  rw [cfc_congr this, cfc_id ℝ E]

/-- `E P{c} = c P{c}`: the spectral projection at a point is the eigenprojection. -/
theorem E_mul_P_singleton (c : ℝ) : E * P E hE {c} = (c : ℂ) • P E hE {c} := by
  by_cases hc : c ∈ spectrum ℝ E
  · have hcn : c ∈ Set.Icc (-‖E‖) ‖E‖ := spectrum_subset_Icc_norm E hc
    have h1 : E * P E hE {c} = bfc E hE (trunc E) * bfc E hE (({c} : Set ℝ).indicator 1) := by
      rw [bfc_trunc]; rfl
    rw [h1, ← bfc_mul E hE (bdd_trunc E) (Bdd.indicator (measurableSet_singleton c)), P,
      ← bfc_const_mul E hE c (Bdd.indicator (measurableSet_singleton c))]
    congr 1
    funext l
    simp only [Pi.mul_apply, Set.indicator, Set.mem_singleton_iff, Pi.one_apply]
    split_ifs with hl
    · subst hl; rw [trunc_of_mem E hcn]
    · simp
  · rw [P_eq_zero_of_disjoint_spectrum E hE (measurableSet_singleton c)
      (Set.disjoint_singleton_left.mpr hc), mul_zero, smul_zero]

theorem P_singleton_eq_zero_of_injective (c : ℝ) (h : ∀ ξ, E ξ = (c : ℂ) • ξ → ξ = 0) :
    P E hE {c} = 0 := by
  ext ξ
  refine h _ ?_
  rw [← mul_apply_eq_comp, E_mul_P_singleton E hE c, smul_apply]

theorem ν_singleton_eq_zero_of_injective (c : ℝ) (h : ∀ ξ, E ξ = (c : ℂ) • ξ → ξ = 0) (ξ : 𝓗) :
    ν E hE ξ {c} = 0 := by
  have := norm_P_apply_sq E hE (measurableSet_singleton c) ξ
  rw [P_singleton_eq_zero_of_injective E hE c h, zero_apply, norm_zero, zero_pow two_ne_zero] at this
  exact (ENNReal.toReal_eq_zero_iff _).mp this.symm |>.resolve_right (measure_ne_top _ _)

/-- If the spectrum lies in `[0,2]` and `0`, `2` are not eigenvalues, the spectral measures
give no mass to `(0,2)ᶜ`. -/
theorem ν_compl_Ioo_eq_zero (hspec : spectrum ℝ E ⊆ Set.Icc 0 2)
    (h0 : ∀ ξ, E ξ = ((0 : ℝ) : ℂ) • ξ → ξ = 0) (h2 : ∀ ξ, E ξ = ((2 : ℝ) : ℂ) • ξ → ξ = 0)
    (ξ : 𝓗) : ν E hE ξ (Set.Ioo (0 : ℝ) 2)ᶜ = 0 := by
  have hsub : (Set.Ioo (0 : ℝ) 2)ᶜ ⊆ {0} ∪ {2} ∪ (spectrum ℝ E)ᶜ := by
    intro l hl
    by_cases hs : l ∈ spectrum ℝ E
    · have := hspec hs
      simp only [Set.mem_compl_iff, Set.mem_Ioo, not_and_or, not_lt] at hl
      simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_compl_iff]
      rcases hl with hl | hl
      · left; left; linarith [this.1]
      · left; right; linarith [this.2]
    · exact Or.inr hs
  refine measure_mono_null hsub ?_
  refine measure_union_null (measure_union_null ?_ ?_) (ν_compl_spectrum E hE ξ)
  · exact ν_singleton_eq_zero_of_injective E hE 0 h0 ξ
  · exact ν_singleton_eq_zero_of_injective E hE 2 h2 ξ

/-- If the spectrum lies in `[0,2]` and `0`, `2` are not eigenvalues, the spectral projection
of `(0,2)ᶜ` vanishes. -/
theorem P_compl_Ioo_eq_zero (hspec : spectrum ℝ E ⊆ Set.Icc 0 2)
    (h0 : ∀ ξ, E ξ = ((0 : ℝ) : ℂ) • ξ → ξ = 0) (h2 : ∀ ξ, E ξ = ((2 : ℝ) : ℂ) • ξ → ξ = 0) :
    P E hE (Set.Ioo (0 : ℝ) 2)ᶜ = 0 := by
  ext ξ
  rw [zero_apply, ← norm_eq_zero, ← pow_eq_zero_iff (two_ne_zero : (2 : ℕ) ≠ 0),
    norm_P_apply_sq E hE measurableSet_Ioo.compl, ν_compl_Ioo_eq_zero E hE hspec h0 h2 ξ,
    ENNReal.toReal_zero]

/-! ## The Fourier converse for a self-adjoint operator with spectral measures on `(0,2)` -/

theorem re_gDel (t l : ℝ) : (gDel t l).re = Real.cos (t * θ l) := by
  unfold gDel
  exact Complex.exp_ofReal_mul_I_re _

theorem im_gDel (t l : ℝ) : (gDel t l).im = Real.sin (t * θ l) := by
  unfold gDel
  exact Complex.exp_ofReal_mul_I_im _

/-- `cbfc (gDel t) = bfc (cos(tθ)) + i bfc (sin(tθ))`. -/
theorem cbfc_gDel_eq (t : ℝ) : cbfc E hE (gDel t) =
    bfc E hE (fun l => Real.cos (t * θ l)) + Complex.I • bfc E hE (fun l => Real.sin (t * θ l)) := by
  unfold cbfc
  simp only [re_gDel, im_gDel]

theorem cbfc_gDel_neg_eq (t : ℝ) : cbfc E hE (gDel (-t)) =
    bfc E hE (fun l => Real.cos (t * θ l)) - Complex.I • bfc E hE (fun l => Real.sin (t * θ l)) := by
  rw [cbfc_gDel_eq]
  have hc : (fun l => Real.cos (-t * θ l)) = fun l => Real.cos (t * θ l) := by
    funext l; rw [neg_mul, Real.cos_neg]
  have hs : (fun l => Real.sin (-t * θ l)) = fun l => (-1 : ℝ) * Real.sin (t * θ l) := by
    funext l; rw [neg_mul, Real.sin_neg, neg_one_mul]
  rw [hc, hs, bfc_const_mul E hE (-1) (bdd_sin_θ t), Complex.ofReal_neg, Complex.ofReal_one,
    neg_one_smul, smul_neg, sub_eq_add_neg]

/-- Commuting with `e^{itθ(E)}` for `t` and `−t` gives commutation with `cos(tθ(E))`, `sin(tθ(E))`. -/
theorem commute_bfc_cos_sin {x : 𝓗 →L[ℂ] 𝓗} (hx : ∀ t, Commute x (cbfc E hE (gDel t))) (t : ℝ) :
    Commute x (bfc E hE (fun l => Real.cos (t * θ l))) ∧
      Commute x (bfc E hE (fun l => Real.sin (t * θ l))) := by
  set C := bfc E hE (fun l => Real.cos (t * θ l))
  set S := bfc E hE (fun l => Real.sin (t * θ l))
  have hA : Commute x (C + Complex.I • S) := by rw [← cbfc_gDel_eq]; exact hx t
  have hB : Commute x (C - Complex.I • S) := by rw [← cbfc_gDel_neg_eq]; exact hx (-t)
  constructor
  · have e : (1 / 2 : ℂ) • ((C + Complex.I • S) + (C - Complex.I • S)) = C := by
      rw [add_add_sub_cancel, ← two_smul ℂ, smul_smul]
      norm_num
    rw [← e]
    exact (hA.add_right hB).smul_right _
  · have e : (-(Complex.I / 2)) • ((C + Complex.I • S) - (C - Complex.I • S)) = S := by
      rw [add_sub_sub_cancel, ← two_smul ℂ, smul_smul, smul_smul]
      have h : -(Complex.I / 2) * 2 * Complex.I = 1 := by
        ring_nf; rw [Complex.I_sq]; norm_num
      rw [h, one_smul]
    rw [← e]
    exact (hA.sub_right hB).smul_right _

/-- **The Fourier converse**: an operator commuting with every `e^{itθ(E)}` commutes with every
bounded Borel function of `E`, when the spectral measures of `E` live on `(0,2)`. -/
theorem commute_bfc_of_commute_cbfc_gDel (hP : P E hE (Set.Ioo (0 : ℝ) 2)ᶜ = 0) {x : 𝓗 →L[ℂ] 𝓗}
    (hx : ∀ t, Commute x (cbfc E hE (gDel t))) {g : ℝ → ℝ} (hg : Bdd g) :
    Commute x (bfc E hE g) := by
  rw [Commute, SemiconjBy]
  refine BorelCalc.ext_of_inner fun η ζ => ?_
  let Φ : (ℝ → ℝ) → ℂ := fun g => pol E hE g η (x ζ) - pol E hE g ((star x) η) ζ
  have hΦ : IsCombo Φ := (isCombo_pol E hE η (x ζ)).sub (isCombo_pol E hE _ ζ)
  have hΦeq : ∀ g, Bdd g →
      Φ g = ⟪η, (bfc E hE g * x) ζ⟫_ℂ - ⟪η, (x * bfc E hE g) ζ⟫_ℂ := by
    intro g hg
    simp only [Φ]
    rw [← inner_bfc E hE hg, ← inner_bfc E hE hg, mul_apply_eq_comp, mul_apply_eq_comp,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  have key : Φ g = 0 := by
    refine IsCombo.eq_zero_of_cos_sin hΦ ?_ ?_ ?_ hg
    · intro g hg
      have hsm : MeasurableSet (Set.Ioo (0 : ℝ) 2)ᶜ := measurableSet_Ioo.compl
      have hb : bfc E hE ((Set.Ioo (0 : ℝ) 2)ᶜ.indicator g) = 0 := by
        have : (Set.Ioo (0 : ℝ) 2)ᶜ.indicator g = g * (Set.Ioo (0 : ℝ) 2)ᶜ.indicator 1 := by
          funext a
          by_cases ha : a ∈ (Set.Ioo (0 : ℝ) 2)ᶜ <;> simp [Set.indicator, ha]
        rw [this, bfc_mul E hE hg (Bdd.indicator hsm), ← P, hP, mul_zero]
      rw [hΦeq _ (Bdd.indicator_of_bdd hsm hg), hb, zero_mul, mul_zero, sub_self]
    · intro t
      rw [hΦeq _ (bdd_cos_θ t), (commute_bfc_cos_sin E hE hx t).1.eq, sub_self]
    · intro t
      rw [hΦeq _ (bdd_sin_θ t), (commute_bfc_cos_sin E hE hx t).2.eq, sub_self]
  rw [hΦeq g hg] at key
  exact (sub_eq_zero.mp key).symm

theorem commute_of_commute_cbfc_gDel (hP : P E hE (Set.Ioo (0 : ℝ) 2)ᶜ = 0) {x : 𝓗 →L[ℂ] 𝓗}
    (hx : ∀ t, Commute x (cbfc E hE (gDel t))) : Commute x E := by
  rw [← bfc_trunc E hE]
  exact commute_bfc_of_commute_cbfc_gDel E hE hP hx (bdd_trunc E)

/-! ## The modular group -/

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (M : VonNeumannAlgebra K) (Ω : K)
variable (hs : IsSeparating (M : Set (K →L[ℂ] K)) Ω) (hc : IsCyclic (M : Set (K →L[ℂ] K)) Ω)

include hs hc in
theorem P_R_compl_Ioo : P (R M Ω) (R_isSelfAdjoint M Ω) (Set.Ioo (0 : ℝ) 2)ᶜ = 0 :=
  P_compl_Ioo_eq_zero _ _ (spectrum_R_subset M Ω)
    (fun ξ h => (R_eq_zero_iff M Ω hc).mp (by rw [h]; simp))
    (fun ξ h => (two_sub_R_eq_zero_iff M Ω hs).mp
      (by rw [sub_apply, h, two_apply_eq, Complex.ofReal_ofNat, two_smul, sub_self]))

include hs hc in
/-- The spectral measures of `R` give no mass to `(0,2)ᶜ`. -/
theorem ν_R_compl_Ioo (ζ : K) :
    ν (R M Ω) (R_isSelfAdjoint M Ω) ζ (Set.Ioo (0 : ℝ) 2)ᶜ = 0 :=
  ν_compl_Ioo_eq_zero _ _ (spectrum_R_subset M Ω)
    (fun ξ h => (R_eq_zero_iff M Ω hc).mp (by rw [h]; simp))
    (fun ξ h => (two_sub_R_eq_zero_iff M Ω hs).mp
      (by rw [sub_apply, h, two_apply_eq, Complex.ofReal_ofNat, two_smul, sub_self])) ζ

include hs hc in
/-- **Fourier converse for the modular group**: commuting with every `Δ^{it}` means commuting
with `R` (the converse of `σ_eq_self_of_commute_R`). -/
theorem commute_R_of_commute_Δit {x : K →L[ℂ] K} (h : ∀ t, Commute x (Δit M Ω t)) :
    Commute x (R M Ω) :=
  commute_of_commute_cbfc_gDel _ _ (P_R_compl_Ioo M Ω hs hc) h

include hs hc in
/-- A fixed point of the modular group in `M` is central. -/
theorem isCentral_of_σ_eq_self {x : K →L[ℂ] K} (hx : x ∈ M) (h : ∀ t, σ M Ω t x = x) :
    IsCentral M Ω x :=
  ⟨hx, commute_R_of_commute_Δit M Ω hs hc fun t => ((σ_eq_self_iff M Ω t x).mp (h t)).symm⟩

end Modular

end VN

end CommutingRepetition

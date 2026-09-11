/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/SpectralMeasure.lean
-/
/-
# Spectral measures of vector states (Stage C1 of `PLAN-modulus-family.md`)

Proof layer of the von Neumann root `exists_modulusFamily` (nodes 1.3.1/1.3.2).

For a self-adjoint bounded operator `E` on a complex Hilbert space and a vector
`ξ`, the positive functional `f ↦ ⟪ξ, f(E) ξ⟫` on `C(spectrum ℝ E, ℝ)` is
represented (Riesz–Markov–Kakutani, Mathlib `RealRMK.rieszMeasure`) by a finite
measure on the compact spectrum; pushed forward to `ℝ` it is the **spectral
measure** `ν E hE ξ`, with `∫ g dν = ⟪ξ, cfc g E ξ⟫` for every continuous
`g : ℝ → ℝ` (`integral_ν`).

The **transfer principle** `transfer`/`transferC`: a linear identity among the
integrals of finitely many finite Borel measures on `ℝ` that holds for every
continuous test function holds for every bounded Borel function. (Finite Borel
measures on `ℝ` are regular and determined by `C_c(ℝ, ℝ)`; the signed
combination is split into two positive finite measures.) This is the only
uniqueness input of the Borel functional calculus in `VN/BorelCalculus.lean`.
Nothing here is a manuscript statement.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.MonotoneLimit

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace BorelCalc

open scoped InnerProductSpace Topology ENNReal CompactlySupported
open Filter MeasureTheory

set_option linter.unusedSectionVars false

/-! ### Finite measures on `ℝ` and the transfer principle -/

section Transfer

/-- Bounded measurable real functions are integrable against finite measures. -/
theorem integrable_of_bdd {μ : Measure ℝ} [IsFiniteMeasure μ] {g : ℝ → ℝ}
    (hg : Measurable g) {C : ℝ} (hC : ∀ t, |g t| ≤ C) : Integrable g μ :=
  Integrable.of_bound hg.aestronglyMeasurable C
    (Eventually.of_forall fun t => by simpa [Real.norm_eq_abs] using hC t)

theorem isFiniteMeasure_smul_of_ne_top {μ : Measure ℝ} [IsFiniteMeasure μ] {c : ℝ≥0∞}
    (hc : c ≠ ⊤) : IsFiniteMeasure (c • μ) :=
  ⟨by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top hc.lt_top (measure_lt_top μ _)⟩

theorem isFiniteMeasure_finset_sum {ι : Type*} (s : Finset ι) (μ : ι → Measure ℝ)
    (h : ∀ i, IsFiniteMeasure (μ i)) : IsFiniteMeasure (∑ i ∈ s, μ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; infer_instance
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have := ih
    have := h a
    infer_instance

theorem integrable_finset_sum_measure {ι : Type*} (s : Finset ι) (μ : ι → Measure ℝ)
    {g : ℝ → ℝ} (hg : ∀ i, Integrable g (μ i)) : Integrable g (∑ i ∈ s, μ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hg a).add_measure ih

theorem integral_finset_sum_measure' {ι : Type*} (s : Finset ι) (μ : ι → Measure ℝ)
    {g : ℝ → ℝ} (hg : ∀ i, Integrable g (μ i)) :
    ∫ t, g t ∂(∑ i ∈ s, μ i) = ∑ i ∈ s, ∫ t, g t ∂(μ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      integral_add_measure (hg a) (integrable_finset_sum_measure s μ hg), ih]

/-- The positive part of a real combination of measures: `∑ (a k)⁺ • m k`. -/
noncomputable def comb {n : ℕ} (m : Fin n → Measure ℝ) (a : Fin n → ℝ) : Measure ℝ :=
  ∑ k, ENNReal.ofReal (a k) • m k

instance comb_isFiniteMeasure {n : ℕ} (m : Fin n → Measure ℝ) [∀ k, IsFiniteMeasure (m k)]
    (a : Fin n → ℝ) : IsFiniteMeasure (comb m a) :=
  isFiniteMeasure_finset_sum _ _ fun k => isFiniteMeasure_smul_of_ne_top ENNReal.ofReal_ne_top

theorem integral_comb {n : ℕ} (m : Fin n → Measure ℝ) (a : Fin n → ℝ) {g : ℝ → ℝ}
    (hg : ∀ k, Integrable g (m k)) :
    ∫ t, g t ∂(comb m a) = ∑ k, max (a k) 0 * ∫ t, g t ∂(m k) := by
  unfold comb
  rw [integral_finset_sum_measure' _ _ fun k => (hg k).smul_measure ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_smul_measure, ENNReal.toReal_ofReal', smul_eq_mul]

/-- **Transfer principle** (real coefficients): a real-linear identity among the
integrals of finitely many finite measures on `ℝ` valid for all continuous test
functions is valid for all bounded Borel functions. -/
theorem transfer {n : ℕ} (m : Fin n → Measure ℝ) [∀ k, IsFiniteMeasure (m k)] (a : Fin n → ℝ)
    (h : ∀ g : ℝ → ℝ, Continuous g → ∑ k, a k * ∫ t, g t ∂(m k) = 0)
    {g : ℝ → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ t, |g t| ≤ C) :
    ∑ k, a k * ∫ t, g t ∂(m k) = 0 := by
  have key : ∀ g : ℝ → ℝ, (∀ k, Integrable g (m k)) →
      ∑ k, a k * ∫ t, g t ∂(m k) = ∫ t, g t ∂(comb m a) - ∫ t, g t ∂(comb m (-a)) := by
    intro g hg
    rw [integral_comb m a hg, integral_comb m (-a) hg, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.neg_apply, ← sub_mul]
    congr 1
    rcases le_total 0 (a k) with h0 | h0
    · rw [max_eq_left h0, max_eq_right (neg_nonpos.mpr h0), sub_zero]
    · rw [max_eq_right h0, max_eq_left (neg_nonneg.mpr h0), zero_sub, neg_neg]
  have heq : comb m a = comb m (-a) := by
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    have hf : Continuous f := f.continuous
    have hint : ∀ k, Integrable f (m k) := fun k =>
      hf.integrable_of_hasCompactSupport f.hasCompactSupport
    have := key f hint
    rw [h f hf] at this
    linarith
  rw [key g fun k => integrable_of_bdd hg hC, heq, sub_self]

/-- **Transfer principle** (complex coefficients). -/
theorem transferC {n : ℕ} (m : Fin n → Measure ℝ) [∀ k, IsFiniteMeasure (m k)] (a : Fin n → ℂ)
    (h : ∀ g : ℝ → ℝ, Continuous g → ∑ k, a k * ((∫ t, g t ∂(m k) : ℝ) : ℂ) = 0)
    {g : ℝ → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ t, |g t| ≤ C) :
    ∑ k, a k * ((∫ t, g t ∂(m k) : ℝ) : ℂ) = 0 := by
  have hre : ∀ g : ℝ → ℝ, (∑ k, a k * ((∫ t, g t ∂(m k) : ℝ) : ℂ)).re
      = ∑ k, (a k).re * ∫ t, g t ∂(m k) := by
    intro g
    simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero]
  have him : ∀ g : ℝ → ℝ, (∑ k, a k * ((∫ t, g t ∂(m k) : ℝ) : ℂ)).im
      = ∑ k, (a k).im * ∫ t, g t ∂(m k) := by
    intro g
    simp only [Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      zero_add]
  apply Complex.ext
  · rw [hre, Complex.zero_re]
    exact transfer m (fun k => (a k).re) (fun g hg => by rw [← hre, h g hg, Complex.zero_re])
      hg hC
  · rw [him, Complex.zero_im]
    exact transfer m (fun k => (a k).im) (fun g hg => by rw [← him, h g hg, Complex.zero_im])
      hg hC

end Transfer

/-! ### Self-adjoint operators: elementary inner-product facts -/

section SelfAdjoint

variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗] [CompleteSpace 𝓗]

theorem inner_sa {T : 𝓗 →L[ℂ] 𝓗} (hT : IsSelfAdjoint T) (x y : 𝓗) :
    ⟪x, T y⟫_ℂ = ⟪T x, y⟫_ℂ := by
  conv_rhs => rw [← ContinuousLinearMap.isSelfAdjoint_iff'.mp hT,
    ContinuousLinearMap.adjoint_inner_left]

/-- The quadratic form of a self-adjoint operator is real. -/
theorem inner_self_real {T : 𝓗 →L[ℂ] 𝓗} (hT : IsSelfAdjoint T) (ξ : 𝓗) :
    (((⟪ξ, T ξ⟫_ℂ).re : ℝ) : ℂ) = ⟪ξ, T ξ⟫_ℂ := by
  rw [← Complex.conj_eq_iff_re, inner_conj_symm, inner_sa hT]

theorem inner_self_im {T : 𝓗 →L[ℂ] 𝓗} (hT : IsSelfAdjoint T) (ξ : 𝓗) :
    (⟪ξ, T ξ⟫_ℂ).im = 0 := by
  have := inner_self_real hT ξ
  rw [← this, Complex.ofReal_im]

end SelfAdjoint

/-! ### The spectral measure of a vector state -/

section Spectral

variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗] [CompleteSpace 𝓗]
variable (E : 𝓗 →L[ℂ] 𝓗) (hE : IsSelfAdjoint E)

/-- The vector state `f ↦ re ⟪ξ, f(E) ξ⟫` on `C(spectrum ℝ E, ℝ)`, real-linear. -/
noncomputable def stateLin (ξ : 𝓗) : C(spectrum ℝ E, ℝ) →ₗ[ℝ] ℝ where
  toFun f := (⟪ξ, cfcHom hE f ξ⟫_ℂ).re
  map_add' f g := by
    rw [map_add, ContinuousLinearMap.add_apply, inner_add_right, Complex.add_re]
  map_smul' c f := by
    have e : c • cfcHom hE f ξ = ((c : ℂ)) • cfcHom hE f ξ :=
      @RCLike.real_smul_eq_coe_smul ℂ 𝓗 _ _ _ _ _ c (cfcHom hE f ξ)
    rw [map_smul, ContinuousLinearMap.smul_apply, RingHom.id_apply, smul_eq_mul, e,
      inner_smul_right, Complex.re_ofReal_mul]

theorem stateLin_apply (ξ : 𝓗) (f : C(spectrum ℝ E, ℝ)) :
    stateLin E hE ξ f = (⟪ξ, cfcHom hE f ξ⟫_ℂ).re := rfl

theorem stateLin_nonneg (ξ : 𝓗) {f : C(spectrum ℝ E, ℝ)} (hf : 0 ≤ f) :
    0 ≤ stateLin E hE ξ f := by
  set h : C(spectrum ℝ E, ℝ) :=
    ⟨fun t => Real.sqrt (f t), Real.continuous_sqrt.comp f.continuous⟩ with hh
  have hfh : f = h * h := by
    ext t
    simp only [ContinuousMap.mul_apply, hh, ContinuousMap.coe_mk]
    rw [Real.mul_self_sqrt (by simpa using ContinuousMap.le_def.mp hf t)]
  have hsa : IsSelfAdjoint (cfcHom hE h) := cfcHom_predicate hE h
  rw [stateLin_apply, hfh, map_mul, Resolver.Douglas.mulA, inner_sa hsa]
  exact inner_self_nonneg (𝕜 := ℂ) (x := cfcHom hE h ξ)

/-- The vector state as a positive linear functional on `C_c(spectrum ℝ E, ℝ)`. -/
noncomputable def Λ (ξ : 𝓗) : C_c(spectrum ℝ E, ℝ) →ₚ[ℝ] ℝ where
  toFun f := stateLin E hE ξ f.toContinuousMap
  map_add' f g := (stateLin E hE ξ).map_add f.toContinuousMap g.toContinuousMap
  map_smul' c f := (stateLin E hE ξ).map_smul c f.toContinuousMap
  monotone' f g hfg := by
    have h0 : 0 ≤ g.toContinuousMap - f.toContinuousMap := by
      rw [sub_nonneg]
      exact ContinuousMap.le_def.mpr fun t => CompactlySupportedContinuousMap.le_def.mp hfg t
    have := stateLin_nonneg E hE ξ h0
    rw [map_sub, sub_nonneg] at this
    exact this

theorem Λ_apply (ξ : 𝓗) (f : C_c(spectrum ℝ E, ℝ)) :
    Λ E hE ξ f = (⟪ξ, cfcHom hE f.toContinuousMap ξ⟫_ℂ).re := rfl

/-- The Riesz measure of the vector state, on the compact spectrum. -/
noncomputable def ν₀ (ξ : 𝓗) : Measure (spectrum ℝ E) := RealRMK.rieszMeasure (Λ E hE ξ)

instance ν₀_isFiniteMeasure (ξ : 𝓗) : IsFiniteMeasure (ν₀ E hE ξ) := by
  unfold ν₀; infer_instance

/-- **The spectral measure** of the vector state `ξ` for the self-adjoint
operator `E`: the Riesz measure of `f ↦ ⟪ξ, f(E) ξ⟫`, pushed forward to `ℝ`. -/
noncomputable def ν (ξ : 𝓗) : Measure ℝ := (ν₀ E hE ξ).map Subtype.val

instance ν_isFiniteMeasure (ξ : 𝓗) : IsFiniteMeasure (ν E hE ξ) :=
  Measure.isFiniteMeasure_map _ _

/-- The defining property: `∫ g dν_ξ = ⟪ξ, g(E) ξ⟫` for continuous `g`. -/
theorem integral_ν (ξ : 𝓗) {g : ℝ → ℝ} (hg : Continuous g) :
    ∫ t, g t ∂(ν E hE ξ) = (⟪ξ, cfc g E ξ⟫_ℂ).re := by
  unfold ν
  rw [integral_map measurable_subtype_coe.aemeasurable hg.aestronglyMeasurable]
  let f : C_c(spectrum ℝ E, ℝ) :=
    CompactlySupportedContinuousMap.continuousMapEquiv
      ((⟨g, hg⟩ : C(ℝ, ℝ)).restrict (spectrum ℝ E))
  have h1 : ∫ s, g (s : ℝ) ∂(ν₀ E hE ξ) = ∫ s, f s ∂(ν₀ E hE ξ) := rfl
  rw [h1]
  unfold ν₀
  rw [RealRMK.integral_rieszMeasure, Λ_apply, cfc_apply g E hE hg.continuousOn]
  rfl

theorem integral_ν_complex (ξ : 𝓗) {g : ℝ → ℝ} (hg : Continuous g) :
    ((∫ t, g t ∂(ν E hE ξ) : ℝ) : ℂ) = ⟪ξ, cfc g E ξ⟫_ℂ := by
  rw [integral_ν E hE ξ hg]
  exact inner_self_real (cfc_predicate g E) ξ

/-- The spectral measure is concentrated on the spectrum. -/
theorem ν_compl_spectrum (ξ : 𝓗) : ν E hE ξ (spectrum ℝ E)ᶜ = 0 := by
  unfold ν
  rw [Measure.map_apply measurable_subtype_coe (spectrum.isClosed E).measurableSet.compl]
  have : (Subtype.val : spectrum ℝ E → ℝ) ⁻¹' (spectrum ℝ E)ᶜ = ∅ := by
    ext s
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false,
      not_not]
    exact s.2
  rw [this, measure_empty]

/-- Total mass: `ν_ξ(ℝ) = ‖ξ‖²`. -/
theorem ν_univ_toReal (ξ : 𝓗) : (ν E hE ξ Set.univ).toReal = ‖ξ‖ ^ 2 := by
  have h := integral_ν E hE ξ (g := fun _ => (1 : ℝ)) continuous_const
  rw [integral_const, cfc_const (1 : ℝ) E hE, map_one, Resolver.Douglas.oneA, smul_eq_mul,
    mul_one, measureReal_def] at h
  rw [h]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) ξ

theorem ν_univ_real (ξ : 𝓗) : (ν E hE ξ).real Set.univ = ‖ξ‖ ^ 2 := ν_univ_toReal E hE ξ

/-- Integrals against the spectral measure are bounded by `C ‖ξ‖²`. -/
theorem abs_integral_ν_le (ξ : 𝓗) {g : ℝ → ℝ} {C : ℝ} (hC : ∀ t, |g t| ≤ C) :
    |∫ t, g t ∂(ν E hE ξ)| ≤ C * ‖ξ‖ ^ 2 := by
  have := norm_integral_le_of_norm_le_const (μ := ν E hE ξ) (f := g) (C := C)
    (Eventually.of_forall fun t => by simpa [Real.norm_eq_abs] using hC t)
  rwa [Real.norm_eq_abs, ν_univ_real] at this

theorem integral_ν_nonneg (ξ : 𝓗) {g : ℝ → ℝ} (hg : ∀ t, 0 ≤ g t) :
    0 ≤ ∫ t, g t ∂(ν E hE ξ) :=
  integral_nonneg hg

theorem integral_ν_mono (ξ : 𝓗) {g h : ℝ → ℝ} (hg : Measurable g) (hh : Measurable h)
    {C : ℝ} (hgC : ∀ t, |g t| ≤ C) (hhC : ∀ t, |h t| ≤ C) (hgh : ∀ t, g t ≤ h t) :
    ∫ t, g t ∂(ν E hE ξ) ≤ ∫ t, h t ∂(ν E hE ξ) :=
  integral_mono (integrable_of_bdd hg hgC) (integrable_of_bdd hh hhC) hgh

end Spectral

end BorelCalc

end CommutingRepetition

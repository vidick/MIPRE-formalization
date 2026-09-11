/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/JointSpectral.lean
-/
/-
# The joint spectral measure of a commuting pair (WP-B7, stage F)

For commuting self-adjoint `E₁, E₂` on a Hilbert space and a vector `ξ`, the
joint spectral measure `νP ξ` on `ℝ²` is the spectral measure of the *normal*
operator `Z = E₁ + i E₂` (Mathlib's `ℂ`-valued continuous functional calculus),
i.e. the Riesz measure of `f ↦ re ⟪ξ, f(Z) ξ⟫` on the compact spectrum of `Z`,
pushed forward to `ℝ²` by `z ↦ (re z, im z)`. Since `re(Z) = E₁` and
`im(Z) = E₂`, one gets `∫ g(s) h(t) dνP = ⟪ξ, g(E₁) h(E₂) ξ⟫` first for bounded
continuous `g, h`, then for bounded Borel `g, h` by the transfer principle of
`VN/BorelCalculus` in each variable separately. Consequences: rectangle masses
`νP(I × J) = ⟪ξ, 1_I(E₁) 1_J(E₂) ξ⟫` and the two marginals.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.SpectralProjection

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace BorelCalc

open scoped InnerProductSpace Topology ENNReal NNReal ComplexConjugate CompactlySupported
open Filter MeasureTheory

variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗] [CompleteSpace 𝓗]

/-! ### Commutation with the Borel calculus -/

section Commute

variable (E : 𝓗 →L[ℂ] 𝓗) (hE : IsSelfAdjoint E)

/-- An operator commuting with `E` commutes with the Borel calculus of `E`. -/
theorem commute_bfc {T : 𝓗 →L[ℂ] 𝓗} (hT : Commute E T) {g : ℝ → ℝ} (hg : Bdd g) :
    Commute (bfc E hE g) T := by
  rw [Commute, SemiconjBy]
  refine ext_of_inner fun ξ η => ?_
  rw [mul_apply_eq_comp, mul_apply_eq_comp, inner_bfc E hE hg,
    ← ContinuousLinearMap.adjoint_inner_left, inner_bfc E hE hg]
  refine IsCombo.eq (isCombo_pol E hE _ _) (isCombo_pol E hE _ _) (fun g hgc _ => ?_) hg
  rw [pol_cfc E hE hgc, pol_cfc E hE hgc, ContinuousLinearMap.adjoint_inner_left]
  show ⟪ξ, (cfc g E * T) η⟫_ℂ = ⟪ξ, (T * cfc g E) η⟫_ℂ
  rw [(hT.cfc_real g).eq]

theorem sa_mul_of_commute {A B : 𝓗 →L[ℂ] 𝓗} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (h : Commute A B) : IsSelfAdjoint (A * B) := by
  show star (A * B) = A * B
  rw [star_mul, hA.star_eq, hB.star_eq, h.eq]

end Commute

/-! ### The spectral measure of a normal operator, pushed to the plane -/

section Normal

variable (Z : 𝓗 →L[ℂ] 𝓗) (hZ : IsStarNormal Z)

/-- Real continuous functions on the spectrum, as complex-valued ones. -/
noncomputable def ofRealCM (f : C(spectrum ℂ Z, ℝ)) : C(spectrum ℂ Z, ℂ) :=
  ⟨fun s => (f s : ℂ), Complex.continuous_ofReal.comp f.continuous⟩

omit [CompleteSpace 𝓗] in
theorem ofRealCM_apply (f : C(spectrum ℂ Z, ℝ)) (s : spectrum ℂ Z) :
    ofRealCM Z f s = (f s : ℂ) := rfl

omit [CompleteSpace 𝓗] in
theorem ofRealCM_add (f g : C(spectrum ℂ Z, ℝ)) :
    ofRealCM Z (f + g) = ofRealCM Z f + ofRealCM Z g := by
  ext s; simp [ofRealCM_apply]

omit [CompleteSpace 𝓗] in
theorem ofRealCM_smul (c : ℝ) (f : C(spectrum ℂ Z, ℝ)) :
    ofRealCM Z (c • f) = (c : ℂ) • ofRealCM Z f := by
  ext s; simp [ofRealCM_apply]

omit [CompleteSpace 𝓗] in
theorem ofRealCM_mul (f g : C(spectrum ℂ Z, ℝ)) :
    ofRealCM Z (f * g) = ofRealCM Z f * ofRealCM Z g := by
  ext s; simp [ofRealCM_apply]

omit [CompleteSpace 𝓗] in
theorem star_ofRealCM (f : C(spectrum ℂ Z, ℝ)) : star (ofRealCM Z f) = ofRealCM Z f := by
  ext s; simp [ofRealCM_apply, Complex.conj_ofReal]

/-- The vector state `f ↦ re ⟪ξ, f(Z) ξ⟫` on `C(spectrum ℂ Z, ℝ)`. -/
noncomputable def stateLinC (ξ : 𝓗) : C(spectrum ℂ Z, ℝ) →ₗ[ℝ] ℝ where
  toFun f := (⟪ξ, cfcHom hZ (ofRealCM Z f) ξ⟫_ℂ).re
  map_add' f g := by
    rw [ofRealCM_add, map_add, add_apply, inner_add_right, Complex.add_re]
  map_smul' c f := by
    rw [ofRealCM_smul, map_smul, smul_apply, RingHom.id_apply, smul_eq_mul,
      inner_smul_right, Complex.re_ofReal_mul]

theorem stateLinC_apply (ξ : 𝓗) (f : C(spectrum ℂ Z, ℝ)) :
    stateLinC Z hZ ξ f = (⟪ξ, cfcHom hZ (ofRealCM Z f) ξ⟫_ℂ).re := rfl

theorem cfcHom_ofRealCM_sa (f : C(spectrum ℂ Z, ℝ)) : IsSelfAdjoint (cfcHom hZ (ofRealCM Z f)) := by
  show star _ = _
  rw [← map_star, star_ofRealCM]

theorem stateLinC_nonneg (ξ : 𝓗) {f : C(spectrum ℂ Z, ℝ)} (hf : 0 ≤ f) :
    0 ≤ stateLinC Z hZ ξ f := by
  set h : C(spectrum ℂ Z, ℝ) :=
    ⟨fun t => Real.sqrt (f t), Real.continuous_sqrt.comp f.continuous⟩ with hh
  have hfh : f = h * h := by
    ext t
    simp only [ContinuousMap.mul_apply, hh, ContinuousMap.coe_mk]
    rw [Real.mul_self_sqrt (by simpa using ContinuousMap.le_def.mp hf t)]
  rw [stateLinC_apply, hfh, ofRealCM_mul, map_mul, mul_apply_eq_comp,
    inner_sa (cfcHom_ofRealCM_sa Z hZ h)]
  exact inner_self_nonneg (𝕜 := ℂ) (x := cfcHom hZ (ofRealCM Z h) ξ)

/-- The vector state as a positive linear functional on `C_c(spectrum ℂ Z, ℝ)`. -/
noncomputable def ΛC (ξ : 𝓗) : C_c(spectrum ℂ Z, ℝ) →ₚ[ℝ] ℝ where
  toFun f := stateLinC Z hZ ξ f.toContinuousMap
  map_add' f g := (stateLinC Z hZ ξ).map_add f.toContinuousMap g.toContinuousMap
  map_smul' c f := (stateLinC Z hZ ξ).map_smul c f.toContinuousMap
  monotone' f g hfg := by
    have h0 : 0 ≤ g.toContinuousMap - f.toContinuousMap := by
      rw [sub_nonneg]
      exact ContinuousMap.le_def.mpr fun t => CompactlySupportedContinuousMap.le_def.mp hfg t
    have := stateLinC_nonneg Z hZ ξ h0
    rw [map_sub, sub_nonneg] at this
    exact this

theorem ΛC_apply (ξ : 𝓗) (f : C_c(spectrum ℂ Z, ℝ)) :
    ΛC Z hZ ξ f = (⟪ξ, cfcHom hZ (ofRealCM Z f.toContinuousMap) ξ⟫_ℂ).re := rfl

/-- The Riesz measure of the vector state on the compact spectrum of `Z`. -/
noncomputable def ρ (ξ : 𝓗) : Measure (spectrum ℂ Z) := RealRMK.rieszMeasure (ΛC Z hZ ξ)

instance ρ_isFiniteMeasure (ξ : 𝓗) : IsFiniteMeasure (ρ Z hZ ξ) := by
  unfold ρ; infer_instance

/-- `z ↦ (re z, im z)` on the spectrum. -/
def toPlane : spectrum ℂ Z → ℝ × ℝ := fun s => ((s : ℂ).re, (s : ℂ).im)

omit [CompleteSpace 𝓗] in
theorem measurable_toPlane : Measurable (toPlane Z) :=
  (Complex.measurable_re.comp measurable_subtype_coe).prodMk
    (Complex.measurable_im.comp measurable_subtype_coe)

/-- **The spectral measure of the normal operator `Z` at `ξ`, on the plane.** -/
noncomputable def νJ (ξ : 𝓗) : Measure (ℝ × ℝ) := (ρ Z hZ ξ).map (toPlane Z)

instance νJ_isFiniteMeasure (ξ : 𝓗) : IsFiniteMeasure (νJ Z hZ ξ) :=
  Measure.isFiniteMeasure_map _ _

/-- The defining property: `∫ F dνJ = re ⟪ξ, F(re Z, im Z) ξ⟫` for continuous `F`. -/
theorem integral_νJ (ξ : 𝓗) {F : ℝ × ℝ → ℝ} (hF : Continuous F) :
    ∫ p, F p ∂(νJ Z hZ ξ) =
      (⟪ξ, cfc (fun z : ℂ => ((F (z.re, z.im) : ℝ) : ℂ)) Z ξ⟫_ℂ).re := by
  have hFc : Continuous fun z : ℂ => F (z.re, z.im) :=
    hF.comp (Complex.continuous_re.prodMk Complex.continuous_im)
  unfold νJ
  rw [integral_map (measurable_toPlane Z).aemeasurable hF.aestronglyMeasurable]
  let f : C_c(spectrum ℂ Z, ℝ) :=
    CompactlySupportedContinuousMap.continuousMapEquiv
      ((⟨fun z : ℂ => F (z.re, z.im), hFc⟩ : C(ℂ, ℝ)).restrict (spectrum ℂ Z))
  have h1 : ∫ s, F (toPlane Z s) ∂(ρ Z hZ ξ) = ∫ s, f s ∂(ρ Z hZ ξ) := rfl
  rw [h1]
  unfold ρ
  rw [RealRMK.integral_rieszMeasure, ΛC_apply,
    cfc_apply (fun z : ℂ => ((F (z.re, z.im) : ℝ) : ℂ)) Z hZ
      (by exact (Complex.continuous_ofReal.comp hFc).continuousOn)]
  rfl

end Normal

/-! ### The commuting pair `E₁, E₂` and `Z = E₁ + i E₂` -/

section Pair

variable (E₁ E₂ : 𝓗 →L[ℂ] 𝓗)

/-- `Z = E₁ + i E₂`. -/
noncomputable def Zp : 𝓗 →L[ℂ] 𝓗 := E₁ + Complex.I • E₂

variable (h₁ : IsSelfAdjoint E₁) (h₂ : IsSelfAdjoint E₂) (hc : Commute E₁ E₂)

include h₁ h₂ in
theorem star_Zp : star (Zp E₁ E₂) = E₁ - Complex.I • E₂ := by
  unfold Zp
  rw [star_add, star_smul, Complex.star_def, Complex.conj_I, h₁.star_eq, h₂.star_eq, neg_smul,
    sub_eq_add_neg]

include h₁ h₂ hc in
theorem Zp_normal : IsStarNormal (Zp E₁ E₂) := by
  refine ⟨?_⟩
  rw [Commute, SemiconjBy, star_Zp E₁ E₂ h₁ h₂]
  unfold Zp
  simp only [mul_add, add_mul, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub,
    smul_smul]
  rw [hc.eq]
  module

include h₁ h₂ hc in
theorem cfc_re : cfc (fun z : ℂ => (z.re : ℂ)) (Zp E₁ E₂) = E₁ := by
  have hZ := Zp_normal E₁ E₂ h₁ h₂ hc
  have e : (fun z : ℂ => (z.re : ℂ)) = fun z => (1 / 2 : ℂ) * (z + star z) := by
    funext z; rw [Complex.re_eq_add_conj, Complex.star_def]; ring
  have hs : cfc (fun z : ℂ => star z) (Zp E₁ E₂) = star (Zp E₁ E₂) :=
    (cfc_star (fun z : ℂ => z) (Zp E₁ E₂)).trans (by rw [cfc_id' ℂ _ hZ])
  rw [e, cfc_const_mul (1 / 2 : ℂ) (fun z : ℂ => z + star z) (Zp E₁ E₂) (by fun_prop),
    cfc_add (Zp E₁ E₂) (fun z : ℂ => z) (fun z : ℂ => star z) (by fun_prop) (by fun_prop), cfc_id' ℂ _ hZ, hs,
    star_Zp E₁ E₂ h₁ h₂]
  unfold Zp
  module

include h₁ h₂ hc in
theorem cfc_im : cfc (fun z : ℂ => (z.im : ℂ)) (Zp E₁ E₂) = E₂ := by
  have hZ := Zp_normal E₁ E₂ h₁ h₂ hc
  have e : (fun z : ℂ => (z.im : ℂ)) = fun z => (-(Complex.I / 2)) * (z - star z) := by
    funext z
    rw [Complex.star_def, Complex.sub_conj, Complex.ofReal_mul]
    push_cast
    linear_combination (z.im : ℂ) * Complex.I_sq
  have hs : cfc (fun z : ℂ => star z) (Zp E₁ E₂) = star (Zp E₁ E₂) :=
    (cfc_star (fun z : ℂ => z) (Zp E₁ E₂)).trans (by rw [cfc_id' ℂ _ hZ])
  rw [e, cfc_const_mul (-(Complex.I / 2)) (fun z : ℂ => z - star z) (Zp E₁ E₂) (by fun_prop),
    cfc_sub (fun z : ℂ => z) (fun z : ℂ => star z) (Zp E₁ E₂) (by fun_prop) (by fun_prop),
    cfc_id' ℂ _ hZ, hs, star_Zp E₁ E₂ h₁ h₂]
  have e2 : Zp E₁ E₂ - (E₁ - Complex.I • E₂) = (2 * Complex.I) • E₂ := by
    unfold Zp; module
  rw [e2, smul_smul, show -(Complex.I / 2) * (2 * Complex.I) = 1 by
    linear_combination -Complex.I_sq, one_smul]

include h₁ h₂ hc in
theorem cfc_re_comp {g : ℝ → ℝ} (hg : Continuous g) :
    cfc (fun z : ℂ => ((g z.re : ℝ) : ℂ)) (Zp E₁ E₂) = cfc g E₁ := by
  have hZ := Zp_normal E₁ E₂ h₁ h₂ hc
  have := cfc_comp' (fun w : ℂ => ((g w.re : ℝ) : ℂ)) (fun z : ℂ => (z.re : ℂ)) (Zp E₁ E₂)
    (Complex.continuous_ofReal.comp (hg.comp Complex.continuous_re)).continuousOn
    (Complex.continuous_ofReal.comp Complex.continuous_re).continuousOn hZ
  rw [cfc_re E₁ E₂ h₁ h₂ hc] at this
  simp only [Complex.ofReal_re] at this
  rw [this, ← cfc_real_eq_complex g h₁]

include h₁ h₂ hc in
theorem cfc_im_comp {g : ℝ → ℝ} (hg : Continuous g) :
    cfc (fun z : ℂ => ((g z.im : ℝ) : ℂ)) (Zp E₁ E₂) = cfc g E₂ := by
  have hZ := Zp_normal E₁ E₂ h₁ h₂ hc
  have := cfc_comp' (fun w : ℂ => ((g w.re : ℝ) : ℂ)) (fun z : ℂ => (z.im : ℂ)) (Zp E₁ E₂)
    (Complex.continuous_ofReal.comp (hg.comp Complex.continuous_re)).continuousOn
    (Complex.continuous_ofReal.comp Complex.continuous_im).continuousOn hZ
  rw [cfc_im E₁ E₂ h₁ h₂ hc] at this
  simp only [Complex.ofReal_re] at this
  rw [this, ← cfc_real_eq_complex g h₂]

/-- **The joint spectral measure** of the commuting pair `(E₁, E₂)` at `ξ`. -/
noncomputable def νP (ξ : 𝓗) : Measure (ℝ × ℝ) := νJ (Zp E₁ E₂) (Zp_normal E₁ E₂ h₁ h₂ hc) ξ

instance νP_isFiniteMeasure (ξ : 𝓗) : IsFiniteMeasure (νP E₁ E₂ h₁ h₂ hc ξ) := by
  unfold νP; infer_instance

include hc in
theorem commute_cfc_cfc (g h : ℝ → ℝ) : Commute (cfc g E₁) (cfc h E₂) :=
  ((hc.cfc_real g).symm.cfc_real h).symm

include hc in
theorem commute_bfc_bfc {g h : ℝ → ℝ} (hg : Bdd g) (hh : Bdd h) :
    Commute (bfc E₁ h₁ g) (bfc E₂ h₂ h) :=
  (commute_bfc E₂ h₂ (commute_bfc E₁ h₁ hc hg).symm hh).symm

/-- Products: for continuous `g, h`, `∫ g(s) h(t) dνP = re ⟪ξ, g(E₁) h(E₂) ξ⟫`. -/
theorem integral_νP_mul_cont {g h : ℝ → ℝ} (hg : Continuous g) (hh : Continuous h) (ξ : 𝓗) :
    ∫ p, g p.1 * h p.2 ∂(νP E₁ E₂ h₁ h₂ hc ξ) = (⟪ξ, cfc g E₁ (cfc h E₂ ξ)⟫_ℂ).re := by
  unfold νP
  rw [integral_νJ _ _ ξ (F := fun p : ℝ × ℝ => g p.1 * h p.2)
    (by exact (hg.comp continuous_fst).mul (hh.comp continuous_snd))]
  simp only [Complex.ofReal_mul]
  rw [cfc_mul (fun z : ℂ => ((g z.re : ℝ) : ℂ)) (fun z : ℂ => ((h z.im : ℝ) : ℂ)) (Zp E₁ E₂)
    (Complex.continuous_ofReal.comp (hg.comp Complex.continuous_re)).continuousOn
    (Complex.continuous_ofReal.comp (hh.comp Complex.continuous_im)).continuousOn,
    cfc_re_comp E₁ E₂ h₁ h₂ hc hg, cfc_im_comp E₁ E₂ h₁ h₂ hc hh, mul_apply_eq_comp]

/-! ### Transfer to bounded Borel functions -/

/-- Bounded measurable functions are integrable against finite measures. -/
theorem integrable_of_bdd' {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ a, |f a| ≤ C) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C
    (Eventually.of_forall fun a => by simpa [Real.norm_eq_abs] using hC a)

theorem _root_.CommutingRepetition.BorelCalc.IsCombo.congr {Φ Ψ : (ℝ → ℝ) → ℂ}
    (hΦ : IsCombo Φ) (h : ∀ g, Bdd g → Φ g = Ψ g) : IsCombo Ψ := by
  obtain ⟨μ₁, μ₂, μ₃, μ₄, f₁, f₂, f₃, f₄, e⟩ := hΦ
  exact ⟨μ₁, μ₂, μ₃, μ₄, f₁, f₂, f₃, f₄, fun g hg => (h g hg).symm.trans (e g hg)⟩

/-- `g ↦ ∫ g(u a) w(a) dμ(a)` is a combination of finite measures on `ℝ`, for a finite
measure `μ`, a measurable `u` and a bounded measurable weight `w`. -/
theorem isCombo_integral_mul {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {u : α → ℝ} (hu : Measurable u) {w : α → ℝ} (hw : Measurable w) {C : ℝ}
    (hC : ∀ a, |w a| ≤ C) :
    IsCombo fun g => ((∫ a, g (u a) * w a ∂μ : ℝ) : ℂ) := by
  have hfin : ∀ v : α → ℝ, (∀ a, |v a| ≤ C) →
      IsFiniteMeasure ((μ.withDensity fun a => ((Real.toNNReal (v a) : ℝ≥0) : ℝ≥0∞)).map u) := by
    intro v hvC
    have : IsFiniteMeasure (μ.withDensity fun a => ((Real.toNNReal (v a) : ℝ≥0) : ℝ≥0∞)) := by
      refine isFiniteMeasure_withDensity ?_
      have hle : (fun a => ((Real.toNNReal (v a) : ℝ≥0) : ℝ≥0∞)) ≤ fun _ => ENNReal.ofReal C :=
        fun a => ENNReal.coe_le_coe.mpr
          (Real.toNNReal_le_toNNReal ((le_abs_self _).trans (hvC a)))
      refine ne_top_of_le_ne_top ?_ (lintegral_mono hle)
      rw [lintegral_const]
      exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ _)).ne
    exact Measure.isFiniteMeasure_map _ _
  have hint : ∀ v : α → ℝ, Measurable v → ∀ g : ℝ → ℝ, Bdd g →
      ∫ t, g t ∂((μ.withDensity fun a => ((Real.toNNReal (v a) : ℝ≥0) : ℝ≥0∞)).map u) =
        ∫ a, max (v a) 0 * g (u a) ∂μ := by
    intro v hv g hg
    rw [integral_map hu.aemeasurable hg.1.aestronglyMeasurable,
      integral_withDensity_eq_integral_smul hv.real_toNNReal]
    simp only [NNReal.smul_def, Real.coe_toNNReal', smul_eq_mul]
  have hCneg : ∀ a, |(-w) a| ≤ C := fun a => by rw [Pi.neg_apply, abs_neg]; exact hC a
  have hbd : ∀ v : α → ℝ, Measurable v → (∀ a, |v a| ≤ C) → ∀ g : ℝ → ℝ, Bdd g →
      Integrable (fun a => max (v a) 0 * g (u a)) μ := by
    intro v hv hvC g hg
    obtain ⟨D, hD⟩ := hg.2
    refine integrable_of_bdd' ((hv.max measurable_const).mul (hg.1.comp hu)) (C := C * D)
      fun a => ?_
    rw [abs_mul, abs_of_nonneg (le_max_right _ _)]
    exact mul_le_mul (max_le ((le_abs_self _).trans (hvC a)) ((abs_nonneg _).trans (hvC a)))
      (hD _) (abs_nonneg _) ((abs_nonneg _).trans (hvC a))
  refine ⟨_, _, 0, 0, hfin w hC, hfin (-w) hCneg, inferInstance, inferInstance,
    fun g hg => ?_⟩
  rw [hint w hw g hg, hint (-w) hw.neg g hg]
  simp only [integral_zero_measure, sub_zero, Complex.ofReal_zero, mul_zero, add_zero]
  congr 1
  rw [← integral_sub (hbd w hw hC g hg) (hbd (-w) hw.neg hCneg g hg)]
  refine integral_congr_ae (Eventually.of_forall fun a => ?_)
  simp only [Pi.neg_apply]
  rcases le_total 0 (w a) with h0 | h0
  · rw [max_eq_left h0, max_eq_right (neg_nonpos.mpr h0)]; ring
  · rw [max_eq_right h0, max_eq_left (neg_nonneg.mpr h0)]; ring

/-- Step 0: bounded continuous `g, h`. -/
theorem inner_bfc_bfc_cont {g h : ℝ → ℝ} (hgc : Continuous g) (hg : Bdd g) (hhc : Continuous h)
    (hh : Bdd h) (ξ : 𝓗) :
    ((∫ p, g p.1 * h p.2 ∂(νP E₁ E₂ h₁ h₂ hc ξ) : ℝ) : ℂ) =
      ⟪ξ, bfc E₁ h₁ g (bfc E₂ h₂ h ξ)⟫_ℂ := by
  rw [integral_νP_mul_cont E₁ E₂ h₁ h₂ hc hgc hhc ξ, bfc_cfc E₁ h₁ hg hgc, bfc_cfc E₂ h₂ hh hhc,
    ← mul_apply_eq_comp]
  exact inner_self_real (sa_mul_of_commute (cfc_predicate g E₁) (cfc_predicate h E₂)
    (commute_cfc_cfc E₁ E₂ hc g h)) ξ

/-- Step 1: bounded Borel `g`, bounded continuous `h` (transfer in `g`). -/
theorem inner_bfc_bfc_left {g h : ℝ → ℝ} (hg : Bdd g) (hhc : Continuous h) (hh : Bdd h)
    (ξ : 𝓗) :
    ((∫ p, g p.1 * h p.2 ∂(νP E₁ E₂ h₁ h₂ hc ξ) : ℝ) : ℂ) =
      ⟪ξ, bfc E₁ h₁ g (bfc E₂ h₂ h ξ)⟫_ℂ := by
  obtain ⟨C, hC⟩ := hh.2
  have hΦ : IsCombo fun g : ℝ → ℝ => ((∫ p, g p.1 * h p.2 ∂(νP E₁ E₂ h₁ h₂ hc ξ) : ℝ) : ℂ) :=
    isCombo_integral_mul (νP E₁ E₂ h₁ h₂ hc ξ) measurable_fst (hh.1.comp measurable_snd)
      fun p => hC p.2
  have hΨ : IsCombo fun g => ⟪ξ, bfc E₁ h₁ g (bfc E₂ h₂ h ξ)⟫_ℂ :=
    (isCombo_pol E₁ h₁ ξ (bfc E₂ h₂ h ξ)).congr fun g hg => (inner_bfc E₁ h₁ hg _ _).symm
  exact IsCombo.eq hΦ hΨ (fun g hgc hgb => inner_bfc_bfc_cont E₁ E₂ h₁ h₂ hc hgc hgb hhc hh ξ) hg

/-- **The product formula** for bounded Borel `g, h`:
`∫ g(s) h(t) dνP_ξ(s, t) = ⟪ξ, g(E₁) h(E₂) ξ⟫` (transfer in `h`). -/
theorem inner_bfc_bfc {g h : ℝ → ℝ} (hg : Bdd g) (hh : Bdd h) (ξ : 𝓗) :
    ((∫ p, g p.1 * h p.2 ∂(νP E₁ E₂ h₁ h₂ hc ξ) : ℝ) : ℂ) =
      ⟪ξ, bfc E₁ h₁ g (bfc E₂ h₂ h ξ)⟫_ℂ := by
  obtain ⟨C, hC⟩ := hg.2
  have hΦ : IsCombo fun h : ℝ → ℝ => ((∫ p, g p.1 * h p.2 ∂(νP E₁ E₂ h₁ h₂ hc ξ) : ℝ) : ℂ) := by
    refine (isCombo_integral_mul (νP E₁ E₂ h₁ h₂ hc ξ) measurable_snd (hg.1.comp measurable_fst)
      fun p => hC p.1).congr fun h _ => ?_
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun p => mul_comm _ _)
  have hΨ : IsCombo fun h => ⟪ξ, bfc E₁ h₁ g (bfc E₂ h₂ h ξ)⟫_ℂ :=
    (isCombo_pol E₂ h₂ (bfc E₁ h₁ g ξ) ξ).congr fun h hh => by
      rw [← inner_bfc E₂ h₂ hh, inner_sa (bfc_isSelfAdjoint E₁ h₁ hg)]
  exact IsCombo.eq hΦ hΨ (fun h hhc hhb => inner_bfc_bfc_left E₁ E₂ h₁ h₂ hc hg hhc hhb ξ) hh

theorem integral_νP_mul {g h : ℝ → ℝ} (hg : Bdd g) (hh : Bdd h) (ξ : 𝓗) :
    ∫ p, g p.1 * h p.2 ∂(νP E₁ E₂ h₁ h₂ hc ξ) = (⟪ξ, bfc E₁ h₁ g (bfc E₂ h₂ h ξ)⟫_ℂ).re := by
  rw [← inner_bfc_bfc E₁ E₂ h₁ h₂ hc hg hh ξ, Complex.ofReal_re]

/-! ### Rectangles and marginals -/

/-- Rectangle masses: `νP_ξ(I × J) = ⟪ξ, 1_I(E₁) 1_J(E₂) ξ⟫`. -/
theorem νP_prod {I J : Set ℝ} (hI : MeasurableSet I) (hJ : MeasurableSet J) (ξ : 𝓗) :
    (((νP E₁ E₂ h₁ h₂ hc ξ) (I ×ˢ J)).toReal : ℂ) = ⟪ξ, P E₁ h₁ I (P E₂ h₂ J ξ)⟫_ℂ := by
  show _ = ⟪ξ, bfc E₁ h₁ (I.indicator 1) (bfc E₂ h₂ (J.indicator 1) ξ)⟫_ℂ
  rw [← inner_bfc_bfc E₁ E₂ h₁ h₂ hc (Bdd.indicator hI) (Bdd.indicator hJ) ξ]
  congr 1
  rw [← measureReal_def, ← integral_indicator_one (hI.prod hJ)]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  obtain ⟨a, b⟩ := p
  exact Set.indicator_prod_one

theorem νP_prod_toReal {I J : Set ℝ} (hI : MeasurableSet I) (hJ : MeasurableSet J) (ξ : 𝓗) :
    ((νP E₁ E₂ h₁ h₂ hc ξ) (I ×ˢ J)).toReal = (⟪ξ, P E₁ h₁ I (P E₂ h₂ J ξ)⟫_ℂ).re := by
  rw [← νP_prod E₁ E₂ h₁ h₂ hc hI hJ ξ, Complex.ofReal_re]

/-- First marginal: the spectral measure of `E₁` at `ξ`. -/
theorem νP_map_fst (ξ : 𝓗) : (νP E₁ E₂ h₁ h₂ hc ξ).map Prod.fst = ν E₁ h₁ ξ := by
  refine Measure.ext fun I hI => ?_
  rw [Measure.map_apply measurable_fst hI, ← Set.prod_univ]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  apply Complex.ofReal_injective
  rw [νP_prod E₁ E₂ h₁ h₂ hc hI MeasurableSet.univ ξ, P_univ, one_apply_eq_self,
    inner_P E₁ h₁ hI]

/-- Second marginal: the spectral measure of `E₂` at `ξ`. -/
theorem νP_map_snd (ξ : 𝓗) : (νP E₁ E₂ h₁ h₂ hc ξ).map Prod.snd = ν E₂ h₂ ξ := by
  refine Measure.ext fun J hJ => ?_
  rw [Measure.map_apply measurable_snd hJ, ← Set.univ_prod]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  apply Complex.ofReal_injective
  rw [νP_prod E₁ E₂ h₁ h₂ hc MeasurableSet.univ hJ ξ, P_univ, one_apply_eq_self,
    inner_P E₂ h₂ hJ]

/-- Total mass `‖ξ‖²`. -/
theorem νP_univ_toReal (ξ : 𝓗) : ((νP E₁ E₂ h₁ h₂ hc ξ) Set.univ).toReal = ‖ξ‖ ^ 2 := by
  have := congrArg (fun m : Measure ℝ => m Set.univ) (νP_map_fst E₁ E₂ h₁ h₂ hc ξ)
  simp only [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ] at this
  rw [this, ν_univ_toReal]

end Pair

end BorelCalc

end CommutingRepetition

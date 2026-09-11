/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/JointBorel.lean
-/
/-
# The joint Borel functional calculus of a commuting self-adjoint pair (density stage E5.0)

For commuting self-adjoint `E₁, E₂` on a Hilbert space and a bounded Borel function
`F : ℝ × ℝ → ℝ`, the operator `F(E₁, E₂)` (`jbfc`) is defined by polarization of the
quadratic form `ξ ↦ ∫ F dνP_ξ`, where `νP_ξ` is the joint spectral measure of
`VN/JointSpectral.lean`. Everything is transferred from bounded *continuous* `F`,
where `F(E₁, E₂) = F(re Z, im Z)` is Mathlib's continuous calculus of the normal
operator `Z = E₁ + i E₂`, by the two-dimensional transfer principle (a combination
of four finite measures on `ℝ²` is determined by its values on compactly supported
continuous functions).

Main results: `jbfc_cfc` (continuous case), `jbfc_fst`/`jbfc_snd` (one-variable
functions give the one-variable Borel calculus), linearity, `jbfc_mul`, self-adjointness,
`norm_sq_jbfc`, `norm_jbfc_le`, dominated convergence `tendsto_jbfc`, commutation
`commute_jbfc`, membership `jbfc_mem`, the composition rule `bfc_jbfc` for continuous
`F` and bounded Borel `g` (`g(F(E₁,E₂)) = (g ∘ F)(E₁, E₂)`), and the complex version
`cjbfc`.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.JointSpectral
import MIPRE.Background.Repetition.CommutingRepetition.VN.ComplexBorel

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace BorelCalc

open scoped InnerProductSpace Topology ENNReal NNReal ComplexConjugate CompactlySupported
open Filter MeasureTheory

set_option linter.unusedSectionVars false

/-! ## Bounded Borel functions on the plane -/

/-- Bounded measurable real functions on `ℝ²`. -/
def Bdd2 (F : ℝ × ℝ → ℝ) : Prop := Measurable F ∧ ∃ C, ∀ p, |F p| ≤ C

namespace Bdd2

variable {F G : ℝ × ℝ → ℝ}

theorem measurable (hF : Bdd2 F) : Measurable F := hF.1

theorem integrable (hF : Bdd2 F) (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] : Integrable F μ := by
  obtain ⟨C, hC⟩ := hF.2
  exact integrable_of_bdd' hF.1 hC

theorem const (c : ℝ) : Bdd2 fun _ => c := ⟨measurable_const, |c|, fun _ => le_rfl⟩

theorem one : Bdd2 (1 : ℝ × ℝ → ℝ) := const 1

theorem zero : Bdd2 (0 : ℝ × ℝ → ℝ) := const 0

theorem add (hF : Bdd2 F) (hG : Bdd2 G) : Bdd2 (F + G) := by
  obtain ⟨C, hC⟩ := hF.2
  obtain ⟨D, hD⟩ := hG.2
  exact ⟨hF.1.add hG.1, C + D, fun p =>
    (abs_add_le _ _).trans (add_le_add (hC p) (hD p))⟩

theorem neg (hF : Bdd2 F) : Bdd2 (-F) := by
  obtain ⟨C, hC⟩ := hF.2
  exact ⟨hF.1.neg, C, fun p => by rw [Pi.neg_apply, abs_neg]; exact hC p⟩

theorem sub (hF : Bdd2 F) (hG : Bdd2 G) : Bdd2 (F - G) := by
  rw [sub_eq_add_neg]; exact hF.add hG.neg

theorem mul (hF : Bdd2 F) (hG : Bdd2 G) : Bdd2 (F * G) := by
  obtain ⟨C, hC⟩ := hF.2
  obtain ⟨D, hD⟩ := hG.2
  exact ⟨hF.1.mul hG.1, C * D, fun p => by
    rw [Pi.mul_apply, abs_mul]
    exact mul_le_mul (hC p) (hD p) (abs_nonneg _) ((abs_nonneg _).trans (hC p))⟩

theorem const_mul (c : ℝ) (hF : Bdd2 F) : Bdd2 fun p => c * F p := by
  have : (fun p => c * F p) = (fun _ => c) * F := rfl
  rw [this]; exact (const c).mul hF

theorem of_continuous (hF : Continuous F) {C : ℝ} (hC : ∀ p, |F p| ≤ C) : Bdd2 F :=
  ⟨hF.measurable, C, hC⟩

theorem comp_fst {g : ℝ → ℝ} (hg : Bdd g) : Bdd2 fun p => g p.1 := by
  obtain ⟨C, hC⟩ := hg.2
  exact ⟨hg.1.comp measurable_fst, C, fun p => hC _⟩

theorem comp_snd {g : ℝ → ℝ} (hg : Bdd g) : Bdd2 fun p => g p.2 := by
  obtain ⟨C, hC⟩ := hg.2
  exact ⟨hg.1.comp measurable_snd, C, fun p => hC _⟩

theorem comp {g : ℝ → ℝ} (hg : Bdd g) (hF : Measurable F) : Bdd2 fun p => g (F p) := by
  obtain ⟨C, hC⟩ := hg.2
  exact ⟨hg.1.comp hF, C, fun p => hC _⟩

theorem max_zero (hF : Bdd2 F) : Bdd2 fun p => max (F p) 0 := by
  obtain ⟨C, hC⟩ := hF.2
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  refine ⟨hF.1.max measurable_const, C, fun p =>
    abs_le.mpr ⟨?_, max_le ((le_abs_self _).trans (hC p)) hC0⟩⟩
  linarith [le_max_right (F p) 0]

theorem of_compactlySupported (f : C_c(ℝ × ℝ, ℝ)) : Bdd2 f := by
  obtain ⟨C, hC⟩ := (f.hasCompactSupport.isCompact_range f.continuous).isBounded.exists_norm_le
  exact ⟨f.continuous.measurable, C, fun p => hC _ (Set.mem_range_self p)⟩

end Bdd2

/-! ## Combinations of finite measures on the plane and the transfer principle -/

/-- `Φ` is a combination of four finite measures on `ℝ²`. -/
def IsCombo2 (Φ : (ℝ × ℝ → ℝ) → ℂ) : Prop :=
  ∃ μ₁ μ₂ μ₃ μ₄ : Measure (ℝ × ℝ), IsFiniteMeasure μ₁ ∧ IsFiniteMeasure μ₂ ∧
    IsFiniteMeasure μ₃ ∧ IsFiniteMeasure μ₄ ∧ ∀ F, Bdd2 F → Φ F =
      (((∫ p, F p ∂μ₁) - ∫ p, F p ∂μ₂ : ℝ) : ℂ) +
        Complex.I * (((∫ p, F p ∂μ₃) - ∫ p, F p ∂μ₄ : ℝ) : ℂ)

namespace IsCombo2

theorem integral (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] :
    IsCombo2 fun F => ((∫ p, F p ∂μ : ℝ) : ℂ) :=
  ⟨μ, 0, 0, 0, inferInstance, inferInstance, inferInstance, inferInstance, fun F _ => by
    simp⟩

theorem congr {Φ Ψ : (ℝ × ℝ → ℝ) → ℂ} (hΦ : IsCombo2 Φ) (h : ∀ F, Bdd2 F → Φ F = Ψ F) :
    IsCombo2 Ψ := by
  obtain ⟨μ₁, μ₂, μ₃, μ₄, f₁, f₂, f₃, f₄, e⟩ := hΦ
  exact ⟨μ₁, μ₂, μ₃, μ₄, f₁, f₂, f₃, f₄, fun F hF => (h F hF).symm.trans (e F hF)⟩

theorem add {Φ Ψ : (ℝ × ℝ → ℝ) → ℂ} (hΦ : IsCombo2 Φ) (hΨ : IsCombo2 Ψ) :
    IsCombo2 fun F => Φ F + Ψ F := by
  obtain ⟨μ₁, μ₂, μ₃, μ₄, h₁, h₂, h₃, h₄, hΦ⟩ := hΦ
  obtain ⟨ν₁, ν₂, ν₃, ν₄, k₁, k₂, k₃, k₄, hΨ⟩ := hΨ
  refine ⟨μ₁ + ν₁, μ₂ + ν₂, μ₃ + ν₃, μ₄ + ν₄, inferInstance, inferInstance, inferInstance,
    inferInstance, fun F hF => ?_⟩
  dsimp only
  rw [hΦ F hF, hΨ F hF, integral_add_measure (hF.integrable _) (hF.integrable _),
    integral_add_measure (hF.integrable _) (hF.integrable _),
    integral_add_measure (hF.integrable _) (hF.integrable _),
    integral_add_measure (hF.integrable _) (hF.integrable _)]
  push_cast
  ring

theorem smul_real (r : ℝ) {Φ : (ℝ × ℝ → ℝ) → ℂ} (hΦ : IsCombo2 Φ) :
    IsCombo2 fun F => (r : ℂ) * Φ F := by
  obtain ⟨μ₁, μ₂, μ₃, μ₄, h₁, h₂, h₃, h₄, hΦ⟩ := hΦ
  have hfin : ∀ (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] (c : ℝ),
      IsFiniteMeasure (ENNReal.ofReal c • μ) := fun μ _ c =>
    ⟨by rw [Measure.smul_apply, smul_eq_mul]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ _)⟩
  rcases le_total 0 r with hr | hr
  · refine ⟨ENNReal.ofReal r • μ₁, ENNReal.ofReal r • μ₂, ENNReal.ofReal r • μ₃,
      ENNReal.ofReal r • μ₄, hfin _ _, hfin _ _, hfin _ _, hfin _ _, fun F hF => ?_⟩
    dsimp only
    rw [hΦ F hF]
    simp only [integral_smul_measure, ENNReal.toReal_ofReal hr, smul_eq_mul]
    push_cast
    ring
  · refine ⟨ENNReal.ofReal (-r) • μ₂, ENNReal.ofReal (-r) • μ₁, ENNReal.ofReal (-r) • μ₄,
      ENNReal.ofReal (-r) • μ₃, hfin _ _, hfin _ _, hfin _ _, hfin _ _, fun F hF => ?_⟩
    dsimp only
    rw [hΦ F hF]
    simp only [integral_smul_measure, ENNReal.toReal_ofReal (neg_nonneg.mpr hr), smul_eq_mul]
    push_cast
    ring

theorem smul_I {Φ : (ℝ × ℝ → ℝ) → ℂ} (hΦ : IsCombo2 Φ) : IsCombo2 fun F => Complex.I * Φ F := by
  obtain ⟨μ₁, μ₂, μ₃, μ₄, h₁, h₂, h₃, h₄, hΦ⟩ := hΦ
  refine ⟨μ₄, μ₃, μ₁, μ₂, h₄, h₃, h₁, h₂, fun F hF => ?_⟩
  dsimp only
  rw [hΦ F hF]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem smul (c : ℂ) {Φ : (ℝ × ℝ → ℝ) → ℂ} (hΦ : IsCombo2 Φ) : IsCombo2 fun F => c * Φ F := by
  have : (fun F => c * Φ F) = fun F => (c.re : ℂ) * Φ F + Complex.I * ((c.im : ℂ) * Φ F) := by
    funext F
    conv_lhs => rw [← Complex.re_add_im c]
    ring
  rw [this]
  exact (hΦ.smul_real c.re).add (hΦ.smul_real c.im).smul_I

theorem neg {Φ : (ℝ × ℝ → ℝ) → ℂ} (hΦ : IsCombo2 Φ) : IsCombo2 fun F => -Φ F := by
  have : (fun F => -Φ F) = fun F => (-1 : ℂ) * Φ F := by funext F; ring
  rw [this]
  exact hΦ.smul (-1)

theorem sub {Φ Ψ : (ℝ × ℝ → ℝ) → ℂ} (hΦ : IsCombo2 Φ) (hΨ : IsCombo2 Ψ) :
    IsCombo2 fun F => Φ F - Ψ F := by
  have : (fun F => Φ F - Ψ F) = fun F => Φ F + -Ψ F := by funext F; ring
  rw [this]
  exact hΦ.add hΨ.neg

theorem conjugate {Φ : (ℝ × ℝ → ℝ) → ℂ} (hΦ : IsCombo2 Φ) : IsCombo2 fun F => conj (Φ F) := by
  obtain ⟨μ₁, μ₂, μ₃, μ₄, h₁, h₂, h₃, h₄, hΦ⟩ := hΦ
  refine ⟨μ₁, μ₂, μ₄, μ₃, h₁, h₂, h₄, h₃, fun F hF => ?_⟩
  dsimp only
  rw [hΦ F hF]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- **Transfer principle** on the plane: a combination vanishing on all compactly supported
continuous functions vanishes on all bounded Borel functions. -/
theorem transfer {Φ : (ℝ × ℝ → ℝ) → ℂ} (hΦ : IsCombo2 Φ)
    (h : ∀ F : ℝ × ℝ → ℝ, Continuous F → Bdd2 F → Φ F = 0) {F : ℝ × ℝ → ℝ} (hF : Bdd2 F) :
    Φ F = 0 := by
  obtain ⟨μ₁, μ₂, μ₃, μ₄, h₁, h₂, h₃, h₄, hΦ⟩ := hΦ
  have key : ∀ f : ℝ × ℝ → ℝ, Bdd2 f → Φ f = 0 → (∫ p, f p ∂μ₁ = ∫ p, f p ∂μ₂) ∧
      (∫ p, f p ∂μ₃ = ∫ p, f p ∂μ₄) := by
    intro f hf h0
    rw [hΦ f hf] at h0
    have hre := congrArg Complex.re h0
    have him := congrArg Complex.im h0
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, Complex.add_im, Complex.mul_im, Complex.zero_re, Complex.zero_im,
      zero_mul, one_mul, sub_zero, zero_add, add_zero, mul_zero] at hre him
    exact ⟨sub_eq_zero.mp hre, sub_eq_zero.mp him⟩
  have e12 : μ₁ = μ₂ := Measure.ext_of_integral_eq_on_compactlySupported fun f =>
    (key f (Bdd2.of_compactlySupported f)
      (h f f.continuous (Bdd2.of_compactlySupported f))).1
  have e34 : μ₃ = μ₄ := Measure.ext_of_integral_eq_on_compactlySupported fun f =>
    (key f (Bdd2.of_compactlySupported f)
      (h f f.continuous (Bdd2.of_compactlySupported f))).2
  rw [hΦ F hF, e12, e34]
  simp

theorem eq {Φ Ψ : (ℝ × ℝ → ℝ) → ℂ} (hΦ : IsCombo2 Φ) (hΨ : IsCombo2 Ψ)
    (h : ∀ F : ℝ × ℝ → ℝ, Continuous F → Bdd2 F → Φ F = Ψ F) {F : ℝ × ℝ → ℝ} (hF : Bdd2 F) :
    Φ F = Ψ F :=
  sub_eq_zero.mp ((hΦ.sub hΨ).transfer (fun F hFc hFb => sub_eq_zero.mpr (h F hFc hFb)) hF)

/-! #### Multiplying the test function by a fixed bounded Borel function -/

/-- The measure `H⁺ dμ`. -/
noncomputable def wd2 (μ : Measure (ℝ × ℝ)) (H : ℝ × ℝ → ℝ) : Measure (ℝ × ℝ) :=
  μ.withDensity fun p => ((Real.toNNReal (H p) : ℝ≥0) : ℝ≥0∞)

theorem wd2_isFiniteMeasure (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] {H : ℝ × ℝ → ℝ}
    (hH : Bdd2 H) : IsFiniteMeasure (wd2 μ H) := by
  obtain ⟨C, hC⟩ := hH.2
  refine isFiniteMeasure_withDensity ?_
  have hle : (fun p => ((Real.toNNReal (H p) : ℝ≥0) : ℝ≥0∞)) ≤ fun _ => ENNReal.ofReal C :=
    fun p => ENNReal.coe_le_coe.mpr (Real.toNNReal_le_toNNReal ((le_abs_self _).trans (hC p)))
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hle)
  rw [lintegral_const]
  exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ _)).ne

theorem integral_wd2 (μ : Measure (ℝ × ℝ)) {H : ℝ × ℝ → ℝ} (hH : Bdd2 H) (F : ℝ × ℝ → ℝ) :
    ∫ p, F p ∂(wd2 μ H) = ∫ p, max (H p) 0 * F p ∂μ := by
  unfold wd2
  rw [integral_withDensity_eq_integral_smul (hH.1.real_toNNReal) F]
  simp only [NNReal.smul_def, Real.coe_toNNReal', smul_eq_mul]

theorem integral_mul_eq_wd2 (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] {F H : ℝ × ℝ → ℝ}
    (hF : Bdd2 F) (hH : Bdd2 H) :
    ∫ p, (F * H) p ∂μ = ∫ p, F p ∂(wd2 μ H) - ∫ p, F p ∂(wd2 μ (-H)) := by
  rw [integral_wd2 μ hH, integral_wd2 μ hH.neg, ← integral_sub]
  · refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only [Pi.mul_apply, Pi.neg_apply]
    rcases le_total 0 (H p) with h0 | h0
    · rw [max_eq_left h0, max_eq_right (neg_nonpos.mpr h0)]; ring
    · rw [max_eq_right h0, max_eq_left (neg_nonneg.mpr h0)]; ring
  · exact (hH.max_zero.mul hF).integrable μ
  · exact (hH.neg.max_zero.mul hF).integrable μ

theorem mul_right {Φ : (ℝ × ℝ → ℝ) → ℂ} (hΦ : IsCombo2 Φ) {H : ℝ × ℝ → ℝ} (hH : Bdd2 H) :
    IsCombo2 fun F => Φ (F * H) := by
  obtain ⟨μ₁, μ₂, μ₃, μ₄, h₁, h₂, h₃, h₄, hΦ⟩ := hΦ
  have f₁ := wd2_isFiniteMeasure μ₁ hH
  have f₁' := wd2_isFiniteMeasure μ₁ hH.neg
  have f₂ := wd2_isFiniteMeasure μ₂ hH
  have f₂' := wd2_isFiniteMeasure μ₂ hH.neg
  have f₃ := wd2_isFiniteMeasure μ₃ hH
  have f₃' := wd2_isFiniteMeasure μ₃ hH.neg
  have f₄ := wd2_isFiniteMeasure μ₄ hH
  have f₄' := wd2_isFiniteMeasure μ₄ hH.neg
  refine ⟨wd2 μ₁ H + wd2 μ₂ (-H), wd2 μ₁ (-H) + wd2 μ₂ H, wd2 μ₃ H + wd2 μ₄ (-H),
    wd2 μ₃ (-H) + wd2 μ₄ H, inferInstance, inferInstance, inferInstance, inferInstance,
    fun F hF => ?_⟩
  dsimp only
  rw [hΦ (F * H) (hF.mul hH), integral_mul_eq_wd2 μ₁ hF hH, integral_mul_eq_wd2 μ₂ hF hH,
    integral_mul_eq_wd2 μ₃ hF hH, integral_mul_eq_wd2 μ₄ hF hH,
    integral_add_measure (hF.integrable _) (hF.integrable _),
    integral_add_measure (hF.integrable _) (hF.integrable _),
    integral_add_measure (hF.integrable _) (hF.integrable _),
    integral_add_measure (hF.integrable _) (hF.integrable _)]
  push_cast
  ring

theorem mul_left {Φ : (ℝ × ℝ → ℝ) → ℂ} (hΦ : IsCombo2 Φ) {H : ℝ × ℝ → ℝ} (hH : Bdd2 H) :
    IsCombo2 fun F => Φ (H * F) := by
  have : (fun F => Φ (H * F)) = fun F => Φ (F * H) := by funext F; rw [mul_comm]
  rw [this]
  exact hΦ.mul_right hH

end IsCombo2

/-! ## The polarized form and the joint calculus -/

section Pair2

variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗] [CompleteSpace 𝓗]
variable (E₁ E₂ : 𝓗 →L[ℂ] 𝓗) (h₁ : IsSelfAdjoint E₁) (h₂ : IsSelfAdjoint E₂) (hc : Commute E₁ E₂)

/-- A real function on the plane, read as a function of a complex variable. -/
def Fc (F : ℝ × ℝ → ℝ) (z : ℂ) : ℂ := ((F (z.re, z.im) : ℝ) : ℂ)

theorem continuous_Fc {F : ℝ × ℝ → ℝ} (hF : Continuous F) : Continuous (Fc F) :=
  Complex.continuous_ofReal.comp (hF.comp (Complex.continuous_re.prodMk Complex.continuous_im))

theorem cfc_Fc_isSelfAdjoint (F : ℝ × ℝ → ℝ) : IsSelfAdjoint (cfc (Fc F) (Zp E₁ E₂)) := by
  show star _ = _
  rw [← cfc_star]
  congr 1
  funext z
  simp only [Fc, Complex.star_def, Complex.conj_ofReal]

/-- The quadratic form `Q2 F ξ = ∫ F dνP_ξ`. -/
noncomputable def Q2 (F : ℝ × ℝ → ℝ) (ξ : 𝓗) : ℂ :=
  ((∫ p, F p ∂(νP E₁ E₂ h₁ h₂ hc ξ) : ℝ) : ℂ)

/-- The polarized form. -/
noncomputable def pol2 (F : ℝ × ℝ → ℝ) (ξ η : 𝓗) : ℂ :=
  (Q2 E₁ E₂ h₁ h₂ hc F (ξ + η) - Q2 E₁ E₂ h₁ h₂ hc F (ξ - η) -
    Complex.I * Q2 E₁ E₂ h₁ h₂ hc F (ξ + Complex.I • η) +
    Complex.I * Q2 E₁ E₂ h₁ h₂ hc F (ξ - Complex.I • η)) / 4

theorem isCombo2_Q2 (ξ : 𝓗) : IsCombo2 fun F => Q2 E₁ E₂ h₁ h₂ hc F ξ := IsCombo2.integral _

theorem isCombo2_pol2 (ξ η : 𝓗) : IsCombo2 fun F => pol2 E₁ E₂ h₁ h₂ hc F ξ η := by
  unfold pol2
  simp_rw [div_eq_inv_mul]
  exact IsCombo2.smul _ ((((isCombo2_Q2 E₁ E₂ h₁ h₂ hc _).sub (isCombo2_Q2 E₁ E₂ h₁ h₂ hc _)).sub
    ((isCombo2_Q2 E₁ E₂ h₁ h₂ hc _).smul _)).add ((isCombo2_Q2 E₁ E₂ h₁ h₂ hc _).smul _))

theorem Q2_cfc {F : ℝ × ℝ → ℝ} (hF : Continuous F) (ξ : 𝓗) :
    Q2 E₁ E₂ h₁ h₂ hc F ξ = ⟪ξ, cfc (Fc F) (Zp E₁ E₂) ξ⟫_ℂ := by
  unfold Q2 νP
  rw [integral_νJ _ _ ξ hF]
  exact inner_self_real (cfc_Fc_isSelfAdjoint E₁ E₂ F) ξ

theorem pol2_cfc {F : ℝ × ℝ → ℝ} (hF : Continuous F) (ξ η : 𝓗) :
    pol2 E₁ E₂ h₁ h₂ hc F ξ η = ⟪ξ, cfc (Fc F) (Zp E₁ E₂) η⟫_ℂ := by
  have hsa := cfc_Fc_isSelfAdjoint E₁ E₂ F
  have key : ∀ ζ, Q2 E₁ E₂ h₁ h₂ hc F ζ =
      ⟪((cfc (Fc F) (Zp E₁ E₂) : 𝓗 →L[ℂ] 𝓗) : 𝓗 →ₗ[ℂ] 𝓗) ζ, ζ⟫_ℂ := fun ζ => by
    rw [Q2_cfc E₁ E₂ h₁ h₂ hc hF, ContinuousLinearMap.coe_coe, inner_sa hsa]
  rw [inner_sa hsa, ← ContinuousLinearMap.coe_coe (cfc (Fc F) (Zp E₁ E₂)),
    inner_map_polarization']
  unfold pol2
  simp only [key]

theorem pol2_add_left {F : ℝ × ℝ → ℝ} (hF : Bdd2 F) (ξ ξ' η : 𝓗) :
    pol2 E₁ E₂ h₁ h₂ hc F (ξ + ξ') η =
      pol2 E₁ E₂ h₁ h₂ hc F ξ η + pol2 E₁ E₂ h₁ h₂ hc F ξ' η :=
  IsCombo2.eq (isCombo2_pol2 E₁ E₂ h₁ h₂ hc _ _)
    ((isCombo2_pol2 E₁ E₂ h₁ h₂ hc _ _).add (isCombo2_pol2 E₁ E₂ h₁ h₂ hc _ _))
    (fun F hFc _ => by simp only [pol2_cfc E₁ E₂ h₁ h₂ hc hFc, inner_add_left]) hF

theorem pol2_smul_left {F : ℝ × ℝ → ℝ} (hF : Bdd2 F) (c : ℂ) (ξ η : 𝓗) :
    pol2 E₁ E₂ h₁ h₂ hc F (c • ξ) η = conj c * pol2 E₁ E₂ h₁ h₂ hc F ξ η :=
  IsCombo2.eq (isCombo2_pol2 E₁ E₂ h₁ h₂ hc _ _) ((isCombo2_pol2 E₁ E₂ h₁ h₂ hc _ _).smul _)
    (fun F hFc _ => by simp only [pol2_cfc E₁ E₂ h₁ h₂ hc hFc, inner_smul_left]) hF

theorem pol2_add_right {F : ℝ × ℝ → ℝ} (hF : Bdd2 F) (ξ η η' : 𝓗) :
    pol2 E₁ E₂ h₁ h₂ hc F ξ (η + η') =
      pol2 E₁ E₂ h₁ h₂ hc F ξ η + pol2 E₁ E₂ h₁ h₂ hc F ξ η' :=
  IsCombo2.eq (isCombo2_pol2 E₁ E₂ h₁ h₂ hc _ _)
    ((isCombo2_pol2 E₁ E₂ h₁ h₂ hc _ _).add (isCombo2_pol2 E₁ E₂ h₁ h₂ hc _ _))
    (fun F hFc _ => by simp only [pol2_cfc E₁ E₂ h₁ h₂ hc hFc, map_add, inner_add_right]) hF

theorem pol2_smul_right {F : ℝ × ℝ → ℝ} (hF : Bdd2 F) (c : ℂ) (ξ η : 𝓗) :
    pol2 E₁ E₂ h₁ h₂ hc F ξ (c • η) = c * pol2 E₁ E₂ h₁ h₂ hc F ξ η :=
  IsCombo2.eq (isCombo2_pol2 E₁ E₂ h₁ h₂ hc _ _) ((isCombo2_pol2 E₁ E₂ h₁ h₂ hc _ _).smul _)
    (fun F hFc _ => by simp only [pol2_cfc E₁ E₂ h₁ h₂ hc hFc, map_smul, inner_smul_right]) hF

theorem pol2_conj {F : ℝ × ℝ → ℝ} (hF : Bdd2 F) (ξ η : 𝓗) :
    conj (pol2 E₁ E₂ h₁ h₂ hc F η ξ) = pol2 E₁ E₂ h₁ h₂ hc F ξ η :=
  IsCombo2.eq ((isCombo2_pol2 E₁ E₂ h₁ h₂ hc _ _).conjugate) (isCombo2_pol2 E₁ E₂ h₁ h₂ hc _ _)
    (fun F hFc _ => by
      rw [pol2_cfc E₁ E₂ h₁ h₂ hc hFc, pol2_cfc E₁ E₂ h₁ h₂ hc hFc, inner_conj_symm,
        inner_sa (cfc_Fc_isSelfAdjoint E₁ E₂ F)]) hF

theorem pol2_self {F : ℝ × ℝ → ℝ} (hF : Bdd2 F) (ξ : 𝓗) :
    pol2 E₁ E₂ h₁ h₂ hc F ξ ξ = Q2 E₁ E₂ h₁ h₂ hc F ξ :=
  IsCombo2.eq (isCombo2_pol2 E₁ E₂ h₁ h₂ hc _ _) (isCombo2_Q2 E₁ E₂ h₁ h₂ hc _)
    (fun F hFc _ => by rw [pol2_cfc E₁ E₂ h₁ h₂ hc hFc, Q2_cfc E₁ E₂ h₁ h₂ hc hFc]) hF

theorem pol2_zero_left {F : ℝ × ℝ → ℝ} (hF : Bdd2 F) (η : 𝓗) :
    pol2 E₁ E₂ h₁ h₂ hc F 0 η = 0 := by
  have := pol2_smul_left E₁ E₂ h₁ h₂ hc hF 0 0 η
  rwa [zero_smul, map_zero, zero_mul] at this

theorem pol2_zero_right {F : ℝ × ℝ → ℝ} (hF : Bdd2 F) (ξ : 𝓗) :
    pol2 E₁ E₂ h₁ h₂ hc F ξ 0 = 0 := by
  have := pol2_smul_right E₁ E₂ h₁ h₂ hc hF 0 ξ 0
  rwa [zero_smul, zero_mul] at this

/-! #### Boundedness -/

theorem norm_Q2_le {F : ℝ × ℝ → ℝ} {C : ℝ} (hC : ∀ p, |F p| ≤ C) (ξ : 𝓗) :
    ‖Q2 E₁ E₂ h₁ h₂ hc F ξ‖ ≤ C * ‖ξ‖ ^ 2 := by
  rw [Q2, Complex.norm_real]
  have h := norm_integral_le_of_norm_le_const (μ := νP E₁ E₂ h₁ h₂ hc ξ) (f := F) (C := C)
    (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hC p)
  rwa [measureReal_def, νP_univ_toReal] at h

theorem norm_pol2_le_sq {F : ℝ × ℝ → ℝ} {C : ℝ} (hC : ∀ p, |F p| ≤ C) (ξ η : 𝓗) :
    ‖pol2 E₁ E₂ h₁ h₂ hc F ξ η‖ ≤ C * (‖ξ‖ ^ 2 + ‖η‖ ^ 2) := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have h1 := norm_Q2_le E₁ E₂ h₁ h₂ hc hC (ξ + η)
  have h2 := norm_Q2_le E₁ E₂ h₁ h₂ hc hC (ξ - η)
  have h3 := norm_Q2_le E₁ E₂ h₁ h₂ hc hC (ξ + Complex.I • η)
  have h4 := norm_Q2_le E₁ E₂ h₁ h₂ hc hC (ξ - Complex.I • η)
  have p1 : ‖ξ + η‖ ^ 2 + ‖ξ - η‖ ^ 2 = 2 * (‖ξ‖ ^ 2 + ‖η‖ ^ 2) := by
    have := parallelogram_law_with_norm ℂ ξ η
    nlinarith [this]
  have p2 : ‖ξ + Complex.I • η‖ ^ 2 + ‖ξ - Complex.I • η‖ ^ 2 = 2 * (‖ξ‖ ^ 2 + ‖η‖ ^ 2) := by
    have := parallelogram_law_with_norm ℂ ξ (Complex.I • η)
    rw [norm_smul, Complex.norm_I, one_mul] at this
    nlinarith [this]
  set Q := Q2 E₁ E₂ h₁ h₂ hc F
  have hn : ‖pol2 E₁ E₂ h₁ h₂ hc F ξ η‖ ≤ (‖Q (ξ + η)‖ + ‖Q (ξ - η)‖ +
      ‖Q (ξ + Complex.I • η)‖ + ‖Q (ξ - Complex.I • η)‖) / 4 := by
    unfold pol2
    rw [norm_div, Complex.norm_ofNat]
    gcongr
    calc ‖Q (ξ + η) - Q (ξ - η) - Complex.I * Q (ξ + Complex.I • η) +
          Complex.I * Q (ξ - Complex.I • η)‖
        ≤ ‖Q (ξ + η) - Q (ξ - η) - Complex.I * Q (ξ + Complex.I • η)‖ +
          ‖Complex.I * Q (ξ - Complex.I • η)‖ := norm_add_le _ _
      _ ≤ ‖Q (ξ + η) - Q (ξ - η)‖ + ‖Complex.I * Q (ξ + Complex.I • η)‖ +
          ‖Complex.I * Q (ξ - Complex.I • η)‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ ‖Q (ξ + η)‖ + ‖Q (ξ - η)‖ + ‖Complex.I * Q (ξ + Complex.I • η)‖ +
          ‖Complex.I * Q (ξ - Complex.I • η)‖ := by gcongr; exact norm_sub_le _ _
      _ = _ := by rw [norm_mul, norm_mul, Complex.norm_I, one_mul, one_mul]
  calc ‖pol2 E₁ E₂ h₁ h₂ hc F ξ η‖ ≤ _ := hn
    _ ≤ (C * ‖ξ + η‖ ^ 2 + C * ‖ξ - η‖ ^ 2 + C * ‖ξ + Complex.I • η‖ ^ 2 +
        C * ‖ξ - Complex.I • η‖ ^ 2) / 4 := by gcongr
    _ = C * (‖ξ‖ ^ 2 + ‖η‖ ^ 2) := by linear_combination (C / 4) * p1 + (C / 4) * p2

theorem norm_pol2_le {F : ℝ × ℝ → ℝ} (hF : Bdd2 F) {C : ℝ} (hC : ∀ p, |F p| ≤ C) (ξ η : 𝓗) :
    ‖pol2 E₁ E₂ h₁ h₂ hc F ξ η‖ ≤ 2 * C * ‖ξ‖ * ‖η‖ := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  by_cases hξ : ξ = 0
  · subst hξ
    rw [pol2_zero_left E₁ E₂ h₁ h₂ hc hF, norm_zero, norm_zero]
    simp
  by_cases hη : η = 0
  · subst hη
    rw [pol2_zero_right E₁ E₂ h₁ h₂ hc hF, norm_zero, norm_zero]
    simp
  have hξn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  have hηn : 0 < ‖η‖ := norm_pos_iff.mpr hη
  set t : ℝ := Real.sqrt (‖η‖ / ‖ξ‖) with ht
  have htpos : 0 < t := Real.sqrt_pos.mpr (div_pos hηn hξn)
  have htsq : t ^ 2 = ‖η‖ / ‖ξ‖ := Real.sq_sqrt (div_pos hηn hξn).le
  have hscale : pol2 E₁ E₂ h₁ h₂ hc F ξ η =
      pol2 E₁ E₂ h₁ h₂ hc F ((t : ℂ) • ξ) (((t⁻¹ : ℝ) : ℂ) • η) := by
    rw [pol2_smul_left E₁ E₂ h₁ h₂ hc hF, pol2_smul_right E₁ E₂ h₁ h₂ hc hF, Complex.conj_ofReal,
      ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ htpos.ne', Complex.ofReal_one, one_mul]
  rw [hscale]
  refine (norm_pol2_le_sq E₁ E₂ h₁ h₂ hc hC _ _).trans (le_of_eq ?_)
  rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos htpos, abs_of_pos (inv_pos.mpr htpos), mul_pow, mul_pow,
    htsq, inv_pow, htsq]
  field_simp
  ring

/-- The polarized form as a bounded sesquilinear map. -/
noncomputable def polForm2 {F : ℝ × ℝ → ℝ} (hF : Bdd2 F) : 𝓗 →L⋆[ℂ] 𝓗 →L[ℂ] ℂ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (pol2 E₁ E₂ h₁ h₂ hc F)
      (pol2_add_left E₁ E₂ h₁ h₂ hc hF)
      (fun c ξ η => by rw [pol2_smul_left E₁ E₂ h₁ h₂ hc hF, smul_eq_mul])
      (pol2_add_right E₁ E₂ h₁ h₂ hc hF)
      (fun c ξ η => by rw [pol2_smul_right E₁ E₂ h₁ h₂ hc hF, smul_eq_mul]; rfl))
    (2 * hF.2.choose) (fun ξ η => norm_pol2_le E₁ E₂ h₁ h₂ hc hF hF.2.choose_spec ξ η)

theorem polForm2_apply {F : ℝ × ℝ → ℝ} (hF : Bdd2 F) (ξ η : 𝓗) :
    polForm2 E₁ E₂ h₁ h₂ hc hF ξ η = pol2 E₁ E₂ h₁ h₂ hc F ξ η := rfl

/-! ### The joint Borel functional calculus -/

/-- **The joint Borel functional calculus** `F(E₁, E₂)` for a bounded Borel `F : ℝ² → ℝ`
(junk value `0` otherwise). -/
noncomputable def jbfc (F : ℝ × ℝ → ℝ) : 𝓗 →L[ℂ] 𝓗 := by
  classical
  exact if hF : Bdd2 F then
    InnerProductSpace.continuousLinearMapOfBilin (polForm2 E₁ E₂ h₁ h₂ hc hF) else 0

theorem jbfc_of_not {F : ℝ × ℝ → ℝ} (hF : ¬ Bdd2 F) : jbfc E₁ E₂ h₁ h₂ hc F = 0 := by
  unfold jbfc; rw [dif_neg hF]

theorem inner_jbfc_left {F : ℝ × ℝ → ℝ} (hF : Bdd2 F) (ξ η : 𝓗) :
    ⟪jbfc E₁ E₂ h₁ h₂ hc F ξ, η⟫_ℂ = pol2 E₁ E₂ h₁ h₂ hc F ξ η := by
  unfold jbfc
  rw [dif_pos hF]
  exact InnerProductSpace.continuousLinearMapOfBilin_apply _ ξ η

theorem inner_jbfc {F : ℝ × ℝ → ℝ} (hF : Bdd2 F) (ξ η : 𝓗) :
    ⟪ξ, jbfc E₁ E₂ h₁ h₂ hc F η⟫_ℂ = pol2 E₁ E₂ h₁ h₂ hc F ξ η := by
  rw [← inner_conj_symm, inner_jbfc_left E₁ E₂ h₁ h₂ hc hF, pol2_conj E₁ E₂ h₁ h₂ hc hF]

theorem inner_jbfc_self {F : ℝ × ℝ → ℝ} (hF : Bdd2 F) (ξ : 𝓗) :
    ⟪ξ, jbfc E₁ E₂ h₁ h₂ hc F ξ⟫_ℂ = Q2 E₁ E₂ h₁ h₂ hc F ξ := by
  rw [inner_jbfc E₁ E₂ h₁ h₂ hc hF, pol2_self E₁ E₂ h₁ h₂ hc hF]

theorem re_inner_jbfc_self {F : ℝ × ℝ → ℝ} (hF : Bdd2 F) (ξ : 𝓗) :
    (⟪ξ, jbfc E₁ E₂ h₁ h₂ hc F ξ⟫_ℂ).re = ∫ p, F p ∂(νP E₁ E₂ h₁ h₂ hc ξ) := by
  rw [inner_jbfc_self E₁ E₂ h₁ h₂ hc hF, Q2, Complex.ofReal_re]

theorem jbfc_unique {F : ℝ × ℝ → ℝ} (hF : Bdd2 F) {T : 𝓗 →L[ℂ] 𝓗}
    (h : ∀ ξ η, ⟪ξ, T η⟫_ℂ = pol2 E₁ E₂ h₁ h₂ hc F ξ η) : T = jbfc E₁ E₂ h₁ h₂ hc F :=
  ext_of_inner fun ξ η => by rw [h, inner_jbfc E₁ E₂ h₁ h₂ hc hF]

/-- On bounded continuous functions the joint calculus is the continuous calculus of
`Z = E₁ + i E₂`. -/
theorem jbfc_cfc {F : ℝ × ℝ → ℝ} (hF : Bdd2 F) (hFc : Continuous F) :
    jbfc E₁ E₂ h₁ h₂ hc F = cfc (Fc F) (Zp E₁ E₂) :=
  (jbfc_unique E₁ E₂ h₁ h₂ hc hF fun ξ η => (pol2_cfc E₁ E₂ h₁ h₂ hc hFc ξ η).symm).symm

theorem jbfc_isSelfAdjoint {F : ℝ × ℝ → ℝ} (hF : Bdd2 F) :
    IsSelfAdjoint (jbfc E₁ E₂ h₁ h₂ hc F) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  exact ext_of_inner fun ξ η => by
    rw [ContinuousLinearMap.adjoint_inner_right, inner_jbfc_left E₁ E₂ h₁ h₂ hc hF,
      inner_jbfc E₁ E₂ h₁ h₂ hc hF]

/-! #### One-variable functions -/

theorem Q2_comp_fst {g : ℝ → ℝ} (hg : Bdd g) (ξ : 𝓗) :
    Q2 E₁ E₂ h₁ h₂ hc (fun p => g p.1) ξ = Q E₁ h₁ g ξ := by
  unfold Q2 Q
  congr 1
  rw [← νP_map_fst E₁ E₂ h₁ h₂ hc ξ, integral_map measurable_fst.aemeasurable
    hg.1.aestronglyMeasurable]

theorem Q2_comp_snd {g : ℝ → ℝ} (hg : Bdd g) (ξ : 𝓗) :
    Q2 E₁ E₂ h₁ h₂ hc (fun p => g p.2) ξ = Q E₂ h₂ g ξ := by
  unfold Q2 Q
  congr 1
  rw [← νP_map_snd E₁ E₂ h₁ h₂ hc ξ, integral_map measurable_snd.aemeasurable
    hg.1.aestronglyMeasurable]

theorem pol2_comp_fst {g : ℝ → ℝ} (hg : Bdd g) (ξ η : 𝓗) :
    pol2 E₁ E₂ h₁ h₂ hc (fun p => g p.1) ξ η = pol E₁ h₁ g ξ η := by
  unfold pol2 pol
  simp only [Q2_comp_fst E₁ E₂ h₁ h₂ hc hg]

theorem pol2_comp_snd {g : ℝ → ℝ} (hg : Bdd g) (ξ η : 𝓗) :
    pol2 E₁ E₂ h₁ h₂ hc (fun p => g p.2) ξ η = pol E₂ h₂ g ξ η := by
  unfold pol2 pol
  simp only [Q2_comp_snd E₁ E₂ h₁ h₂ hc hg]

theorem jbfc_fst {g : ℝ → ℝ} (hg : Bdd g) :
    jbfc E₁ E₂ h₁ h₂ hc (fun p => g p.1) = bfc E₁ h₁ g :=
  (jbfc_unique E₁ E₂ h₁ h₂ hc (Bdd2.comp_fst hg) fun ξ η => by
    rw [inner_bfc E₁ h₁ hg, pol2_comp_fst E₁ E₂ h₁ h₂ hc hg]).symm

theorem jbfc_snd {g : ℝ → ℝ} (hg : Bdd g) :
    jbfc E₁ E₂ h₁ h₂ hc (fun p => g p.2) = bfc E₂ h₂ g :=
  (jbfc_unique E₁ E₂ h₁ h₂ hc (Bdd2.comp_snd hg) fun ξ η => by
    rw [inner_bfc E₂ h₂ hg, pol2_comp_snd E₁ E₂ h₁ h₂ hc hg]).symm

/-! #### Linearity -/

theorem Q2_add {F G : ℝ × ℝ → ℝ} (hF : Bdd2 F) (hG : Bdd2 G) (ξ : 𝓗) :
    Q2 E₁ E₂ h₁ h₂ hc (F + G) ξ = Q2 E₁ E₂ h₁ h₂ hc F ξ + Q2 E₁ E₂ h₁ h₂ hc G ξ := by
  unfold Q2
  rw [← Complex.ofReal_add, ← integral_add (hF.integrable _) (hG.integrable _)]
  rfl

theorem Q2_sub {F G : ℝ × ℝ → ℝ} (hF : Bdd2 F) (hG : Bdd2 G) (ξ : 𝓗) :
    Q2 E₁ E₂ h₁ h₂ hc (F - G) ξ = Q2 E₁ E₂ h₁ h₂ hc F ξ - Q2 E₁ E₂ h₁ h₂ hc G ξ := by
  unfold Q2
  rw [← Complex.ofReal_sub, ← integral_sub (hF.integrable _) (hG.integrable _)]
  rfl

theorem Q2_const_mul (c : ℝ) (F : ℝ × ℝ → ℝ) (ξ : 𝓗) :
    Q2 E₁ E₂ h₁ h₂ hc (fun p => c * F p) ξ = (c : ℂ) * Q2 E₁ E₂ h₁ h₂ hc F ξ := by
  unfold Q2
  rw [← Complex.ofReal_mul, MeasureTheory.integral_const_mul]

theorem pol2_add_fun {F G : ℝ × ℝ → ℝ} (hF : Bdd2 F) (hG : Bdd2 G) (ξ η : 𝓗) :
    pol2 E₁ E₂ h₁ h₂ hc (F + G) ξ η =
      pol2 E₁ E₂ h₁ h₂ hc F ξ η + pol2 E₁ E₂ h₁ h₂ hc G ξ η := by
  unfold pol2
  simp only [Q2_add E₁ E₂ h₁ h₂ hc hF hG]
  ring

theorem pol2_sub_fun {F G : ℝ × ℝ → ℝ} (hF : Bdd2 F) (hG : Bdd2 G) (ξ η : 𝓗) :
    pol2 E₁ E₂ h₁ h₂ hc (F - G) ξ η =
      pol2 E₁ E₂ h₁ h₂ hc F ξ η - pol2 E₁ E₂ h₁ h₂ hc G ξ η := by
  unfold pol2
  simp only [Q2_sub E₁ E₂ h₁ h₂ hc hF hG]
  ring

theorem pol2_const_mul (c : ℝ) (F : ℝ × ℝ → ℝ) (ξ η : 𝓗) :
    pol2 E₁ E₂ h₁ h₂ hc (fun p => c * F p) ξ η = (c : ℂ) * pol2 E₁ E₂ h₁ h₂ hc F ξ η := by
  unfold pol2
  simp only [Q2_const_mul E₁ E₂ h₁ h₂ hc c F]
  ring

theorem jbfc_add {F G : ℝ × ℝ → ℝ} (hF : Bdd2 F) (hG : Bdd2 G) :
    jbfc E₁ E₂ h₁ h₂ hc (F + G) = jbfc E₁ E₂ h₁ h₂ hc F + jbfc E₁ E₂ h₁ h₂ hc G :=
  (jbfc_unique E₁ E₂ h₁ h₂ hc (hF.add hG) fun ξ η => by
    rw [_root_.add_apply, inner_add_right, inner_jbfc E₁ E₂ h₁ h₂ hc hF,
      inner_jbfc E₁ E₂ h₁ h₂ hc hG, pol2_add_fun E₁ E₂ h₁ h₂ hc hF hG]).symm

theorem jbfc_sub {F G : ℝ × ℝ → ℝ} (hF : Bdd2 F) (hG : Bdd2 G) :
    jbfc E₁ E₂ h₁ h₂ hc (F - G) = jbfc E₁ E₂ h₁ h₂ hc F - jbfc E₁ E₂ h₁ h₂ hc G :=
  (jbfc_unique E₁ E₂ h₁ h₂ hc (hF.sub hG) fun ξ η => by
    rw [_root_.sub_apply, inner_sub_right, inner_jbfc E₁ E₂ h₁ h₂ hc hF,
      inner_jbfc E₁ E₂ h₁ h₂ hc hG, pol2_sub_fun E₁ E₂ h₁ h₂ hc hF hG]).symm

theorem jbfc_const_mul (c : ℝ) {F : ℝ × ℝ → ℝ} (hF : Bdd2 F) :
    jbfc E₁ E₂ h₁ h₂ hc (fun p => c * F p) = (c : ℂ) • jbfc E₁ E₂ h₁ h₂ hc F :=
  (jbfc_unique E₁ E₂ h₁ h₂ hc (hF.const_mul c) fun ξ η => by
    rw [_root_.smul_apply, inner_smul_right, inner_jbfc E₁ E₂ h₁ h₂ hc hF,
      pol2_const_mul E₁ E₂ h₁ h₂ hc c F]).symm

theorem jbfc_one : jbfc E₁ E₂ h₁ h₂ hc 1 = 1 := by
  have : (1 : ℝ × ℝ → ℝ) = fun p => (1 : ℝ → ℝ) p.1 := rfl
  rw [this, jbfc_fst E₁ E₂ h₁ h₂ hc Bdd.one, bfc_one]

theorem jbfc_zero : jbfc E₁ E₂ h₁ h₂ hc 0 = 0 := by
  have : (0 : ℝ × ℝ → ℝ) = fun p => (0 : ℝ → ℝ) p.1 := rfl
  rw [this, jbfc_fst E₁ E₂ h₁ h₂ hc Bdd.zero, bfc_zero]

theorem jbfc_const (c : ℝ) : jbfc E₁ E₂ h₁ h₂ hc (fun _ => c) = (c : ℂ) • 1 := by
  have : (fun _ : ℝ × ℝ => c) = fun p => c * (1 : ℝ × ℝ → ℝ) p := by funext p; simp
  rw [this, jbfc_const_mul E₁ E₂ h₁ h₂ hc c Bdd2.one, jbfc_one]

/-! #### Multiplicativity -/

theorem cfc_Fc_mul {F G : ℝ × ℝ → ℝ} (hF : Continuous F) (hG : Continuous G) :
    cfc (Fc (F * G)) (Zp E₁ E₂) = cfc (Fc F) (Zp E₁ E₂) * cfc (Fc G) (Zp E₁ E₂) := by
  have : Fc (F * G) = fun z => Fc F z * Fc G z := by
    funext z; simp only [Fc, Pi.mul_apply, Complex.ofReal_mul]
  rw [this, cfc_mul (Fc F) (Fc G) (Zp E₁ E₂) (continuous_Fc hF).continuousOn
    (continuous_Fc hG).continuousOn]

/-- Step 1: continuous `F`, Borel `G` (transfer in `G`). -/
theorem pol2_jbfc_right_cont {F G : ℝ × ℝ → ℝ} (hFc : Continuous F) (hF : Bdd2 F) (hG : Bdd2 G)
    (ξ η : 𝓗) :
    pol2 E₁ E₂ h₁ h₂ hc F ξ (jbfc E₁ E₂ h₁ h₂ hc G η) = pol2 E₁ E₂ h₁ h₂ hc (F * G) ξ η := by
  rw [pol2_cfc E₁ E₂ h₁ h₂ hc hFc, inner_sa (cfc_Fc_isSelfAdjoint E₁ E₂ F),
    inner_jbfc E₁ E₂ h₁ h₂ hc hG]
  refine IsCombo2.eq (isCombo2_pol2 E₁ E₂ h₁ h₂ hc _ _)
    ((isCombo2_pol2 E₁ E₂ h₁ h₂ hc ξ η).mul_left hF) (fun G hGc _ => ?_) hG
  rw [pol2_cfc E₁ E₂ h₁ h₂ hc hGc, pol2_cfc E₁ E₂ h₁ h₂ hc (hFc.mul hGc), cfc_Fc_mul E₁ E₂ hFc hGc,
    mul_apply_eq_comp, inner_sa (cfc_Fc_isSelfAdjoint E₁ E₂ F)]

/-- Step 2: Borel `F` and `G` (transfer in `F`). -/
theorem pol2_jbfc_right {F G : ℝ × ℝ → ℝ} (hF : Bdd2 F) (hG : Bdd2 G) (ξ η : 𝓗) :
    pol2 E₁ E₂ h₁ h₂ hc F ξ (jbfc E₁ E₂ h₁ h₂ hc G η) = pol2 E₁ E₂ h₁ h₂ hc (F * G) ξ η :=
  IsCombo2.eq (isCombo2_pol2 E₁ E₂ h₁ h₂ hc _ _) ((isCombo2_pol2 E₁ E₂ h₁ h₂ hc ξ η).mul_right hG)
    (fun _ hFc hFb => pol2_jbfc_right_cont E₁ E₂ h₁ h₂ hc hFc hFb hG ξ η) hF

/-- **Multiplicativity** of the joint Borel calculus. -/
theorem jbfc_mul {F G : ℝ × ℝ → ℝ} (hF : Bdd2 F) (hG : Bdd2 G) :
    jbfc E₁ E₂ h₁ h₂ hc (F * G) = jbfc E₁ E₂ h₁ h₂ hc F * jbfc E₁ E₂ h₁ h₂ hc G :=
  (jbfc_unique E₁ E₂ h₁ h₂ hc (hF.mul hG) fun ξ η => by
    rw [mul_apply_eq_comp, inner_jbfc E₁ E₂ h₁ h₂ hc hF, pol2_jbfc_right E₁ E₂ h₁ h₂ hc hF hG]).symm

theorem jbfc_comm {F G : ℝ × ℝ → ℝ} (hF : Bdd2 F) (hG : Bdd2 G) :
    jbfc E₁ E₂ h₁ h₂ hc F * jbfc E₁ E₂ h₁ h₂ hc G =
      jbfc E₁ E₂ h₁ h₂ hc G * jbfc E₁ E₂ h₁ h₂ hc F := by
  rw [← jbfc_mul E₁ E₂ h₁ h₂ hc hF hG, ← jbfc_mul E₁ E₂ h₁ h₂ hc hG hF, mul_comm]

/-! #### Norms and order -/

/-- `‖F(E₁,E₂) ξ‖² = ∫ F² dνP_ξ`. -/
theorem norm_sq_jbfc {F : ℝ × ℝ → ℝ} (hF : Bdd2 F) (ξ : 𝓗) :
    ‖jbfc E₁ E₂ h₁ h₂ hc F ξ‖ ^ 2 = ∫ p, F p ^ 2 ∂(νP E₁ E₂ h₁ h₂ hc ξ) := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_sa (jbfc_isSelfAdjoint E₁ E₂ h₁ h₂ hc hF),
    ← mul_apply_eq_comp, ← jbfc_mul E₁ E₂ h₁ h₂ hc hF hF]
  refine (re_inner_jbfc_self E₁ E₂ h₁ h₂ hc (hF.mul hF) ξ).trans ?_
  congr 1
  funext p
  simp only [Pi.mul_apply, sq]

theorem norm_jbfc_apply_le {F : ℝ × ℝ → ℝ} (hF : Bdd2 F) {C : ℝ} (hC : ∀ p, |F p| ≤ C) (ξ : 𝓗) :
    ‖jbfc E₁ E₂ h₁ h₂ hc F ξ‖ ≤ C * ‖ξ‖ := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
  rw [norm_sq_jbfc E₁ E₂ h₁ h₂ hc hF, mul_pow]
  have hF2 : Bdd2 fun p => F p ^ 2 := by
    have := hF.mul hF
    rwa [show F * F = fun p => F p ^ 2 from funext fun p => (sq (F p)).symm] at this
  calc ∫ p, F p ^ 2 ∂(νP E₁ E₂ h₁ h₂ hc ξ) ≤ ∫ _, C ^ 2 ∂(νP E₁ E₂ h₁ h₂ hc ξ) :=
        integral_mono (hF2.integrable _) (integrable_const _) fun p => by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hC p) 2
    _ = C ^ 2 * ‖ξ‖ ^ 2 := by
        rw [integral_const, smul_eq_mul, measureReal_def, νP_univ_toReal, mul_comm]

theorem norm_jbfc_le {F : ℝ × ℝ → ℝ} (hF : Bdd2 F) {C : ℝ} (hC : ∀ p, |F p| ≤ C) :
    ‖jbfc E₁ E₂ h₁ h₂ hc F‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ ((abs_nonneg _).trans (hC 0))
    (norm_jbfc_apply_le E₁ E₂ h₁ h₂ hc hF hC)

theorem jbfc_nonneg {F : ℝ × ℝ → ℝ} (hF : Bdd2 F) (h0 : ∀ p, 0 ≤ F p) :
    0 ≤ jbfc E₁ E₂ h₁ h₂ hc F :=
  Resolver.Douglas.nonneg_of_re_inner (jbfc_isSelfAdjoint E₁ E₂ h₁ h₂ hc hF) fun ξ => by
    rw [← inner_sa (jbfc_isSelfAdjoint E₁ E₂ h₁ h₂ hc hF), re_inner_jbfc_self E₁ E₂ h₁ h₂ hc hF]
    exact integral_nonneg h0

theorem jbfc_mono {F G : ℝ × ℝ → ℝ} (hF : Bdd2 F) (hG : Bdd2 G) (hle : ∀ p, F p ≤ G p) :
    jbfc E₁ E₂ h₁ h₂ hc F ≤ jbfc E₁ E₂ h₁ h₂ hc G := by
  rw [← sub_nonneg, ← jbfc_sub E₁ E₂ h₁ h₂ hc hG hF]
  exact jbfc_nonneg E₁ E₂ h₁ h₂ hc (hG.sub hF) fun p => by
    rw [Pi.sub_apply]; exact sub_nonneg.mpr (hle p)

/-- Dominated convergence: uniformly bounded `F i → Finf` pointwise gives
`F i (E₁,E₂) ξ → Finf (E₁,E₂) ξ`. -/
theorem tendsto_jbfc {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {F : ι → ℝ × ℝ → ℝ}
    {Finf : ℝ × ℝ → ℝ} (hF : ∀ i, Bdd2 (F i)) (hFinf : Bdd2 Finf) {C : ℝ}
    (hC : ∀ i p, |F i p| ≤ C) (hCinf : ∀ p, |Finf p| ≤ C)
    (hlim : ∀ p, Tendsto (fun i => F i p) l (𝓝 (Finf p))) (ξ : 𝓗) :
    Tendsto (fun i => jbfc E₁ E₂ h₁ h₂ hc (F i) ξ) l (𝓝 (jbfc E₁ E₂ h₁ h₂ hc Finf ξ)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq : Tendsto (fun i => ‖jbfc E₁ E₂ h₁ h₂ hc (F i) ξ - jbfc E₁ E₂ h₁ h₂ hc Finf ξ‖ ^ 2) l
      (𝓝 0) := by
    have heq : ∀ i, ‖jbfc E₁ E₂ h₁ h₂ hc (F i) ξ - jbfc E₁ E₂ h₁ h₂ hc Finf ξ‖ ^ 2 =
        ∫ p, (F i p - Finf p) ^ 2 ∂(νP E₁ E₂ h₁ h₂ hc ξ) := fun i => by
      rw [← _root_.sub_apply, ← jbfc_sub E₁ E₂ h₁ h₂ hc (hF i) hFinf,
        norm_sq_jbfc E₁ E₂ h₁ h₂ hc ((hF i).sub hFinf)]
      rfl
    simp only [heq]
    have h0 : (0 : ℝ) = ∫ _p, (0 : ℝ) ∂(νP E₁ E₂ h₁ h₂ hc ξ) := by simp
    rw [h0]
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => (2 * C) ^ 2)
      (Eventually.of_forall fun i =>
        (((hF i).1.sub hFinf.1).pow_const 2).aestronglyMeasurable)
      (Eventually.of_forall fun i => Eventually.of_forall fun p => ?_) (integrable_const _)
      (Eventually.of_forall fun p => ?_)
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← sq_abs]
      refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
      calc |F i p - Finf p| ≤ |F i p| + |Finf p| := abs_sub _ _
        _ ≤ C + C := add_le_add (hC i p) (hCinf p)
        _ = 2 * C := by ring
    · have : Tendsto (fun i => F i p - Finf p) l (𝓝 0) := by
        simpa using (hlim p).sub_const (Finf p)
      simpa using this.pow 2
  have := hsq.sqrt
  simpa only [Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] using this

/-! #### Commutation and membership -/

theorem commute_Zp {T : 𝓗 →L[ℂ] 𝓗} (hT₁ : Commute E₁ T) (hT₂ : Commute E₂ T) :
    Commute (Zp E₁ E₂) T := by
  unfold Zp
  exact hT₁.add_left (hT₂.smul_left _)

include h₁ h₂ in
theorem commute_star_Zp {T : 𝓗 →L[ℂ] 𝓗} (hT₁ : Commute E₁ T) (hT₂ : Commute E₂ T) :
    Commute (star (Zp E₁ E₂)) T := by
  rw [star_Zp E₁ E₂ h₁ h₂]
  exact hT₁.sub_left (hT₂.smul_left _)

/-- An operator commuting with `E₁` and `E₂` commutes with the joint calculus. -/
theorem commute_jbfc {T : 𝓗 →L[ℂ] 𝓗} (hT₁ : Commute E₁ T) (hT₂ : Commute E₂ T) {F : ℝ × ℝ → ℝ}
    (hF : Bdd2 F) : Commute (jbfc E₁ E₂ h₁ h₂ hc F) T := by
  rw [Commute, SemiconjBy]
  refine ext_of_inner fun ξ η => ?_
  rw [mul_apply_eq_comp, mul_apply_eq_comp, inner_jbfc E₁ E₂ h₁ h₂ hc hF,
    ← ContinuousLinearMap.adjoint_inner_left, inner_jbfc E₁ E₂ h₁ h₂ hc hF]
  refine IsCombo2.eq (isCombo2_pol2 E₁ E₂ h₁ h₂ hc _ _) (isCombo2_pol2 E₁ E₂ h₁ h₂ hc _ _)
    (fun F hFc _ => ?_) hF
  rw [pol2_cfc E₁ E₂ h₁ h₂ hc hFc, pol2_cfc E₁ E₂ h₁ h₂ hc hFc,
    ContinuousLinearMap.adjoint_inner_left]
  show ⟪ξ, (cfc (Fc F) (Zp E₁ E₂) * T) η⟫_ℂ = ⟪ξ, (T * cfc (Fc F) (Zp E₁ E₂)) η⟫_ℂ
  rw [((commute_Zp E₁ E₂ hT₁ hT₂).cfc (commute_star_Zp E₁ E₂ h₁ h₂ hT₁ hT₂) (Fc F)).eq]

/-- The joint calculus of a pair in a von Neumann algebra stays in it. -/
theorem jbfc_mem (N : VonNeumannAlgebra 𝓗) (hE₁ : E₁ ∈ N) (hE₂ : E₂ ∈ N) {F : ℝ × ℝ → ℝ}
    (hF : Bdd2 F) : jbfc E₁ E₂ h₁ h₂ hc F ∈ N := by
  refine VN.mem_of_commute_commutant N fun y hy => ?_
  exact (commute_jbfc E₁ E₂ h₁ h₂ hc (VN.commutant_mul_of_mem hE₁ hy).symm
    (VN.commutant_mul_of_mem hE₂ hy).symm hF).symm

/-! #### Composition with a one-variable Borel function (continuous `F`) -/

/-- The spectral measure of `F(E₁,E₂)` at `ξ` is the pushforward of `νP_ξ` under `F`. -/
theorem Q_jbfc {F : ℝ × ℝ → ℝ} (hF : Bdd2 F) (hFc : Continuous F) {g : ℝ → ℝ} (hg : Bdd g)
    (ξ : 𝓗) :
    Q (jbfc E₁ E₂ h₁ h₂ hc F) (jbfc_isSelfAdjoint E₁ E₂ h₁ h₂ hc hF) g ξ =
      Q2 E₁ E₂ h₁ h₂ hc (fun p => g (F p)) ξ := by
  have hsa := jbfc_isSelfAdjoint E₁ E₂ h₁ h₂ hc hF
  have hΨ : IsCombo fun g : ℝ → ℝ => Q2 E₁ E₂ h₁ h₂ hc (fun p => g (F p)) ξ := by
    refine (IsCombo.integral ((νP E₁ E₂ h₁ h₂ hc ξ).map F)).congr fun g hg => ?_
    unfold Q2
    congr 1
    rw [integral_map hF.1.aemeasurable hg.1.aestronglyMeasurable]
  refine IsCombo.eq (isCombo_Q _ hsa ξ) hΨ (fun g hgc hgb => ?_) hg
  rw [← inner_bfc_self _ hsa hgb, bfc_cfc _ hsa hgb hgc, jbfc_cfc E₁ E₂ h₁ h₂ hc hF hFc,
    Q2_cfc E₁ E₂ h₁ h₂ hc (F := fun p => g (F p)) (hgc.comp hFc),
    cfc_real_eq_complex g (cfc_Fc_isSelfAdjoint E₁ E₂ F),
    ← cfc_comp' (fun x : ℂ => ((g x.re : ℝ) : ℂ)) (Fc F) (Zp E₁ E₂)
      (Complex.continuous_ofReal.comp (hgc.comp Complex.continuous_re)).continuousOn
      (continuous_Fc hFc).continuousOn (Zp_normal E₁ E₂ h₁ h₂ hc)]
  have e : (fun x : ℂ => ((g (Fc F x).re : ℝ) : ℂ)) = Fc fun p => g (F p) := by
    funext z; simp only [Fc, Complex.ofReal_re]
  rw [e]

/-- **Composition**: `g(F(E₁,E₂)) = (g ∘ F)(E₁,E₂)` for continuous bounded `F` and bounded
Borel `g`. -/
theorem bfc_jbfc {F : ℝ × ℝ → ℝ} (hF : Bdd2 F) (hFc : Continuous F) {g : ℝ → ℝ} (hg : Bdd g) :
    bfc (jbfc E₁ E₂ h₁ h₂ hc F) (jbfc_isSelfAdjoint E₁ E₂ h₁ h₂ hc hF) g =
      jbfc E₁ E₂ h₁ h₂ hc (fun p => g (F p)) := by
  refine ext_of_inner_self fun ξ => ?_
  rw [inner_bfc_self _ _ hg, inner_jbfc_self E₁ E₂ h₁ h₂ hc (Bdd2.comp hg hF.1),
    Q_jbfc E₁ E₂ h₁ h₂ hc hF hFc hg]

/-- Almost-everywhere equal functions give the same operator. -/
theorem jbfc_congr_ae {F G : ℝ × ℝ → ℝ} (hF : Bdd2 F) (hG : Bdd2 G)
    (h : ∀ ξ, F =ᵐ[νP E₁ E₂ h₁ h₂ hc ξ] G) : jbfc E₁ E₂ h₁ h₂ hc F = jbfc E₁ E₂ h₁ h₂ hc G := by
  ext ξ
  rw [← sub_eq_zero, ← _root_.sub_apply, ← jbfc_sub E₁ E₂ h₁ h₂ hc hF hG, ← norm_eq_zero,
    ← pow_eq_zero_iff two_ne_zero, norm_sq_jbfc E₁ E₂ h₁ h₂ hc (hF.sub hG)]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [h ξ] with p hp
  simp [Pi.sub_apply, hp]

/-! ## Complex-valued functions -/

/-- Bounded measurable complex functions on the plane. -/
def CBdd2 (F : ℝ × ℝ → ℂ) : Prop := Measurable F ∧ ∃ C, ∀ p, ‖F p‖ ≤ C

namespace CBdd2

variable {F G : ℝ × ℝ → ℂ}

theorem re (hF : CBdd2 F) : Bdd2 fun p => (F p).re := by
  obtain ⟨C, hC⟩ := hF.2
  exact ⟨Complex.measurable_re.comp hF.1, C, fun p => (Complex.abs_re_le_norm _).trans (hC p)⟩

theorem im (hF : CBdd2 F) : Bdd2 fun p => (F p).im := by
  obtain ⟨C, hC⟩ := hF.2
  exact ⟨Complex.measurable_im.comp hF.1, C, fun p => (Complex.abs_im_le_norm _).trans (hC p)⟩

theorem ofReal {F : ℝ × ℝ → ℝ} (hF : Bdd2 F) : CBdd2 fun p => (F p : ℂ) := by
  obtain ⟨C, hC⟩ := hF.2
  exact ⟨Complex.measurable_ofReal.comp hF.1, C, fun p => by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hC p⟩

theorem const (z : ℂ) : CBdd2 fun _ => z := ⟨measurable_const, ‖z‖, fun _ => le_rfl⟩

theorem add (hF : CBdd2 F) (hG : CBdd2 G) : CBdd2 (F + G) := by
  obtain ⟨C, hC⟩ := hF.2
  obtain ⟨D, hD⟩ := hG.2
  exact ⟨hF.1.add hG.1, C + D, fun p => (norm_add_le _ _).trans (add_le_add (hC p) (hD p))⟩

theorem mul (hF : CBdd2 F) (hG : CBdd2 G) : CBdd2 (F * G) := by
  obtain ⟨C, hC⟩ := hF.2
  obtain ⟨D, hD⟩ := hG.2
  exact ⟨hF.1.mul hG.1, C * D, fun p => by
    rw [Pi.mul_apply, norm_mul]
    exact mul_le_mul (hC p) (hD p) (norm_nonneg _) ((norm_nonneg _).trans (hC p))⟩

theorem comp_fst {G : ℝ → ℂ} (hG : CBdd G) : CBdd2 fun p => G p.1 := by
  obtain ⟨C, hC⟩ := hG.2
  exact ⟨hG.1.comp measurable_fst, C, fun p => hC _⟩

theorem comp_snd {G : ℝ → ℂ} (hG : CBdd G) : CBdd2 fun p => G p.2 := by
  obtain ⟨C, hC⟩ := hG.2
  exact ⟨hG.1.comp measurable_snd, C, fun p => hC _⟩

theorem comp {G : ℝ → ℂ} (hG : CBdd G) {F : ℝ × ℝ → ℝ} (hF : Measurable F) :
    CBdd2 fun p => G (F p) := by
  obtain ⟨C, hC⟩ := hG.2
  exact ⟨hG.1.comp hF, C, fun p => hC _⟩

end CBdd2

/-- The complex joint Borel calculus `F(E₁,E₂) := (Re F)(E₁,E₂) + i (Im F)(E₁,E₂)`. -/
noncomputable def cjbfc (F : ℝ × ℝ → ℂ) : 𝓗 →L[ℂ] 𝓗 :=
  jbfc E₁ E₂ h₁ h₂ hc (fun p => (F p).re) + Complex.I • jbfc E₁ E₂ h₁ h₂ hc (fun p => (F p).im)

theorem cjbfc_ofReal (F : ℝ × ℝ → ℝ) :
    cjbfc E₁ E₂ h₁ h₂ hc (fun p => (F p : ℂ)) = jbfc E₁ E₂ h₁ h₂ hc F := by
  unfold cjbfc
  have h1 : (fun p => ((F p : ℂ)).re) = F := by funext p; exact Complex.ofReal_re _
  have h2 : (fun p => ((F p : ℂ)).im) = 0 := by funext p; exact Complex.ofReal_im _
  rw [h1, h2, jbfc_zero, smul_zero, add_zero]

theorem cjbfc_fst {G : ℝ → ℂ} (hG : CBdd G) :
    cjbfc E₁ E₂ h₁ h₂ hc (fun p => G p.1) = cbfc E₁ h₁ G := by
  unfold cjbfc cbfc
  rw [jbfc_fst E₁ E₂ h₁ h₂ hc (g := fun t => (G t).re) hG.re,
    jbfc_fst E₁ E₂ h₁ h₂ hc (g := fun t => (G t).im) hG.im]

theorem cjbfc_snd {G : ℝ → ℂ} (hG : CBdd G) :
    cjbfc E₁ E₂ h₁ h₂ hc (fun p => G p.2) = cbfc E₂ h₂ G := by
  unfold cjbfc cbfc
  rw [jbfc_snd E₁ E₂ h₁ h₂ hc (g := fun t => (G t).re) hG.re,
    jbfc_snd E₁ E₂ h₁ h₂ hc (g := fun t => (G t).im) hG.im]

theorem cjbfc_add {F G : ℝ × ℝ → ℂ} (hF : CBdd2 F) (hG : CBdd2 G) :
    cjbfc E₁ E₂ h₁ h₂ hc (F + G) = cjbfc E₁ E₂ h₁ h₂ hc F + cjbfc E₁ E₂ h₁ h₂ hc G := by
  unfold cjbfc
  have e1 : (fun p => ((F + G) p).re) = (fun p => (F p).re) + fun p => (G p).re := by
    funext p; simp
  have e2 : (fun p => ((F + G) p).im) = (fun p => (F p).im) + fun p => (G p).im := by
    funext p; simp
  rw [e1, e2, jbfc_add E₁ E₂ h₁ h₂ hc hF.re hG.re, jbfc_add E₁ E₂ h₁ h₂ hc hF.im hG.im, smul_add]
  abel

theorem cjbfc_mul {F G : ℝ × ℝ → ℂ} (hF : CBdd2 F) (hG : CBdd2 G) :
    cjbfc E₁ E₂ h₁ h₂ hc (F * G) = cjbfc E₁ E₂ h₁ h₂ hc F * cjbfc E₁ E₂ h₁ h₂ hc G := by
  unfold cjbfc
  have e1 : (fun p => ((F * G) p).re) =
      (fun p => (F p).re) * (fun p => (G p).re) - (fun p => (F p).im) * fun p => (G p).im := by
    funext p; simp [Complex.mul_re]
  have e2 : (fun p => ((F * G) p).im) =
      (fun p => (F p).re) * (fun p => (G p).im) + (fun p => (F p).im) * fun p => (G p).re := by
    funext p; simp [Complex.mul_im]
  rw [e1, e2, jbfc_sub E₁ E₂ h₁ h₂ hc (hF.re.mul hG.re) (hF.im.mul hG.im),
    jbfc_add E₁ E₂ h₁ h₂ hc (hF.re.mul hG.im) (hF.im.mul hG.re),
    jbfc_mul E₁ E₂ h₁ h₂ hc hF.re hG.re, jbfc_mul E₁ E₂ h₁ h₂ hc hF.im hG.im,
    jbfc_mul E₁ E₂ h₁ h₂ hc hF.re hG.im, jbfc_mul E₁ E₂ h₁ h₂ hc hF.im hG.re]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, Complex.I_mul_I,
    neg_one_smul, smul_add]
  abel

theorem cjbfc_star {F : ℝ × ℝ → ℂ} (hF : CBdd2 F) :
    star (cjbfc E₁ E₂ h₁ h₂ hc F) = cjbfc E₁ E₂ h₁ h₂ hc fun p => conj (F p) := by
  unfold cjbfc
  have e1 : (fun p => (conj (F p)).re) = fun p => (F p).re := by funext p; simp
  have e2 : (fun p => (conj (F p)).im) = fun p => (-1 : ℝ) * (F p).im := by funext p; simp
  rw [e1, e2, jbfc_const_mul E₁ E₂ h₁ h₂ hc (-1) hF.im, star_add, star_smul,
    (jbfc_isSelfAdjoint E₁ E₂ h₁ h₂ hc hF.re).star_eq,
    (jbfc_isSelfAdjoint E₁ E₂ h₁ h₂ hc hF.im).star_eq, Complex.star_def, Complex.conj_I,
    Complex.ofReal_neg, Complex.ofReal_one, neg_one_smul, smul_neg, neg_smul]

/-- **Composition** for complex `G`: `G(F(E₁,E₂)) = (G ∘ F)(E₁,E₂)` (continuous bounded real `F`,
bounded Borel `G`). -/
theorem cbfc_jbfc {F : ℝ × ℝ → ℝ} (hF : Bdd2 F) (hFc : Continuous F) {G : ℝ → ℂ} (hG : CBdd G) :
    cbfc (jbfc E₁ E₂ h₁ h₂ hc F) (jbfc_isSelfAdjoint E₁ E₂ h₁ h₂ hc hF) G =
      cjbfc E₁ E₂ h₁ h₂ hc (fun p => G (F p)) := by
  unfold cbfc cjbfc
  rw [bfc_jbfc E₁ E₂ h₁ h₂ hc hF hFc hG.re, bfc_jbfc E₁ E₂ h₁ h₂ hc hF hFc hG.im]

theorem commute_cjbfc {T : 𝓗 →L[ℂ] 𝓗} (hT₁ : Commute E₁ T) (hT₂ : Commute E₂ T) {F : ℝ × ℝ → ℂ}
    (hF : CBdd2 F) : Commute (cjbfc E₁ E₂ h₁ h₂ hc F) T := by
  unfold cjbfc
  exact (commute_jbfc E₁ E₂ h₁ h₂ hc hT₁ hT₂ hF.re).add_left
    ((commute_jbfc E₁ E₂ h₁ h₂ hc hT₁ hT₂ hF.im).smul_left _)

theorem cjbfc_mem (N : VonNeumannAlgebra 𝓗) (hE₁ : E₁ ∈ N) (hE₂ : E₂ ∈ N) {F : ℝ × ℝ → ℂ}
    (hF : CBdd2 F) : cjbfc E₁ E₂ h₁ h₂ hc F ∈ N := by
  unfold cjbfc
  exact add_mem (jbfc_mem E₁ E₂ h₁ h₂ hc N hE₁ hE₂ hF.re)
    (VN.smul_mem_vn N _ (jbfc_mem E₁ E₂ h₁ h₂ hc N hE₁ hE₂ hF.im))

theorem cjbfc_congr_ae {F G : ℝ × ℝ → ℂ} (hF : CBdd2 F) (hG : CBdd2 G)
    (h : ∀ ξ, F =ᵐ[νP E₁ E₂ h₁ h₂ hc ξ] G) : cjbfc E₁ E₂ h₁ h₂ hc F = cjbfc E₁ E₂ h₁ h₂ hc G := by
  unfold cjbfc
  rw [jbfc_congr_ae E₁ E₂ h₁ h₂ hc hF.re hG.re fun ξ => by
      filter_upwards [h ξ] with p hp; simp only [hp],
    jbfc_congr_ae E₁ E₂ h₁ h₂ hc hF.im hG.im fun ξ => by
      filter_upwards [h ξ] with p hp; simp only [hp]]

/-- `‖F(E₁,E₂) ξ‖² = ∫ |F|² dνP_ξ` for complex `F`. -/
theorem norm_sq_cjbfc {F : ℝ × ℝ → ℂ} (hF : CBdd2 F) (ξ : 𝓗) :
    ‖cjbfc E₁ E₂ h₁ h₂ hc F ξ‖ ^ 2 = ∫ p, ‖F p‖ ^ 2 ∂(νP E₁ E₂ h₁ h₂ hc ξ) := by
  have h1 : ⟪cjbfc E₁ E₂ h₁ h₂ hc F ξ, cjbfc E₁ E₂ h₁ h₂ hc F ξ⟫_ℂ =
      ⟪ξ, cjbfc E₁ E₂ h₁ h₂ hc (fun p => conj (F p) * F p) ξ⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
      cjbfc_star E₁ E₂ h₁ h₂ hc hF, ← mul_apply_eq_comp,
      ← cjbfc_mul E₁ E₂ h₁ h₂ hc (⟨Complex.continuous_conj.measurable.comp hF.1,
        hF.2.choose, fun p => by rw [Complex.norm_conj]; exact hF.2.choose_spec p⟩ :
        CBdd2 fun p => conj (F p)) hF]
    rfl
  have h2 : (fun p => conj (F p) * F p) = fun p => ((‖F p‖ ^ 2 : ℝ) : ℂ) := by
    funext p
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  have hb : Bdd2 fun p => ‖F p‖ ^ 2 := by
    obtain ⟨C, hC⟩ := hF.2
    refine ⟨(continuous_norm.measurable.comp hF.1).pow_const 2, C ^ 2, fun p => ?_⟩
    rw [abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hC p) 2
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), h1, h2, cjbfc_ofReal, inner_jbfc_self E₁ E₂ h₁ h₂ hc hb]
  rfl

end Pair2

end BorelCalc

end CommutingRepetition

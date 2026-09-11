/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/BorelCalculus.lean
-/
/-
# The Borel functional calculus of a self-adjoint operator (Stage C2)

Proof layer of the von Neumann root `exists_modulusFamily` (nodes 1.3.1/1.3.2).

For a self-adjoint bounded operator `E` on a complex Hilbert space and a
bounded Borel function `g : ℝ → ℝ`, `bfc E hE g` is the bounded operator whose
sesquilinear form is the polarization
`pol g ξ η = (Q(ξ+η) − Q(ξ−η) − i Q(ξ+iη) + i Q(ξ−iη))/4`,
`Q(ζ) = ∫ g dν_ζ`, of the spectral measures of `VN/SpectralMeasure.lean`.

The only analytic input is the **transfer principle**: every algebraic identity
of the forms `pol g` that holds for continuous `g` (where `pol g ξ η =
⟪ξ, cfc g E η⟫` by the polarization identity) holds for bounded Borel `g`,
because both sides are "combinations" `g ↦ (∫ g dμ₁ − ∫ g dμ₂) + i (∫ g dμ₃ −
∫ g dμ₄)` of finite measures, and finite Borel measures on `ℝ` are determined
by `C_c(ℝ)`. This gives sesquilinearity and boundedness (hence the operator, by
Riesz–Fréchet), self-adjointness, agreement with `cfc` on continuous functions,
linearity, and — through the identity `pol g ξ (bfc h η) = pol (g h) ξ η`,
proved first for continuous `g` by transfer in `h`, then by transfer in `g` —
**multiplicativity** `bfc (g h) = bfc g * bfc h`. Order properties follow from
the quadratic form. Nothing here is a manuscript statement.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.SpectralMeasure

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace BorelCalc

open scoped InnerProductSpace Topology ENNReal NNReal ComplexConjugate CompactlySupported
open Filter MeasureTheory

set_option linter.unusedSectionVars false

/-! ### Bounded Borel functions -/

/-- Bounded Borel functions on `ℝ`: the domain of the Borel functional calculus. -/
def Bdd (g : ℝ → ℝ) : Prop := Measurable g ∧ ∃ C, ∀ t, |g t| ≤ C

namespace Bdd

theorem measurable {g : ℝ → ℝ} (hg : Bdd g) : Measurable g := hg.1

theorem integrable {g : ℝ → ℝ} (hg : Bdd g) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable g μ := by
  obtain ⟨C, hC⟩ := hg.2
  exact integrable_of_bdd hg.1 hC

theorem const (c : ℝ) : Bdd fun _ => c := ⟨measurable_const, |c|, fun _ => le_rfl⟩

theorem one : Bdd (1 : ℝ → ℝ) := const 1

theorem zero : Bdd (0 : ℝ → ℝ) := const 0

theorem add {g h : ℝ → ℝ} (hg : Bdd g) (hh : Bdd h) : Bdd (g + h) := by
  obtain ⟨C, hC⟩ := hg.2
  obtain ⟨D, hD⟩ := hh.2
  exact ⟨hg.1.add hh.1, C + D, fun t =>
    (abs_add_le _ _).trans (add_le_add (hC t) (hD t))⟩

theorem neg {g : ℝ → ℝ} (hg : Bdd g) : Bdd (-g) := by
  obtain ⟨C, hC⟩ := hg.2
  exact ⟨hg.1.neg, C, fun t => by rw [Pi.neg_apply, abs_neg]; exact hC t⟩

theorem sub {g h : ℝ → ℝ} (hg : Bdd g) (hh : Bdd h) : Bdd (g - h) := by
  rw [sub_eq_add_neg]; exact hg.add hh.neg

theorem mul {g h : ℝ → ℝ} (hg : Bdd g) (hh : Bdd h) : Bdd (g * h) := by
  obtain ⟨C, hC⟩ := hg.2
  obtain ⟨D, hD⟩ := hh.2
  refine ⟨hg.1.mul hh.1, C * D, fun t => ?_⟩
  rw [Pi.mul_apply, abs_mul]
  exact mul_le_mul (hC t) (hD t) (abs_nonneg _) ((abs_nonneg _).trans (hC t))

theorem const_mul (c : ℝ) {g : ℝ → ℝ} (hg : Bdd g) : Bdd fun t => c * g t := (const c).mul hg

theorem indicator {I : Set ℝ} (hI : MeasurableSet I) : Bdd (I.indicator 1) :=
  ⟨measurable_one.indicator hI, 1, fun t => by
    by_cases h : t ∈ I <;> simp [Set.indicator, h]⟩

theorem of_continuous {g : ℝ → ℝ} (hg : Continuous g) {C : ℝ} (hC : ∀ t, |g t| ≤ C) : Bdd g :=
  ⟨hg.measurable, C, hC⟩

theorem measurableSet_of_indicator {I : Set ℝ} (h : Bdd (I.indicator (1 : ℝ → ℝ))) :
    MeasurableSet I := by
  have : I = (I.indicator (1 : ℝ → ℝ)) ⁻¹' {1} := by
    ext t
    by_cases ht : t ∈ I <;> simp [Set.indicator, ht]
  rw [this]
  exact h.1 (measurableSet_singleton 1)

theorem of_compactlySupported (f : C_c(ℝ, ℝ)) : Bdd f :=
  of_continuous f.continuous (C := ‖f.toBoundedContinuousFunction‖) fun t => by
    have := BoundedContinuousFunction.norm_coe_le_norm f.toBoundedContinuousFunction t
    simpa [Real.norm_eq_abs] using this

end Bdd

/-! ### Combinations of finite measures and the transfer principle -/

/-- `Φ` is a *combination*: `Φ g = (∫ g dμ₁ − ∫ g dμ₂) + i (∫ g dμ₃ − ∫ g dμ₄)` for
bounded Borel `g`, with `μ₁, …, μ₄` finite measures on `ℝ`. -/
def IsCombo (Φ : (ℝ → ℝ) → ℂ) : Prop :=
  ∃ μ₁ μ₂ μ₃ μ₄ : Measure ℝ, IsFiniteMeasure μ₁ ∧ IsFiniteMeasure μ₂ ∧ IsFiniteMeasure μ₃ ∧
    IsFiniteMeasure μ₄ ∧ ∀ g, Bdd g → Φ g =
      (((∫ t, g t ∂μ₁) - ∫ t, g t ∂μ₂ : ℝ) : ℂ) +
        Complex.I * (((∫ t, g t ∂μ₃) - ∫ t, g t ∂μ₄ : ℝ) : ℂ)

namespace IsCombo

theorem integral (μ : Measure ℝ) [IsFiniteMeasure μ] :
    IsCombo fun g => ((∫ t, g t ∂μ : ℝ) : ℂ) :=
  ⟨μ, 0, 0, 0, inferInstance, inferInstance, inferInstance, inferInstance, fun g _ => by
    simp⟩

theorem add {Φ Ψ : (ℝ → ℝ) → ℂ} (hΦ : IsCombo Φ) (hΨ : IsCombo Ψ) :
    IsCombo fun g => Φ g + Ψ g := by
  obtain ⟨μ₁, μ₂, μ₃, μ₄, h₁, h₂, h₃, h₄, hΦ⟩ := hΦ
  obtain ⟨ν₁, ν₂, ν₃, ν₄, k₁, k₂, k₃, k₄, hΨ⟩ := hΨ
  refine ⟨μ₁ + ν₁, μ₂ + ν₂, μ₃ + ν₃, μ₄ + ν₄, inferInstance, inferInstance, inferInstance,
    inferInstance, fun g hg => ?_⟩
  dsimp only
  rw [hΦ g hg, hΨ g hg, integral_add_measure (hg.integrable _) (hg.integrable _),
    integral_add_measure (hg.integrable _) (hg.integrable _),
    integral_add_measure (hg.integrable _) (hg.integrable _),
    integral_add_measure (hg.integrable _) (hg.integrable _)]
  push_cast
  ring

theorem smul_real (r : ℝ) {Φ : (ℝ → ℝ) → ℂ} (hΦ : IsCombo Φ) :
    IsCombo fun g => (r : ℂ) * Φ g := by
  obtain ⟨μ₁, μ₂, μ₃, μ₄, h₁, h₂, h₃, h₄, hΦ⟩ := hΦ
  rcases le_total 0 r with hr | hr
  · refine ⟨ENNReal.ofReal r • μ₁, ENNReal.ofReal r • μ₂, ENNReal.ofReal r • μ₃,
      ENNReal.ofReal r • μ₄, isFiniteMeasure_smul_of_ne_top ENNReal.ofReal_ne_top,
      isFiniteMeasure_smul_of_ne_top ENNReal.ofReal_ne_top,
      isFiniteMeasure_smul_of_ne_top ENNReal.ofReal_ne_top,
      isFiniteMeasure_smul_of_ne_top ENNReal.ofReal_ne_top, fun g hg => ?_⟩
    dsimp only
    rw [hΦ g hg]
    simp only [integral_smul_measure, ENNReal.toReal_ofReal hr, smul_eq_mul]
    push_cast
    ring
  · refine ⟨ENNReal.ofReal (-r) • μ₂, ENNReal.ofReal (-r) • μ₁, ENNReal.ofReal (-r) • μ₄,
      ENNReal.ofReal (-r) • μ₃, isFiniteMeasure_smul_of_ne_top ENNReal.ofReal_ne_top,
      isFiniteMeasure_smul_of_ne_top ENNReal.ofReal_ne_top,
      isFiniteMeasure_smul_of_ne_top ENNReal.ofReal_ne_top,
      isFiniteMeasure_smul_of_ne_top ENNReal.ofReal_ne_top, fun g hg => ?_⟩
    dsimp only
    rw [hΦ g hg]
    simp only [integral_smul_measure, ENNReal.toReal_ofReal (neg_nonneg.mpr hr), smul_eq_mul]
    push_cast
    ring

theorem smul_I {Φ : (ℝ → ℝ) → ℂ} (hΦ : IsCombo Φ) : IsCombo fun g => Complex.I * Φ g := by
  obtain ⟨μ₁, μ₂, μ₃, μ₄, h₁, h₂, h₃, h₄, hΦ⟩ := hΦ
  refine ⟨μ₄, μ₃, μ₁, μ₂, h₄, h₃, h₁, h₂, fun g hg => ?_⟩
  dsimp only
  rw [hΦ g hg]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem smul (c : ℂ) {Φ : (ℝ → ℝ) → ℂ} (hΦ : IsCombo Φ) : IsCombo fun g => c * Φ g := by
  have : (fun g => c * Φ g) = fun g => (c.re : ℂ) * Φ g + Complex.I * ((c.im : ℂ) * Φ g) := by
    funext g
    conv_lhs => rw [← Complex.re_add_im c]
    ring
  rw [this]
  exact (hΦ.smul_real c.re).add (hΦ.smul_real c.im).smul_I

theorem neg {Φ : (ℝ → ℝ) → ℂ} (hΦ : IsCombo Φ) : IsCombo fun g => -Φ g := by
  have : (fun g => -Φ g) = fun g => (-1 : ℂ) * Φ g := by funext g; ring
  rw [this]
  exact hΦ.smul (-1)

theorem sub {Φ Ψ : (ℝ → ℝ) → ℂ} (hΦ : IsCombo Φ) (hΨ : IsCombo Ψ) :
    IsCombo fun g => Φ g - Ψ g := by
  have : (fun g => Φ g - Ψ g) = fun g => Φ g + -Ψ g := by funext g; ring
  rw [this]
  exact hΦ.add hΨ.neg

theorem conjugate {Φ : (ℝ → ℝ) → ℂ} (hΦ : IsCombo Φ) : IsCombo fun g => conj (Φ g) := by
  obtain ⟨μ₁, μ₂, μ₃, μ₄, h₁, h₂, h₃, h₄, hΦ⟩ := hΦ
  refine ⟨μ₁, μ₂, μ₄, μ₃, h₁, h₂, h₄, h₃, fun g hg => ?_⟩
  dsimp only
  rw [hΦ g hg]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- **Transfer principle**: a combination vanishing on all bounded continuous
functions vanishes on all bounded Borel functions. -/
theorem transfer {Φ : (ℝ → ℝ) → ℂ} (hΦ : IsCombo Φ)
    (h : ∀ g : ℝ → ℝ, Continuous g → Bdd g → Φ g = 0) {g : ℝ → ℝ} (hg : Bdd g) : Φ g = 0 := by
  obtain ⟨μ₁, μ₂, μ₃, μ₄, h₁, h₂, h₃, h₄, hΦ⟩ := hΦ
  have key : ∀ f : ℝ → ℝ, Bdd f → Φ f = 0 → (∫ t, f t ∂μ₁ = ∫ t, f t ∂μ₂) ∧
      (∫ t, f t ∂μ₃ = ∫ t, f t ∂μ₄) := by
    intro f hf h0
    rw [hΦ f hf] at h0
    have hre := congrArg Complex.re h0
    have him := congrArg Complex.im h0
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, Complex.add_im, Complex.mul_im, Complex.zero_re, Complex.zero_im,
      zero_mul, one_mul, sub_zero, zero_add, add_zero, mul_zero] at hre him
    exact ⟨sub_eq_zero.mp hre, sub_eq_zero.mp him⟩
  have e12 : μ₁ = μ₂ := Measure.ext_of_integral_eq_on_compactlySupported fun f =>
    (key f (Bdd.of_compactlySupported f) (h f f.continuous (Bdd.of_compactlySupported f))).1
  have e34 : μ₃ = μ₄ := Measure.ext_of_integral_eq_on_compactlySupported fun f =>
    (key f (Bdd.of_compactlySupported f) (h f f.continuous (Bdd.of_compactlySupported f))).2
  rw [hΦ g hg, e12, e34]
  simp

/-- Two combinations agreeing on bounded continuous functions agree on bounded Borel
functions. -/
theorem eq {Φ Ψ : (ℝ → ℝ) → ℂ} (hΦ : IsCombo Φ) (hΨ : IsCombo Ψ)
    (h : ∀ g : ℝ → ℝ, Continuous g → Bdd g → Φ g = Ψ g) {g : ℝ → ℝ} (hg : Bdd g) : Φ g = Ψ g :=
  sub_eq_zero.mp ((hΦ.sub hΨ).transfer (fun g hgc hgb => sub_eq_zero.mpr (h g hgc hgb)) hg)

/-! #### Multiplying the test function by a fixed bounded Borel function -/

/-- The measure `h⁺ dμ`. -/
noncomputable def wd (μ : Measure ℝ) (h : ℝ → ℝ) : Measure ℝ :=
  μ.withDensity fun t => ((Real.toNNReal (h t) : ℝ≥0) : ℝ≥0∞)

theorem wd_isFiniteMeasure (μ : Measure ℝ) [IsFiniteMeasure μ] {h : ℝ → ℝ} (hh : Bdd h) :
    IsFiniteMeasure (wd μ h) := by
  obtain ⟨C, hC⟩ := hh.2
  refine isFiniteMeasure_withDensity ?_
  have hle : (fun t => ((Real.toNNReal (h t) : ℝ≥0) : ℝ≥0∞)) ≤ fun _ => ENNReal.ofReal C :=
    fun t => ENNReal.coe_le_coe.mpr (Real.toNNReal_le_toNNReal ((le_abs_self _).trans (hC t)))
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hle)
  rw [lintegral_const]
  exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ _)).ne

theorem integral_wd (μ : Measure ℝ) {h : ℝ → ℝ} (hh : Bdd h) (g : ℝ → ℝ) :
    ∫ t, g t ∂(wd μ h) = ∫ t, max (h t) 0 * g t ∂μ := by
  unfold wd
  rw [integral_withDensity_eq_integral_smul (hh.1.real_toNNReal) g]
  simp only [NNReal.smul_def, Real.coe_toNNReal', smul_eq_mul]

theorem _root_.CommutingRepetition.BorelCalc.Bdd.max_zero {h : ℝ → ℝ} (hh : Bdd h) :
    Bdd fun t => max (h t) 0 := by
  obtain ⟨C, hC⟩ := hh.2
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  refine ⟨hh.1.max measurable_const, C, fun t => abs_le.mpr ⟨?_, max_le ((le_abs_self _).trans (hC t)) hC0⟩⟩
  linarith [le_max_right (h t) 0]

theorem integral_mul_eq_wd (μ : Measure ℝ) [IsFiniteMeasure μ] {g h : ℝ → ℝ} (hg : Bdd g)
    (hh : Bdd h) : ∫ t, (g * h) t ∂μ = ∫ t, g t ∂(wd μ h) - ∫ t, g t ∂(wd μ (-h)) := by
  rw [integral_wd μ hh, integral_wd μ hh.neg, ← integral_sub]
  · refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [Pi.mul_apply, Pi.neg_apply]
    rcases le_total 0 (h t) with h0 | h0
    · rw [max_eq_left h0, max_eq_right (neg_nonpos.mpr h0)]; ring
    · rw [max_eq_right h0, max_eq_left (neg_nonneg.mpr h0)]; ring
  · exact (hh.max_zero.mul hg).integrable μ
  · exact (hh.neg.max_zero.mul hg).integrable μ

theorem mul_right {Φ : (ℝ → ℝ) → ℂ} (hΦ : IsCombo Φ) {h : ℝ → ℝ} (hh : Bdd h) :
    IsCombo fun g => Φ (g * h) := by
  obtain ⟨μ₁, μ₂, μ₃, μ₄, h₁, h₂, h₃, h₄, hΦ⟩ := hΦ
  have f₁ := wd_isFiniteMeasure μ₁ hh
  have f₁' := wd_isFiniteMeasure μ₁ hh.neg
  have f₂ := wd_isFiniteMeasure μ₂ hh
  have f₂' := wd_isFiniteMeasure μ₂ hh.neg
  have f₃ := wd_isFiniteMeasure μ₃ hh
  have f₃' := wd_isFiniteMeasure μ₃ hh.neg
  have f₄ := wd_isFiniteMeasure μ₄ hh
  have f₄' := wd_isFiniteMeasure μ₄ hh.neg
  refine ⟨wd μ₁ h + wd μ₂ (-h), wd μ₁ (-h) + wd μ₂ h, wd μ₃ h + wd μ₄ (-h),
    wd μ₃ (-h) + wd μ₄ h, inferInstance, inferInstance, inferInstance, inferInstance,
    fun g hg => ?_⟩
  dsimp only
  rw [hΦ (g * h) (hg.mul hh), integral_mul_eq_wd μ₁ hg hh, integral_mul_eq_wd μ₂ hg hh,
    integral_mul_eq_wd μ₃ hg hh, integral_mul_eq_wd μ₄ hg hh,
    integral_add_measure (hg.integrable _) (hg.integrable _),
    integral_add_measure (hg.integrable _) (hg.integrable _),
    integral_add_measure (hg.integrable _) (hg.integrable _),
    integral_add_measure (hg.integrable _) (hg.integrable _)]
  push_cast
  ring

theorem mul_left {Φ : (ℝ → ℝ) → ℂ} (hΦ : IsCombo Φ) {h : ℝ → ℝ} (hh : Bdd h) :
    IsCombo fun g => Φ (h * g) := by
  have : (fun g => Φ (h * g)) = fun g => Φ (g * h) := by funext g; rw [mul_comm]
  rw [this]
  exact hΦ.mul_right hh

end IsCombo

/-! ### The polarized form -/

section Pol

variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗] [CompleteSpace 𝓗]
variable (E : 𝓗 →L[ℂ] 𝓗) (hE : IsSelfAdjoint E)

/-- The quadratic form `Q g ξ = ∫ g dν_ξ` (as a complex number). -/
noncomputable def Q (g : ℝ → ℝ) (ξ : 𝓗) : ℂ := ((∫ t, g t ∂(ν E hE ξ) : ℝ) : ℂ)

/-- The polarized form: `pol g ξ η = ⟪ξ, g(E) η⟫` for continuous `g`. -/
noncomputable def pol (g : ℝ → ℝ) (ξ η : 𝓗) : ℂ :=
  (Q E hE g (ξ + η) - Q E hE g (ξ - η) - Complex.I * Q E hE g (ξ + Complex.I • η) +
    Complex.I * Q E hE g (ξ - Complex.I • η)) / 4

theorem isCombo_Q (ξ : 𝓗) : IsCombo fun g => Q E hE g ξ := IsCombo.integral _

theorem isCombo_pol (ξ η : 𝓗) : IsCombo fun g => pol E hE g ξ η := by
  unfold pol
  simp_rw [div_eq_inv_mul]
  exact IsCombo.smul _ ((((isCombo_Q E hE _).sub (isCombo_Q E hE _)).sub
    ((isCombo_Q E hE _).smul _)).add ((isCombo_Q E hE _).smul _))

theorem pol_cfc {g : ℝ → ℝ} (hg : Continuous g) (ξ η : 𝓗) :
    pol E hE g ξ η = ⟪ξ, cfc g E η⟫_ℂ := by
  have hsa : IsSelfAdjoint (cfc g E) := cfc_predicate g E
  have key : ∀ ζ, Q E hE g ζ = ⟪((cfc g E : 𝓗 →L[ℂ] 𝓗) : 𝓗 →ₗ[ℂ] 𝓗) ζ, ζ⟫_ℂ := fun ζ => by
    rw [Q, integral_ν_complex E hE ζ hg, ContinuousLinearMap.coe_coe, inner_sa hsa]
  rw [inner_sa hsa, ← ContinuousLinearMap.coe_coe (cfc g E), inner_map_polarization']
  unfold pol
  simp only [key]

theorem pol_add_left {g : ℝ → ℝ} (hg : Bdd g) (ξ ξ' η : 𝓗) :
    pol E hE g (ξ + ξ') η = pol E hE g ξ η + pol E hE g ξ' η :=
  IsCombo.eq (isCombo_pol E hE _ _) ((isCombo_pol E hE _ _).add (isCombo_pol E hE _ _))
    (fun g hgc _ => by simp only [pol_cfc E hE hgc, inner_add_left]) hg

theorem pol_smul_left {g : ℝ → ℝ} (hg : Bdd g) (c : ℂ) (ξ η : 𝓗) :
    pol E hE g (c • ξ) η = conj c * pol E hE g ξ η :=
  IsCombo.eq (isCombo_pol E hE _ _) ((isCombo_pol E hE _ _).smul _)
    (fun g hgc _ => by simp only [pol_cfc E hE hgc, inner_smul_left]) hg

theorem pol_add_right {g : ℝ → ℝ} (hg : Bdd g) (ξ η η' : 𝓗) :
    pol E hE g ξ (η + η') = pol E hE g ξ η + pol E hE g ξ η' :=
  IsCombo.eq (isCombo_pol E hE _ _) ((isCombo_pol E hE _ _).add (isCombo_pol E hE _ _))
    (fun g hgc _ => by simp only [pol_cfc E hE hgc, map_add, inner_add_right]) hg

theorem pol_smul_right {g : ℝ → ℝ} (hg : Bdd g) (c : ℂ) (ξ η : 𝓗) :
    pol E hE g ξ (c • η) = c * pol E hE g ξ η :=
  IsCombo.eq (isCombo_pol E hE _ _) ((isCombo_pol E hE _ _).smul _)
    (fun g hgc _ => by simp only [pol_cfc E hE hgc, map_smul, inner_smul_right]) hg

theorem pol_conj {g : ℝ → ℝ} (hg : Bdd g) (ξ η : 𝓗) :
    conj (pol E hE g η ξ) = pol E hE g ξ η :=
  IsCombo.eq ((isCombo_pol E hE _ _).conjugate) (isCombo_pol E hE _ _)
    (fun g hgc _ => by
      rw [pol_cfc E hE hgc, pol_cfc E hE hgc, inner_conj_symm, inner_sa (cfc_predicate g E)]) hg

theorem pol_self {g : ℝ → ℝ} (hg : Bdd g) (ξ : 𝓗) : pol E hE g ξ ξ = Q E hE g ξ :=
  IsCombo.eq (isCombo_pol E hE _ _) (isCombo_Q E hE _)
    (fun g hgc _ => by rw [pol_cfc E hE hgc, Q, integral_ν_complex E hE ξ hgc]) hg

theorem pol_zero_left {g : ℝ → ℝ} (hg : Bdd g) (η : 𝓗) : pol E hE g 0 η = 0 := by
  have := pol_smul_left E hE hg 0 0 η
  rwa [zero_smul, map_zero, zero_mul] at this

theorem pol_zero_right {g : ℝ → ℝ} (hg : Bdd g) (ξ : 𝓗) : pol E hE g ξ 0 = 0 := by
  have := pol_smul_right E hE hg 0 ξ 0
  rwa [zero_smul, zero_mul] at this

/-! #### Boundedness -/

theorem norm_Q_le {g : ℝ → ℝ} {C : ℝ} (hC : ∀ t, |g t| ≤ C) (ξ : 𝓗) :
    ‖Q E hE g ξ‖ ≤ C * ‖ξ‖ ^ 2 := by
  rw [Q, Complex.norm_real, Real.norm_eq_abs]
  exact abs_integral_ν_le E hE ξ hC

theorem norm_pol_le_sq {g : ℝ → ℝ} {C : ℝ} (hC : ∀ t, |g t| ≤ C) (ξ η : 𝓗) :
    ‖pol E hE g ξ η‖ ≤ C * (‖ξ‖ ^ 2 + ‖η‖ ^ 2) := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have h1 := norm_Q_le E hE hC (ξ + η)
  have h2 := norm_Q_le E hE hC (ξ - η)
  have h3 := norm_Q_le E hE hC (ξ + Complex.I • η)
  have h4 := norm_Q_le E hE hC (ξ - Complex.I • η)
  have p1 : ‖ξ + η‖ ^ 2 + ‖ξ - η‖ ^ 2 = 2 * (‖ξ‖ ^ 2 + ‖η‖ ^ 2) := by
    have := parallelogram_law_with_norm ℂ ξ η
    nlinarith [this]
  have p2 : ‖ξ + Complex.I • η‖ ^ 2 + ‖ξ - Complex.I • η‖ ^ 2 = 2 * (‖ξ‖ ^ 2 + ‖η‖ ^ 2) := by
    have := parallelogram_law_with_norm ℂ ξ (Complex.I • η)
    rw [norm_smul, Complex.norm_I, one_mul] at this
    nlinarith [this]
  have hn : ‖pol E hE g ξ η‖ ≤ (‖Q E hE g (ξ + η)‖ + ‖Q E hE g (ξ - η)‖ +
      ‖Q E hE g (ξ + Complex.I • η)‖ + ‖Q E hE g (ξ - Complex.I • η)‖) / 4 := by
    unfold pol
    rw [norm_div, Complex.norm_ofNat]
    gcongr
    calc ‖Q E hE g (ξ + η) - Q E hE g (ξ - η) - Complex.I * Q E hE g (ξ + Complex.I • η) +
          Complex.I * Q E hE g (ξ - Complex.I • η)‖
        ≤ ‖Q E hE g (ξ + η) - Q E hE g (ξ - η) - Complex.I * Q E hE g (ξ + Complex.I • η)‖ +
          ‖Complex.I * Q E hE g (ξ - Complex.I • η)‖ := norm_add_le _ _
      _ ≤ ‖Q E hE g (ξ + η) - Q E hE g (ξ - η)‖ + ‖Complex.I * Q E hE g (ξ + Complex.I • η)‖ +
          ‖Complex.I * Q E hE g (ξ - Complex.I • η)‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ ‖Q E hE g (ξ + η)‖ + ‖Q E hE g (ξ - η)‖ + ‖Complex.I * Q E hE g (ξ + Complex.I • η)‖ +
          ‖Complex.I * Q E hE g (ξ - Complex.I • η)‖ := by gcongr; exact norm_sub_le _ _
      _ = _ := by rw [norm_mul, norm_mul, Complex.norm_I, one_mul, one_mul]
  calc ‖pol E hE g ξ η‖ ≤ _ := hn
    _ ≤ (C * ‖ξ + η‖ ^ 2 + C * ‖ξ - η‖ ^ 2 + C * ‖ξ + Complex.I • η‖ ^ 2 +
        C * ‖ξ - Complex.I • η‖ ^ 2) / 4 := by gcongr
    _ = C * (‖ξ‖ ^ 2 + ‖η‖ ^ 2) := by linear_combination (C / 4) * p1 + (C / 4) * p2

theorem norm_pol_le {g : ℝ → ℝ} (hg : Bdd g) {C : ℝ} (hC : ∀ t, |g t| ≤ C) (ξ η : 𝓗) :
    ‖pol E hE g ξ η‖ ≤ 2 * C * ‖ξ‖ * ‖η‖ := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  by_cases hξ : ξ = 0
  · subst hξ
    rw [pol_zero_left E hE hg, norm_zero, norm_zero]
    simp
  by_cases hη : η = 0
  · subst hη
    rw [pol_zero_right E hE hg, norm_zero, norm_zero]
    simp
  have hξn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  have hηn : 0 < ‖η‖ := norm_pos_iff.mpr hη
  set t : ℝ := Real.sqrt (‖η‖ / ‖ξ‖) with ht
  have htpos : 0 < t := Real.sqrt_pos.mpr (div_pos hηn hξn)
  have htsq : t ^ 2 = ‖η‖ / ‖ξ‖ := Real.sq_sqrt (div_pos hηn hξn).le
  have hscale : pol E hE g ξ η = pol E hE g ((t : ℂ) • ξ) (((t⁻¹ : ℝ) : ℂ) • η) := by
    rw [pol_smul_left E hE hg, pol_smul_right E hE hg, Complex.conj_ofReal, ← mul_assoc,
      ← Complex.ofReal_mul, mul_inv_cancel₀ htpos.ne', Complex.ofReal_one, one_mul]
  rw [hscale]
  refine (norm_pol_le_sq E hE hC _ _).trans (le_of_eq ?_)
  rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos htpos, abs_of_pos (inv_pos.mpr htpos), mul_pow, mul_pow,
    htsq, inv_pow, htsq]
  field_simp
  ring

/-- The polarized form as a bounded sesquilinear map. -/
noncomputable def polForm {g : ℝ → ℝ} (hg : Bdd g) : 𝓗 →L⋆[ℂ] 𝓗 →L[ℂ] ℂ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (pol E hE g) (pol_add_left E hE hg)
      (fun c ξ η => by rw [pol_smul_left E hE hg, smul_eq_mul]) (pol_add_right E hE hg)
      (fun c ξ η => by rw [pol_smul_right E hE hg, smul_eq_mul]; rfl))
    (2 * hg.2.choose) (fun ξ η => norm_pol_le E hE hg hg.2.choose_spec ξ η)

theorem polForm_apply {g : ℝ → ℝ} (hg : Bdd g) (ξ η : 𝓗) :
    polForm E hE hg ξ η = pol E hE g ξ η := rfl

end Pol

/-! ### The Borel functional calculus -/

section Bfc

variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗] [CompleteSpace 𝓗]
variable (E : 𝓗 →L[ℂ] 𝓗) (hE : IsSelfAdjoint E)

/-- **The Borel functional calculus** `g(E)` for a bounded Borel function `g` (junk value
`0` otherwise): the operator of the polarized form of the spectral measures. -/
noncomputable def bfc (g : ℝ → ℝ) : 𝓗 →L[ℂ] 𝓗 := by
  classical
  exact if hg : Bdd g then InnerProductSpace.continuousLinearMapOfBilin (polForm E hE hg) else 0

theorem bfc_of_not {g : ℝ → ℝ} (hg : ¬ Bdd g) : bfc E hE g = 0 := by
  unfold bfc; rw [dif_neg hg]

theorem inner_bfc_left {g : ℝ → ℝ} (hg : Bdd g) (ξ η : 𝓗) :
    ⟪bfc E hE g ξ, η⟫_ℂ = pol E hE g ξ η := by
  unfold bfc
  rw [dif_pos hg]
  exact InnerProductSpace.continuousLinearMapOfBilin_apply _ ξ η

theorem inner_bfc {g : ℝ → ℝ} (hg : Bdd g) (ξ η : 𝓗) :
    ⟪ξ, bfc E hE g η⟫_ℂ = pol E hE g ξ η := by
  rw [← inner_conj_symm, inner_bfc_left E hE hg, pol_conj E hE hg]

theorem inner_bfc_self {g : ℝ → ℝ} (hg : Bdd g) (ξ : 𝓗) :
    ⟪ξ, bfc E hE g ξ⟫_ℂ = Q E hE g ξ := by
  rw [inner_bfc E hE hg, pol_self E hE hg]

theorem re_inner_bfc_self {g : ℝ → ℝ} (hg : Bdd g) (ξ : 𝓗) :
    (⟪ξ, bfc E hE g ξ⟫_ℂ).re = ∫ t, g t ∂(ν E hE ξ) := by
  rw [inner_bfc_self E hE hg, Q, Complex.ofReal_re]

theorem ext_of_inner {S T : 𝓗 →L[ℂ] 𝓗} (h : ∀ ξ η, ⟪ξ, S η⟫_ℂ = ⟪ξ, T η⟫_ℂ) : S = T :=
  ContinuousLinearMap.ext fun η => ext_inner_left ℂ fun ξ => h ξ η

/-- An operator is determined by its quadratic form. -/
theorem ext_of_inner_self {S T : 𝓗 →L[ℂ] 𝓗} (h : ∀ ξ, ⟪ξ, S ξ⟫_ℂ = ⟪ξ, T ξ⟫_ℂ) : S = T := by
  apply ContinuousLinearMap.coe_injective
  refine (ext_inner_map (S : 𝓗 →ₗ[ℂ] 𝓗) (T : 𝓗 →ₗ[ℂ] 𝓗)).mp fun ξ => ?_
  rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe, ← inner_conj_symm, h,
    inner_conj_symm]

theorem bfc_unique {g : ℝ → ℝ} (hg : Bdd g) {T : 𝓗 →L[ℂ] 𝓗}
    (h : ∀ ξ η, ⟪ξ, T η⟫_ℂ = pol E hE g ξ η) : T = bfc E hE g :=
  ext_of_inner fun ξ η => by rw [h, inner_bfc E hE hg]

/-- On bounded continuous functions the Borel calculus is the continuous one. -/
theorem bfc_cfc {g : ℝ → ℝ} (hg : Bdd g) (hc : Continuous g) : bfc E hE g = cfc g E :=
  (bfc_unique E hE hg fun ξ η => (pol_cfc E hE hc ξ η).symm).symm

/-- Rewriting the operator inside `bfc` (the self-adjointness proof is transported). -/
theorem bfc_congr_op {E E' : 𝓗 →L[ℂ] 𝓗} (h : E = E') (hE : IsSelfAdjoint E)
    (hE' : IsSelfAdjoint E') (g : ℝ → ℝ) : bfc E hE g = bfc E' hE' g := by
  subst h; rfl

theorem bfc_isSelfAdjoint {g : ℝ → ℝ} (hg : Bdd g) : IsSelfAdjoint (bfc E hE g) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  exact ext_of_inner fun ξ η => by
    rw [ContinuousLinearMap.adjoint_inner_right, inner_bfc_left E hE hg, inner_bfc E hE hg]

/-! #### Linearity -/

theorem Q_add {g h : ℝ → ℝ} (hg : Bdd g) (hh : Bdd h) (ξ : 𝓗) :
    Q E hE (g + h) ξ = Q E hE g ξ + Q E hE h ξ := by
  unfold Q
  rw [← Complex.ofReal_add, ← integral_add (hg.integrable _) (hh.integrable _)]
  rfl

theorem Q_sub {g h : ℝ → ℝ} (hg : Bdd g) (hh : Bdd h) (ξ : 𝓗) :
    Q E hE (g - h) ξ = Q E hE g ξ - Q E hE h ξ := by
  unfold Q
  rw [← Complex.ofReal_sub, ← integral_sub (hg.integrable _) (hh.integrable _)]
  rfl

theorem Q_const_mul (c : ℝ) (g : ℝ → ℝ) (ξ : 𝓗) :
    Q E hE (fun t => c * g t) ξ = (c : ℂ) * Q E hE g ξ := by
  unfold Q
  rw [← Complex.ofReal_mul, integral_const_mul]

theorem pol_add_fun {g h : ℝ → ℝ} (hg : Bdd g) (hh : Bdd h) (ξ η : 𝓗) :
    pol E hE (g + h) ξ η = pol E hE g ξ η + pol E hE h ξ η := by
  unfold pol
  simp only [Q_add E hE hg hh]
  ring

theorem pol_sub_fun {g h : ℝ → ℝ} (hg : Bdd g) (hh : Bdd h) (ξ η : 𝓗) :
    pol E hE (g - h) ξ η = pol E hE g ξ η - pol E hE h ξ η := by
  unfold pol
  simp only [Q_sub E hE hg hh]
  ring

theorem pol_const_mul (c : ℝ) (g : ℝ → ℝ) (ξ η : 𝓗) :
    pol E hE (fun t => c * g t) ξ η = (c : ℂ) * pol E hE g ξ η := by
  unfold pol
  simp only [Q_const_mul E hE c g]
  ring

theorem bfc_add {g h : ℝ → ℝ} (hg : Bdd g) (hh : Bdd h) :
    bfc E hE (g + h) = bfc E hE g + bfc E hE h :=
  (bfc_unique E hE (hg.add hh) fun ξ η => by
    rw [ContinuousLinearMap.add_apply, inner_add_right, inner_bfc E hE hg, inner_bfc E hE hh,
      pol_add_fun E hE hg hh]).symm

theorem bfc_sub {g h : ℝ → ℝ} (hg : Bdd g) (hh : Bdd h) :
    bfc E hE (g - h) = bfc E hE g - bfc E hE h :=
  (bfc_unique E hE (hg.sub hh) fun ξ η => by
    rw [ContinuousLinearMap.sub_apply, inner_sub_right, inner_bfc E hE hg, inner_bfc E hE hh,
      pol_sub_fun E hE hg hh]).symm

theorem bfc_const_mul (c : ℝ) {g : ℝ → ℝ} (hg : Bdd g) :
    bfc E hE (fun t => c * g t) = (c : ℂ) • bfc E hE g :=
  (bfc_unique E hE (hg.const_mul c) fun ξ η => by
    rw [ContinuousLinearMap.smul_apply, inner_smul_right, inner_bfc E hE hg,
      pol_const_mul E hE c g]).symm

theorem bfc_one : bfc E hE 1 = 1 := by
  rw [bfc_cfc E hE Bdd.one continuous_const, cfc_one ℝ E hE]

theorem bfc_zero : bfc E hE 0 = 0 := by
  rw [bfc_cfc E hE Bdd.zero continuous_const, cfc_zero ℝ E]

theorem bfc_const (c : ℝ) : bfc E hE (fun _ => c) = (c : ℂ) • 1 := by
  have : (fun _ : ℝ => c) = fun t => c * (1 : ℝ → ℝ) t := by funext t; simp
  rw [this, bfc_const_mul E hE c Bdd.one, bfc_one]

/-! #### Multiplicativity -/

theorem cfc_mul_apply {g h : ℝ → ℝ} (hg : Continuous g) (hh : Continuous h) :
    cfc (g * h) E = cfc g E * cfc h E := by
  have : (g * h) = fun x => g x * h x := rfl
  rw [this, cfc_mul g h E hg.continuousOn hh.continuousOn]

/-- Step 1: for continuous `g` and Borel `h`, by transfer in `h`. -/
theorem pol_bfc_right_cont {g h : ℝ → ℝ} (hgc : Continuous g) (hg : Bdd g) (hh : Bdd h)
    (ξ η : 𝓗) : pol E hE g ξ (bfc E hE h η) = pol E hE (g * h) ξ η := by
  rw [pol_cfc E hE hgc, inner_sa (cfc_predicate g E), inner_bfc E hE hh]
  refine IsCombo.eq (isCombo_pol E hE _ _) ((isCombo_pol E hE ξ η).mul_left hg)
    (fun h hhc _ => ?_) hh
  rw [pol_cfc E hE hhc, pol_cfc E hE (hgc.mul hhc), cfc_mul_apply E hgc hhc,
    Resolver.Douglas.mulA, inner_sa (cfc_predicate g E)]

/-- Step 2: for Borel `g` and `h`, by transfer in `g`. -/
theorem pol_bfc_right {g h : ℝ → ℝ} (hg : Bdd g) (hh : Bdd h) (ξ η : 𝓗) :
    pol E hE g ξ (bfc E hE h η) = pol E hE (g * h) ξ η :=
  IsCombo.eq (isCombo_pol E hE _ _) ((isCombo_pol E hE ξ η).mul_right hh)
    (fun _ hgc hgb => pol_bfc_right_cont E hE hgc hgb hh ξ η) hg

/-- **Multiplicativity** of the Borel functional calculus. -/
theorem bfc_mul {g h : ℝ → ℝ} (hg : Bdd g) (hh : Bdd h) :
    bfc E hE (g * h) = bfc E hE g * bfc E hE h :=
  (bfc_unique E hE (hg.mul hh) fun ξ η => by
    rw [Resolver.Douglas.mulA, inner_bfc E hE hg, pol_bfc_right E hE hg hh]).symm

theorem bfc_comm {g h : ℝ → ℝ} (hg : Bdd g) (hh : Bdd h) :
    bfc E hE g * bfc E hE h = bfc E hE h * bfc E hE g := by
  rw [← bfc_mul E hE hg hh, ← bfc_mul E hE hh hg, mul_comm]

/-- The spectral measure of `h(E) ξ`: `∫ g dν_{h(E)ξ} = ∫ g h² dν_ξ`. -/
theorem integral_ν_bfc {g h : ℝ → ℝ} (hg : Bdd g) (hh : Bdd h) (ξ : 𝓗) :
    ∫ t, g t ∂(ν E hE (bfc E hE h ξ)) = ∫ t, (h * g * h) t ∂(ν E hE ξ) := by
  rw [← re_inner_bfc_self E hE hg, ← re_inner_bfc_self E hE ((hh.mul hg).mul hh),
    bfc_mul E hE (hh.mul hg) hh, bfc_mul E hE hh hg, Resolver.Douglas.mulA,
    Resolver.Douglas.mulA, inner_sa (bfc_isSelfAdjoint E hE hh)]

/-! #### Order -/

theorem bfc_nonneg {g : ℝ → ℝ} (hg : Bdd g) (h0 : ∀ t, 0 ≤ g t) : 0 ≤ bfc E hE g :=
  Resolver.Douglas.nonneg_of_re_inner (bfc_isSelfAdjoint E hE hg) fun ξ => by
    rw [← inner_sa (bfc_isSelfAdjoint E hE hg), re_inner_bfc_self E hE hg]
    exact integral_nonneg h0

theorem bfc_mono {g h : ℝ → ℝ} (hg : Bdd g) (hh : Bdd h) (hle : ∀ t, g t ≤ h t) :
    bfc E hE g ≤ bfc E hE h := by
  rw [← sub_nonneg, ← bfc_sub E hE hh hg]
  exact bfc_nonneg E hE (hh.sub hg) fun t => by
    rw [Pi.sub_apply]; exact sub_nonneg.mpr (hle t)

theorem bfc_le_one {g : ℝ → ℝ} (hg : Bdd g) (h1 : ∀ t, g t ≤ 1) : bfc E hE g ≤ 1 := by
  rw [← bfc_one E hE]
  exact bfc_mono E hE hg Bdd.one h1

theorem bfc_norm_le_one {g : ℝ → ℝ} (hg : Bdd g) (h0 : ∀ t, 0 ≤ g t) (h1 : ∀ t, g t ≤ 1) :
    ‖bfc E hE g‖ ≤ 1 :=
  StrongLimit.norm_le_one_of_nonneg_le_one (bfc_nonneg E hE hg h0) (bfc_le_one E hE hg h1)

end Bfc

end BorelCalc

end CommutingRepetition

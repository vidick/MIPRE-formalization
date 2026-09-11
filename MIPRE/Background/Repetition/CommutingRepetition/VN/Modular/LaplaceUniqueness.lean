/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/Modular/LaplaceUniqueness.lean
-/
/-
# Uniqueness for the two-sided Laplace transform (density stage E4.3e)

The analytic step of Rieffel–van Daele's Lemma 4.8: if `g` is bounded and
continuous on `ℝ` and `∫ e^{-φt}/(2cosh πt) · g(t) dt = 0` for every real
`|φ| < π`, then `g = 0`.

Proof: `F(z) = ∫ e^{-zt} G(t) dt`, `G = g/(2cosh πt)`, is analytic on the strip
`|Re z| < π` (differentiation under the integral, dominated by `C|t|e^{-ε|t|}`);
it vanishes on the real segment `(-π, π)`, hence on the whole strip by the
identity theorem, in particular on the imaginary axis, where it is the Fourier
transform of `G`. Fourier inversion gives `G = 0`.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.Modular.StripCauchy
import MIPRE.Background.Repetition.CommutingRepetition.VN.Modular.AnalyticFamily

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace LaplaceUniq

open Complex MeasureTheory Filter Topology Set StripCauchy
open scoped Real FourierTransform

/-- The open strip `|Re z| < π`. -/
def U : Set ℂ := {z | |z.re| < π}

theorem isOpen_U : IsOpen U := isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const

theorem convex_U : Convex ℝ U := by
  have : U = Complex.reLm ⁻¹' Ioo (-π) π := by
    ext z; simp [U, abs_lt, Complex.reLm]
  rw [this]
  exact (convex_Ioo _ _).linear_preimage _

theorem zero_mem_U : (0 : ℂ) ∈ U := by simp [U, Real.pi_pos]

section Main

variable {g : ℝ → ℂ} (hg : Continuous g) {C : ℝ} (hC : ∀ t, ‖g t‖ ≤ C)

/-- `G t = g t / (2 cosh(πt))`. -/
noncomputable def G (g : ℝ → ℂ) (t : ℝ) : ℂ := g t / (2 * Real.cosh (π * t))

include hg in
theorem continuous_G : Continuous (G g) := by
  unfold G
  refine hg.div (by fun_prop) fun t => ?_
  exact_mod_cast (by have := Real.cosh_pos (π * t); positivity : (2 * Real.cosh (π * t) : ℝ) ≠ 0)

include hC in
theorem norm_G_le (t : ℝ) : ‖G g t‖ ≤ C * Real.exp (-(π * |t|)) := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hc := exp_abs_div_two_le_cosh (π * t)
  have hcpos := Real.cosh_pos (π * t)
  unfold G
  rw [norm_div, Complex.norm_mul, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_of_nonneg hcpos.le, div_le_iff₀ (by positivity)]
  calc ‖g t‖ ≤ C := hC t
    _ = C * Real.exp (-(π * |t|)) * Real.exp |π * t| := by
        rw [abs_mul, abs_of_pos Real.pi_pos, mul_assoc, ← Real.exp_add]; simp
    _ = C * Real.exp (-(π * |t|)) * (2 * (Real.exp |π * t| / 2)) := by ring
    _ ≤ C * Real.exp (-(π * |t|)) * (2 * Real.cosh (π * t)) := by gcongr

/-- `|t| e^{-ε|t|} ≤ K_ε (1 + t²)⁻¹`. -/
theorem abs_mul_exp_neg_le {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    |t| * Real.exp (-(ε * |t|)) ≤ 2 / ε * max 1 (2 / (ε / 2) ^ 2) * (1 + t ^ 2)⁻¹ := by
  have h1 : |t| * Real.exp (-(ε / 2 * |t|)) ≤ 1 / (ε / 2) :=
    VN.Modular.mul_exp_neg_le (by positivity) (abs_nonneg t)
  have h2 : Real.exp (-(ε / 2 * |t|)) ≤ max 1 (2 / (ε / 2) ^ 2) * (1 + |t| ^ 2)⁻¹ :=
    exp_neg_le_inv_one_add_sq (by positivity) (abs_nonneg t)
  rw [sq_abs] at h2
  calc |t| * Real.exp (-(ε * |t|))
      = (|t| * Real.exp (-(ε / 2 * |t|))) * Real.exp (-(ε / 2 * |t|)) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ (1 / (ε / 2)) * (max 1 (2 / (ε / 2) ^ 2) * (1 + t ^ 2)⁻¹) :=
        mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
    _ = 2 / ε * max 1 (2 / (ε / 2) ^ 2) * (1 + t ^ 2)⁻¹ := by field_simp <;> ring

/-- The Laplace transform `F z = ∫ e^{-zt} G t dt`. -/
noncomputable def F (g : ℝ → ℂ) (z : ℂ) : ℂ := ∫ t : ℝ, Complex.exp (-(z * t)) * G g t

include hg hC in
/-- Integrability of `e^{-zt} G t` for `|Re z| < π`. -/
theorem integrable_F_integrand {z : ℂ} (hz : |z.re| < π) :
    Integrable fun t : ℝ => Complex.exp (-(z * t)) * G g t := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  set a := π - |z.re| with ha
  have hapos : 0 < a := sub_pos.mpr hz
  refine Integrable.mono' ((integrable_inv_one_add_sq.const_mul (C * max 1 (2 / a ^ 2))))
    ((Complex.continuous_exp.comp (by fun_prop)).mul (continuous_G hg)).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [norm_mul, Complex.norm_exp]
  have hre : (-(z * t)).re ≤ |z.re| * |t| := by
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero]
    calc -(z.re * t) ≤ |-(z.re * t)| := le_abs_self _
      _ = |z.re| * |t| := by rw [abs_neg, abs_mul]
  calc Real.exp (-(z * t)).re * ‖G g t‖ ≤ Real.exp (|z.re| * |t|) * (C * Real.exp (-(π * |t|))) :=
        mul_le_mul (Real.exp_le_exp.mpr hre) (norm_G_le hC t) (norm_nonneg _) (Real.exp_pos _).le
    _ = C * Real.exp (-(a * |t|)) := by
        rw [ha, ← mul_assoc, mul_comm (Real.exp _) C, mul_assoc, ← Real.exp_add]
        congr 2; ring
    _ ≤ C * (max 1 (2 / a ^ 2) * (1 + |t| ^ 2)⁻¹) := by
        gcongr
        exact exp_neg_le_inv_one_add_sq hapos (abs_nonneg t)
    _ = C * max 1 (2 / a ^ 2) * (1 + t ^ 2)⁻¹ := by rw [sq_abs]; ring

include hg hC in
/-- `F` is complex differentiable on the strip. -/
theorem hasDerivAt_F {z₀ : ℂ} (hz₀ : |z₀.re| < π) :
    HasDerivAt (F g) (∫ t : ℝ, -(t : ℂ) * Complex.exp (-(z₀ * t)) * G g t) z₀ := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  set ε := (π - |z₀.re|) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun (z : ℂ) (t : ℝ) => Complex.exp (-(z * t)) * G g t)
    (F' := fun (z : ℂ) (t : ℝ) => -(t : ℂ) * Complex.exp (-(z * t)) * G g t)
    (bound := fun t : ℝ => C * (2 / ε * max 1 (2 / (ε / 2) ^ 2) * (1 + t ^ 2)⁻¹))
    (Metric.ball_mem_nhds z₀ hεpos) ?_ (integrable_F_integrand hg hC hz₀) ?_ ?_ ?_ ?_
  · exact key.2
  · exact Eventually.of_forall fun z =>
      ((Complex.continuous_exp.comp (by fun_prop)).mul (continuous_G hg)).aestronglyMeasurable
  · exact (((Complex.continuous_ofReal.neg).mul (Complex.continuous_exp.comp (by fun_prop))).mul
      (continuous_G hg)).aestronglyMeasurable
  · refine Eventually.of_forall fun t z hz => ?_
    have hzre : |z.re| ≤ π - ε := by
      have h1 : |z.re - z₀.re| < ε := by
        calc |z.re - z₀.re| = |(z - z₀).re| := by simp
          _ ≤ ‖z - z₀‖ := Complex.abs_re_le_norm _
          _ < ε := by rwa [Metric.mem_ball, dist_eq_norm] at hz
      calc |z.re| = |(z.re - z₀.re) + z₀.re| := by ring_nf
        _ ≤ |z.re - z₀.re| + |z₀.re| := abs_add_le _ _
        _ ≤ ε + |z₀.re| := by linarith
        _ = π - ε := by rw [hε]; ring
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    have hre : (-(z * t)).re ≤ (π - ε) * |t| := by
      simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        sub_zero]
      calc -(z.re * t) ≤ |-(z.re * t)| := le_abs_self _
        _ = |z.re| * |t| := by rw [abs_neg, abs_mul]
        _ ≤ (π - ε) * |t| := by gcongr
    calc |t| * Real.exp (-(z * t)).re * ‖G g t‖
        ≤ |t| * Real.exp ((π - ε) * |t|) * (C * Real.exp (-(π * |t|))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hre) (abs_nonneg t))
            (norm_G_le hC t) (norm_nonneg _) (by positivity)
      _ = C * (|t| * Real.exp (-(ε * |t|))) := by
          rw [show -(ε * |t|) = (π - ε) * |t| + -(π * |t|) by ring, Real.exp_add]; ring
      _ ≤ C * (2 / ε * max 1 (2 / (ε / 2) ^ 2) * (1 + t ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left (abs_mul_exp_neg_le hεpos t) hC0
  · exact (integrable_inv_one_add_sq.const_mul _).const_mul C
  · refine Eventually.of_forall fun t z _ => ?_
    have h1 : HasDerivAt (fun z : ℂ => -(z * t)) (-(t : ℂ)) z :=
      (hasDerivAt_mul_const (t : ℂ)).neg
    exact (((Complex.hasDerivAt_exp _).comp z h1).mul_const (G g t)).congr_deriv (by ring)

include hg hC in
theorem differentiableOn_F : DifferentiableOn ℂ (F g) U := fun z hz =>
  (hasDerivAt_F hg hC hz).differentiableAt.differentiableWithinAt

include hg hC in
theorem analyticOnNhd_F : AnalyticOnNhd ℂ (F g) U :=
  (Complex.analyticOnNhd_iff_differentiableOn isOpen_U).mpr (differentiableOn_F hg hC)

/-- `F φ = ∫ w φ t · g t` for real `φ`. -/
theorem F_real (φ : ℝ) : F g φ = ∫ t : ℝ, (w φ t : ℂ) * g t := by
  unfold F G w
  congr 1
  funext t
  have hc : Complex.cosh ((π : ℂ) * t) ≠ 0 := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_cosh]
    exact_mod_cast (Real.cosh_pos _).ne'
  push_cast
  rw [neg_mul]
  field_simp <;> ring

include hg hC in
/-- If `F` vanishes on the real segment `(-π, π)`, it vanishes on the whole strip. -/
theorem F_eq_zero_of_real (h : ∀ φ : ℝ, |φ| < π → F g φ = 0) {z : ℂ} (hz : z ∈ U) : F g z = 0 := by
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), F g z = 0 := by
    rw [Filter.frequently_iff]
    intro s hs
    rw [Metric.mem_nhdsWithin_iff] at hs
    obtain ⟨ε, hε, hsub⟩ := hs
    set r : ℝ := min (ε / 2) (π / 2) with hr
    have hrpos : 0 < r := by rw [hr]; exact lt_min (by positivity) (by positivity)
    refine ⟨(r : ℂ), hsub ⟨?_, ?_⟩, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg hrpos.le]
      exact (min_le_left _ _).trans_lt (by linarith)
    · rw [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact_mod_cast hrpos.ne'
    · apply h
      rw [abs_of_pos hrpos]
      exact (min_le_right _ _).trans_lt (by linarith [Real.pi_pos])
  have := (analyticOnNhd_F hg hC).eqOn_zero_of_preconnected_of_frequently_eq_zero
    convex_U.isPreconnected zero_mem_U hfreq
  exact this hz

include hg hC in
/-- The Fourier transform of `G` is `F` on the imaginary axis. -/
theorem fourier_G_eq (w : ℝ) : 𝓕 (G g) w = F g (2 * π * w * I) := by
  rw [Real.fourier_real_eq_integral_exp_smul, F]
  congr 1
  funext t
  rw [smul_eq_mul]
  congr 2
  push_cast
  ring

include hg hC in
/-- **Laplace uniqueness**: if `∫ w φ t · g t dt = 0` for all `|φ| < π`, then `g = 0`. -/
theorem eq_zero_of_forall_integral_w_eq_zero
    (h : ∀ φ : ℝ, |φ| < π → ∫ t : ℝ, (w φ t : ℂ) * g t = 0) (t : ℝ) : g t = 0 := by
  have hF : ∀ φ : ℝ, |φ| < π → F g φ = 0 := fun φ hφ => by rw [F_real]; exact h φ hφ
  have hfour : 𝓕 (G g) = 0 := by
    funext w
    rw [fourier_G_eq hg hC, F_eq_zero_of_real hg hC hF]
    · rfl
    · show |(2 * π * w * I : ℂ).re| < π
      simp [Real.pi_pos]
  have hGint : Integrable (G g) := by
    have := integrable_F_integrand hg hC (z := 0) (by simp [Real.pi_pos])
    simpa using this
  have hinv := (continuous_G hg).fourierInv_fourier_eq hGint (by rw [hfour]; exact integrable_zero _ _ _)
  rw [hfour] at hinv
  have hG0 : G g t = 0 := by
    have := congrFun hinv t
    rw [← this, Real.fourierInv_eq]
    simp
  unfold G at hG0
  have hc : (2 * (Real.cosh (π * t) : ℂ)) ≠ 0 := by
    exact_mod_cast (by have := Real.cosh_pos (π * t); positivity : (2 * Real.cosh (π * t) : ℝ) ≠ 0)
  exact (div_eq_zero_iff.mp hG0).resolve_right hc

end Main

end LaplaceUniq

end CommutingRepetition

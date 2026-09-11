/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/Modular/StripCauchy.lean
-/
/-
# Cauchy's formula on the strip `|Re z| ≤ 1/2` (density stage E4.3b)

Rieffel–van Daele, Lemma 4.6: let `f` be continuous and bounded on the closed
strip `|Re z| ≤ 1/2` and analytic inside, and let `λ = e^{iφ/2}` with `|φ| < π`.
Then
```
f 0 = ∫ t, e^{-φt} / (e^{πt} + e^{-πt}) · (λ f(1/2 + it) + λ̄ f(-1/2 + it)) dt.
```
Proof (as in RvD, arranged to use only Cauchy–Goursat on rectangles): with
`g z = e^{iφz} f z` and `ψ z = πz / sin(πz)` (analytic near the strip, `ψ 0 = 1`),
the function `G = g ψ` is analytic on the open strip and continuous on the closed
one, and `H = dslope G 0 = (G z − G 0)/z` has a removable singularity at `0`.
Cauchy–Goursat on the rectangles `[-1/2, 1/2] × [-N, N]` gives, as `N → ∞` (the
horizontal edges contribute `O(N e^{-(π-|φ|)N})`),
`∫ (H(1/2 + it) − H(-1/2 + it)) dt = 0`, i.e.
`∫ (G(1/2+it)/(1/2+it) − G(-1/2+it)/(-1/2+it)) dt = G 0 · ∫ (1/4 + t²)⁻¹ dt = 2π f 0`,
and `G(±1/2 + it)/(±1/2 + it) = ± e^{±iφ/2} e^{-φt} π f(±1/2+it) / cosh(πt)`.
-/
import Mathlib

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace StripCauchy

open Complex MeasureTheory Filter Topology Set intervalIntegral
open scoped Real

/-! ## Elementary bounds -/

/-- `|sinh (Im z)| ≤ ‖sin z‖`. -/
theorem abs_sinh_im_le_norm_sin (z : ℂ) : |Real.sinh z.im| ≤ ‖Complex.sin z‖ := by
  have h : Complex.sin z = (exp (-z * I) - exp (z * I)) * I / 2 := rfl
  rw [h, norm_div, norm_mul, norm_I, mul_one, Complex.norm_ofNat]
  have h1 : ‖exp (-z * I)‖ = Real.exp z.im := by
    rw [Complex.norm_exp]; congr 1; simp
  have h2 : ‖exp (z * I)‖ = Real.exp (-z.im) := by
    rw [Complex.norm_exp]; congr 1; simp
  have h3 := abs_norm_sub_norm_le (exp (-z * I)) (exp (z * I))
  rw [h1, h2] at h3
  rw [Real.sinh_eq, abs_div, abs_two]
  exact div_le_div_of_nonneg_right h3 (by norm_num)

/-- `e^x / 4 ≤ sinh x` for `x ≥ 1`. -/
theorem exp_div_four_le_sinh {x : ℝ} (hx : 1 ≤ x) : Real.exp x / 4 ≤ Real.sinh x := by
  rw [Real.sinh_eq]
  have h1 : Real.exp (-x) ≤ Real.exp x / 2 := by
    rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos x)]
    have : Real.exp 1 ≤ Real.exp x := Real.exp_le_exp.mpr hx
    have h2 : (2 : ℝ) < Real.exp 1 := by
      have := Real.add_one_lt_exp (one_ne_zero (α := ℝ))
      linarith
    nlinarith [Real.exp_pos x, Real.exp_pos 1]
  linarith

/-- `e^{|x|} / 2 ≤ cosh x`. -/
theorem exp_abs_div_two_le_cosh (x : ℝ) : Real.exp |x| / 2 ≤ Real.cosh x := by
  rw [Real.cosh_eq]
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]; linarith [Real.exp_pos (-x)]
  · rw [abs_of_neg h]; linarith [Real.exp_pos x]

/-- `e^{-a s} ≤ C_a (1 + s²)⁻¹` for `s ≥ 0`, `a > 0`. -/
theorem exp_neg_le_inv_one_add_sq {a : ℝ} (ha : 0 < a) {s : ℝ} (hs : 0 ≤ s) :
    Real.exp (-(a * s)) ≤ max 1 (2 / a ^ 2) * (1 + s ^ 2)⁻¹ := by
  have hq := Real.quadratic_le_exp_of_nonneg (mul_nonneg ha.le hs)
  have hpos : 0 < 1 + s ^ 2 := by positivity
  have hm : 0 < max 1 (2 / a ^ 2) := lt_max_of_lt_left one_pos
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
  have key : 1 + s ^ 2 ≤ max 1 (2 / a ^ 2) * (1 + a * s + (a * s) ^ 2 / 2) := by
    have e1 : (1 : ℝ) ≤ max 1 (2 / a ^ 2) := le_max_left _ _
    have e2 : 2 / a ^ 2 ≤ max 1 (2 / a ^ 2) := le_max_right _ _
    have e3 : s ^ 2 ≤ max 1 (2 / a ^ 2) * ((a * s) ^ 2 / 2) := by
      calc s ^ 2 = (2 / a ^ 2) * ((a * s) ^ 2 / 2) := by field_simp <;> ring
        _ ≤ max 1 (2 / a ^ 2) * ((a * s) ^ 2 / 2) := by gcongr
    nlinarith [mul_nonneg ha.le hs, mul_nonneg hm.le (mul_nonneg ha.le hs)]
  calc (1 : ℝ) = (1 + s ^ 2)⁻¹ * (1 + s ^ 2) := by field_simp
    _ ≤ (1 + s ^ 2)⁻¹ * (max 1 (2 / a ^ 2) * (1 + a * s + (a * s) ^ 2 / 2)) := by gcongr
    _ ≤ (1 + s ^ 2)⁻¹ * (max 1 (2 / a ^ 2) * Real.exp (a * s)) := by gcongr
    _ = max 1 (2 / a ^ 2) * (1 + s ^ 2)⁻¹ * Real.exp (a * s) := by ring

/-- The weight `w φ t = e^{-φt} / (2 cosh(πt))`. -/
noncomputable def w (φ t : ℝ) : ℝ := Real.exp (-φ * t) / (2 * Real.cosh (π * t))

theorem continuous_w (φ : ℝ) : Continuous (w φ) := by
  unfold w
  exact Continuous.div (by fun_prop) (by fun_prop) fun t => by
    have := Real.cosh_pos (π * t); positivity

theorem w_pos (φ t : ℝ) : 0 < w φ t := by
  unfold w
  have := Real.cosh_pos (π * t)
  positivity

/-- `w φ t ≤ e^{-(π-|φ|)|t|}`. -/
theorem w_le_exp {φ : ℝ} (t : ℝ) : w φ t ≤ Real.exp (-((π - |φ|) * |t|)) := by
  unfold w
  have hc := exp_abs_div_two_le_cosh (π * t)
  have hcpos := Real.cosh_pos (π * t)
  rw [div_le_iff₀ (by positivity)]
  have h1 : Real.exp (-φ * t) ≤ Real.exp (|φ| * |t|) := by
    apply Real.exp_le_exp.mpr
    calc -φ * t ≤ |-φ * t| := le_abs_self _
      _ = |φ| * |t| := by rw [abs_mul, abs_neg]
  calc Real.exp (-φ * t) ≤ Real.exp (|φ| * |t|) := h1
    _ = Real.exp (-((π - |φ|) * |t|)) * Real.exp |π * t| := by
        rw [← Real.exp_add, abs_mul, abs_of_pos Real.pi_pos]; congr 1; ring
    _ = Real.exp (-((π - |φ|) * |t|)) * (2 * (Real.exp |π * t| / 2)) := by ring
    _ ≤ Real.exp (-((π - |φ|) * |t|)) * (2 * Real.cosh (π * t)) := by gcongr

/-- `w φ` is dominated by `C (1 + t²)⁻¹`. -/
theorem w_le_inv_one_add_sq {φ : ℝ} (hφ : |φ| < π) (t : ℝ) :
    w φ t ≤ max 1 (2 / (π - |φ|) ^ 2) * (1 + t ^ 2)⁻¹ := by
  have ha : 0 < π - |φ| := sub_pos.mpr hφ
  calc w φ t ≤ Real.exp (-((π - |φ|) * |t|)) := w_le_exp t
    _ ≤ max 1 (2 / (π - |φ|) ^ 2) * (1 + |t| ^ 2)⁻¹ := exp_neg_le_inv_one_add_sq ha (abs_nonneg t)
    _ = max 1 (2 / (π - |φ|) ^ 2) * (1 + t ^ 2)⁻¹ := by rw [sq_abs]

/-- Integrability of `t ↦ w φ t • v t` for bounded measurable `v`. -/
theorem integrable_w_mul {φ : ℝ} (hφ : |φ| < π) {v : ℝ → ℂ} (hv : AEStronglyMeasurable v volume)
    {C : ℝ} (hC : ∀ t, ‖v t‖ ≤ C) : Integrable fun t => (w φ t : ℂ) * v t := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine Integrable.mono' ((integrable_inv_one_add_sq.const_mul
    (max 1 (2 / (π - |φ|) ^ 2) * C))) ?_ (Eventually.of_forall fun t => ?_)
  · exact (Complex.continuous_ofReal.comp (continuous_w φ)).aestronglyMeasurable.mul hv
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (w_pos φ t).le]
    calc w φ t * ‖v t‖ ≤ (max 1 (2 / (π - |φ|) ^ 2) * (1 + t ^ 2)⁻¹) * C := by
          gcongr
          · exact w_le_inv_one_add_sq hφ t
          · exact hC t
      _ = max 1 (2 / (π - |φ|) ^ 2) * C * (1 + t ^ 2)⁻¹ := by ring

/-! ## Values of `sin` on the boundary lines and the kernel `(1/4 + t²)⁻¹` -/

theorem sin_pi_mul_half_add (t : ℝ) : Complex.sin (π * (1 / 2 + t * I)) = Real.cosh (π * t) := by
  have : (π : ℂ) * (1 / 2 + t * I) = (π * t : ℝ) * I + π / 2 := by push_cast; ring
  rw [this, Complex.sin_add_pi_div_two, Complex.cos_mul_I, Complex.ofReal_cosh]

theorem sin_pi_mul_neg_half_add (t : ℝ) :
    Complex.sin (π * (-1 / 2 + t * I)) = -Real.cosh (π * t) := by
  have : (π : ℂ) * (-1 / 2 + t * I) = (π * t : ℝ) * I - π / 2 := by push_cast; ring
  rw [this, Complex.sin_sub_pi_div_two, Complex.cos_mul_I, Complex.ofReal_cosh]

theorem half_add_ne_zero (t : ℝ) : (1 / 2 + t * I : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

theorem neg_half_add_ne_zero (t : ℝ) : (-1 / 2 + t * I : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

theorem inv_sub_inv_eq (t : ℝ) :
    (1 / 2 + t * I : ℂ)⁻¹ - (-1 / 2 + t * I)⁻¹ = (((1 / 4 + t ^ 2 : ℝ)⁻¹ : ℝ) : ℂ) := by
  have h1 := half_add_ne_zero t
  have h2 := neg_half_add_ne_zero t
  have hab : (1 / 2 + t * I : ℂ) * (-1 / 2 + t * I) = -((1 / 4 + t ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [Complex.ofReal_inv]
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← neg_neg ((1 / 4 + t ^ 2 : ℝ) : ℂ), ← hab, mul_neg, sub_mul, inv_mul_cancel_left₀ h1,
    mul_comm (1 / 2 + t * I : ℂ), inv_mul_cancel_left₀ h2]
  ring

theorem integrable_inv_quarter_add_sq : Integrable fun t : ℝ => (1 / 4 + t ^ 2)⁻¹ := by
  have : (fun t : ℝ => (1 / 4 + t ^ 2)⁻¹) = fun t => 4 * (1 + (2 * t) ^ 2)⁻¹ := by
    funext t; field_simp; ring
  rw [this]
  exact (integrable_inv_one_add_sq.comp_mul_left' two_ne_zero).const_mul 4

theorem integral_inv_quarter_add_sq : ∫ t : ℝ, (1 / 4 + t ^ 2)⁻¹ = 2 * π := by
  have : (fun t : ℝ => (1 / 4 + t ^ 2)⁻¹) = fun t => 4 * (1 + (2 * t) ^ 2)⁻¹ := by
    funext t; field_simp; ring
  rw [this, MeasureTheory.integral_const_mul,
    Measure.integral_comp_mul_left (fun x : ℝ => (1 + x ^ 2)⁻¹) 2, integral_univ_inv_one_add_sq,
    abs_inv, abs_two, smul_eq_mul]
  ring

/-! ## The functions `S`, `ψ`, `G`, `H` -/

/-- The closed strip. -/
def strip : Set ℂ := {z | |z.re| ≤ 1 / 2}

/-- The open strip. -/
def ostrip : Set ℂ := {z | |z.re| < 1 / 2}

theorem isOpen_ostrip : IsOpen ostrip :=
  isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const

theorem ostrip_subset_strip : ostrip ⊆ strip := fun z h => show |z.re| ≤ 1 / 2 from le_of_lt h

theorem zero_mem_ostrip : (0 : ℂ) ∈ ostrip := by simp [ostrip]

theorem ostrip_mem_nhds : ostrip ∈ 𝓝 (0 : ℂ) := isOpen_ostrip.mem_nhds zero_mem_ostrip

theorem strip_mem_nhds : strip ∈ 𝓝 (0 : ℂ) := mem_of_superset ostrip_mem_nhds ostrip_subset_strip

/-- `S z = sin(πz)/z`, with `S 0 = π`. -/
noncomputable def S : ℂ → ℂ := dslope (fun z => Complex.sin (π * z)) 0

theorem differentiable_sinPi : Differentiable ℂ fun z : ℂ => Complex.sin (π * z) := by fun_prop

theorem differentiable_S : Differentiable ℂ S := by
  have := (differentiableOn_dslope (s := Set.univ) (univ_mem : Set.univ ∈ 𝓝 (0 : ℂ))).mpr
    differentiable_sinPi.differentiableOn
  exact differentiableOn_univ.mp this

theorem S_zero : S 0 = π := by
  unfold S
  rw [dslope_same]
  have : HasDerivAt (fun z : ℂ => Complex.sin (π * z)) (Complex.cos (π * 0) * π) 0 := by
    have h1 : HasDerivAt (fun z : ℂ => (π : ℂ) * z) (π : ℂ) 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_mul (π : ℂ)
    exact (Complex.hasDerivAt_sin _).comp 0 h1
  rw [this.deriv]
  simp

theorem S_of_ne {z : ℂ} (hz : z ≠ 0) : S z = Complex.sin (π * z) / z := by
  unfold S
  rw [dslope_of_ne _ hz, slope_def_field]
  simp

theorem S_ne_zero {z : ℂ} (hz : z ∈ strip) : S z ≠ 0 := by
  by_cases h0 : z = 0
  · rw [h0, S_zero]; exact_mod_cast Real.pi_ne_zero
  · rw [S_of_ne h0]
    refine div_ne_zero ?_ h0
    intro hs
    rw [Complex.sin_eq_zero_iff] at hs
    obtain ⟨k, hk⟩ := hs
    have hz' : z = k := by
      have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have := hk
      rw [mul_comm] at this
      exact mul_right_cancel₀ hπ this
    have hre : |(k : ℝ)| ≤ 1 / 2 := by
      have := hz
      simp only [strip, Set.mem_setOf_eq, hz', Complex.intCast_re] at this
      exact this
    have hk0 : k = 0 := by
      have h1 : |(k : ℝ)| < 1 := by linarith
      have h2 : |k| < 1 := by exact_mod_cast h1
      have := abs_lt.mp h2
      omega
    exact h0 (by rw [hz', hk0]; simp)

/-- `ψ z = πz / sin(πz) = π / S z`. -/
noncomputable def ψ : ℂ → ℂ := fun z => π / S z

theorem ψ_zero : ψ 0 = 1 := by
  unfold ψ
  rw [S_zero]
  exact div_self (by exact_mod_cast Real.pi_ne_zero)

theorem differentiableOn_ψ : DifferentiableOn ℂ ψ strip := fun z hz =>
  (differentiableAt_const _ |>.div (differentiable_S z) (S_ne_zero hz)).differentiableWithinAt

theorem ψ_of_ne {z : ℂ} (hz : z ≠ 0) : ψ z = π * z / Complex.sin (π * z) := by
  unfold ψ
  rw [S_of_ne hz, div_div_eq_mul_div]

section Main

variable (f : ℂ → ℂ) (φ : ℝ)

/-- `g z = e^{iφz} f z`. -/
noncomputable def g : ℂ → ℂ := fun z => Complex.exp (I * φ * z) * f z

/-- `G = g ψ`. -/
noncomputable def G : ℂ → ℂ := fun z => g f φ z * ψ z

/-- `H = dslope G 0`. -/
noncomputable def H : ℂ → ℂ := dslope (G f φ) 0

theorem G_zero : G f φ 0 = f 0 := by
  simp [G, g, ψ_zero]

variable (hf_cont : ContinuousOn f strip) (hf_diff : DifferentiableOn ℂ f ostrip)
include hf_cont hf_diff

theorem continuousOn_G : ContinuousOn (G f φ) strip :=
  ((Complex.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
    hf_cont).mul differentiableOn_ψ.continuousOn

theorem differentiableOn_G : DifferentiableOn ℂ (G f φ) ostrip :=
  ((Complex.differentiable_exp.comp (differentiable_const _ |>.mul differentiable_id))
    |>.differentiableOn.mul hf_diff).mul (differentiableOn_ψ.mono ostrip_subset_strip)

theorem differentiableAt_G_zero : DifferentiableAt ℂ (G f φ) 0 :=
  (differentiableOn_G f φ hf_cont hf_diff).differentiableAt ostrip_mem_nhds

theorem continuousOn_H : ContinuousOn (H f φ) strip :=
  (continuousOn_dslope strip_mem_nhds).mpr
    ⟨continuousOn_G f φ hf_cont hf_diff, differentiableAt_G_zero f φ hf_cont hf_diff⟩

theorem differentiableOn_H : DifferentiableOn ℂ (H f φ) ostrip :=
  (differentiableOn_dslope ostrip_mem_nhds).mpr (differentiableOn_G f φ hf_cont hf_diff)

omit hf_cont hf_diff in
theorem H_of_ne {z : ℂ} (hz : z ≠ 0) : H f φ z = (G f φ z - f 0) / z := by
  unfold H
  rw [dslope_of_ne _ hz, slope_def_field, G_zero]
  simp

/-- The rectangle `[-1/2, 1/2] × [-N, N]`: Cauchy–Goursat for `H`. -/
theorem rect_eq_zero (N : ℝ) :
    (∫ x : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ), H f φ (x + -(N : ℂ) * I)) -
      (∫ x : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ), H f φ (x + N * I)) +
      I • (∫ y : ℝ in (-N)..N, H f φ (1 / 2 + y * I)) -
      I • (∫ y : ℝ in (-N)..N, H f φ (-1 / 2 + y * I)) = 0 := by
  have := integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn (H f φ)
    (Complex.mk (-1 / 2) (-N)) (Complex.mk (1 / 2) N) ?_ ?_
  · simpa using this
  · refine (continuousOn_H f φ hf_cont hf_diff).mono fun z hz => ?_
    rw [Complex.mem_reProdIm] at hz
    have h1 := hz.1
    dsimp only at h1
    rw [uIcc_of_le (by norm_num)] at h1
    show |z.re| ≤ 1 / 2
    rw [abs_le]
    exact ⟨by linarith [h1.1], h1.2⟩
  · refine (differentiableOn_H f φ hf_cont hf_diff).mono fun z hz => ?_
    rw [Complex.mem_reProdIm] at hz
    have h1 := hz.1
    dsimp only at h1
    rw [min_eq_left (by norm_num), max_eq_right (by norm_num)] at h1
    show |z.re| < 1 / 2
    rw [abs_lt]
    exact ⟨by linarith [h1.1], h1.2⟩

omit hf_cont hf_diff

theorem zero_mem_strip : (0 : ℂ) ∈ strip := by simp [strip]

theorem half_add_mem_strip (y : ℝ) : (1 / 2 + y * I : ℂ) ∈ strip := by
  show |(1 / 2 + y * I : ℂ).re| ≤ 1 / 2
  simp

theorem neg_half_add_mem_strip (y : ℝ) : (-1 / 2 + y * I : ℂ) ∈ strip := by
  show |(-1 / 2 + y * I : ℂ).re| ≤ 1 / 2
  simp <;> norm_num

theorem norm_exp_I_mul (z : ℂ) : ‖exp (I * φ * z)‖ = Real.exp (-(φ * z.im)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

variable {C : ℝ} (hf_bdd : ∀ z ∈ strip, ‖f z‖ ≤ C) (hφ : |φ| < π)
include hf_bdd

/-- The bound on `G` away from the real axis. -/
theorem norm_G_le {z : ℂ} (hz : z ∈ strip) (hN : 1 ≤ |z.im|) :
    ‖G f φ z‖ ≤ 8 * π * C * |z.im| * Real.exp (-((π - |φ|) * |z.im|)) := by
  have hz0 : z ≠ 0 := fun h => by rw [h] at hN; norm_num at hN
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hf_bdd 0 zero_mem_strip)
  have h1 : ‖exp (I * φ * z)‖ ≤ Real.exp (|φ| * |z.im|) := by
    rw [norm_exp_I_mul]
    apply Real.exp_le_exp.mpr
    calc -(φ * z.im) ≤ |-(φ * z.im)| := le_abs_self _
      _ = |φ| * |z.im| := by rw [abs_neg, abs_mul]
  have h2 : ‖f z‖ ≤ C := hf_bdd z hz
  have hsin : Real.exp (π * |z.im|) / 4 ≤ ‖Complex.sin (π * z)‖ := by
    calc Real.exp (π * |z.im|) / 4 ≤ Real.sinh (π * |z.im|) :=
          exp_div_four_le_sinh (by nlinarith [Real.pi_gt_three])
      _ = |Real.sinh (π * z.im)| := by rw [Real.abs_sinh, abs_mul, abs_of_pos Real.pi_pos]
      _ = |Real.sinh ((π : ℂ) * z).im| := by simp
      _ ≤ ‖Complex.sin (π * z)‖ := abs_sinh_im_le_norm_sin _
  have hnz : ‖z‖ ≤ 2 * |z.im| := by
    calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ 1 / 2 + |z.im| := by gcongr; exact hz
      _ ≤ 2 * |z.im| := by linarith
  have he : Real.exp (-(π * |z.im|)) * Real.exp (π * |z.im|) = 1 := by
    rw [← Real.exp_add]; simp
  have hψ : ‖ψ z‖ ≤ 8 * π * |z.im| * Real.exp (-(π * |z.im|)) := by
    rw [ψ_of_ne hz0, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    have hpos : 0 < ‖Complex.sin (π * z)‖ := lt_of_lt_of_le (by positivity) hsin
    rw [div_le_iff₀ hpos]
    calc π * ‖z‖ ≤ π * (2 * |z.im|) := by gcongr
      _ = 8 * π * |z.im| * Real.exp (-(π * |z.im|)) * (Real.exp (π * |z.im|) / 4) := by
          rw [show 8 * π * |z.im| * Real.exp (-(π * |z.im|)) * (Real.exp (π * |z.im|) / 4) =
            2 * π * |z.im| * (Real.exp (-(π * |z.im|)) * Real.exp (π * |z.im|)) by ring, he]
          ring
      _ ≤ 8 * π * |z.im| * Real.exp (-(π * |z.im|)) * ‖Complex.sin (π * z)‖ := by gcongr
  calc ‖G f φ z‖ = ‖exp (I * φ * z)‖ * ‖f z‖ * ‖ψ z‖ := by rw [G, g, norm_mul, norm_mul]
    _ ≤ Real.exp (|φ| * |z.im|) * C * (8 * π * |z.im| * Real.exp (-(π * |z.im|))) := by gcongr
    _ = 8 * π * C * |z.im| * Real.exp (-((π - |φ|) * |z.im|)) := by
        rw [show -((π - |φ|) * |z.im|) = |φ| * |z.im| + -(π * |z.im|) by ring, Real.exp_add]
        ring

/-- The bound on `H` away from the real axis. -/
theorem norm_H_le {z : ℂ} (hz : z ∈ strip) (hN : 1 ≤ |z.im|) :
    ‖H f φ z‖ ≤ 8 * π * C * Real.exp (-((π - |φ|) * |z.im|)) + ‖f 0‖ / |z.im| := by
  have hz0 : z ≠ 0 := fun h => by rw [h] at hN; norm_num at hN
  have hpos : 0 < |z.im| := by linarith
  rw [H_of_ne f φ hz0, norm_div]
  have hzn : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hpos hzn
  calc ‖G f φ z - f 0‖ / ‖z‖ ≤ (‖G f φ z‖ + ‖f 0‖) / |z.im| := by
        gcongr
        exact norm_sub_le _ _
    _ ≤ (8 * π * C * |z.im| * Real.exp (-((π - |φ|) * |z.im|)) + ‖f 0‖) / |z.im| := by
        gcongr
        exact norm_G_le f φ hf_bdd hz hN
    _ = 8 * π * C * Real.exp (-((π - |φ|) * |z.im|)) + ‖f 0‖ / |z.im| := by
        field_simp <;> ring

/-- The horizontal edges: `‖∫ H(x + yI) dx‖ ≤ 8πC e^{-(π-|φ|)|y|} + ‖f 0‖/|y|` for `|y| ≥ 1`. -/
theorem norm_edge_le {y : ℝ} (hy : 1 ≤ |y|) :
    ‖∫ x : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ), H f φ (x + y * I)‖ ≤
      8 * π * C * Real.exp (-((π - |φ|) * |y|)) + ‖f 0‖ / |y| := by
  have := norm_integral_le_of_norm_le_const (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
    (f := fun x : ℝ => H f φ (x + y * I))
    (C := 8 * π * C * Real.exp (-((π - |φ|) * |y|)) + ‖f 0‖ / |y|) fun x hx => by
      have hx' : x ∈ Set.Ioc (-1 / 2 : ℝ) (1 / 2) := by
        rwa [uIoc_of_le (by norm_num)] at hx
      have hz : (x + y * I : ℂ) ∈ strip := by
        show |(x + y * I : ℂ).re| ≤ 1 / 2
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_self, add_zero]
        rw [abs_le]; exact ⟨by linarith [hx'.1], hx'.2⟩
      have him : (x + y * I : ℂ).im = y := by simp
      have := norm_H_le f φ hf_bdd hz (by rw [him]; exact hy)
      rwa [him] at this
  calc _ ≤ (8 * π * C * Real.exp (-((π - |φ|) * |y|)) + ‖f 0‖ / |y|) * |(1 / 2 : ℝ) - (-1 / 2)| :=
        this
    _ = _ := by norm_num

include hφ

/-- The horizontal edges vanish as `N → ∞`. -/
theorem tendsto_edges :
    Tendsto (fun N : ℕ => (∫ x : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ), H f φ (x + -(N : ℂ) * I)) -
      (∫ x : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ), H f φ (x + N * I))) atTop (𝓝 0) := by
  have ha : 0 < π - |φ| := sub_pos.mpr hφ
  -- the bound tends to zero
  have hb : Tendsto (fun N : ℕ => 8 * π * C * Real.exp (-((π - |φ|) * (N : ℝ))) + ‖f 0‖ / (N : ℝ))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => Real.exp (-((π - |φ|) * (N : ℝ)))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_natCast_atTop_atTop.const_mul_atTop ha)
    have h2 := tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) ‖f 0‖
    have := (h1.const_mul (8 * π * C)).add h2
    simpa using this
  have hbound : ∀ᶠ N : ℕ in atTop,
      ‖(∫ x : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ), H f φ (x + -(N : ℂ) * I)) -
        (∫ x : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ), H f φ (x + N * I))‖ ≤
        2 * (8 * π * C * Real.exp (-((π - |φ|) * (N : ℝ))) + ‖f 0‖ / (N : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN' : (1 : ℝ) ≤ |(N : ℝ)| := by
      rw [abs_of_nonneg (Nat.cast_nonneg N)]; exact_mod_cast hN
    have hN'' : (1 : ℝ) ≤ |(-(N : ℝ))| := by rwa [abs_neg]
    have e1 := norm_edge_le f φ hf_bdd hN''
    have e2 := norm_edge_le f φ hf_bdd hN'
    simp only [Complex.ofReal_neg, Complex.ofReal_natCast] at e1 e2
    rw [abs_neg, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N)] at e1
    rw [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N)] at e2
    calc _ ≤ ‖∫ x : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ), H f φ (x + -(N : ℂ) * I)‖ +
          ‖∫ x : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ), H f φ (x + N * I)‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  refine squeeze_zero_norm' hbound ?_
  simpa using hb.const_mul 2

omit hφ

/-- The vertical-edge integrand: `V t = G(1/2+it)/(1/2+it) − G(-1/2+it)/(-1/2+it)`. -/
noncomputable def V : ℝ → ℂ := fun y =>
  G f φ (1 / 2 + y * I) / (1 / 2 + y * I) - G f φ (-1 / 2 + y * I) / (-1 / 2 + y * I)

omit hf_bdd in
theorem H_sub_H (y : ℝ) : H f φ (1 / 2 + y * I) - H f φ (-1 / 2 + y * I) =
    V f φ y - f 0 * (((1 / 4 + y ^ 2 : ℝ)⁻¹ : ℝ) : ℂ) := by
  rw [H_of_ne f φ (half_add_ne_zero y), H_of_ne f φ (neg_half_add_ne_zero y), ← inv_sub_inv_eq y, V]
  ring

omit hf_bdd in
/-- The explicit form of `V`. -/
theorem V_eq (y : ℝ) : V f φ y = 2 * π * ((w φ y : ℂ) *
    (exp (I * φ / 2) * f (1 / 2 + y * I) + exp (-(I * φ / 2)) * f (-1 / 2 + y * I))) := by
  have hc : (Real.cosh (π * y) : ℂ) ≠ 0 := by exact_mod_cast (Real.cosh_pos _).ne'
  have h1 := half_add_ne_zero y
  have h2 := neg_half_add_ne_zero y
  have hw : (w φ y : ℂ) = Complex.exp (-(φ * y : ℝ)) / (2 * Real.cosh (π * y)) := by
    unfold w
    push_cast
    ring_nf
  have e1 : I * φ * (1 / 2 + y * I) = I * φ / 2 + (-(φ * y) : ℝ) := by
    push_cast; ring_nf; rw [Complex.I_sq]; ring
  have e2 : I * φ * (-1 / 2 + y * I) = -(I * φ / 2) + (-(φ * y) : ℝ) := by
    push_cast; ring_nf; rw [Complex.I_sq]; ring
  have t1 : G f φ (1 / 2 + y * I) / (1 / 2 + y * I) =
      exp (I * φ / 2) * exp (-(φ * y) : ℝ) * f (1 / 2 + y * I) * (π / Real.cosh (π * y)) := by
    rw [div_eq_iff h1]
    unfold G g
    rw [ψ_of_ne h1, sin_pi_mul_half_add, e1, Complex.exp_add]
    field_simp <;> ring
  have t2 : G f φ (-1 / 2 + y * I) / (-1 / 2 + y * I) =
      -(exp (-(I * φ / 2)) * exp (-(φ * y) : ℝ) * f (-1 / 2 + y * I) * (π / Real.cosh (π * y))) := by
    rw [div_eq_iff h2]
    unfold G g
    rw [ψ_of_ne h2, sin_pi_mul_neg_half_add, e2, Complex.exp_add]
    field_simp <;> ring
  rw [V, t1, t2, hw]
  push_cast
  field_simp
  ring

include hf_cont hf_diff

omit hf_bdd in
theorem continuous_V : Continuous (V f φ) := by
  have hG := continuousOn_G f φ hf_cont hf_diff
  have c1 : Continuous fun y : ℝ => G f φ (1 / 2 + y * I) :=
    hG.comp_continuous (by fun_prop) half_add_mem_strip
  have c2 : Continuous fun y : ℝ => G f φ (-1 / 2 + y * I) :=
    hG.comp_continuous (by fun_prop) neg_half_add_mem_strip
  exact (c1.div (by fun_prop) half_add_ne_zero).sub (c2.div (by fun_prop) neg_half_add_ne_zero)

include hφ

theorem integrable_V : Integrable (V f φ) := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hf_bdd 0 zero_mem_strip)
  have hv : Continuous fun y : ℝ =>
      exp (I * φ / 2) * f (1 / 2 + y * I) + exp (-(I * φ / 2)) * f (-1 / 2 + y * I) := by
    have c1 : Continuous fun y : ℝ => f (1 / 2 + y * I) :=
      hf_cont.comp_continuous (by fun_prop) half_add_mem_strip
    have c2 : Continuous fun y : ℝ => f (-1 / 2 + y * I) :=
      hf_cont.comp_continuous (by fun_prop) neg_half_add_mem_strip
    exact (continuous_const.mul c1).add (continuous_const.mul c2)
  have hnorm : ∀ y : ℝ, ‖exp (I * φ / 2) * f (1 / 2 + y * I) +
      exp (-(I * φ / 2)) * f (-1 / 2 + y * I)‖ ≤ 2 * C := fun y => by
    have n1 : ‖exp (I * φ / 2)‖ = 1 := by rw [Complex.norm_exp]; simp
    have n2 : ‖exp (-(I * φ / 2))‖ = 1 := by rw [Complex.norm_exp]; simp
    calc _ ≤ ‖exp (I * φ / 2) * f (1 / 2 + y * I)‖ + ‖exp (-(I * φ / 2)) * f (-1 / 2 + y * I)‖ :=
          norm_add_le _ _
      _ = ‖f (1 / 2 + y * I)‖ + ‖f (-1 / 2 + y * I)‖ := by rw [norm_mul, norm_mul, n1, n2, one_mul, one_mul]
      _ ≤ C + C := add_le_add (hf_bdd _ (half_add_mem_strip y)) (hf_bdd _ (neg_half_add_mem_strip y))
      _ = 2 * C := by ring
  have := (integrable_w_mul hφ hv.aestronglyMeasurable hnorm).const_mul (2 * π : ℂ)
  refine this.congr (Eventually.of_forall fun y => ?_)
  rw [V_eq]

/-- `∫ V = 2π f 0`. -/
theorem integral_V : ∫ y : ℝ, V f φ y = 2 * π * f 0 := by
  have hV := integrable_V f φ hf_cont hf_diff hf_bdd hφ
  have hH : Continuous fun y : ℝ => H f φ (1 / 2 + y * I) :=
    (continuousOn_H f φ hf_cont hf_diff).comp_continuous (by fun_prop) half_add_mem_strip
  have hH' : Continuous fun y : ℝ => H f φ (-1 / 2 + y * I) :=
    (continuousOn_H f φ hf_cont hf_diff).comp_continuous (by fun_prop) neg_half_add_mem_strip
  have hker : Continuous fun y : ℝ => (((1 / 4 + y ^ 2 : ℝ)⁻¹ : ℝ) : ℂ) := by
    refine Complex.continuous_ofReal.comp (Continuous.inv₀ (by fun_prop) fun y => ?_)
    positivity
  -- the vertical edges for each `N`
  have hvert : ∀ N : ℝ, I • (∫ y : ℝ in (-N)..N, H f φ (1 / 2 + y * I)) -
      I • (∫ y : ℝ in (-N)..N, H f φ (-1 / 2 + y * I)) =
      I • ((∫ y : ℝ in (-N)..N, V f φ y) - f 0 * ∫ y : ℝ in (-N)..N, (((1 / 4 + y ^ 2 : ℝ)⁻¹ : ℝ) : ℂ)) := by
    intro N
    rw [← smul_sub, ← intervalIntegral.integral_sub (hH.intervalIntegrable _ _) (hH'.intervalIntegrable _ _),
      ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub ((continuous_V f φ hf_cont hf_diff).intervalIntegrable _ _)
        ((hker.const_mul (f 0)).intervalIntegrable _ _)]
    congr 1
    exact intervalIntegral.integral_congr fun y _ => H_sub_H f φ y
  -- the limit of the vertical edges
  have hlimV : Tendsto (fun N : ℕ => ∫ y : ℝ in (-(N : ℝ))..(N : ℝ), V f φ y) atTop
      (𝓝 (∫ y : ℝ, V f φ y)) :=
    intervalIntegral_tendsto_integral hV (tendsto_neg_atBot_iff.mpr tendsto_natCast_atTop_atTop)
      tendsto_natCast_atTop_atTop
  have hker_int : Integrable fun y : ℝ => (((1 / 4 + y ^ 2 : ℝ)⁻¹ : ℝ) : ℂ) :=
    integrable_inv_quarter_add_sq.ofReal
  have hker_val : ∫ y : ℝ, (((1 / 4 + y ^ 2 : ℝ)⁻¹ : ℝ) : ℂ) = 2 * π := by
    rw [integral_complex_ofReal, integral_inv_quarter_add_sq]; push_cast; ring
  have hlimK : Tendsto (fun N : ℕ => ∫ y : ℝ in (-(N : ℝ))..(N : ℝ), (((1 / 4 + y ^ 2 : ℝ)⁻¹ : ℝ) : ℂ))
      atTop (𝓝 (2 * π)) := by
    rw [← hker_val]
    exact intervalIntegral_tendsto_integral hker_int
      (tendsto_neg_atBot_iff.mpr tendsto_natCast_atTop_atTop) tendsto_natCast_atTop_atTop
  have hlim2 : Tendsto (fun N : ℕ => I • (∫ y : ℝ in (-(N : ℝ))..(N : ℝ), H f φ (1 / 2 + y * I)) -
      I • (∫ y : ℝ in (-(N : ℝ))..(N : ℝ), H f φ (-1 / 2 + y * I))) atTop
      (𝓝 (I • ((∫ y : ℝ, V f φ y) - f 0 * (2 * π)))) := by
    have := (hlimV.sub (hlimK.const_mul (f 0))).const_smul I
    refine this.congr fun N => ?_
    rw [hvert]
  have hlim1 := tendsto_edges f φ hf_bdd hφ
  have htot := hlim1.add hlim2
  have hzero : (fun N : ℕ => ((∫ x : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ), H f φ (x + -(N : ℂ) * I)) -
      (∫ x : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ), H f φ (x + N * I))) +
      (I • (∫ y : ℝ in (-(N : ℝ))..(N : ℝ), H f φ (1 / 2 + y * I)) -
      I • (∫ y : ℝ in (-(N : ℝ))..(N : ℝ), H f φ (-1 / 2 + y * I)))) = fun _ => 0 := by
    funext N
    have := rect_eq_zero f φ hf_cont hf_diff (N : ℝ)
    linear_combination this
  rw [hzero] at htot
  have h0 : (0 : ℂ) + I • ((∫ y : ℝ, V f φ y) - f 0 * (2 * π)) = 0 :=
    tendsto_nhds_unique htot tendsto_const_nhds
  rw [zero_add, smul_eq_mul, mul_eq_zero, sub_eq_zero] at h0
  rcases h0 with h0 | h0
  · exact absurd h0 I_ne_zero
  · rw [h0]; ring

/-- **RvD Lemma 4.6 (Cauchy's formula on the strip)**: for `f` bounded continuous on
`|Re z| ≤ 1/2` and analytic inside, and `|φ| < π`,
`f 0 = ∫ t, e^{-φt}/(2cosh πt) · (e^{iφ/2} f(1/2 + it) + e^{-iφ/2} f(-1/2 + it)) dt`. -/
theorem strip_cauchy : f 0 = ∫ t : ℝ, (w φ t : ℂ) *
    (exp (I * φ / 2) * f (1 / 2 + t * I) + exp (-(I * φ / 2)) * f (-1 / 2 + t * I)) := by
  have h := integral_V f φ hf_cont hf_diff hf_bdd hφ
  have hV : (V f φ) = fun t => (2 * π : ℂ) * ((w φ t : ℂ) *
      (exp (I * φ / 2) * f (1 / 2 + t * I) + exp (-(I * φ / 2)) * f (-1 / 2 + t * I))) :=
    funext fun t => V_eq f φ t
  rw [hV, MeasureTheory.integral_const_mul] at h
  have h2 : (2 * π : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
  exact (mul_left_cancel₀ h2 h).symm

end Main

end StripCauchy

end CommutingRepetition

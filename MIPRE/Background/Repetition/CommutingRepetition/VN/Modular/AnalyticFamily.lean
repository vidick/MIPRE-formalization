/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/Modular/AnalyticFamily.lean
-/
/-
# The analytic family `E(z) = e^{zθ}(R) T` (density stage E4.3c)

Rieffel–van Daele's proof of Lemma 4.7 uses the operator family
`R^{-z+1/2} (2−R)^{z+1/2}` on the strip `|Re z| ≤ 1/2` (their Lemma 3.6). In the
variable `θ = log((2−λ)/λ)` of `VN/Modular/ModularGroup`, this family is
`E(z) := cbfc(R)(λ ↦ e^{zθ(λ)} gT(λ))` where `gT(λ) = √(λ(2−λ)) = 1/cosh(θ/2)`:
`e^{θ/2} gT = 2 − λ`, `e^{-θ/2} gT = λ` on `(0,2)`. Consequently
`E(0) = T`, `E(1/2 + it) = (2−R) Δ^{it}`, `E(-1/2 + it) = R Δ^{it}`, `E(z)* = E(z̄)`,
`J E(z) = E(-z̄) J`, `‖E(z)‖ ≤ 2` on the closed strip, `z ↦ E(z)ξ` is continuous
on the closed strip and complex differentiable on the open strip (with derivative
`cbfc(θ e^{zθ} gT) ξ`, by dominated convergence for the Borel calculus).

The boundary identities need the spectral measures of `R` to have no atoms at
`0` and `2` (`R` and `2−R` are injective); the general fact "no atom at a
non-eigenvalue" is proved here for the Borel calculus of `VN/BorelCalculus`.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.Modular.LinearRN
import MIPRE.Background.Repetition.CommutingRepetition.VN.Modular.StripCauchy

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

open scoped InnerProductSpace ComplexConjugate
open Filter Topology BorelCalc MeasureTheory

/-! ## No atoms at non-eigenvalues; Borel functions equal a.e. give the same operator -/

namespace BorelCalc

variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗] [CompleteSpace 𝓗]
variable (E : 𝓗 →L[ℂ] 𝓗) (hE : IsSelfAdjoint E)

/-- If `E − c` is injective, the spectral projection of `{c}` vanishes. -/
theorem P_singleton_eq_zero {c : ℝ} (hinj : ∀ x, E x = (c : ℂ) • x → x = 0) :
    P E hE {c} = 0 := by
  by_cases hc : |c| ≤ ‖E‖
  · ext ξ
    rw [_root_.zero_apply]
    apply hinj
    have h1 : E * P E hE {c} = (c : ℂ) • P E hE {c} := by
      have hEb : E = bfc E hE (VN.Modular.clamp ‖E‖) := (VN.Modular.bfc_clamp_eq hE).symm
      nth_rw 1 [hEb]
      rw [P, ← bfc_mul E hE (VN.Modular.bdd_clamp (norm_nonneg E))
        (Bdd.indicator (measurableSet_singleton c)),
        ← bfc_const_mul E hE c (Bdd.indicator (measurableSet_singleton c))]
      congr 1
      funext t
      by_cases ht : t = c
      · subst ht
        simp [VN.Modular.clamp_eq_of_abs_le hc]
      · simp [ht]
    exact congrArg (fun S : 𝓗 →L[ℂ] 𝓗 => S ξ) h1
  · rw [P_eq_zero_of_disjoint_spectrum E hE (measurableSet_singleton c)]
    rw [Set.disjoint_singleton_left]
    intro hmem
    exact hc (abs_le.mpr (VN.Modular.spectrum_subset_Icc_norm E hmem))

/-- No atom of the spectral measures at a non-eigenvalue. -/
theorem ν_singleton_eq_zero {c : ℝ} (hinj : ∀ x, E x = (c : ℂ) • x → x = 0) (ξ : 𝓗) :
    ν E hE ξ {c} = 0 := by
  have h := norm_P_apply_sq E hE (measurableSet_singleton c) ξ
  rw [P_singleton_eq_zero E hE hinj, _root_.zero_apply, norm_zero, zero_pow two_ne_zero] at h
  exact (ENNReal.toReal_eq_zero_iff _).mp h.symm |>.resolve_right (measure_ne_top _ _)

/-- Borel functions which agree a.e. for every spectral measure give the same operator. -/
theorem cbfc_congr_ae {G G' : ℝ → ℂ} (hG : CBdd G) (hG' : CBdd G')
    (h : ∀ ξ, G =ᵐ[ν E hE ξ] G') : cbfc E hE G = cbfc E hE G' := by
  ext ξ
  rw [← sub_eq_zero, ← _root_.sub_apply, ← cbfc_sub E hE hG hG', ← norm_eq_zero,
    ← pow_eq_zero_iff two_ne_zero, norm_sq_cbfc E hE (hG.sub hG')]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [h ξ] with t ht
  simp [Pi.sub_apply, ht]

end BorelCalc

namespace VN

namespace Modular

open ClosedSubmodule StripCauchy

set_option linter.unusedSectionVars false

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ## The scalar functions `gE z = e^{zθ} gT` -/

/-- `gE z l = e^{z θ(l)} gT(l)`. -/
noncomputable def gE (z : ℂ) (l : ℝ) : ℂ := Complex.exp (z * θ l) * gT l

theorem measurable_gE (z : ℂ) : Measurable (gE z) := by
  unfold gE
  exact (Complex.measurable_exp.comp (measurable_const.mul
    (Complex.measurable_ofReal.comp measurable_θ))).mul
    (Complex.measurable_ofReal.comp continuous_gT.measurable)

theorem norm_gE (z : ℂ) (l : ℝ) : ‖gE z l‖ = Real.exp (z.re * θ l) * gT l := by
  unfold gE
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_of_nonneg (gT_nonneg l)]
  congr 2
  simp [Complex.mul_re]

theorem gT_eq_zero_of_notMem {l : ℝ} (hl : l ∉ Set.Ioo (0 : ℝ) 2) : gT l = 0 := by
  unfold gT
  rw [Real.sqrt_eq_zero']
  simp only [Set.mem_Ioo, not_and_or, not_lt] at hl
  rcases hl with h | h <;> nlinarith

theorem θ_of_mem {l : ℝ} (hl : l ∈ Set.Ioo (0 : ℝ) 2) : θ l = Real.log ((2 - l) / l) := by
  unfold θ; rw [if_pos hl]

theorem θ_of_notMem {l : ℝ} (hl : l ∉ Set.Ioo (0 : ℝ) 2) : θ l = 0 := by
  unfold θ; rw [if_neg hl]

/-- `e^{θ/2} gT = 2 − l` on `(0, 2)`. -/
theorem exp_half_θ_mul_gT {l : ℝ} (hl : l ∈ Set.Ioo (0 : ℝ) 2) :
    Real.exp (θ l / 2) * gT l = 2 - l := by
  have hl0 : 0 < l := hl.1
  have hl2 : 0 < 2 - l := by linarith [hl.2]
  have hprod : 0 ≤ l * (2 - l) := by positivity
  have hsq : (Real.exp (θ l / 2) * gT l) ^ 2 = (2 - l) ^ 2 := by
    rw [mul_pow, sq (Real.exp _), ← Real.exp_add, add_halves, θ_of_mem hl,
      Real.exp_log (by positivity), gT, Real.sq_sqrt hprod]
    field_simp
  exact (pow_left_inj₀ (mul_nonneg (Real.exp_pos _).le (gT_nonneg l)) hl2.le two_ne_zero).mp hsq

/-- `e^{-θ/2} gT = l` on `(0, 2)`. -/
theorem exp_neg_half_θ_mul_gT {l : ℝ} (hl : l ∈ Set.Ioo (0 : ℝ) 2) :
    Real.exp (-(θ l / 2)) * gT l = l := by
  have hl0 : 0 < l := hl.1
  have hl2 : 0 < 2 - l := by linarith [hl.2]
  have hprod : 0 ≤ l * (2 - l) := by positivity
  have hsq : (Real.exp (-(θ l / 2)) * gT l) ^ 2 = l ^ 2 := by
    rw [mul_pow, sq (Real.exp _), ← Real.exp_add, ← neg_add, add_halves, θ_of_mem hl,
      Real.exp_neg, Real.exp_log (by positivity), gT, Real.sq_sqrt hprod]
    field_simp
  exact (pow_left_inj₀ (mul_nonneg (Real.exp_pos _).le (gT_nonneg l)) hl0.le two_ne_zero).mp hsq

/-- `e^{|θ|/2} gT ≤ 2`. -/
theorem exp_abs_half_θ_mul_gT_le (l : ℝ) : Real.exp (|θ l| / 2) * gT l ≤ 2 := by
  by_cases hl : l ∈ Set.Ioo (0 : ℝ) 2
  · have h1 := exp_half_θ_mul_gT hl
    have h2 := exp_neg_half_θ_mul_gT hl
    have hg := gT_nonneg l
    have : Real.exp (|θ l| / 2) ≤ Real.exp (θ l / 2) + Real.exp (-(θ l / 2)) := by
      rcases le_or_gt 0 (θ l) with h | h
      · rw [abs_of_nonneg h]; linarith [Real.exp_pos (-(θ l / 2))]
      · rw [abs_of_neg h, neg_div]; linarith [Real.exp_pos (θ l / 2)]
    calc Real.exp (|θ l| / 2) * gT l ≤ (Real.exp (θ l / 2) + Real.exp (-(θ l / 2))) * gT l := by
          gcongr
      _ = 2 := by rw [add_mul, h1, h2]; ring
  · rw [gT_eq_zero_of_notMem hl, mul_zero]; norm_num

/-- `‖gE z l‖ ≤ 2` on the closed strip. -/
theorem norm_gE_le {z : ℂ} (hz : |z.re| ≤ 1 / 2) (l : ℝ) : ‖gE z l‖ ≤ 2 := by
  rw [norm_gE]
  have hre : z.re * θ l ≤ |θ l| / 2 := by
    calc z.re * θ l ≤ |z.re * θ l| := le_abs_self _
      _ = |z.re| * |θ l| := abs_mul _ _
      _ ≤ 1 / 2 * |θ l| := by gcongr
      _ = |θ l| / 2 := by ring
  calc Real.exp (z.re * θ l) * gT l ≤ Real.exp (|θ l| / 2) * gT l :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hre) (gT_nonneg l)
    _ ≤ 2 := exp_abs_half_θ_mul_gT_le l

/-- `s e^{-a s} ≤ 1/a` for `a > 0`, `s ≥ 0`. -/
theorem mul_exp_neg_le {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) : s * Real.exp (-(a * s)) ≤ 1 / a := by
  have h := Real.add_one_le_exp (a * s)
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) ha]
  nlinarith

/-- `‖θ gE z‖ ≤ 2/δ` for `|Re z| ≤ 1/2 − δ`. -/
theorem norm_θ_mul_gE_le {z : ℂ} {δ : ℝ} (hδ : 0 < δ) (hz : |z.re| ≤ 1 / 2 - δ) (l : ℝ) :
    ‖(θ l : ℂ) * gE z l‖ ≤ 2 / δ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_gE]
  have hθ := abs_nonneg (θ l)
  have hg := gT_nonneg l
  have hre : z.re * θ l ≤ (1 / 2 - δ) * |θ l| := by
    calc z.re * θ l ≤ |z.re| * |θ l| := by rw [← abs_mul]; exact le_abs_self _
      _ ≤ (1 / 2 - δ) * |θ l| := by gcongr
  calc |θ l| * (Real.exp (z.re * θ l) * gT l)
      ≤ |θ l| * (Real.exp ((1 / 2 - δ) * |θ l|) * gT l) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hre) hg) hθ
    _ = (|θ l| * Real.exp (-(δ * |θ l|))) * (Real.exp (|θ l| / 2) * gT l) := by
        rw [show (1 / 2 - δ) * |θ l| = -(δ * |θ l|) + |θ l| / 2 by ring, Real.exp_add]; ring
    _ ≤ (1 / δ) * 2 :=
        mul_le_mul (mul_exp_neg_le hδ hθ) (exp_abs_half_θ_mul_gT_le l)
          (mul_nonneg (Real.exp_pos _).le hg) (by positivity)
    _ = 2 / δ := by ring

/-- `‖(e^{w} − 1)/h‖ ≤ |θ|(e^{|h||θ|} + 2)` for `w = h θ`, `h ≠ 0`. -/
theorem norm_exp_sub_one_div_le {h : ℂ} (hh : h ≠ 0) (θ₀ : ℝ) :
    ‖(Complex.exp (h * θ₀) - 1) / h‖ ≤ |θ₀| * (Real.exp (‖h‖ * |θ₀|) + 2) := by
  have hn : 0 < ‖h‖ := norm_pos_iff.mpr hh
  rw [norm_div, div_le_iff₀ hn]
  have hw : ‖h * (θ₀ : ℂ)‖ = ‖h‖ * |θ₀| := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  by_cases hsmall : ‖h * (θ₀ : ℂ)‖ ≤ 1
  · calc ‖Complex.exp (h * θ₀) - 1‖ ≤ 2 * ‖h * (θ₀ : ℂ)‖ := Complex.norm_exp_sub_one_le hsmall
      _ = |θ₀| * 2 * ‖h‖ := by rw [hw]; ring
      _ ≤ |θ₀| * (Real.exp (‖h‖ * |θ₀|) + 2) * ‖h‖ := by
          gcongr
          linarith [Real.exp_pos (‖h‖ * |θ₀|)]
  · rw [not_le, hw] at hsmall
    have h1 : ‖Complex.exp (h * θ₀) - 1‖ ≤ Real.exp (‖h‖ * |θ₀|) + 1 := by
      calc ‖Complex.exp (h * θ₀) - 1‖ ≤ ‖Complex.exp (h * θ₀)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = Real.exp ((h * θ₀ : ℂ).re) + 1 := by rw [Complex.norm_exp, norm_one]
        _ ≤ Real.exp (‖h‖ * |θ₀|) + 1 := by
            gcongr
            calc (h * θ₀ : ℂ).re ≤ ‖h * (θ₀ : ℂ)‖ := Complex.re_le_norm _
              _ = ‖h‖ * |θ₀| := hw
    have h2 : 1 ≤ |θ₀| * ‖h‖ := by nlinarith
    calc ‖Complex.exp (h * θ₀) - 1‖ ≤ Real.exp (‖h‖ * |θ₀|) + 1 := h1
      _ = (Real.exp (‖h‖ * |θ₀|) + 1) * 1 := (mul_one _).symm
      _ ≤ (Real.exp (‖h‖ * |θ₀|) + 1) * (|θ₀| * ‖h‖) := by gcongr
      _ ≤ (Real.exp (‖h‖ * |θ₀|) + 2) * (|θ₀| * ‖h‖) := by gcongr; norm_num
      _ = |θ₀| * (Real.exp (‖h‖ * |θ₀|) + 2) * ‖h‖ := by ring

/-- The difference quotient bound: for `|Re z₀| = 1/2 − δ` and `‖h‖ ≤ δ/2`,
`‖(gE (z₀ + h) l − gE z₀ l)/h‖ ≤ 12/δ`. -/
theorem norm_gE_quotient_le {z₀ h : ℂ} {δ : ℝ} (hδ : 0 < δ) (hz : |z₀.re| ≤ 1 / 2 - δ)
    (hh : ‖h‖ ≤ δ / 2) (hh0 : h ≠ 0) (l : ℝ) :
    ‖(gE (z₀ + h) l - gE z₀ l) / h‖ ≤ 12 / δ := by
  have hθ := abs_nonneg (θ l)
  have hg := gT_nonneg l
  have e : gE (z₀ + h) l - gE z₀ l = gE z₀ l * (Complex.exp (h * θ l) - 1) := by
    unfold gE
    rw [add_mul, Complex.exp_add]
    ring
  rw [e, mul_div_assoc, norm_mul, norm_gE]
  have hq := norm_exp_sub_one_div_le hh0 (θ l)
  have hre : z₀.re * θ l ≤ (1 / 2 - δ) * |θ l| := by
    calc z₀.re * θ l ≤ |z₀.re| * |θ l| := by rw [← abs_mul]; exact le_abs_self _
      _ ≤ (1 / 2 - δ) * |θ l| := by gcongr
  have hq' : ‖(Complex.exp (h * θ l) - 1) / h‖ ≤ |θ l| * (Real.exp (δ / 2 * |θ l|) + 2) :=
    hq.trans (mul_le_mul_of_nonneg_left (add_le_add_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hh hθ)) 2) hθ)
  have hone : (1 : ℝ) ≤ Real.exp (δ / 2 * |θ l|) := Real.one_le_exp (by positivity)
  have hnn : 0 ≤ Real.exp ((1 / 2 - δ) * |θ l|) * gT l := mul_nonneg (Real.exp_pos _).le hg
  calc Real.exp (z₀.re * θ l) * gT l * ‖(Complex.exp (h * θ l) - 1) / h‖
      ≤ Real.exp ((1 / 2 - δ) * |θ l|) * gT l * (|θ l| * (Real.exp (δ / 2 * |θ l|) + 2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hre) hg) hq'
          (norm_nonneg _) hnn
    _ ≤ Real.exp ((1 / 2 - δ) * |θ l|) * gT l * (|θ l| * (3 * Real.exp (δ / 2 * |θ l|))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hθ) hnn
    _ = 3 * (|θ l| * Real.exp (-(δ / 2 * |θ l|))) * (Real.exp (|θ l| / 2) * gT l) := by
        rw [show (1 / 2 - δ) * |θ l| = (|θ l| / 2 + -(δ / 2 * |θ l|)) + -(δ / 2 * |θ l|) by ring,
          Real.exp_add, Real.exp_add]
        have : Real.exp (-(δ / 2 * |θ l|)) * Real.exp (δ / 2 * |θ l|) = 1 := by
          rw [← Real.exp_add]; simp
        calc _ = 3 * |θ l| * Real.exp (|θ l| / 2) * Real.exp (-(δ / 2 * |θ l|)) * gT l *
              (Real.exp (-(δ / 2 * |θ l|)) * Real.exp (δ / 2 * |θ l|)) := by ring
          _ = _ := by rw [this]; ring
    _ ≤ 3 * (1 / (δ / 2)) * 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left (mul_exp_neg_le (by positivity) hθ) (by norm_num))
          (exp_abs_half_θ_mul_gT_le l) (mul_nonneg (Real.exp_pos _).le hg) (by positivity)
    _ = 12 / δ := by field_simp; ring

/-! ## The operator family `E(z)` -/

theorem cbdd_gE {z : ℂ} (hz : |z.re| ≤ 1 / 2) : CBdd (gE z) := ⟨measurable_gE z, 2, norm_gE_le hz⟩

/-- `cbfc (c * H) = c • cbfc H`. -/
theorem _root_.CommutingRepetition.BorelCalc.cbfc_const_mul' {𝓗 : Type*} [NormedAddCommGroup 𝓗]
    [InnerProductSpace ℂ 𝓗] [CompleteSpace 𝓗] (E : 𝓗 →L[ℂ] 𝓗) (hE : IsSelfAdjoint E) (c : ℂ)
    {H : ℝ → ℂ} (hH : CBdd H) : cbfc E hE (fun t => c * H t) = c • cbfc E hE H := by
  rw [show (fun t => c * H t) = (fun _ => c) * H from rfl, cbfc_mul E hE (CBdd.const c) hH,
    cbfc_const, smul_mul_assoc, one_mul]

variable (M : VonNeumannAlgebra K) (Ω : K)

/-- The analytic family `E(z) = cbfc(R)(e^{zθ} gT)`. -/
noncomputable def Efam (z : ℂ) : K →L[ℂ] K := cbfc (R M Ω) (R_isSelfAdjoint M Ω) (gE z)

/-- Its derivative `E'(z) = cbfc(R)(θ e^{zθ} gT)`. -/
noncomputable def Efam' (z : ℂ) : K →L[ℂ] K :=
  cbfc (R M Ω) (R_isSelfAdjoint M Ω) fun l => (θ l : ℂ) * gE z l

theorem norm_Efam_le {z : ℂ} (hz : |z.re| ≤ 1 / 2) : ‖Efam M Ω z‖ ≤ 2 :=
  norm_cbfc_le _ _ (cbdd_gE hz) (by norm_num) (norm_gE_le hz)

theorem norm_Efam_apply_le {z : ℂ} (hz : |z.re| ≤ 1 / 2) (ξ : K) : ‖Efam M Ω z ξ‖ ≤ 2 * ‖ξ‖ :=
  ((Efam M Ω z).le_opNorm ξ).trans (by gcongr; exact norm_Efam_le M Ω hz)

theorem Efam_zero : Efam M Ω 0 = Tm M Ω := by
  unfold Efam
  have : gE 0 = fun l => (gT l : ℂ) := by funext l; simp [gE]
  rw [this, cbfc_ofReal, Tm_eq_bfc]

theorem star_Efam {z : ℂ} (hz : |z.re| ≤ 1 / 2) : star (Efam M Ω z) = Efam M Ω (conj z) := by
  unfold Efam
  rw [cbfc_star _ _ (cbdd_gE hz)]
  congr 1
  funext l
  simp only [gE, map_mul, ← Complex.exp_conj, Complex.conj_ofReal]

variable (hs : IsSeparating (M : Set (K →L[ℂ] K)) Ω) (hc : IsCyclic (M : Set (K →L[ℂ] K)) Ω)

include hs hc in
/-- `J E(z) = E(-z̄) J`. -/
theorem Jm_Efam {z : ℂ} (hz : |z.re| ≤ 1 / 2) (ξ : K) :
    Jm M Ω (Efam M Ω z ξ) = Efam M Ω (-conj z) (Jm M Ω ξ) := by
  unfold Efam
  rw [Jm_cbfc M Ω hs hc (cbdd_gE hz)]
  have : (fun l => conj (gE z (2 - l))) = gE (-conj z) := by
    funext l
    simp only [gE, θ_two_sub, gT_two_sub, map_mul, ← Complex.exp_conj, Complex.conj_ofReal,
      Complex.ofReal_neg, map_neg, mul_neg, neg_mul]
  rw [this]

/-! ### The spectral measures of `R` live on `(0, 2)` -/

include hs hc in
theorem ae_mem_Ioo (ξ : K) :
    ∀ᵐ l ∂(ν (R M Ω) (R_isSelfAdjoint M Ω) ξ), l ∈ Set.Ioo (0 : ℝ) 2 := by
  rw [ae_iff]
  refine measure_mono_null (t := (spectrum ℝ (R M Ω))ᶜ ∪ ({0} ∪ {2})) ?_ ?_
  · intro l hl
    simp only [Set.mem_setOf_eq, Set.mem_Ioo, not_and_or, not_lt] at hl
    by_cases hsp : l ∈ spectrum ℝ (R M Ω)
    · right
      have hI := spectrum_R_subset M Ω hsp
      rcases hl with h | h
      · left; exact le_antisymm h hI.1
      · right; exact le_antisymm hI.2 h
    · left; exact hsp
  · refine measure_union_null (ν_compl_spectrum _ _ ξ) (measure_union_null ?_ ?_)
    · refine ν_singleton_eq_zero _ _ (fun x hx => ?_) ξ
      rw [Complex.ofReal_zero, zero_smul] at hx
      exact (R_eq_zero_iff M Ω hc).mp hx
    · refine ν_singleton_eq_zero _ _ (fun x hx => ?_) ξ
      apply (two_sub_R_eq_zero_iff M Ω hs).mp
      rw [_root_.sub_apply, hx, Complex.ofReal_ofNat, sub_eq_zero]
      rw [show (2 : K →L[ℂ] K) = 1 + 1 from one_add_one_eq_two.symm, _root_.add_apply,
        one_apply_eq_self, two_smul]

/-! ### Boundary values -/

/-- `g₁ l = l` on `[0, 2]`, bounded continuous. -/
noncomputable def g₁ (l : ℝ) : ℝ := clamp 1 (l - 1) + 1

/-- `g₂ l = 2 − l` on `[0, 2]`, bounded continuous. -/
noncomputable def g₂ (l : ℝ) : ℝ := 2 - g₁ l

theorem g₁_eq {l : ℝ} (hl : l ∈ Set.Icc (0 : ℝ) 2) : g₁ l = l := by
  unfold g₁
  rw [clamp_eq_of_abs_le (abs_le.mpr ⟨by linarith [hl.1], by linarith [hl.2]⟩)]
  ring

theorem g₂_eq {l : ℝ} (hl : l ∈ Set.Icc (0 : ℝ) 2) : g₂ l = 2 - l := by
  unfold g₂; rw [g₁_eq hl]

theorem continuous_g₁ : Continuous g₁ := by unfold g₁; exact (continuous_clamp 1).comp (by fun_prop) |>.add continuous_const

theorem continuous_g₂ : Continuous g₂ := by unfold g₂; exact continuous_const.sub continuous_g₁

theorem bdd_g₁ : Bdd g₁ :=
  Bdd.of_continuous continuous_g₁ (C := 2) fun l => by
    unfold g₁
    have := abs_clamp_le (zero_le_one' ℝ) (l - 1)
    rw [abs_le] at this ⊢
    constructor <;> linarith

theorem bdd_g₂ : Bdd g₂ :=
  Bdd.of_continuous continuous_g₂ (C := 4) fun l => by
    unfold g₂ g₁
    have := abs_clamp_le (zero_le_one' ℝ) (l - 1)
    rw [abs_le] at this ⊢
    constructor <;> linarith

theorem bfc_g₁ : bfc (R M Ω) (R_isSelfAdjoint M Ω) g₁ = R M Ω := by
  rw [bfc_cfc _ _ bdd_g₁ continuous_g₁]
  calc cfc g₁ (R M Ω) = cfc (fun l : ℝ => l) (R M Ω) :=
        cfc_congr fun l hl => g₁_eq (spectrum_R_subset M Ω hl)
    _ = R M Ω := cfc_id' ℝ (R M Ω) (R_isSelfAdjoint M Ω)

theorem bfc_g₂ : bfc (R M Ω) (R_isSelfAdjoint M Ω) g₂ = 2 - R M Ω := by
  rw [bfc_cfc _ _ bdd_g₂ continuous_g₂]
  calc cfc g₂ (R M Ω) = cfc (fun l : ℝ => 2 - l) (R M Ω) :=
        cfc_congr fun l hl => g₂_eq (spectrum_R_subset M Ω hl)
    _ = 2 - R M Ω := cfc_two_sub M Ω

theorem re_half_add (t : ℝ) : |((1 / 2 : ℂ) + t * Complex.I).re| ≤ 1 / 2 := by simp

theorem re_neg_half_add (t : ℝ) : |((-1 / 2 : ℂ) + t * Complex.I).re| ≤ 1 / 2 := by
  simp; norm_num

include hs hc in
/-- `E(1/2 + it) = (2 − R) Δ^{it}`. -/
theorem Efam_half_add (t : ℝ) : Efam M Ω (1 / 2 + t * Complex.I) = (2 - R M Ω) * Δit M Ω t := by
  have h1 : Efam M Ω (1 / 2 + t * Complex.I) =
      cbfc (R M Ω) (R_isSelfAdjoint M Ω) (fun l => (g₂ l : ℂ)) *
        cbfc (R M Ω) (R_isSelfAdjoint M Ω) (gDel t) := by
    unfold Efam
    rw [← cbfc_mul _ _ (CBdd.ofReal bdd_g₂) (cbdd_gDel t)]
    refine cbfc_congr_ae _ _ (cbdd_gE (re_half_add t)) ((CBdd.ofReal bdd_g₂).mul (cbdd_gDel t))
      fun ξ => ?_
    filter_upwards [ae_mem_Ioo M Ω hs hc ξ] with l hl
    simp only [gE, gDel, Pi.mul_apply]
    rw [g₂_eq ⟨hl.1.le, hl.2.le⟩, ← exp_half_θ_mul_gT hl]
    have e : ((1 / 2 : ℂ) + t * Complex.I) * θ l =
        ((θ l / 2 : ℝ) : ℂ) + ((t * θ l : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [e, Complex.exp_add]
    push_cast
    ring
  rw [h1, cbfc_ofReal, bfc_g₂]
  rfl

include hs hc in
/-- `E(-1/2 + it) = R Δ^{it}`. -/
theorem Efam_neg_half_add (t : ℝ) : Efam M Ω (-1 / 2 + t * Complex.I) = R M Ω * Δit M Ω t := by
  have h1 : Efam M Ω (-1 / 2 + t * Complex.I) =
      cbfc (R M Ω) (R_isSelfAdjoint M Ω) (fun l => (g₁ l : ℂ)) *
        cbfc (R M Ω) (R_isSelfAdjoint M Ω) (gDel t) := by
    unfold Efam
    rw [← cbfc_mul _ _ (CBdd.ofReal bdd_g₁) (cbdd_gDel t)]
    refine cbfc_congr_ae _ _ (cbdd_gE (re_neg_half_add t)) ((CBdd.ofReal bdd_g₁).mul (cbdd_gDel t))
      fun ξ => ?_
    filter_upwards [ae_mem_Ioo M Ω hs hc ξ] with l hl
    simp only [gE, gDel, Pi.mul_apply]
    rw [g₁_eq ⟨hl.1.le, hl.2.le⟩]
    have e0 : (l : ℂ) = ((Real.exp (-(θ l / 2)) * gT l : ℝ) : ℂ) := by
      rw [exp_neg_half_θ_mul_gT hl]
    rw [e0]
    have e : ((-1 / 2 : ℂ) + t * Complex.I) * θ l =
        ((-(θ l / 2) : ℝ) : ℂ) + ((t * θ l : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [e, Complex.exp_add]
    push_cast
    ring
  rw [h1, cbfc_ofReal, bfc_g₁]
  rfl

/-! ### Continuity on the closed strip and analyticity on the open strip -/

theorem continuous_gE_left (l : ℝ) : Continuous fun z : ℂ => gE z l := by
  unfold gE; fun_prop

/-- `z ↦ E(z) ξ` is continuous on the closed strip. -/
theorem continuousOn_Efam_apply (ξ : K) : ContinuousOn (fun z => Efam M Ω z ξ) strip := by
  intro z₀ hz₀
  have hz₀' : |z₀.re| ≤ 1 / 2 := hz₀
  let G : ℂ → ℝ → ℂ := fun y l => Set.indicator strip (fun y => gE y l) y
  have hGmem : ∀ y ∈ strip, G y = gE y := fun y hy => funext fun l => Set.indicator_of_mem hy _
  have hGnot : ∀ y ∉ strip, G y = fun _ => 0 := fun y hy =>
    funext fun l => Set.indicator_of_notMem hy _
  have hG : ∀ y, CBdd (G y) := fun y => by
    by_cases hy : y ∈ strip
    · rw [hGmem y hy]; exact cbdd_gE hy
    · rw [hGnot y hy]; exact CBdd.const 0
  have hbd : ∀ y l, ‖G y l‖ ≤ 2 := fun y l => by
    by_cases hy : y ∈ strip
    · rw [hGmem y hy]; exact norm_gE_le hy l
    · rw [hGnot y hy, norm_zero]; norm_num
  have hlim : ∀ l, Tendsto (fun y => G y l) (𝓝[strip] z₀) (𝓝 (gE z₀ l)) := fun l => by
    refine (tendsto_nhdsWithin_of_tendsto_nhds ((continuous_gE_left l).tendsto z₀)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    rw [hGmem y hy]
  have := tendsto_cbfc (R M Ω) (R_isSelfAdjoint M Ω) hG (cbdd_gE hz₀') hbd (norm_gE_le hz₀') hlim ξ
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  rw [hGmem y hy]
  rfl

theorem mem_strip_of_close {z₀ y : ℂ} {δ : ℝ} (hz : |z₀.re| ≤ 1 / 2 - δ) (hy : ‖y - z₀‖ ≤ δ / 2)
    (hδ : 0 < δ) : |y.re| ≤ 1 / 2 := by
  have h1 : |y.re - z₀.re| ≤ δ / 2 := by
    calc |y.re - z₀.re| = |(y - z₀).re| := by simp
      _ ≤ ‖y - z₀‖ := Complex.abs_re_le_norm _
      _ ≤ δ / 2 := hy
  calc |y.re| = |(y.re - z₀.re) + z₀.re| := by ring_nf
    _ ≤ |y.re - z₀.re| + |z₀.re| := abs_add_le _ _
    _ ≤ δ / 2 + (1 / 2 - δ) := add_le_add h1 hz
    _ ≤ 1 / 2 := by linarith

/-- `z ↦ E(z) ξ` is complex differentiable on the open strip, with derivative `E'(z) ξ`. -/
theorem hasDerivAt_Efam_apply {z₀ : ℂ} (hz₀ : |z₀.re| < 1 / 2) (ξ : K) :
    HasDerivAt (fun z => Efam M Ω z ξ) (Efam' M Ω z₀ ξ) z₀ := by
  rw [hasDerivAt_iff_tendsto_slope]
  obtain ⟨δ, hδ, hδz⟩ : ∃ δ : ℝ, 0 < δ ∧ |z₀.re| ≤ 1 / 2 - δ :=
    ⟨1 / 2 - |z₀.re|, by linarith, by linarith⟩
  set B := Metric.closedBall z₀ (δ / 2) with hB
  have hmemB : ∀ y, y ∈ B ↔ ‖y - z₀‖ ≤ δ / 2 := fun y => by
    rw [hB, Metric.mem_closedBall, dist_eq_norm]
  let Q : ℂ → ℝ → ℂ := fun y l => Set.indicator B (fun y => (y - z₀)⁻¹ * (gE y l - gE z₀ l)) y
  have hQmem : ∀ y ∈ B, Q y = fun l => (y - z₀)⁻¹ * (gE y l - gE z₀ l) := fun y hy =>
    funext fun l => Set.indicator_of_mem hy _
  have hQnot : ∀ y ∉ B, Q y = fun _ => 0 := fun y hy => funext fun l => Set.indicator_of_notMem hy _
  have hQb : ∀ y l, ‖Q y l‖ ≤ 12 / δ := fun y l => by
    by_cases hy : y ∈ B
    · by_cases hy0 : y = z₀
      · have h0 : Q y l = 0 := by
          rw [hQmem y hy, hy0]; simp
        rw [h0, norm_zero]; positivity
      · rw [hQmem y hy]
        have := norm_gE_quotient_le hδ hδz (h := y - z₀) ((hmemB y).mp hy)
          (sub_ne_zero.mpr hy0) l
        rwa [add_sub_cancel, div_eq_inv_mul] at this
    · rw [hQnot y hy, norm_zero]; positivity
  have hQ : ∀ y, CBdd (Q y) := fun y => by
    by_cases hy : y ∈ B
    · refine ⟨?_, 12 / δ, hQb y⟩
      rw [hQmem y hy]
      exact measurable_const.mul ((measurable_gE y).sub (measurable_gE z₀))
    · rw [hQnot y hy]; exact CBdd.const 0
  have hθE : CBdd fun l => (θ l : ℂ) * gE z₀ l :=
    ⟨(Complex.measurable_ofReal.comp measurable_θ).mul (measurable_gE z₀), 2 / δ,
      norm_θ_mul_gE_le hδ hδz⟩
  have hθb : ∀ l, ‖(θ l : ℂ) * gE z₀ l‖ ≤ 12 / δ := fun l =>
    (norm_θ_mul_gE_le hδ hδz l).trans (by gcongr; norm_num)
  have hBev : ∀ᶠ y in 𝓝[≠] z₀, y ∈ B :=
    eventually_nhdsWithin_of_eventually_nhds (Metric.closedBall_mem_nhds z₀ (by positivity))
  have hlim : ∀ l, Tendsto (fun y => Q y l) (𝓝[≠] z₀) (𝓝 ((θ l : ℂ) * gE z₀ l)) := fun l => by
    have hd : HasDerivAt (fun y : ℂ => gE y l) ((θ l : ℂ) * gE z₀ l) z₀ := by
      have h1 : HasDerivAt (fun y : ℂ => Complex.exp (y * θ l))
          (Complex.exp (z₀ * θ l) * θ l) z₀ :=
        (Complex.hasDerivAt_exp _).comp z₀ (hasDerivAt_mul_const _)
      exact (h1.mul_const (gT l : ℂ)).congr_deriv (by simp only [gE]; ring)
    refine (hasDerivAt_iff_tendsto_slope.mp hd).congr' ?_
    filter_upwards [hBev] with y hy
    rw [show Q y l = (y - z₀)⁻¹ * (gE y l - gE z₀ l) from Set.indicator_of_mem hy _,
      slope_def_field, div_eq_inv_mul]
  have := tendsto_cbfc (R M Ω) (R_isSelfAdjoint M Ω) hQ hθE hQb hθb hlim ξ
  refine this.congr' ?_
  filter_upwards [hBev] with y hy
  have hys : |y.re| ≤ 1 / 2 := mem_strip_of_close hδz ((hmemB y).mp hy) hδ
  have hz₀s : |z₀.re| ≤ 1 / 2 := by linarith [abs_nonneg z₀.re]
  have e : (fun l => (y - z₀)⁻¹ * (gE y l - gE z₀ l)) =
      fun t => (y - z₀)⁻¹ * (gE y - gE z₀) t := rfl
  rw [hQmem y hy, slope, vsub_eq_sub, e, cbfc_const_mul' _ _ _ ((cbdd_gE hys).sub (cbdd_gE hz₀s)),
    cbfc_sub _ _ (cbdd_gE hys) (cbdd_gE hz₀s)]
  rfl

end Modular

end VN

end CommutingRepetition

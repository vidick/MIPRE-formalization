/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/Modular/Tomita.lean
-/
/-
# Tomita's theorem (density stage E4.3d–f)

Rieffel–van Daele §4, Lemmas 4.7–4.9 and Theorem 4.2, for a von Neumann algebra
`M` with cyclic separating vector `Ω`:

* **Lemma 4.7**: with `x′ ∈ M′` self-adjoint, `|φ| < π`, `λ = e^{iφ/2}` and `x ∈ M`
  as in Lemma 4.5, `x = ∫ w_φ(t) Δ^{it} (J x′ J) Δ^{-it} dt` (a weak integral `W`).
  Proof: Cauchy's formula on the strip (`StripCauchy`) for
  `f(z) = ⟪η, E(z) x E(−z) ξ⟫` (`AnalyticFamily`) and Lemma 4.5 give
  `T x T = T W T`; `T` is injective with dense range.
* **Lemma 4.8**: `Δ^{it} (J x′ J) Δ^{-it} ∈ M` for `x′ ∈ M′`: every `y′ ∈ M′`
  commutes with the integrals above for all `|φ| < π`, so the bounded continuous
  function `t ↦ ⟪η, [y′, Δ^{it} J x′ J Δ^{-it}] ξ⟫` has vanishing Laplace
  transform on `(−π, π)` and is zero (`LaplaceUniqueness`).
* **Lemma 4.9**: `J M J ⊆ M′`, by RvD's direct argument from `JΩ = Ω` and the
  reality of `⟪J xΩ, yΩ⟫` for `x, y ∈ M_s`.
* **Theorem 4.2**: `J M J = M′` and `Δ^{it} M Δ^{-it} = M`; the modular
  automorphism group `σ_t(x) = Δ^{it} x Δ^{-it}` and its basic properties.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.Modular.LinearRN
import MIPRE.Background.Repetition.CommutingRepetition.VN.Modular.StripCauchy
import MIPRE.Background.Repetition.CommutingRepetition.VN.Modular.AnalyticFamily
import MIPRE.Background.Repetition.CommutingRepetition.VN.Modular.LaplaceUniqueness

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace VN

namespace Modular

open scoped InnerProductSpace ComplexConjugate Real
open Filter Topology BorelCalc ClosedSubmodule MeasureTheory StripCauchy

set_option linter.unusedSectionVars false

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ## Joint continuity of `x ↦ U x (ζ x)` for uniformly bounded strongly continuous `U` -/

theorem continuousWithinAt_apply_of_bdd {X : Type*} [TopologicalSpace X] {U : X → K →L[ℂ] K}
    {ζ : X → K} {s : Set X} {x₀ : X} {C : ℝ} (hU : ∀ x ∈ s, ‖U x‖ ≤ C)
    (hUc : ∀ v, ContinuousWithinAt (fun x => U x v) s x₀) (hζ : ContinuousWithinAt ζ s x₀)
    (hx₀ : x₀ ∈ s) : ContinuousWithinAt (fun x => U x (ζ x)) s x₀ := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hU x₀ hx₀)
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have h1 : Tendsto (fun x => C * ‖ζ x - ζ x₀‖) (𝓝[s] x₀) (𝓝 0) := by
    have := (tendsto_iff_norm_sub_tendsto_zero.mp hζ).const_mul C
    simpa using this
  have h2 : Tendsto (fun x => ‖U x (ζ x₀) - U x₀ (ζ x₀)‖) (𝓝[s] x₀) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp (hUc (ζ x₀))
  have h3 := h1.add h2
  rw [add_zero] at h3
  refine squeeze_zero_norm' ?_ h3
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [norm_norm]
  calc ‖U x (ζ x) - U x₀ (ζ x₀)‖
      = ‖U x (ζ x - ζ x₀) + (U x (ζ x₀) - U x₀ (ζ x₀))‖ := by rw [map_sub]; congr 1; abel
    _ ≤ ‖U x (ζ x - ζ x₀)‖ + ‖U x (ζ x₀) - U x₀ (ζ x₀)‖ := norm_add_le _ _
    _ ≤ C * ‖ζ x - ζ x₀‖ + ‖U x (ζ x₀) - U x₀ (ζ x₀)‖ := by
        gcongr
        exact ((U x).le_opNorm _).trans (by gcongr; exact hU x hx)

theorem continuousOn_apply_of_bdd {X : Type*} [TopologicalSpace X] {U : X → K →L[ℂ] K}
    {ζ : X → K} {s : Set X} {C : ℝ} (hU : ∀ x ∈ s, ‖U x‖ ≤ C)
    (hUc : ∀ v, ContinuousOn (fun x => U x v) s) (hζ : ContinuousOn ζ s) :
    ContinuousOn (fun x => U x (ζ x)) s := fun x₀ hx₀ =>
  continuousWithinAt_apply_of_bdd hU (fun v => hUc v x₀ hx₀) (hζ x₀ hx₀) hx₀

theorem continuous_apply_of_bdd {X : Type*} [TopologicalSpace X] {U : X → K →L[ℂ] K}
    {ζ : X → K} {C : ℝ} (hU : ∀ x, ‖U x‖ ≤ C) (hUc : ∀ v, Continuous (fun x => U x v))
    (hζ : Continuous ζ) : Continuous (fun x => U x (ζ x)) := by
  rw [← continuousOn_univ]
  exact continuousOn_apply_of_bdd (fun x _ => hU x) (fun v => (hUc v).continuousOn)
    hζ.continuousOn

variable (M : VonNeumannAlgebra K) (Ω : K)

theorem continuous_Δit_comp {ζ : ℝ → K} (hζ : Continuous ζ) :
    Continuous fun t => Δit M Ω t (ζ t) :=
  continuous_apply_of_bdd (norm_Δit_le M Ω) (continuous_Δit_apply M Ω) hζ

/-! ## The weak integral `W = ∫ w_φ(t) Δ^{it} B Δ^{-it} dt` -/

theorem integrable_w {φ : ℝ} (hφ : |φ| < π) : Integrable (w φ) := by
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (max 1 (2 / (π - |φ|) ^ 2)))
    (continuous_w φ).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  rw [Real.norm_of_nonneg (w_pos φ t).le]
  exact w_le_inv_one_add_sq hφ t

/-- Integrability of `t ↦ w φ t • v t` for bounded continuous `v : ℝ → K`. -/
theorem integrable_w_smul {φ : ℝ} (hφ : |φ| < π) {v : ℝ → K} (hv : Continuous v) {C : ℝ}
    (hC : ∀ t, ‖v t‖ ≤ C) : Integrable fun t => (w φ t : ℂ) • v t := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine Integrable.mono' ((integrable_w hφ).const_mul C)
    ((Complex.continuous_ofReal.comp (continuous_w φ)).smul hv).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (w_pos φ t).le, mul_comm]
  exact mul_le_mul_of_nonneg_right (hC t) (w_pos φ t).le

variable (B : K →L[ℂ] K) (φ : ℝ)

/-- The integrand `t ↦ w φ t • Δ^{it} B Δ^{-it} ξ`. -/
noncomputable def Wint (ξ : K) (t : ℝ) : K := (w φ t : ℂ) • Δit M Ω t (B (Δit M Ω (-t) ξ))

theorem continuous_Wint (ξ : K) : Continuous (Wint M Ω B φ ξ) := by
  unfold Wint
  refine (Complex.continuous_ofReal.comp (continuous_w φ)).smul ?_
  refine continuous_Δit_comp M Ω (B.continuous.comp ?_)
  exact (continuous_Δit_comp M Ω continuous_const).comp continuous_neg

theorem norm_conj_apply_le (ξ : K) (t : ℝ) :
    ‖Δit M Ω t (B (Δit M Ω (-t) ξ))‖ ≤ ‖B‖ * ‖ξ‖ := by
  rw [norm_Δit_apply]
  calc ‖B (Δit M Ω (-t) ξ)‖ ≤ ‖B‖ * ‖Δit M Ω (-t) ξ‖ := B.le_opNorm _
    _ = ‖B‖ * ‖ξ‖ := by rw [norm_Δit_apply]

theorem integrable_Wint {φ : ℝ} (hφ : |φ| < π) (ξ : K) : Integrable (Wint M Ω B φ ξ) :=
  integrable_w_smul hφ (continuous_Δit_comp M Ω (B.continuous.comp
    ((continuous_Δit_comp M Ω continuous_const).comp continuous_neg))) (norm_conj_apply_le M Ω B ξ)

/-- The operator `W`. -/
noncomputable def Wop (hφ : |φ| < π) : K →L[ℂ] K :=
  LinearMap.mkContinuous
    { toFun := fun ξ => ∫ t, Wint M Ω B φ ξ t
      map_add' := fun ξ η => by
        rw [← integral_add (integrable_Wint M Ω B hφ ξ) (integrable_Wint M Ω B hφ η)]
        congr 1
        funext t
        simp only [Wint, map_add, smul_add]
      map_smul' := fun c ξ => by
        rw [RingHom.id_apply, ← integral_smul]
        congr 1
        funext t
        simp only [Wint, map_smul, smul_comm c] }
    (‖B‖ * ∫ t, w φ t) fun ξ => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      calc ‖∫ t, Wint M Ω B φ ξ t‖ ≤ ∫ t, w φ t * (‖B‖ * ‖ξ‖) :=
            norm_integral_le_of_norm_le ((integrable_w hφ).mul_const _)
              (Eventually.of_forall fun t => by
                rw [Wint, norm_smul, Complex.norm_real, Real.norm_of_nonneg (w_pos φ t).le]
                exact mul_le_mul_of_nonneg_left (norm_conj_apply_le M Ω B ξ t) (w_pos φ t).le)
        _ = ‖B‖ * (∫ t, w φ t) * ‖ξ‖ := by rw [integral_mul_const]; ring

theorem Wop_apply (hφ : |φ| < π) (ξ : K) :
    Wop M Ω B φ hφ ξ = ∫ t, (w φ t : ℂ) • Δit M Ω t (B (Δit M Ω (-t) ξ)) := rfl

theorem inner_Wop (hφ : |φ| < π) (η ξ : K) :
    ⟪η, Wop M Ω B φ hφ ξ⟫_ℂ = ∫ t, (w φ t : ℂ) * ⟪η, Δit M Ω t (B (Δit M Ω (-t) ξ))⟫_ℂ := by
  show ⟪η, ∫ t, Wint M Ω B φ ξ t⟫_ℂ = _
  rw [← integral_inner (integrable_Wint M Ω B hφ ξ)]
  congr 1
  funext t
  simp only [Wint, inner_smul_right]

theorem clm_Wop (hφ : |φ| < π) (S : K →L[ℂ] K) (ξ : K) :
    S (Wop M Ω B φ hφ ξ) = ∫ t, (w φ t : ℂ) • S (Δit M Ω t (B (Δit M Ω (-t) ξ))) := by
  show S (∫ t, Wint M Ω B φ ξ t) = _
  rw [← S.integral_comp_comm (integrable_Wint M Ω B hφ ξ)]
  congr 1
  funext t
  simp only [Wint, map_smul]

/-! ## The bilinear form `β(u, v) = ⟪J u, v⟫` -/

/-- `β(u, v) = ⟪J u, v⟫`, a continuous `ℂ`-bilinear form. -/
noncomputable def βop : K →L[ℂ] K →L[ℂ] ℂ :=
  LinearMap.mkContinuous₂
    { toFun := fun u =>
        { toFun := fun v => ⟪Jm M Ω u, v⟫_ℂ
          map_add' := fun v w => inner_add_right _ _ _
          map_smul' := fun c v => by simp only [inner_smul_right, RingHom.id_apply, smul_eq_mul] }
      map_add' := fun u w => by ext v; simp only [map_add, inner_add_left, LinearMap.coe_mk,
        AddHom.coe_mk, LinearMap.add_apply]
      map_smul' := fun c u => by
        ext v
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, smul_eq_mul, Jm_smul,
          inner_smul_left, RingHom.id_apply, Complex.conj_conj] }
    ‖Jm M Ω‖ fun u v => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      calc ‖⟪Jm M Ω u, v⟫_ℂ‖ ≤ ‖Jm M Ω u‖ * ‖v‖ := norm_inner_le_norm _ _
        _ ≤ ‖Jm M Ω‖ * ‖u‖ * ‖v‖ := by gcongr; exact (Jm M Ω).le_opNorm u

theorem βop_apply (u v : K) : βop M Ω u v = ⟪Jm M Ω u, v⟫_ℂ := rfl

variable (hs : IsSeparating (M : Set (K →L[ℂ] K)) Ω) (hc : IsCyclic (M : Set (K →L[ℂ] K)) Ω)

include hs hc in
theorem inner_eq_βop (a v : K) : ⟪a, v⟫_ℂ = βop M Ω (Jm M Ω a) v := by
  rw [βop_apply, Jm_Jm M Ω hs hc]

/-! ## RvD Lemma 4.7 -/

section Lemma47

variable {x' : K →L[ℂ] K} (hx' : x' ∈ M.commutant) (hsa' : IsSelfAdjoint x')
  {φ : ℝ} (hφ : |φ| < π)

theorem re_exp_half_pos (hφ : |φ| < π) : 0 < (Complex.exp (Complex.I * φ / 2)).re := by
  rw [Complex.exp_re]
  have h1 : (Complex.I * φ / 2 : ℂ).re = 0 := by simp
  have h2 : (Complex.I * φ / 2 : ℂ).im = φ / 2 := by simp
  rw [h1, h2, Real.exp_zero, one_mul]
  apply Real.cos_pos_of_mem_Ioo
  rw [abs_lt] at hφ
  constructor <;> linarith [hφ.1, hφ.2]

theorem conj_exp_half (φ : ℝ) :
    conj (Complex.exp (Complex.I * φ / 2)) = Complex.exp (-(Complex.I * φ / 2)) := by
  rw [← Complex.exp_conj]
  congr 1
  rw [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  ring

/-- `Δ^{it}` commutes with `2 − R`. -/
theorem Δit_commute_two_sub_R (t : ℝ) : Commute (Δit M Ω t) (2 - R M Ω) := by
  refine Commute.sub_right ?_ (Δit_commute_R M Ω t)
  rw [show (2 : K →L[ℂ] K) = 1 + 1 from one_add_one_eq_two.symm]
  exact (Commute.one_right _).add_right (Commute.one_right _)

/-- The function `f(z) = ⟪η, E(z) x E(−z) ξ⟫`. -/
noncomputable def fz (x : K →L[ℂ] K) (η ξ : K) (z : ℂ) : ℂ := ⟪η, Efam M Ω z (x (Efam M Ω (-z) ξ))⟫_ℂ

theorem neg_mem_strip {z : ℂ} (hz : z ∈ strip) : -z ∈ strip := by
  show |(-z).re| ≤ 1 / 2
  rw [Complex.neg_re, abs_neg]; exact hz

theorem continuousOn_fz (x : K →L[ℂ] K) (η ξ : K) : ContinuousOn (fz M Ω x η ξ) strip := by
  have h1 : ContinuousOn (fun z => Efam M Ω (-z) ξ) strip :=
    (continuousOn_Efam_apply M Ω ξ).comp continuousOn_neg fun z hz => neg_mem_strip hz
  have h2 : ContinuousOn (fun z => x (Efam M Ω (-z) ξ)) strip := x.continuous.comp_continuousOn h1
  have h3 : ContinuousOn (fun z => Efam M Ω z (x (Efam M Ω (-z) ξ))) strip :=
    continuousOn_apply_of_bdd (fun z hz => norm_Efam_le M Ω hz) (continuousOn_Efam_apply M Ω) h2
  exact (continuous_const.inner continuous_id).comp_continuousOn h3

theorem norm_fz_le (x : K →L[ℂ] K) (η ξ : K) {z : ℂ} (hz : z ∈ strip) :
    ‖fz M Ω x η ξ z‖ ≤ ‖η‖ * (2 * (‖x‖ * (2 * ‖ξ‖))) := by
  unfold fz
  calc ‖⟪η, Efam M Ω z (x (Efam M Ω (-z) ξ))⟫_ℂ‖ ≤ ‖η‖ * ‖Efam M Ω z (x (Efam M Ω (-z) ξ))‖ :=
        norm_inner_le_norm _ _
    _ ≤ ‖η‖ * (2 * ‖x (Efam M Ω (-z) ξ)‖) := by gcongr; exact norm_Efam_apply_le M Ω hz _
    _ ≤ ‖η‖ * (2 * (‖x‖ * ‖Efam M Ω (-z) ξ‖)) := by gcongr; exact x.le_opNorm _
    _ ≤ ‖η‖ * (2 * (‖x‖ * (2 * ‖ξ‖))) := by
        gcongr; exact norm_Efam_apply_le M Ω (neg_mem_strip hz) ξ

include hs hc in
/-- On the strip, `f(z) = β(E(−z) Jη, x E(−z) ξ)`. -/
theorem fz_eq_βop (x : K →L[ℂ] K) (η ξ : K) {z : ℂ} (hz : z ∈ strip) :
    fz M Ω x η ξ z = βop M Ω (Efam M Ω (-z) (Jm M Ω η)) (x (Efam M Ω (-z) ξ)) := by
  have hz' : |z.re| ≤ 1 / 2 := hz
  have hzc : |(conj z).re| ≤ 1 / 2 := by rw [Complex.conj_re]; exact hz'
  unfold fz
  rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
    star_Efam M Ω hz', inner_eq_βop M Ω hs hc, Jm_Efam M Ω hs hc hzc, Complex.conj_conj]

include hs hc in
theorem differentiableOn_fz (x : K →L[ℂ] K) (η ξ : K) : DifferentiableOn ℂ (fz M Ω x η ξ) ostrip := by
  have hd : ∀ z₀ ∈ ostrip, HasDerivAt
      (fun z => βop M Ω (Efam M Ω (-z) (Jm M Ω η)) (x (Efam M Ω (-z) ξ)))
      (βop M Ω ((-1 : ℂ) • Efam' M Ω (-z₀) (Jm M Ω η)) (x (Efam M Ω (-z₀) ξ)) +
        βop M Ω (Efam M Ω (-z₀) (Jm M Ω η)) (x ((-1 : ℂ) • Efam' M Ω (-z₀) ξ))) z₀ := by
    intro z₀ hz₀
    have hz₀' : |(-z₀).re| < 1 / 2 := by rw [Complex.neg_re, abs_neg]; exact hz₀
    have hneg : HasDerivAt (fun z : ℂ => -z) (-1 : ℂ) z₀ := hasDerivAt_neg z₀
    have h1 : HasDerivAt (fun z => Efam M Ω (-z) (Jm M Ω η)) ((-1 : ℂ) • Efam' M Ω (-z₀) (Jm M Ω η)) z₀ :=
      (hasDerivAt_Efam_apply M Ω hz₀' (Jm M Ω η)).scomp z₀ hneg
    have h2 : HasDerivAt (fun z => Efam M Ω (-z) ξ) ((-1 : ℂ) • Efam' M Ω (-z₀) ξ) z₀ :=
      (hasDerivAt_Efam_apply M Ω hz₀' ξ).scomp z₀ hneg
    have h3 : HasDerivAt (fun z => x (Efam M Ω (-z) ξ)) (x ((-1 : ℂ) • Efam' M Ω (-z₀) ξ)) z₀ :=
      x.hasFDerivAt.comp_hasDerivAt z₀ h2
    have h4 : HasDerivAt (fun z => βop M Ω (Efam M Ω (-z) (Jm M Ω η)))
        (βop M Ω ((-1 : ℂ) • Efam' M Ω (-z₀) (Jm M Ω η))) z₀ :=
      (βop M Ω).hasFDerivAt.comp_hasDerivAt z₀ h1
    exact h4.clm_apply h3
  exact DifferentiableOn.congr (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt)
    fun z hz => fz_eq_βop M Ω hs hc x η ξ (ostrip_subset_strip hz)

theorem fz_zero (x : K →L[ℂ] K) (η ξ : K) : fz M Ω x η ξ 0 = ⟪η, Tm M Ω (x (Tm M Ω ξ))⟫_ℂ := by
  unfold fz
  rw [neg_zero, Efam_zero]

include hs hc in
theorem fz_half_add (x : K →L[ℂ] K) (η ξ : K) (t : ℝ) :
    fz M Ω x η ξ (1 / 2 + t * Complex.I) =
      ⟪η, (2 - R M Ω) (Δit M Ω t (x (R M Ω (Δit M Ω (-t) ξ))))⟫_ℂ := by
  unfold fz
  have e : -(1 / 2 + t * Complex.I : ℂ) = -1 / 2 + (-t : ℝ) * Complex.I := by push_cast; ring
  rw [e, Efam_half_add M Ω hs hc, Efam_neg_half_add M Ω hs hc, mul_apply_eq_comp, mul_apply_eq_comp]

include hs hc in
theorem fz_neg_half_add (x : K →L[ℂ] K) (η ξ : K) (t : ℝ) :
    fz M Ω x η ξ (-1 / 2 + t * Complex.I) =
      ⟪η, R M Ω (Δit M Ω t (x ((2 - R M Ω) (Δit M Ω (-t) ξ))))⟫_ℂ := by
  unfold fz
  have e : -(-1 / 2 + t * Complex.I : ℂ) = 1 / 2 + (-t : ℝ) * Complex.I := by push_cast; ring
  rw [e, Efam_half_add M Ω hs hc, Efam_neg_half_add M Ω hs hc, mul_apply_eq_comp, mul_apply_eq_comp]

/-- The operator identity behind `λ f(1/2+it) + λ̄ f(-1/2+it) = ⟪η, T Δ^{it} B Δ^{-it} T ξ⟫`. -/
theorem sandwich_eq (x B : K →L[ℂ] K) (l : ℂ)
    (hB : Tm M Ω * B * Tm M Ω = l • ((2 - R M Ω) * x * R M Ω) + conj l • (R M Ω * x * (2 - R M Ω)))
    (t : ℝ) :
    l • ((2 - R M Ω) * Δit M Ω t * x * (R M Ω * Δit M Ω (-t))) +
      conj l • (R M Ω * Δit M Ω t * x * ((2 - R M Ω) * Δit M Ω (-t))) =
      Tm M Ω * (Δit M Ω t * B * Δit M Ω (-t)) * Tm M Ω := by
  have hR := (Δit_commute_R M Ω t).eq
  have h2R := (Δit_commute_two_sub_R M Ω t).eq
  have hT := (Δit_commute_Tm M Ω t).eq
  have hT' := (Δit_commute_Tm M Ω (-t)).eq
  calc l • ((2 - R M Ω) * Δit M Ω t * x * (R M Ω * Δit M Ω (-t))) +
        conj l • (R M Ω * Δit M Ω t * x * ((2 - R M Ω) * Δit M Ω (-t)))
      = Δit M Ω t * (l • ((2 - R M Ω) * x * R M Ω) + conj l • (R M Ω * x * (2 - R M Ω))) *
          Δit M Ω (-t) := by
        rw [mul_add, add_mul, mul_smul_comm, mul_smul_comm, smul_mul_assoc, smul_mul_assoc]
        congr 2
        · simp only [mul_assoc]
          rw [← mul_assoc (Δit M Ω t) (2 - R M Ω), h2R, mul_assoc]
        · simp only [mul_assoc]
          rw [← mul_assoc (Δit M Ω t) (R M Ω), hR, mul_assoc]
    _ = Δit M Ω t * (Tm M Ω * B * Tm M Ω) * Δit M Ω (-t) := by rw [hB]
    _ = Tm M Ω * (Δit M Ω t * B * Δit M Ω (-t)) * Tm M Ω := by
        simp only [mul_assoc]
        rw [← mul_assoc (Δit M Ω t) (Tm M Ω), hT, hT', mul_assoc]

include hs hc hx' hsa' hφ in
/-- **RvD Lemma 4.7**: `T x T = T W T` for `x` as in Lemma 4.5 (with `λ = e^{iφ/2}`). -/
theorem Tm_mul_eq_Tm_Wop {x : K →L[ℂ] K}
    (hB : Tm M Ω * conjJm M Ω x' * Tm M Ω =
      Complex.exp (Complex.I * φ / 2) • ((2 - R M Ω) * x * R M Ω) +
        conj (Complex.exp (Complex.I * φ / 2)) • (R M Ω * x * (2 - R M Ω))) :
    Tm M Ω * x * Tm M Ω = Tm M Ω * Wop M Ω (conjJm M Ω x') φ hφ * Tm M Ω := by
  set l := Complex.exp (Complex.I * φ / 2) with hl
  ext ξ
  refine ext_inner_left ℂ fun η => ?_
  have hcauchy := strip_cauchy (fz M Ω x η ξ) φ (continuousOn_fz M Ω x η ξ)
    (differentiableOn_fz M Ω hs hc x η ξ) (fun z hz => norm_fz_le M Ω x η ξ hz) hφ
  rw [fz_zero] at hcauchy
  have hsand := sandwich_eq M Ω x (conjJm M Ω x') l hB
  have hint : Integrable fun t =>
      (w φ t : ℂ) • Tm M Ω (Δit M Ω t (conjJm M Ω x' (Δit M Ω (-t) (Tm M Ω ξ)))) := by
    refine ((Tm M Ω).integrable_comp (integrable_Wint M Ω (conjJm M Ω x') hφ (Tm M Ω ξ))).congr
      (Eventually.of_forall fun t => ?_)
    simp only [Wint, map_smul]
  rw [mul_apply_eq_comp, mul_apply_eq_comp, hcauchy, mul_apply_eq_comp, mul_apply_eq_comp,
    clm_Wop, ← integral_inner hint]
  congr 1
  funext t
  rw [fz_half_add M Ω hs hc, fz_neg_half_add M Ω hs hc, inner_smul_right, ← conj_exp_half φ, ← hl]
  have := congrArg (fun S : K →L[ℂ] K => ⟪η, S ξ⟫_ℂ) (hsand t)
  simp only [_root_.add_apply, _root_.smul_apply, inner_add_right, inner_smul_right,
    mul_apply_eq_comp] at this
  rw [this]

include hs hc in
/-- **RvD Lemma 4.7** (operator form): `x = ∫ w_φ(t) Δ^{it} (J x′ J) Δ^{-it} dt`. -/
theorem eq_Wop_of_Tm_mul_eq {x : K →L[ℂ] K} {S : K →L[ℂ] K}
    (h : Tm M Ω * x * Tm M Ω = Tm M Ω * S * Tm M Ω) : x = S := by
  ext ζ
  refine congrFun (ext_of_Tm M Ω hs hc x.continuous S.continuous fun ξ => ?_) ζ
  have := congrArg (fun U : K →L[ℂ] K => U ξ) h
  simp only [mul_apply_eq_comp] at this
  have h2 : Tm M Ω (x (Tm M Ω ξ) - S (Tm M Ω ξ)) = 0 := by rw [map_sub, this, sub_self]
  exact sub_eq_zero.mp ((Tm_eq_zero_iff M Ω hs hc).mp h2)

include hs hc hx' hsa' hφ in
/-- For self-adjoint `x′ ∈ M′` and `|φ| < π`, the weak integral `W` lies in `M`. -/
theorem Wop_conjJm_mem : Wop M Ω (conjJm M Ω x') φ hφ ∈ M := by
  obtain ⟨x, hxM, -, hB⟩ := exists_operator_eq M Ω hs hc hx' hsa' (re_exp_half_pos hφ)
  have := Tm_mul_eq_Tm_Wop M Ω hs hc hx' hsa' hφ hB
  rw [← eq_Wop_of_Tm_mul_eq M Ω hs hc this]
  exact hxM

end Lemma47


/-! ## RvD Lemma 4.8: `Δ^{it} (J x′ J) Δ^{-it} ∈ M` -/

section Lemma48

variable (B : K →L[ℂ] K) {φ : ℝ}

theorem integrable_clm_Wint (hφ : |φ| < π) (S : K →L[ℂ] K) (ξ : K) :
    Integrable fun t => (w φ t : ℂ) • S (Δit M Ω t (B (Δit M Ω (-t) ξ))) := by
  refine (S.integrable_comp (integrable_Wint M Ω B hφ ξ)).congr (Eventually.of_forall fun t => ?_)
  simp only [Wint, map_smul]

theorem integrable_w_mul_inner (hφ : |φ| < π) (S : K →L[ℂ] K) (η ξ : K) :
    Integrable fun t => (w φ t : ℂ) * ⟪η, S (Δit M Ω t (B (Δit M Ω (-t) ξ)))⟫_ℂ := by
  refine ((integrable_clm_Wint M Ω B hφ S ξ).const_inner η).congr (Eventually.of_forall fun t => ?_)
  simp only [inner_smul_right]

theorem inner_clm_Wop (hφ : |φ| < π) (S : K →L[ℂ] K) (η ξ : K) :
    ⟪η, S (Wop M Ω B φ hφ ξ)⟫_ℂ =
      ∫ t, (w φ t : ℂ) * ⟪η, S (Δit M Ω t (B (Δit M Ω (-t) ξ)))⟫_ℂ := by
  rw [clm_Wop, ← integral_inner (integrable_clm_Wint M Ω B hφ S ξ)]
  congr 1
  funext t
  rw [inner_smul_right]

/-- Every `x ∈ N` is `a + i b` with `a, b ∈ N` self-adjoint. -/
theorem exists_sa_decomp (N : VonNeumannAlgebra K) {x : K →L[ℂ] K} (hx : x ∈ N) :
    ∃ a b : K →L[ℂ] K, a ∈ N ∧ b ∈ N ∧ IsSelfAdjoint a ∧ IsSelfAdjoint b ∧
      x = a + Complex.I • b :=
  ⟨(1 / 2 : ℂ) • (x + star x), (-(1 / 2 : ℂ) * Complex.I) • (x - star x),
    VN.smul_mem_vn N _ (add_mem hx (star_mem hx)), VN.smul_mem_vn N _ (sub_mem hx (star_mem hx)),
    isSelfAdjoint_half_add_star x, isSelfAdjoint_half_I_sub_star x, eq_sa_add_I_smul_sa x⟩

theorem conjJm_add (G H : K →L[ℂ] K) : conjJm M Ω (G + H) = conjJm M Ω G + conjJm M Ω H := by
  ext ξ; simp only [conjJm_apply, _root_.add_apply, map_add]

theorem conjJm_smul (c : ℂ) (G : K →L[ℂ] K) : conjJm M Ω (c • G) = conj c • conjJm M Ω G := by
  ext ξ; simp only [conjJm_apply, _root_.smul_apply, Jm_smul]

theorem conjJm_zero : conjJm M Ω (0 : K →L[ℂ] K) = 0 := by
  ext ξ; simp only [conjJm_apply, _root_.zero_apply, map_zero]

include hs hc in
theorem conjJm_mul (G H : K →L[ℂ] K) : conjJm M Ω (G * H) = conjJm M Ω G * conjJm M Ω H := by
  ext ξ; simp only [conjJm_apply, mul_apply_eq_comp, Jm_Jm M Ω hs hc]

include hs hc in
theorem conjJm_conjJm (G : K →L[ℂ] K) : conjJm M Ω (conjJm M Ω G) = G := by
  ext ξ; simp only [conjJm_apply, Jm_Jm M Ω hs hc]

include hs hc in
theorem conjJm_one : conjJm M Ω (1 : K →L[ℂ] K) = 1 := by
  ext ξ; simp only [conjJm_apply, one_apply_eq_self, Jm_Jm M Ω hs hc]

include hs hc in
theorem star_conjJm (G : K →L[ℂ] K) : star (conjJm M Ω G) = conjJm M Ω (star G) := by
  rw [ContinuousLinearMap.star_eq_adjoint (conjJm M Ω G)]
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro ξ η
  rw [conjJm_apply, conjJm_apply, inner_Jm_left M Ω hs hc, ContinuousLinearMap.star_eq_adjoint G,
    ContinuousLinearMap.adjoint_inner_right, ← Jm_Jm M Ω hs hc (G (Jm M Ω η)),
    inner_Jm_left M Ω hs hc, Jm_Jm M Ω hs hc, Jm_Jm M Ω hs hc]

include hs hc in
/-- **RvD Lemma 4.8** (self-adjoint case): `Δ^{it} (J x′ J) Δ^{-it} ∈ M` for self-adjoint
`x′ ∈ M′`, by Laplace-transform uniqueness applied to the commutator with `y′ ∈ M′`. -/
theorem sa_Δit_conjJm_mem {x' : K →L[ℂ] K} (hx' : x' ∈ M.commutant) (hsa' : IsSelfAdjoint x')
    (t : ℝ) : Δit M Ω t * conjJm M Ω x' * Δit M Ω (-t) ∈ M := by
  set B := conjJm M Ω x' with hBdef
  suffices h : Δit M Ω t * B * Δit M Ω (-t) ∈ M.commutant.commutant by
    rwa [VonNeumannAlgebra.commutant_commutant] at h
  rw [VonNeumannAlgebra.mem_commutant_iff]
  intro y' hy'
  ext ξ
  refine ext_inner_left ℂ fun η => ?_
  simp only [mul_apply_eq_comp]
  have hcont : ∀ ζ : K, Continuous fun s => Δit M Ω s (B (Δit M Ω (-s) ζ)) := fun ζ =>
    continuous_Δit_comp M Ω (B.continuous.comp
      ((continuous_Δit_comp M Ω continuous_const).comp continuous_neg))
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℂ, g = fun s => ⟪η, y' (Δit M Ω s (B (Δit M Ω (-s) ξ)))⟫_ℂ -
      ⟪η, Δit M Ω s (B (Δit M Ω (-s) (y' ξ)))⟫_ℂ := ⟨_, rfl⟩
  have hgc : Continuous g := by
    rw [hg]
    exact (continuous_const.inner (y'.continuous.comp (hcont ξ))).sub
      (continuous_const.inner (hcont (y' ξ)))
  have hgC : ∀ s, ‖g s‖ ≤ ‖η‖ * (‖y'‖ * (‖B‖ * ‖ξ‖)) + ‖η‖ * (‖B‖ * (‖y'‖ * ‖ξ‖)) := by
    intro s
    rw [hg]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · calc ‖⟪η, y' (Δit M Ω s (B (Δit M Ω (-s) ξ)))⟫_ℂ‖
          ≤ ‖η‖ * ‖y' (Δit M Ω s (B (Δit M Ω (-s) ξ)))‖ := norm_inner_le_norm _ _
        _ ≤ ‖η‖ * (‖y'‖ * ‖Δit M Ω s (B (Δit M Ω (-s) ξ))‖) := by
            gcongr; exact y'.le_opNorm _
        _ ≤ ‖η‖ * (‖y'‖ * (‖B‖ * ‖ξ‖)) := by gcongr; exact norm_conj_apply_le M Ω B ξ s
    · calc ‖⟪η, Δit M Ω s (B (Δit M Ω (-s) (y' ξ)))⟫_ℂ‖
          ≤ ‖η‖ * ‖Δit M Ω s (B (Δit M Ω (-s) (y' ξ)))‖ := norm_inner_le_norm _ _
        _ ≤ ‖η‖ * (‖B‖ * ‖y' ξ‖) := by gcongr; exact norm_conj_apply_le M Ω B (y' ξ) s
        _ ≤ ‖η‖ * (‖B‖ * (‖y'‖ * ‖ξ‖)) := by gcongr; exact y'.le_opNorm _
  have hint : ∀ φ : ℝ, |φ| < π → ∫ s, (w φ s : ℂ) * g s = 0 := by
    intro φ hφ
    have hW := Wop_conjJm_mem M Ω hs hc hx' hsa' hφ
    have hcomm : y' * Wop M Ω B φ hφ = Wop M Ω B φ hφ * y' :=
      ((VonNeumannAlgebra.mem_commutant_iff.mp hy') _ hW).symm
    have h1 : ⟪η, y' (Wop M Ω B φ hφ ξ)⟫_ℂ = ⟪η, Wop M Ω B φ hφ (y' ξ)⟫_ℂ := by
      rw [← mul_apply_eq_comp, hcomm, mul_apply_eq_comp]
    rw [inner_clm_Wop, inner_Wop] at h1
    calc ∫ s, (w φ s : ℂ) * g s
        = ∫ s, ((w φ s : ℂ) * ⟪η, y' (Δit M Ω s (B (Δit M Ω (-s) ξ)))⟫_ℂ -
            (w φ s : ℂ) * ⟪η, Δit M Ω s (B (Δit M Ω (-s) (y' ξ)))⟫_ℂ) := by
          congr 1; funext s; rw [hg]; ring
      _ = 0 := by
          have hi2 : Integrable fun s =>
              (w φ s : ℂ) * ⟪η, Δit M Ω s (B (Δit M Ω (-s) (y' ξ)))⟫_ℂ := by
            have := integrable_w_mul_inner M Ω B hφ 1 η (y' ξ)
            simpa only [one_apply_eq_self] using this
          rw [integral_sub (integrable_w_mul_inner M Ω B hφ y' η ξ) hi2, h1, sub_self]
  have hzero := LaplaceUniq.eq_zero_of_forall_integral_w_eq_zero hgc hgC hint t
  rw [hg, sub_eq_zero] at hzero
  exact hzero

include hs hc in
/-- **RvD Lemma 4.8**: `Δ^{it} (J x′ J) Δ^{-it} ∈ M` for every `x′ ∈ M′`. -/
theorem Δit_conjJm_Δit_mem {x' : K →L[ℂ] K} (hx' : x' ∈ M.commutant) (t : ℝ) :
    Δit M Ω t * conjJm M Ω x' * Δit M Ω (-t) ∈ M := by
  obtain ⟨a, b, ha, hb, hsa, hsb, rfl⟩ := exists_sa_decomp M.commutant hx'
  rw [conjJm_add, conjJm_smul, mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
  exact add_mem (sa_Δit_conjJm_mem M Ω hs hc ha hsa t)
    (VN.smul_mem_vn M _ (sa_Δit_conjJm_mem M Ω hs hc hb hsb t))

include hs hc in
/-- `J M′ J ⊆ M`. -/
theorem conjJm_mem {x' : K →L[ℂ] K} (hx' : x' ∈ M.commutant) : conjJm M Ω x' ∈ M := by
  have := Δit_conjJm_Δit_mem M Ω hs hc hx' 0
  rwa [neg_zero, Δit_zero, one_mul, mul_one] at this

end Lemma48

/-! ## RvD Lemma 4.9: `J M J ⊆ M′` -/

section Lemma49

include hs hc in
/-- For `ξ ∈ 𝒦`, `Q (J ξ) = 0`. -/
theorem Qre_Jm_of_mem {ξ : K} (hξ : ξ ∈ Kre M Ω) : Qre M Ω (Jm M Ω ξ) = 0 := by
  have hP : Pre M Ω ξ = ξ := Pre_eq_self M Ω hξ
  have h1 : R M Ω (Jm M Ω ξ) = Jm M Ω ((2 - R M Ω) ξ) := by
    have := Jm_R M Ω hs hc (Jm M Ω ξ)
    rw [Jm_Jm M Ω hs hc] at this
    rw [← this, Jm_Jm M Ω hs hc]
  have h2 : Am M Ω (Jm M Ω ξ) = Jm M Ω (Am M Ω ξ) := by
    rw [← Tm_Jm M Ω hs hc (Jm M Ω ξ), Jm_Jm M Ω hs hc, ← Jm_Tm M Ω hs hc ξ, Jm_Jm M Ω hs hc]
  have h3 : (2 - R M Ω) ξ = Am M Ω ξ := by
    have h2' : ((2 : K →L[ℂ] K) ξ) = ξ + ξ := by
      rw [show (2 : K →L[ℂ] K) = 1 + 1 from one_add_one_eq_two.symm, _root_.add_apply,
        one_apply_eq_self]
    rw [Am_apply, _root_.sub_apply, R_apply, hP, h2']
    abel
  have h4 : R M Ω (Jm M Ω ξ) - Am M Ω (Jm M Ω ξ) = (2 : ℝ) • Qre M Ω (Jm M Ω ξ) := by
    rw [R_apply, Am_apply, two_smul]; abel
  rw [h1, h2, h3, sub_self] at h4
  exact (smul_eq_zero.mp h4.symm).resolve_left two_ne_zero

include hs hc in
/-- For `ξ, η ∈ 𝒦`, `⟪J ξ, η⟫` is real. -/
theorem im_inner_Jm_of_mem {ξ η : K} (hξ : ξ ∈ Kre M Ω) (hη : η ∈ Kre M Ω) :
    (⟪Jm M Ω ξ, η⟫_ℂ).im = 0 := by
  have hQ := Qre_Jm_of_mem M Ω hs hc hξ
  rw [Qre_eq_zero_iff, Submodule.mem_orthogonal] at hQ
  have h := hQ (Complex.I • η) (I_smul_mem_mulI_Kre M Ω hη)
  rw [inner_real_eq_re_inner, inner_smul_left, Complex.conj_I, neg_mul, Complex.neg_re,
    Complex.I_mul_re, neg_neg] at h
  rw [← inner_conj_symm, Complex.conj_im, h, neg_zero]

include hs hc in
/-- Claim A (self-adjoint case): `⟪Ω, y J x Ω⟫ = ⟪x J y Ω, Ω⟫` for `x, y ∈ M_s`. -/
theorem inner_conjJm_Ω_sa {x y : K →L[ℂ] K} (hx : x ∈ M) (hxs : IsSelfAdjoint x) (hy : y ∈ M)
    (hys : IsSelfAdjoint y) :
    ⟪Ω, y (conjJm M Ω x Ω)⟫_ℂ = ⟪x (conjJm M Ω y Ω), Ω⟫_ℂ := by
  rw [conjJm_apply, conjJm_apply, Jm_Ω M Ω hs hc, BorelCalc.inner_sa hys,
    ← BorelCalc.inner_sa hxs, inner_Jm_left M Ω hs hc (y Ω) (x Ω),
    ← inner_conj_symm (Jm M Ω (x Ω)) (y Ω)]
  symm
  rw [Complex.conj_eq_iff_im, ← inner_conj_symm, Complex.conj_im, neg_eq_zero]
  exact im_inner_Jm_of_mem M Ω hs hc (mem_Kre_of_sa M Ω hx hxs) (mem_Kre_of_sa M Ω hy hys)

include hs hc in
/-- Claim A: `⟪Ω, y J x Ω⟫ = ⟪x J y Ω, Ω⟫` for `x, y ∈ M`. -/
theorem inner_conjJm_Ω {x y : K →L[ℂ] K} (hx : x ∈ M) (hy : y ∈ M) :
    ⟪Ω, y (conjJm M Ω x Ω)⟫_ℂ = ⟪x (conjJm M Ω y Ω), Ω⟫_ℂ := by
  obtain ⟨a, b, ha, hb, hsa, hsb, rfl⟩ := exists_sa_decomp M hx
  obtain ⟨c, d, hc', hd, hsc, hsd, rfl⟩ := exists_sa_decomp M hy
  have h1 := inner_conjJm_Ω_sa M Ω hs hc ha hsa hc' hsc
  have h2 := inner_conjJm_Ω_sa M Ω hs hc ha hsa hd hsd
  have h3 := inner_conjJm_Ω_sa M Ω hs hc hb hsb hc' hsc
  have h4 := inner_conjJm_Ω_sa M Ω hs hc hb hsb hd hsd
  simp only [conjJm_add, conjJm_smul, Complex.conj_I, _root_.add_apply, _root_.smul_apply,
    map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    map_neg, neg_neg]
  linear_combination (norm := skip) h1 + Complex.I * h2 - Complex.I * h3 + h4
  ring_nf
  simp only [Complex.I_sq]
  ring

include hs hc in
/-- Claim B: `(J y J)(x Ω) = x (J y J Ω)` for `x, y ∈ M`. -/
theorem conjJm_apply_Ω_comm {x y : K →L[ℂ] K} (hx : x ∈ M) (hy : y ∈ M) :
    conjJm M Ω y (x Ω) = x (conjJm M Ω y Ω) := by
  refine eq_of_inner_commutant M Ω hs fun y' hy' => ?_
  have hv : conjJm M Ω (star y') * y ∈ M := mul_mem (conjJm_mem M Ω hs hc (star_mem hy')) hy
  have hA := inner_conjJm_Ω M Ω hs hc hv hx
  have hxy : star x * y' = y' * star x := (VonNeumannAlgebra.mem_commutant_iff.mp hy') _ (star_mem hx)
  symm
  calc ⟪y' Ω, x (conjJm M Ω y Ω)⟫_ℂ
      = ⟪star x (y' Ω), conjJm M Ω y Ω⟫_ℂ := by
        rw [ContinuousLinearMap.star_eq_adjoint x, ContinuousLinearMap.adjoint_inner_left]
    _ = ⟪y' (star x Ω), conjJm M Ω y Ω⟫_ℂ := by
        rw [← mul_apply_eq_comp, hxy, mul_apply_eq_comp]
    _ = ⟪star x Ω, star y' (conjJm M Ω y Ω)⟫_ℂ := by
        rw [ContinuousLinearMap.star_eq_adjoint y', ContinuousLinearMap.adjoint_inner_right]
    _ = ⟪star x Ω, conjJm M Ω (conjJm M Ω (star y') * y) Ω⟫_ℂ := by
        simp only [conjJm_apply, mul_apply_eq_comp, Jm_Jm M Ω hs hc, Jm_Ω M Ω hs hc]
    _ = ⟪Ω, x (conjJm M Ω (conjJm M Ω (star y') * y) Ω)⟫_ℂ := by
        rw [ContinuousLinearMap.star_eq_adjoint x, ContinuousLinearMap.adjoint_inner_left]
    _ = ⟪(conjJm M Ω (star y') * y) (conjJm M Ω x Ω), Ω⟫_ℂ := hA
    _ = ⟪Jm M Ω (star y' (Jm M Ω (y (Jm M Ω (x Ω))))), Ω⟫_ℂ := by
        simp only [conjJm_apply, mul_apply_eq_comp, Jm_Ω M Ω hs hc]
    _ = ⟪Ω, star y' (Jm M Ω (y (Jm M Ω (x Ω))))⟫_ℂ := by
        rw [inner_Jm_left M Ω hs hc, Jm_Ω M Ω hs hc]
    _ = ⟪y' Ω, conjJm M Ω y (x Ω)⟫_ℂ := by
        rw [ContinuousLinearMap.star_eq_adjoint y', ContinuousLinearMap.adjoint_inner_right,
          conjJm_apply]

include hs hc in
/-- **RvD Lemma 4.9**: `J M J ⊆ M′`. -/
theorem conjJm_mem_commutant {y : K →L[ℂ] K} (hy : y ∈ M) : conjJm M Ω y ∈ M.commutant := by
  rw [VonNeumannAlgebra.mem_commutant_iff]
  intro x hx
  have hd : Dense (orbit (M : Set (K →L[ℂ] K)) Ω : Set K) := hc
  have := Continuous.ext_on hd (f := fun v => (x * conjJm M Ω y) v)
    (g := fun v => (conjJm M Ω y * x) v) (x * conjJm M Ω y).continuous
    (conjJm M Ω y * x).continuous (by
      intro v hv
      obtain ⟨z, hz, rfl⟩ := exists_of_mem_orbit_vn M hv
      simp only [mul_apply_eq_comp]
      rw [conjJm_apply_Ω_comm M Ω hs hc hz hy, ← mul_apply_eq_comp x z,
        ← conjJm_apply_Ω_comm M Ω hs hc (mul_mem hx hz) hy, mul_apply_eq_comp])
  ext ζ
  exact congrFun this ζ

end Lemma49

/-! ## RvD Theorem 4.2 and the modular automorphism group -/

section Theorem42

include hs hc in
/-- **Tomita's theorem, part 1**: `J M J = M′`. -/
theorem conjJm_mem_commutant_iff (x : K →L[ℂ] K) : conjJm M Ω x ∈ M.commutant ↔ x ∈ M := by
  refine ⟨fun h => ?_, conjJm_mem_commutant M Ω hs hc⟩
  have := conjJm_mem M Ω hs hc h
  rwa [conjJm_conjJm M Ω hs hc] at this

include hs hc in
/-- **Tomita's theorem, part 1′**: `J M′ J = M`. -/
theorem conjJm_mem_iff (x : K →L[ℂ] K) : conjJm M Ω x ∈ M ↔ x ∈ M.commutant := by
  refine ⟨fun h => ?_, conjJm_mem M Ω hs hc⟩
  have := conjJm_mem_commutant M Ω hs hc h
  rwa [conjJm_conjJm M Ω hs hc] at this

/-- The modular automorphism group `σ_t(x) = Δ^{it} x Δ^{-it}`. -/
noncomputable def σ (t : ℝ) (x : K →L[ℂ] K) : K →L[ℂ] K := Δit M Ω t * x * Δit M Ω (-t)

theorem σ_apply (t : ℝ) (x : K →L[ℂ] K) (ξ : K) :
    σ M Ω t x ξ = Δit M Ω t (x (Δit M Ω (-t) ξ)) := rfl

include hs hc in
/-- **Tomita's theorem, part 2**: `Δ^{it} M Δ^{-it} ⊆ M`. -/
theorem σ_mem {x : K →L[ℂ] K} (hx : x ∈ M) (t : ℝ) : σ M Ω t x ∈ M := by
  have := Δit_conjJm_Δit_mem M Ω hs hc ((conjJm_mem_commutant_iff M Ω hs hc x).mpr hx) t
  rwa [conjJm_conjJm M Ω hs hc] at this

include hs hc in
theorem conjJm_σ (t : ℝ) (x : K →L[ℂ] K) : conjJm M Ω (σ M Ω t x) = σ M Ω t (conjJm M Ω x) := by
  ext ξ
  simp only [σ_apply, conjJm_apply, Jm_Δit M Ω hs hc]

include hs hc in
theorem σ_mem_commutant {x : K →L[ℂ] K} (hx : x ∈ M.commutant) (t : ℝ) :
    σ M Ω t x ∈ M.commutant := by
  have h1 : σ M Ω t (conjJm M Ω x) ∈ M := σ_mem M Ω hs hc (conjJm_mem M Ω hs hc hx) t
  have h2 := conjJm_mem_commutant M Ω hs hc h1
  rwa [← conjJm_σ M Ω hs hc, conjJm_conjJm M Ω hs hc] at h2

theorem σ_zero (x : K →L[ℂ] K) : σ M Ω 0 x = x := by
  simp only [σ, neg_zero, Δit_zero, one_mul, mul_one]

theorem σ_add (s t : ℝ) (x : K →L[ℂ] K) : σ M Ω (s + t) x = σ M Ω s (σ M Ω t x) := by
  simp only [σ]
  rw [Δit_add, neg_add, Δit_add, Δit_comm M Ω (-s) (-t)]
  simp only [mul_assoc]

theorem σ_neg_σ (t : ℝ) (x : K →L[ℂ] K) : σ M Ω (-t) (σ M Ω t x) = x := by
  rw [← σ_add, neg_add_cancel, σ_zero]

theorem σ_σ_neg (t : ℝ) (x : K →L[ℂ] K) : σ M Ω t (σ M Ω (-t) x) = x := by
  rw [← σ_add, add_neg_cancel, σ_zero]

theorem σ_mul (t : ℝ) (x y : K →L[ℂ] K) : σ M Ω t (x * y) = σ M Ω t x * σ M Ω t y := by
  simp only [σ]
  calc Δit M Ω t * (x * y) * Δit M Ω (-t)
      = Δit M Ω t * x * (Δit M Ω (-t) * Δit M Ω t) * y * Δit M Ω (-t) := by
        rw [Δit_neg_mul, mul_one]; simp only [mul_assoc]
    _ = _ := by simp only [mul_assoc]

theorem σ_add_op (t : ℝ) (x y : K →L[ℂ] K) : σ M Ω t (x + y) = σ M Ω t x + σ M Ω t y := by
  simp only [σ, mul_add, add_mul]

theorem σ_smul (t : ℝ) (c : ℂ) (x : K →L[ℂ] K) : σ M Ω t (c • x) = c • σ M Ω t x := by
  simp only [σ, mul_smul_comm, smul_mul_assoc]

theorem σ_star (t : ℝ) (x : K →L[ℂ] K) : σ M Ω t (star x) = star (σ M Ω t x) := by
  simp only [σ, star_mul, Δit_star, neg_neg, mul_assoc]

theorem σ_one (t : ℝ) : σ M Ω t (1 : K →L[ℂ] K) = 1 := by
  simp only [σ, mul_one, Δit_mul_neg]

theorem σ_apply_Ω (t : ℝ) (x : K →L[ℂ] K) : σ M Ω t x Ω = Δit M Ω t (x Ω) := by
  rw [σ_apply, Δit_Ω]

/-- `ψ ∘ σ_t = ψ` for the vector state `ψ = ⟪Ω, · Ω⟫`. -/
theorem inner_Ω_σ (t : ℝ) (x : K →L[ℂ] K) : ⟪Ω, σ M Ω t x Ω⟫_ℂ = ⟪Ω, x Ω⟫_ℂ := by
  rw [σ_apply_Ω, ← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
    Δit_star, Δit_Ω]

theorem σ_eq_self_iff (t : ℝ) (x : K →L[ℂ] K) : σ M Ω t x = x ↔ Commute (Δit M Ω t) x := by
  constructor
  · intro h
    have := congrArg (· * Δit M Ω t) h
    simp only [σ, mul_assoc, Δit_neg_mul, mul_one] at this
    exact this
  · intro h
    simp only [σ]
    rw [h.eq, mul_assoc, Δit_mul_neg, mul_one]

/-- Elements commuting with `R` are fixed by the modular group. -/
theorem σ_eq_self_of_commute_R {x : K →L[ℂ] K} (h : Commute x (R M Ω)) (t : ℝ) :
    σ M Ω t x = x :=
  (σ_eq_self_iff M Ω t x).mpr
    ((BorelCalc.commute_cbfc (R M Ω) (R_isSelfAdjoint M Ω) h.symm (cbdd_gDel t)))

end Theorem42

end Modular

end VN

end CommutingRepetition

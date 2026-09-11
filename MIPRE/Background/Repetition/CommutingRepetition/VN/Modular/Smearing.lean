/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/Modular/Smearing.lean
-/
/-
# Gaussian smearing (density stage E4.5)

HJX Lemma 2.5(i) needs a `‖·‖_ψ`-dense set of *left-bounded* elements of `M`:
`x` with `ψ(x* y x) ≤ c ψ(y)` for all `y ≥ 0`. HJX use analytic elements; here
they are replaced by explicit Gaussian smearing (`PLAN-tomita.md` §3.5):

* `x_k := ∫ a_k(t) σ_t(x) dt` with `a_k(t) = √(k/π) e^{-kt²}`, and the companion
  `x_k^♭ := e^{k/4} ∫ a_k(t) e^{-ikt} σ_t(x*) dt`, both in `M`.
* Spectrally, `x_k Ω = e^{-θ²/(4k)}(R) xΩ` and `x_k^♭ Ω = (e^{-θ²/(4k)} e^{θ/2})(R) x*Ω`
  (Gaussian Fourier transform, `fourierIntegral_gaussian`), hence
  `J x_k^♭ Ω = x_k Ω` by the bounded identity `T J x*Ω = (2−R) xΩ`.
* Therefore `x_k Ω = c Ω` with `c = J x_k^♭ J ∈ M′` (Tomita), so
  `ψ(x_k* y x_k) ≤ ‖x_k^♭‖² ψ(y)` for `y ≥ 0`; and `x_k Ω → xΩ` as `k → ∞`
  (dominated convergence in the Borel calculus).
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.Modular.Tomita

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace VN

namespace Modular

open scoped InnerProductSpace ComplexConjugate Real
open Filter Topology BorelCalc MeasureTheory

set_option linter.unusedSectionVars false

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ## The smearing operator `∫ a(t) U(t) dt` -/

section Smear

variable (a : ℝ → ℂ) (ha : Integrable a) (U : ℝ → K →L[ℂ] K) {C : ℝ}
  (hUc : ∀ v, Continuous fun t => U t v) (hUb : ∀ t, ‖U t‖ ≤ C)

include ha hUc hUb in
theorem integrable_smul_apply (ξ : K) : Integrable fun t => a t • U t ξ := by
  refine Integrable.mono' (ha.norm.mul_const (C * ‖ξ‖))
    (ha.aestronglyMeasurable.smul (hUc ξ).aestronglyMeasurable) (Eventually.of_forall fun t => ?_)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (((U t).le_opNorm ξ).trans
    (mul_le_mul_of_nonneg_right (hUb t) (norm_nonneg ξ))) (norm_nonneg _)

/-- The smearing operator `ξ ↦ ∫ a(t) U(t) ξ dt` of a uniformly bounded strongly continuous
family `U` against an integrable weight `a`. -/
noncomputable def smear : K →L[ℂ] K :=
  LinearMap.mkContinuous
    { toFun := fun ξ => ∫ t, a t • U t ξ
      map_add' := fun ξ η => by
        rw [← integral_add (integrable_smul_apply a ha U hUc hUb ξ)
          (integrable_smul_apply a ha U hUc hUb η)]
        congr 1
        funext t
        simp only [map_add, smul_add]
      map_smul' := fun c ξ => by
        rw [RingHom.id_apply, ← integral_smul]
        congr 1
        funext t
        simp only [map_smul, smul_comm c] }
    ((∫ t, ‖a t‖) * C) fun ξ => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      calc ‖∫ t, a t • U t ξ‖ ≤ ∫ t, ‖a t‖ * (C * ‖ξ‖) :=
            norm_integral_le_of_norm_le (ha.norm.mul_const _) (Eventually.of_forall fun t => by
              rw [norm_smul]
              exact mul_le_mul_of_nonneg_left (((U t).le_opNorm ξ).trans
                (mul_le_mul_of_nonneg_right (hUb t) (norm_nonneg ξ))) (norm_nonneg _))
        _ = (∫ t, ‖a t‖) * C * ‖ξ‖ := by rw [integral_mul_const]; ring

theorem smear_apply (ξ : K) : smear a ha U hUc hUb ξ = ∫ t, a t • U t ξ := rfl

include ha hUc hUb in
theorem norm_smear_le : ‖smear a ha U hUc hUb‖ ≤ (∫ t, ‖a t‖) * C := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hUb 0)
  exact LinearMap.mkContinuous_norm_le _
    (mul_nonneg (integral_nonneg fun t => norm_nonneg _) hC0) _

theorem inner_smear (η ξ : K) :
    ⟪η, smear a ha U hUc hUb ξ⟫_ℂ = ∫ t, a t * ⟪η, U t ξ⟫_ℂ := by
  rw [smear_apply, ← integral_inner (integrable_smul_apply a ha U hUc hUb ξ)]
  congr 1
  funext t
  rw [inner_smul_right]

theorem clm_smear (S : K →L[ℂ] K) (ξ : K) :
    S (smear a ha U hUc hUb ξ) = ∫ t, a t • S (U t ξ) := by
  rw [smear_apply, ← S.integral_comp_comm (integrable_smul_apply a ha U hUc hUb ξ)]
  congr 1
  funext t
  rw [map_smul]

/-- Smearing a family of elements of a von Neumann algebra stays in it. -/
theorem smear_mem (N : VonNeumannAlgebra K) (hU : ∀ t, U t ∈ N) :
    smear a ha U hUc hUb ∈ N := by
  suffices h : smear a ha U hUc hUb ∈ N.commutant.commutant by
    rwa [VonNeumannAlgebra.commutant_commutant] at h
  rw [VonNeumannAlgebra.mem_commutant_iff]
  intro y' hy'
  ext ξ
  simp only [mul_apply_eq_comp]
  rw [clm_smear, smear_apply]
  congr 1
  funext t
  have h := VonNeumannAlgebra.mem_commutant_iff.mp hy' _ (hU t)
  rw [← mul_apply_eq_comp, ← h, mul_apply_eq_comp]

end Smear

variable (M : VonNeumannAlgebra K) (Ω : K)

/-! ## Exchange: `∫ a(t) Δ^{it} ζ dt = â(θ)(R) ζ` -/

theorem measurable_gDel_uncurry : Measurable fun z : ℝ × ℝ => gDel z.1 z.2 := by
  unfold gDel
  refine Complex.continuous_exp.measurable.comp (Measurable.mul ?_ measurable_const)
  exact Complex.measurable_ofReal.comp (measurable_fst.mul (measurable_θ.comp measurable_snd))

theorem integrable_mul_gDel {a : ℝ → ℂ} (ha : Integrable a) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (fun z : ℝ × ℝ => a z.1 * gDel z.1 z.2) (volume.prod μ) := by
  have h1 : Integrable (fun z : ℝ × ℝ => a z.1) (volume.prod μ) := by
    simpa using ha.mul_prod (integrable_const (1 : ℂ))
  refine h1.norm.mono' (h1.aestronglyMeasurable.mul measurable_gDel_uncurry.aestronglyMeasurable)
    (Eventually.of_forall fun z => ?_)
  rw [norm_mul, norm_gDel, mul_one]

/-- `∫ a(t) Δ^{it} dt = Ĝ(R)` where `Ĝ(l) = ∫ a(t) e^{itθ(l)} dt`. -/
theorem smear_Δit_eq_cbfc {a : ℝ → ℂ} (ha : Integrable a) {Ĝ : ℝ → ℂ} (hĜ : CBdd Ĝ)
    (hint : ∀ l, ∫ t, a t * gDel t l = Ĝ l) :
    smear a ha (fun t => Δit M Ω t) (continuous_Δit_apply M Ω) (norm_Δit_le M Ω) =
      cbfc (R M Ω) (R_isSelfAdjoint M Ω) Ĝ := by
  refine ext_of_inner_self fun ξ => ?_
  rw [inner_smear, inner_cbfc_self _ _ hĜ]
  have h1 : ∀ t, ⟪ξ, Δit M Ω t ξ⟫_ℂ = ∫ l, gDel t l ∂(ν (R M Ω) (R_isSelfAdjoint M Ω) ξ) :=
    fun t => inner_cbfc_self _ _ (cbdd_gDel t) ξ
  calc ∫ t, a t * ⟪ξ, Δit M Ω t ξ⟫_ℂ
      = ∫ t, ∫ l, a t * gDel t l ∂(ν (R M Ω) (R_isSelfAdjoint M Ω) ξ) := by
        congr 1; funext t; rw [h1 t, MeasureTheory.integral_const_mul]
    _ = ∫ l, (∫ t, a t * gDel t l) ∂(ν (R M Ω) (R_isSelfAdjoint M Ω) ξ) :=
        integral_integral_swap (f := fun t l => a t * gDel t l)
          (integrable_mul_gDel ha _)
    _ = ∫ l, Ĝ l ∂(ν (R M Ω) (R_isSelfAdjoint M Ω) ξ) := by congr 1; funext l; exact hint l

theorem integral_smul_Δit {a : ℝ → ℂ} (ha : Integrable a) {Ĝ : ℝ → ℂ} (hĜ : CBdd Ĝ)
    (hint : ∀ l, ∫ t, a t * gDel t l = Ĝ l) (ζ : K) :
    ∫ t, a t • Δit M Ω t ζ = cbfc (R M Ω) (R_isSelfAdjoint M Ω) Ĝ ζ := by
  rw [← smear_apply a ha (fun t => Δit M Ω t) (continuous_Δit_apply M Ω) (norm_Δit_le M Ω),
    smear_Δit_eq_cbfc M Ω ha hĜ hint]

/-! ## Gaussians and their Fourier transforms -/

/-- The normalized Gaussian `a_k(t) = √(k/π) e^{-kt²}`. -/
noncomputable def gauss (k t : ℝ) : ℝ := Real.sqrt (k / π) * Real.exp (-k * t ^ 2)

theorem gauss_nonneg (k t : ℝ) : 0 ≤ gauss k t :=
  mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le

@[fun_prop]
theorem continuous_gauss (k : ℝ) : Continuous (gauss k) := by unfold gauss; fun_prop

theorem integrable_gauss {k : ℝ} (hk : 0 < k) : Integrable (gauss k) :=
  (integrable_exp_neg_mul_sq hk).const_mul _

theorem integral_gauss {k : ℝ} (hk : 0 < k) : ∫ t, gauss k t = 1 := by
  unfold gauss
  rw [MeasureTheory.integral_const_mul, integral_gaussian,
    ← Real.sqrt_mul (div_nonneg hk.le Real.pi_pos.le),
    show k / π * (π / k) = 1 by field_simp, Real.sqrt_one]

theorem integrable_gaussC {k : ℝ} (hk : 0 < k) : Integrable fun t => (gauss k t : ℂ) :=
  (integrable_gauss hk).ofReal

theorem integral_norm_gaussC {k : ℝ} (hk : 0 < k) : ∫ t, ‖(gauss k t : ℂ)‖ = 1 := by
  simp_rw [Complex.norm_real, Real.norm_of_nonneg (gauss_nonneg _ _)]
  exact integral_gauss hk

/-- The Gaussian Fourier transform: `∫ a_k(t) e^{itu} dt = e^{-u²/(4k)}`. -/
theorem integral_gaussC_mul_exp {k : ℝ} (hk : 0 < k) (u : ℝ) :
    ∫ t, (gauss k t : ℂ) * Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) =
      (Real.exp (-u ^ 2 / (4 * k)) : ℂ) := by
  have hb : (0 : ℝ) < (k : ℂ).re := by simpa using hk
  have hF := fourierIntegral_gaussian hb (u : ℂ)
  have h1 : ∀ t : ℝ, (gauss k t : ℂ) * Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) =
      (Real.sqrt (k / π) : ℂ) *
        (Complex.exp (Complex.I * u * t) * Complex.exp (-(k : ℂ) * t ^ 2)) := by
    intro t
    unfold gauss
    rw [Complex.ofReal_mul, Complex.ofReal_exp]
    push_cast
    rw [show ((t : ℂ) * u * Complex.I) = Complex.I * u * t by ring]
    ring
  simp_rw [h1]
  rw [MeasureTheory.integral_const_mul, hF]
  have h2 : ((π : ℂ) / k) ^ (1 / 2 : ℂ) = (Real.sqrt (π / k) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (div_nonneg Real.pi_pos.le hk.le)]
    push_cast
    ring_nf
  rw [h2, ← mul_assoc, ← Complex.ofReal_mul, ← Real.sqrt_mul (div_nonneg hk.le Real.pi_pos.le),
    show k / π * (π / k) = 1 by field_simp, Real.sqrt_one, Complex.ofReal_one, one_mul,
    Complex.ofReal_exp]
  push_cast
  ring_nf

/-- The modulated Gaussian `a_k^♭(t) = e^{k/4} a_k(t) e^{-ikt}`. -/
noncomputable def gaussFlat (k t : ℝ) : ℂ :=
  (Real.exp (k / 4) : ℂ) * (gauss k t : ℂ) * Complex.exp (-(((k * t : ℝ) : ℂ) * Complex.I))

theorem norm_gaussFlat (k t : ℝ) : ‖gaussFlat k t‖ = Real.exp (k / 4) * gauss k t := by
  unfold gaussFlat
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_exp,
    Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (gauss_nonneg _ _)]
  simp

theorem integrable_gaussFlat {k : ℝ} (hk : 0 < k) : Integrable (gaussFlat k) := by
  refine Integrable.mono' ((integrable_gauss hk).const_mul (Real.exp (k / 4)))
    ?_ (Eventually.of_forall fun t => (norm_gaussFlat k t).le)
  unfold gaussFlat
  exact (Continuous.aestronglyMeasurable (by fun_prop))

theorem integral_norm_gaussFlat {k : ℝ} (hk : 0 < k) :
    ∫ t, ‖gaussFlat k t‖ = Real.exp (k / 4) := by
  simp_rw [norm_gaussFlat]
  rw [MeasureTheory.integral_const_mul, integral_gauss hk, mul_one]

/-- `∫ a_k^♭(t) e^{itu} dt = e^{-u²/(4k)} e^{u/2}`. -/
theorem integral_gaussFlat_mul_exp {k : ℝ} (hk : 0 < k) (u : ℝ) :
    ∫ t, gaussFlat k t * Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) =
      (Real.exp (-u ^ 2 / (4 * k)) * Real.exp (u / 2) : ℂ) := by
  have h1 : ∀ t : ℝ, gaussFlat k t * Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) =
      (Real.exp (k / 4) : ℂ) *
        ((gauss k t : ℂ) * Complex.exp (((t * (u - k) : ℝ) : ℂ) * Complex.I)) := by
    intro t
    unfold gaussFlat
    rw [mul_assoc, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  simp_rw [h1]
  rw [MeasureTheory.integral_const_mul, integral_gaussC_mul_exp hk, ← Complex.ofReal_mul,
    ← Complex.ofReal_mul, ← Real.exp_add, ← Real.exp_add]
  congr 2
  field_simp
  ring

/-! ## The spectral functions `e^{-θ²/(4k)}` and `e^{-θ²/(4k)} e^{θ/2}` -/

/-- `gk k l = e^{-θ(l)²/(4k)}`. -/
noncomputable def gk (k l : ℝ) : ℝ := Real.exp (-(θ l) ^ 2 / (4 * k))

/-- `gkFlat k l = e^{-θ(l)²/(4k)} e^{θ(l)/2}`. -/
noncomputable def gkFlat (k l : ℝ) : ℝ := gk k l * Real.exp (θ l / 2)

theorem gk_pos (k l : ℝ) : 0 < gk k l := Real.exp_pos _

theorem gk_le_one {k : ℝ} (hk : 0 < k) (l : ℝ) : gk k l ≤ 1 := by
  unfold gk
  rw [Real.exp_le_one_iff]
  apply div_nonpos_of_nonpos_of_nonneg
  · exact neg_nonpos.mpr (sq_nonneg _)
  · positivity

theorem measurable_gk (k : ℝ) : Measurable (gk k) := by
  unfold gk
  exact Real.measurable_exp.comp ((measurable_θ.pow_const 2).neg.div_const _)

theorem bdd_gk {k : ℝ} (hk : 0 < k) : Bdd (gk k) :=
  ⟨measurable_gk k, 1, fun l => by
    rw [abs_of_pos (gk_pos k l)]; exact gk_le_one hk l⟩

theorem gkFlat_le {k : ℝ} (hk : 0 < k) (l : ℝ) : gkFlat k l ≤ Real.exp (k / 4) := by
  unfold gkFlat gk
  rw [← Real.exp_add, Real.exp_le_exp]
  have h : -(θ l) ^ 2 / (4 * k) + θ l / 2 = k / 4 - (θ l - k) ^ 2 / (4 * k) := by
    field_simp
    ring
  rw [h]
  have : 0 ≤ (θ l - k) ^ 2 / (4 * k) := by positivity
  linarith

theorem gkFlat_pos (k l : ℝ) : 0 < gkFlat k l := mul_pos (gk_pos k l) (Real.exp_pos _)

theorem measurable_gkFlat (k : ℝ) : Measurable (gkFlat k) :=
  (measurable_gk k).mul (Real.measurable_exp.comp (measurable_θ.div_const _))

theorem bdd_gkFlat {k : ℝ} (hk : 0 < k) : Bdd (gkFlat k) :=
  ⟨measurable_gkFlat k, Real.exp (k / 4), fun l => by
    rw [abs_of_pos (gkFlat_pos k l)]; exact gkFlat_le hk l⟩

theorem integral_gaussC_mul_gDel {k : ℝ} (hk : 0 < k) (l : ℝ) :
    ∫ t, (gauss k t : ℂ) * gDel t l = (gk k l : ℂ) :=
  integral_gaussC_mul_exp hk (θ l)

theorem integral_gaussFlat_mul_gDel {k : ℝ} (hk : 0 < k) (l : ℝ) :
    ∫ t, gaussFlat k t * gDel t l = (gkFlat k l : ℂ) := by
  rw [gkFlat, Complex.ofReal_mul]
  exact integral_gaussFlat_mul_exp hk (θ l)

/-! ## The smeared elements `x_k` and `x_k^♭` -/

theorem norm_σ_le (t : ℝ) (x : K →L[ℂ] K) : ‖σ M Ω t x‖ ≤ ‖x‖ := by
  calc ‖Δit M Ω t * x * Δit M Ω (-t)‖ ≤ ‖Δit M Ω t * x‖ * ‖Δit M Ω (-t)‖ := norm_mul_le _ _
    _ ≤ ‖Δit M Ω t‖ * ‖x‖ * ‖Δit M Ω (-t)‖ := by gcongr; exact norm_mul_le _ _
    _ ≤ 1 * ‖x‖ * 1 := by gcongr <;> exact norm_Δit_le M Ω _
    _ = ‖x‖ := by ring

theorem continuous_σ_apply (x : K →L[ℂ] K) (v : K) : Continuous fun t => σ M Ω t x v := by
  show Continuous fun t => Δit M Ω t (x (Δit M Ω (-t) v))
  exact continuous_Δit_comp M Ω
    (x.continuous.comp ((continuous_Δit_comp M Ω continuous_const).comp continuous_neg))

/-- The Gaussian smearing `x_k = ∫ a_k(t) σ_t(x) dt`. -/
noncomputable def xk (k : ℝ) (hk : 0 < k) (x : K →L[ℂ] K) : K →L[ℂ] K :=
  smear (fun t => (gauss k t : ℂ)) (integrable_gaussC hk) (fun t => σ M Ω t x)
    (continuous_σ_apply M Ω x) (fun t => norm_σ_le M Ω t x)

/-- The companion `x_k^♭ = e^{k/4} ∫ a_k(t) e^{-ikt} σ_t(x*) dt`. -/
noncomputable def xkFlat (k : ℝ) (hk : 0 < k) (x : K →L[ℂ] K) : K →L[ℂ] K :=
  smear (gaussFlat k) (integrable_gaussFlat hk) (fun t => σ M Ω t (star x))
    (continuous_σ_apply M Ω (star x)) (fun t => norm_σ_le M Ω t (star x))

variable (hs : IsSeparating (M : Set (K →L[ℂ] K)) Ω) (hc : IsCyclic (M : Set (K →L[ℂ] K)) Ω)

include hs hc in
theorem xk_mem {k : ℝ} (hk : 0 < k) {x : K →L[ℂ] K} (hx : x ∈ M) : xk M Ω k hk x ∈ M :=
  smear_mem _ _ _ _ _ M fun t => σ_mem M Ω hs hc hx t

include hs hc in
theorem xkFlat_mem {k : ℝ} (hk : 0 < k) {x : K →L[ℂ] K} (hx : x ∈ M) : xkFlat M Ω k hk x ∈ M :=
  smear_mem _ _ _ _ _ M fun t => σ_mem M Ω hs hc (star_mem hx) t

theorem norm_xk_le {k : ℝ} (hk : 0 < k) (x : K →L[ℂ] K) : ‖xk M Ω k hk x‖ ≤ ‖x‖ := by
  refine (norm_smear_le _ _ _ _ _).trans_eq ?_
  rw [integral_norm_gaussC hk, one_mul]

theorem norm_xkFlat_le {k : ℝ} (hk : 0 < k) (x : K →L[ℂ] K) :
    ‖xkFlat M Ω k hk x‖ ≤ Real.exp (k / 4) * ‖x‖ := by
  refine (norm_smear_le _ _ _ _ _).trans_eq ?_
  rw [integral_norm_gaussFlat hk, norm_star]

/-- `x_k Ω = e^{-θ²/(4k)}(R) xΩ`. -/
theorem xk_apply_Ω {k : ℝ} (hk : 0 < k) (x : K →L[ℂ] K) :
    xk M Ω k hk x Ω = bfc (R M Ω) (R_isSelfAdjoint M Ω) (gk k) (x Ω) := by
  have h : xk M Ω k hk x Ω = ∫ t, (gauss k t : ℂ) • Δit M Ω t (x Ω) := by
    show ∫ t, _ = ∫ t, _
    congr 1; funext t; rw [σ_apply_Ω]
  rw [h, integral_smul_Δit M Ω (integrable_gaussC hk) (CBdd.ofReal (bdd_gk hk))
    (fun l => integral_gaussC_mul_gDel hk l), cbfc_ofReal]

/-- `x_k^♭ Ω = (e^{-θ²/(4k)} e^{θ/2})(R) x*Ω`. -/
theorem xkFlat_apply_Ω {k : ℝ} (hk : 0 < k) (x : K →L[ℂ] K) :
    xkFlat M Ω k hk x Ω = bfc (R M Ω) (R_isSelfAdjoint M Ω) (gkFlat k) (star x Ω) := by
  have h : xkFlat M Ω k hk x Ω = ∫ t, gaussFlat k t • Δit M Ω t (star x Ω) := by
    show ∫ t, _ = ∫ t, _
    congr 1; funext t; rw [σ_apply_Ω]
  rw [h, integral_smul_Δit M Ω (integrable_gaussFlat hk) (CBdd.ofReal (bdd_gkFlat hk))
    (fun l => integral_gaussFlat_mul_gDel hk l), cbfc_ofReal]

theorem gk_two_sub (k l : ℝ) : gk k (2 - l) = gk k l := by
  unfold gk; rw [θ_two_sub, neg_sq]

/-- The reflected companion function `gkFlat k (2 − l) = e^{-θ²/(4k)} e^{-θ/2}`. -/
theorem gkFlat_two_sub (k l : ℝ) : gkFlat k (2 - l) = gk k l * Real.exp (-(θ l / 2)) := by
  unfold gkFlat; rw [gk_two_sub, θ_two_sub, neg_div]

include hs hc in
/-- **The key identity** `J x_k^♭ Ω = x_k Ω`. -/
theorem Jm_xkFlat_apply_Ω {k : ℝ} (hk : 0 < k) {x : K →L[ℂ] K} (hx : x ∈ M) :
    Jm M Ω (xkFlat M Ω k hk x Ω) = xk M Ω k hk x Ω := by
  have hR := R_isSelfAdjoint M Ω
  rw [xkFlat_apply_Ω, xk_apply_Ω, ← cbfc_ofReal, ← cbfc_ofReal,
    Jm_cbfc M Ω hs hc (CBdd.ofReal (bdd_gkFlat hk))]
  -- both sides are `cbfc` applied to `J x*Ω` resp. `xΩ`; compare after applying `T`
  have hF : (fun l => conj ((gkFlat k (2 - l) : ℝ) : ℂ)) =
      fun l => ((gk k l * Real.exp (-(θ l / 2)) : ℝ) : ℂ) := by
    funext l; rw [Complex.conj_ofReal, gkFlat_two_sub]
  rw [hF]
  have hbdd₁ : Bdd fun l => gk k l * Real.exp (-(θ l / 2)) := by
    have : (fun l => gk k l * Real.exp (-(θ l / 2))) = fun l => gkFlat k (2 - l) := by
      funext l; rw [gkFlat_two_sub]
    rw [this]
    exact (bdd_gkFlat hk).comp_two_sub
  have hT : ∀ u v : K, Tm M Ω u = Tm M Ω v → u = v := fun u v h =>
    sub_eq_zero.mp ((Tm_eq_zero_iff M Ω hs hc).mp (by rw [map_sub, h, sub_self]))
  apply hT
  have hTJ : Tm M Ω (Jm M Ω (star x Ω)) = (2 - R M Ω) (x Ω) := by
    rw [Tm_Jm_apply_mem M Ω hs hc (star_mem hx), star_star]
  have hbdd₂ : Bdd fun l => gk k l * Real.exp (-(θ l / 2)) * g₂ l := hbdd₁.mul bdd_g₂
  have hbdd₃ : Bdd fun l => gT l * gk k l := bdd_gT.mul (bdd_gk hk)
  calc Tm M Ω (cbfc (R M Ω) hR (fun l => ((gk k l * Real.exp (-(θ l / 2)) : ℝ) : ℂ))
        (Jm M Ω (star x Ω)))
      = cbfc (R M Ω) hR (fun l => ((gk k l * Real.exp (-(θ l / 2)) : ℝ) : ℂ))
          (Tm M Ω (Jm M Ω (star x Ω))) := by
        rw [Tm_eq_bfc, ← cbfc_ofReal, ← mul_apply_eq_comp, ← mul_apply_eq_comp,
          cbfc_comm _ _ (CBdd.ofReal bdd_gT) (CBdd.ofReal hbdd₁)]
    _ = cbfc (R M Ω) hR (fun l => ((gk k l * Real.exp (-(θ l / 2)) * g₂ l : ℝ) : ℂ)) (x Ω) := by
        rw [hTJ, ← bfc_g₂, ← cbfc_ofReal, ← mul_apply_eq_comp,
          ← cbfc_mul _ _ (CBdd.ofReal hbdd₁) (CBdd.ofReal bdd_g₂)]
        congr 2
        funext l
        simp only [Pi.mul_apply, Complex.ofReal_mul]
    _ = cbfc (R M Ω) hR (fun l => ((gT l * gk k l : ℝ) : ℂ)) (x Ω) := by
        congr 1
        apply cbfc_congr_ae _ _ (CBdd.ofReal hbdd₂) (CBdd.ofReal hbdd₃)
        intro ξ
        filter_upwards [ae_mem_Ioo M Ω hs hc ξ] with l hl
        rw [g₂_eq (Set.Ioo_subset_Icc_self hl), ← exp_half_θ_mul_gT hl, Real.exp_neg]
        have hne : Real.exp (θ l / 2) * (Real.exp (θ l / 2))⁻¹ = 1 :=
          mul_inv_cancel₀ (Real.exp_pos _).ne'
        congr 1
        linear_combination (gk k l * gT l) * hne
    _ = Tm M Ω (cbfc (R M Ω) hR (fun l => (gk k l : ℂ)) (x Ω)) := by
        rw [Tm_eq_bfc, ← cbfc_ofReal,
          ← mul_apply_eq_comp (cbfc (R M Ω) _ fun t => (gT t : ℂ))
            (cbfc (R M Ω) _ fun l => (gk k l : ℂ)) (x Ω),
          ← cbfc_mul _ _ (CBdd.ofReal bdd_gT) (CBdd.ofReal (bdd_gk hk))]
        congr 2
        funext l
        simp only [Pi.mul_apply, Complex.ofReal_mul]

/-! ## Left boundedness -/

/-- For `c ∈ M′` and `0 ≤ y ∈ M`: `⟪cΩ, y cΩ⟫ ≤ ‖c‖² ⟪Ω, yΩ⟫`. -/
theorem re_inner_commutant_apply_le {c y : K →L[ℂ] K} (hc' : c ∈ M.commutant) (hy : y ∈ M)
    (hy0 : 0 ≤ y) : (⟪c Ω, y (c Ω)⟫_ℂ).re ≤ ‖c‖ ^ 2 * (⟪Ω, y Ω⟫_ℂ).re := by
  obtain ⟨r, hr, hrs, hrr⟩ := exists_sqrt_mem M hy hy0
  have hcr : r * c = c * r := VonNeumannAlgebra.mem_commutant_iff.mp hc' r hr
  have h1 : (⟪c Ω, y (c Ω)⟫_ℂ).re = ‖c (r Ω)‖ ^ 2 := by
    rw [← hrr, mul_apply_eq_comp, inner_sa hrs, ← mul_apply_eq_comp, hcr, mul_apply_eq_comp]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  have h2 : (⟪Ω, y Ω⟫_ℂ).re = ‖r Ω‖ ^ 2 := by
    rw [← hrr, mul_apply_eq_comp, inner_sa hrs]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  rw [h1, h2]
  calc ‖c (r Ω)‖ ^ 2 ≤ (‖c‖ * ‖r Ω‖) ^ 2 := by gcongr; exact c.le_opNorm _
    _ = ‖c‖ ^ 2 * ‖r Ω‖ ^ 2 := by ring

include hs hc in
theorem norm_conjJm_le (G : K →L[ℂ] K) : ‖conjJm M Ω G‖ ≤ ‖G‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun ξ => ?_
  rw [conjJm_apply, norm_Jm_apply M Ω hs hc]
  calc ‖G (Jm M Ω ξ)‖ ≤ ‖G‖ * ‖Jm M Ω ξ‖ := G.le_opNorm _
    _ = ‖G‖ * ‖ξ‖ := by rw [norm_Jm_apply M Ω hs hc]

theorem inner_Ω_star_mul_mul (a y : K →L[ℂ] K) :
    ⟪Ω, (star a * y * a) Ω⟫_ℂ = ⟪a Ω, y (a Ω)⟫_ℂ := by
  rw [mul_apply_eq_comp, mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]

include hs hc in
/-- **HJX Lemma 2.5(i) for the smeared elements**: `ψ(x_k* y x_k) ≤ ‖x_k^♭‖² ψ(y)` for
`0 ≤ y ∈ M`. -/
theorem re_inner_xk_le {k : ℝ} (hk : 0 < k) {x y : K →L[ℂ] K} (hx : x ∈ M) (hy : y ∈ M)
    (hy0 : 0 ≤ y) :
    (⟪Ω, (star (xk M Ω k hk x) * y * xk M Ω k hk x) Ω⟫_ℂ).re ≤
      ‖xkFlat M Ω k hk x‖ ^ 2 * (⟪Ω, y Ω⟫_ℂ).re := by
  rw [inner_Ω_star_mul_mul]
  have hcΩ : conjJm M Ω (xkFlat M Ω k hk x) Ω = xk M Ω k hk x Ω := by
    rw [conjJm_apply, Jm_Ω M Ω hs hc, Jm_xkFlat_apply_Ω M Ω hs hc hk hx]
  rw [← hcΩ]
  refine (re_inner_commutant_apply_le M Ω
    (conjJm_mem_commutant M Ω hs hc (xkFlat_mem M Ω hs hc hk hx)) hy hy0).trans ?_
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (norm_conjJm_le M Ω hs hc _) 2)
    (Resolver.Douglas.re_inner_nonneg_of_nonneg hy0 Ω)

/-! ## Convergence `x_k Ω → xΩ` -/

theorem tendsto_gk (l : ℝ) :
    Tendsto (fun n : ℕ => ((gk ((n : ℝ) + 1) l : ℝ) : ℂ)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun n : ℕ => -(θ l) ^ 2 / (4 * ((n : ℝ) + 1))) atTop (𝓝 0) := by
    refine tendsto_const_nhds.div_atTop ?_
    exact (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).const_mul_atTop
      (by norm_num)
  have h2 : Tendsto (fun n : ℕ => gk ((n : ℝ) + 1) l) atTop (𝓝 1) := by
    have := (Real.continuous_exp.tendsto 0).comp h1
    rw [Real.exp_zero] at this
    exact this
  have := (Complex.continuous_ofReal.tendsto 1).comp h2
  rw [Complex.ofReal_one] at this
  exact this

/-- `x_k Ω → xΩ` along `k = n + 1 → ∞`: the smeared elements are `‖·‖_ψ`-dense. -/
theorem tendsto_xk_apply_Ω (x : K →L[ℂ] K) :
    Tendsto (fun n : ℕ => xk M Ω ((n : ℝ) + 1) (Nat.cast_add_one_pos n) x Ω) atTop
      (𝓝 (x Ω)) := by
  have hR := R_isSelfAdjoint M Ω
  have h : ∀ n : ℕ, xk M Ω ((n : ℝ) + 1) (Nat.cast_add_one_pos n) x Ω =
      cbfc (R M Ω) hR (fun l => ((gk ((n : ℝ) + 1) l : ℝ) : ℂ)) (x Ω) := fun n => by
    rw [xk_apply_Ω, cbfc_ofReal]
  simp only [h]
  have := tendsto_cbfc (R M Ω) hR (G := fun n : ℕ => fun l => ((gk ((n : ℝ) + 1) l : ℝ) : ℂ))
    (Ginf := fun _ => (1 : ℂ)) (l := atTop)
    (fun n => CBdd.ofReal (bdd_gk (Nat.cast_add_one_pos n))) CBdd.one (C := 1)
    (fun n l => by
      rw [Complex.norm_real, Real.norm_of_nonneg (gk_pos _ _).le]
      exact gk_le_one (Nat.cast_add_one_pos n) l)
    (fun _ => by simp) (fun l => tendsto_gk l) (x Ω)
  rwa [cbfc_one, one_apply_eq_self] at this

end Modular

end VN

end CommutingRepetition

/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Resolver/CfcIntegral.lean
-/
/-
# Integrals of continuous-functional-calculus families (node 1.2.6.3)

The one integral/CFC exchange used by the resolver corner: for a self-adjoint
`C` and a jointly continuous two-variable function `g`,

    ∫ u in α..T, cfc (g u) C = cfc (fun t => ∫ u in α..T, g u t) C.

Proof: `cfcL` is a continuous linear map `C(σ(C), ℝ) →L[ℝ] A`, Bochner
integrals commute with continuous linear maps
(`ContinuousLinearMap.intervalIntegral_comp_comm`), and evaluation at a point
commutes with `C(σ(C), ℝ)`-valued integrals (via `ContinuousMap.evalCLM`).

Corollaries (with `res`/`fib` of `Resolver/Resolvent.lean`, all for
`0 ≤ F`, `0 < α`, `0 < T`), by the fundamental theorem of calculus in ℝ:

* `∫ u in α..T, u • res F u = cfc (hfun α T) F`,
  `hfun α T t = (T − α) − t log(t+T) + t log(t+α)`;
* `∫ u in α..T, fib F u * fib F u = cfc (gfun α T) F`,
  `gfun α T t = t² ((t+α)⁻¹ − (t+T)⁻¹)`;

and the two-cutoff limits, as explicit norm bounds for `0 ≤ F ≤ 1`:

* `‖cfc (gfun α T) F − F‖ ≤ α + T⁻¹`;
* `cfc (hfun α T) F = (T − α) • 1 − log T • F + Ecorr α T F` with
  `‖Ecorr α T F + cfc negMulLog F‖ ≤ α + T⁻¹`.

Nothing here is a manuscript statement (proof-side helpers for node 1.2.6).
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Resolver.Resolvent

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace Resolver

open scoped BigOperators
open MeasureTheory intervalIntegral ContinuousMap

set_option linter.unusedSectionVars false

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-! ## The exchange theorem -/

/-- Parametrized `cfc` is continuous in the parameter wherever the two-variable
function is jointly continuous on `s × spectrum`. -/
theorem continuousOn_cfc_param {C : A} (hC : IsSelfAdjoint C) (g : ℝ → ℝ → ℝ) {s : Set ℝ}
    (hg : ContinuousOn (Function.uncurry g) (s ×ˢ spectrum ℝ C)) :
    ContinuousOn (fun u => cfc (g u) C) s := by
  have hG : ContinuousOn (fun u => mkD ((spectrum ℝ C).domRestrict (g u)) (0 : C(spectrum ℝ C, ℝ)))
      s := continuousOn_mkD_restrict_of_uncurry g 0 hg
  have : (fun u => cfc (g u) C)
      = fun u => cfcL hC (mkD ((spectrum ℝ C).domRestrict (g u)) (0 : C(spectrum ℝ C, ℝ))) := by
    funext u
    exact cfc_eq_cfcL_mkD (g u) C hC
  rw [this]
  exact (cfcL hC).continuous.comp_continuousOn hG

/-- **Integral/CFC exchange.** -/
theorem intervalIntegral_cfc {C : A} (hC : IsSelfAdjoint C) (g : ℝ → ℝ → ℝ) {α T : ℝ}
    (hg : ContinuousOn (Function.uncurry g) (Set.uIcc α T ×ˢ spectrum ℝ C)) :
    ∫ u in α..T, cfc (g u) C = cfc (fun t => ∫ u in α..T, g u t) C := by
  set G : ℝ → C(spectrum ℝ C, ℝ) :=
    fun u => mkD ((spectrum ℝ C).domRestrict (g u)) (0 : C(spectrum ℝ C, ℝ)) with hGdef
  have hGcont : ContinuousOn G (Set.uIcc α T) := continuousOn_mkD_restrict_of_uncurry g 0 hg
  have hGint : IntervalIntegrable G volume α T := hGcont.intervalIntegrable
  have hgu : ∀ u ∈ Set.uIcc α T, ContinuousOn (g u) (spectrum ℝ C) := fun u hu =>
    hg.comp (Continuous.prodMk_right u).continuousOn fun t ht => ⟨hu, ht⟩
  -- evaluation of the `C(σ, ℝ)`-valued integral
  have hval : ∀ t : spectrum ℝ C, (∫ u in α..T, G u) t = ∫ u in α..T, g u t := by
    intro t
    have h1 := (ContinuousLinearMap.intervalIntegral_comp_comm (evalCLM ℝ t) hGint).symm
    change (∫ u in α..T, G u) t = _
    rw [show (∫ u in α..T, G u) t = evalCLM ℝ t (∫ u in α..T, G u) from rfl, h1]
    refine integral_congr fun u hu => ?_
    show (G u) t = g u t
    simp only [hGdef]
    exact mkD_apply_of_continuousOn (hgu u hu)
  have hint : (∫ u in α..T, cfc (g u) C) = cfcL hC (∫ u in α..T, G u) := by
    have : (fun u => cfc (g u) C) = fun u => cfcL hC (G u) := by
      funext u; exact cfc_eq_cfcL_mkD (g u) C hC
    rw [this]
    exact ContinuousLinearMap.intervalIntegral_comp_comm _ hGint
  have hcont : ContinuousOn (fun t => ∫ u in α..T, g u t) (spectrum ℝ C) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : (spectrum ℝ C).domRestrict (fun t => ∫ u in α..T, g u t) = ⇑(∫ u in α..T, G u) := by
      funext t; exact (hval t).symm
    rw [this]; exact map_continuous _
  rw [hint, cfc_eq_cfcL hC hcont]
  congr 1
  ext t
  exact hval t

/-! ## Scalar integrals (fundamental theorem of calculus) -/

/-- Positivity of `t + u` on the relevant set. -/
theorem add_pos_of_mem_uIcc {t α T u : ℝ} (ht : 0 ≤ t) (hα : 0 < α) (hT : 0 < T)
    (hu : u ∈ Set.uIcc α T) : 0 < t + u :=
  add_pos_of_nonneg_of_pos ht (lt_of_lt_of_le (lt_min hα hT) hu.1)

/-- `∫ₐᵀ u/(t+u) du = (T − α) − t log(t+T) + t log(t+α)`. -/
theorem integral_smul_res_scalar {t α T : ℝ} (ht : 0 ≤ t) (hα : 0 < α) (hT : 0 < T) :
    ∫ u in α..T, u * (t + u)⁻¹ = (T - α) - t * Real.log (t + T) + t * Real.log (t + α) := by
  have hderiv : ∀ u ∈ Set.uIcc α T,
      HasDerivAt (fun u => u - t * Real.log (t + u)) (u * (t + u)⁻¹) u := by
    intro u hu
    have hpos := add_pos_of_mem_uIcc ht hα hT hu
    have hne : t + u ≠ 0 := hpos.ne'
    have h : HasDerivAt (fun u => u - t * Real.log (t + u)) (1 - t * (1 / (t + u))) u :=
      (hasDerivAt_id' u).sub ((((hasDerivAt_id' u).const_add t).log hne).const_mul t)
    exact h.congr_deriv (by linear_combination -(mul_inv_cancel₀ hne))
  have hint : IntervalIntegrable (fun u => u * (t + u)⁻¹) volume α T := by
    refine ContinuousOn.intervalIntegrable ?_
    refine (continuousOn_id' _).mul ((continuousOn_const.add (continuousOn_id' _)).inv₀ ?_)
    intro u hu
    exact (add_pos_of_mem_uIcc ht hα hT hu).ne'
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  ring

/-- `∫ₐᵀ (t/(t+u))² du = t² ((t+α)⁻¹ − (t+T)⁻¹)`. -/
theorem integral_fib_sq_scalar {t α T : ℝ} (ht : 0 ≤ t) (hα : 0 < α) (hT : 0 < T) :
    ∫ u in α..T, (t / (t + u)) * (t / (t + u)) = t ^ 2 * ((t + α)⁻¹ - (t + T)⁻¹) := by
  have hderiv : ∀ u ∈ Set.uIcc α T,
      HasDerivAt (fun u => -(t ^ 2) * (t + u)⁻¹) ((t / (t + u)) * (t / (t + u))) u := by
    intro u hu
    have hpos := add_pos_of_mem_uIcc ht hα hT hu
    have hne : t + u ≠ 0 := hpos.ne'
    have h : HasDerivAt (fun u => -(t ^ 2) * (t + u)⁻¹) (-(t ^ 2) * (-1 / (t + u) ^ 2)) u :=
      (((hasDerivAt_id' u).const_add t).inv hne).const_mul (-(t ^ 2))
    exact h.congr_deriv (by field_simp)
  have hint : IntervalIntegrable (fun u => (t / (t + u)) * (t / (t + u))) volume α T := by
    refine ContinuousOn.intervalIntegrable ?_
    have hc : ContinuousOn (fun u : ℝ => t / (t + u)) (Set.uIcc α T) := by
      refine continuousOn_const.div (continuousOn_const.add (continuousOn_id' _)) ?_
      intro u hu
      exact (add_pos_of_mem_uIcc ht hα hT hu).ne'
    exact hc.mul hc
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  ring

/-! ## Operator integrals of the resolvent family -/

/-- The antiderivative of `u ↦ u/(t+u)`: `(T − α) − t log(t+T) + t log(t+α)`. -/
noncomputable def hfun (α T t : ℝ) : ℝ := (T - α) - t * Real.log (t + T) + t * Real.log (t + α)

/-- The antiderivative of `u ↦ (t/(t+u))²`: `t² ((t+α)⁻¹ − (t+T)⁻¹)`. -/
noncomputable def gfun (α T t : ℝ) : ℝ := t ^ 2 * ((t + α)⁻¹ - (t + T)⁻¹)

/-- Joint continuity of `(u, t) ↦ u/(t+u)` on `[α, T] × spectrum`. -/
theorem continuousOn_uncurry_res {F : A} (hF0 : 0 ≤ F) {α T : ℝ} (hα : 0 < α) (hT : 0 < T) :
    ContinuousOn (Function.uncurry fun u t : ℝ => u * (t + u)⁻¹)
      (Set.uIcc α T ×ˢ spectrum ℝ F) := by
  refine continuousOn_fst.mul ((continuousOn_snd.add continuousOn_fst).inv₀ ?_)
  rintro ⟨u, t⟩ ⟨hu, ht⟩
  exact (add_pos_of_mem_uIcc (spectrum_nonneg hF0 ht) hα hT hu).ne'

/-- Joint continuity of `(u, t) ↦ t/(t+u)` on `[α, T] × spectrum`. -/
theorem continuousOn_uncurry_fib {F : A} (hF0 : 0 ≤ F) {α T : ℝ} (hα : 0 < α) (hT : 0 < T) :
    ContinuousOn (Function.uncurry fun u t : ℝ => t / (t + u))
      (Set.uIcc α T ×ˢ spectrum ℝ F) := by
  refine continuousOn_snd.div (continuousOn_snd.add continuousOn_fst) ?_
  rintro ⟨u, t⟩ ⟨hu, ht⟩
  exact (add_pos_of_mem_uIcc (spectrum_nonneg hF0 ht) hα hT hu).ne'

/-- `∫ₐᵀ u • res F u du = hfun α T (F)`. -/
theorem integral_smul_res {F : A} (hF0 : 0 ≤ F) {α T : ℝ} (hα : 0 < α) (hT : 0 < T) :
    ∫ u in α..T, u • res F u = cfc (hfun α T) F := by
  have hsa : IsSelfAdjoint F := IsSelfAdjoint.of_nonneg hF0
  have h1 : ∫ u in α..T, u • res F u = ∫ u in α..T, cfc (fun t => u * (t + u)⁻¹) F := by
    refine integral_congr fun u hu => ?_
    have hu0 : 0 < u := lt_of_lt_of_le (lt_min hα hT) hu.1
    unfold res
    exact (cfc_const_mul u _ F (continuousOn_res hF0 hu0)).symm
  rw [h1, intervalIntegral_cfc hsa (fun u t => u * (t + u)⁻¹) (continuousOn_uncurry_res hF0 hα hT)]
  refine cfc_congr fun t ht => ?_
  exact integral_smul_res_scalar (spectrum_nonneg hF0 ht) hα hT

/-- `∫ₐᵀ fib F u * fib F u du = gfun α T (F)`. -/
theorem integral_fib_mul_fib {F : A} (hF0 : 0 ≤ F) {α T : ℝ} (hα : 0 < α) (hT : 0 < T) :
    ∫ u in α..T, fib F u * fib F u = cfc (gfun α T) F := by
  have hsa : IsSelfAdjoint F := IsSelfAdjoint.of_nonneg hF0
  have h1 : ∫ u in α..T, fib F u * fib F u
      = ∫ u in α..T, cfc (fun t => (t / (t + u)) * (t / (t + u))) F := by
    refine integral_congr fun u hu => ?_
    have hu0 : 0 < u := lt_of_lt_of_le (lt_min hα hT) hu.1
    unfold fib
    exact (cfc_mul _ _ F (continuousOn_fib hF0 hu0) (continuousOn_fib hF0 hu0)).symm
  rw [h1, intervalIntegral_cfc hsa (fun u t => (t / (t + u)) * (t / (t + u))) ?_]
  · refine cfc_congr fun t ht => ?_
    exact integral_fib_sq_scalar (spectrum_nonneg hF0 ht) hα hT
  · have hc := continuousOn_uncurry_fib hF0 hα hT
    exact hc.mul hc

/-- Continuity of `u ↦ res F u` on `(0, ∞)`. -/
theorem continuousOn_res_param {F : A} (hF0 : 0 ≤ F) :
    ContinuousOn (fun u => res F u) (Set.Ioi 0) := by
  have hsa : IsSelfAdjoint F := IsSelfAdjoint.of_nonneg hF0
  refine continuousOn_cfc_param hsa (fun u t => (t + u)⁻¹) ?_
  refine (continuousOn_snd.add continuousOn_fst).inv₀ ?_
  rintro ⟨u, t⟩ ⟨hu, ht⟩
  exact (add_pos_of_nonneg_of_pos (spectrum_nonneg hF0 ht) hu).ne'

/-- Continuity of `u ↦ fib F u` on `(0, ∞)`. -/
theorem continuousOn_fib_param {F : A} (hF0 : 0 ≤ F) :
    ContinuousOn (fun u => fib F u) (Set.Ioi 0) := by
  have hsa : IsSelfAdjoint F := IsSelfAdjoint.of_nonneg hF0
  refine continuousOn_cfc_param hsa (fun u t => t / (t + u)) ?_
  refine continuousOn_snd.div (continuousOn_snd.add continuousOn_fst) ?_
  rintro ⟨u, t⟩ ⟨hu, ht⟩
  exact (add_pos_of_nonneg_of_pos (spectrum_nonneg hF0 ht) hu).ne'

/-! ## The two-cutoff limits as norm bounds -/

/-- Scalar bound: `|gfun α T t − t| ≤ α + T⁻¹` on `[0, 1]`. -/
theorem abs_gfun_sub_le {t α T : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hα : 0 < α) (hT : 0 < T) :
    |gfun α T t - t| ≤ α + T⁻¹ := by
  have hα' : 0 < t + α := by linarith
  have hT' : 0 < t + T := by linarith
  have e : gfun α T t - t = -(t * α / (t + α)) - t ^ 2 / (t + T) := by
    unfold gfun; field_simp; ring
  have h1 : 0 ≤ t * α / (t + α) := by positivity
  have h2 : t * α / (t + α) ≤ α := by
    rw [div_le_iff₀ hα']; nlinarith
  have h3 : 0 ≤ t ^ 2 / (t + T) := by positivity
  have h4 : t ^ 2 / (t + T) ≤ T⁻¹ := by
    rw [div_le_iff₀ hT', ← one_div, div_mul_eq_mul_div, one_mul, le_div_iff₀ hT]
    have ht2 : t ^ 2 * T ≤ 1 * T := mul_le_mul_of_nonneg_right (by nlinarith) hT.le
    linarith
  rw [e, abs_le]
  constructor <;> linarith

/-- `‖gfun α T (F) − F‖ ≤ α + T⁻¹` for a positive contraction `F`. -/
theorem norm_cfc_gfun_sub_le {F : A} (hF0 : 0 ≤ F) (hF1 : F ≤ 1) {α T : ℝ} (hα : 0 < α)
    (hT : 0 < T) : ‖cfc (gfun α T) F - F‖ ≤ α + T⁻¹ := by
  have hsa : IsSelfAdjoint F := IsSelfAdjoint.of_nonneg hF0
  have hg : ContinuousOn (gfun α T) (spectrum ℝ F) := by
    unfold gfun
    refine (continuousOn_pow 2).mul (ContinuousOn.sub ?_ ?_)
    · refine ((continuousOn_id' _).add continuousOn_const).inv₀ fun t ht => ?_
      exact (add_pos_of_nonneg_of_pos (spectrum_nonneg hF0 ht) hα).ne'
    · refine ((continuousOn_id' _).add continuousOn_const).inv₀ fun t ht => ?_
      exact (add_pos_of_nonneg_of_pos (spectrum_nonneg hF0 ht) hT).ne'
  have h : cfc (fun t => gfun α T t - t) F = cfc (gfun α T) F - F := by
    rw [cfc_sub (f := gfun α T) (g := fun t => t) (hf := hg) (hg := continuousOn_id' _),
      cfc_id' ℝ F hsa]
  rw [← h]
  refine norm_cfc_le (by positivity) fun t ht => ?_
  rw [Real.norm_eq_abs]
  exact abs_gfun_sub_le (spectrum_nonneg hF0 ht) (spectrum_le_one hF1 ht) hα hT

/-- The entropic correction: `t log(t+α) − t log(1 + t/T)` applied to `F`. -/
noncomputable def Ecorr (α T : ℝ) (F : A) : A :=
  cfc (fun t => t * Real.log (t + α)) F - cfc (fun t => t * Real.log (1 + t / T)) F

theorem continuousOn_mul_log_add {F : A} (hF0 : 0 ≤ F) {α : ℝ} (hα : 0 < α) :
    ContinuousOn (fun t => t * Real.log (t + α)) (spectrum ℝ F) := by
  refine (continuousOn_id' _).mul (((continuousOn_id' _).add continuousOn_const).log ?_)
  intro t ht
  exact (add_pos_of_nonneg_of_pos (spectrum_nonneg hF0 ht) hα).ne'

theorem continuousOn_mul_log_one_add_div {F : A} (hF0 : 0 ≤ F) {T : ℝ} (hT : 0 < T) :
    ContinuousOn (fun t => t * Real.log (1 + t / T)) (spectrum ℝ F) := by
  refine (continuousOn_id' _).mul
    ((continuousOn_const.add ((continuousOn_id' _).div_const T)).log ?_)
  intro t ht
  have := spectrum_nonneg hF0 ht
  have : 0 ≤ t / T := div_nonneg this hT.le
  show (1 : ℝ) + t / T ≠ 0
  exact (by linarith : (0 : ℝ) < 1 + t / T).ne'

/-- Decomposition of `hfun α T (F)` into its constant, linear and correction parts. -/
theorem cfc_hfun_eq {F : A} (hF0 : 0 ≤ F) {α T : ℝ} (hα : 0 < α) (hT : 0 < T) :
    cfc (hfun α T) F = (T - α) • (1 : A) - Real.log T • F + Ecorr α T F := by
  have hsa : IsSelfAdjoint F := IsSelfAdjoint.of_nonneg hF0
  have hlog : ∀ t ∈ spectrum ℝ F, Real.log (t + T) = Real.log T + Real.log (1 + t / T) := by
    intro t ht
    have ht0 := spectrum_nonneg hF0 ht
    have h1 : t + T = T * (1 + t / T) := by field_simp; ring
    rw [h1, Real.log_mul hT.ne' (by positivity)]
  have hc : ContinuousOn (fun t : ℝ => (T - α) - Real.log T * t) (spectrum ℝ F) :=
    continuousOn_const.sub (continuousOn_const.mul (continuousOn_id' _))
  have h1 : cfc (hfun α T) F
      = cfc (fun t => ((T - α) - Real.log T * t) - t * Real.log (1 + t / T)
          + t * Real.log (t + α)) F := by
    refine cfc_congr fun t ht => ?_
    unfold hfun
    rw [hlog t ht]
    ring
  rw [h1, cfc_add (f := fun t : ℝ => ((T - α) - Real.log T * t) - t * Real.log (1 + t / T))
      (g := fun t => t * Real.log (t + α))
      (hf := hc.sub (continuousOn_mul_log_one_add_div hF0 hT))
      (hg := continuousOn_mul_log_add hF0 hα),
    cfc_sub (f := fun t : ℝ => (T - α) - Real.log T * t) (g := fun t => t * Real.log (1 + t / T))
      (hf := hc) (hg := continuousOn_mul_log_one_add_div hF0 hT),
    cfc_sub (f := fun _ : ℝ => T - α) (g := fun t => Real.log T * t) (hf := continuousOn_const)
      (hg := continuousOn_const.mul (continuousOn_id' _)),
    cfc_const (T - α) F hsa, cfc_const_mul_id (Real.log T) F hsa, Algebra.algebraMap_eq_smul_one]
  unfold Ecorr
  abel

/-- Scalar bound for the entropic correction on `[0, 1]`:
`|t log(t+α) − t log(1+t/T) + negMulLog t| ≤ α + T⁻¹`. -/
theorem abs_ecorr_scalar_le {t α T : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hα : 0 < α) (hT : 0 < T) :
    |t * Real.log (t + α) - t * Real.log (1 + t / T) + Real.negMulLog t| ≤ α + T⁻¹ := by
  -- the `α`-term
  have hX : 0 ≤ t * Real.log (t + α) - t * Real.log t
      ∧ t * Real.log (t + α) - t * Real.log t ≤ α := by
    rcases ht0.lt_or_eq with ht | ht
    · have hq : 0 < (t + α) / t := by positivity
      have e : t * Real.log (t + α) - t * Real.log t = t * Real.log ((t + α) / t) := by
        rw [Real.log_div (by linarith) ht.ne']; ring
      rw [e]
      constructor
      · refine mul_nonneg ht0 (Real.log_nonneg ?_)
        rw [le_div_iff₀ ht]; linarith
      · have := Real.log_le_sub_one_of_pos hq
        have h2 : (t + α) / t - 1 = α / t := by field_simp; ring
        calc t * Real.log ((t + α) / t) ≤ t * (α / t) :=
              mul_le_mul_of_nonneg_left (by linarith) ht0
          _ = α := by field_simp
    · subst ht; simp [hα.le]
  -- the `T`-term
  have hY : 0 ≤ t * Real.log (1 + t / T) ∧ t * Real.log (1 + t / T) ≤ T⁻¹ := by
    have hq : 0 ≤ t / T := div_nonneg ht0 hT.le
    constructor
    · exact mul_nonneg ht0 (Real.log_nonneg (by linarith))
    · have := Real.log_le_sub_one_of_pos (show 0 < 1 + t / T by linarith)
      calc t * Real.log (1 + t / T) ≤ t * (t / T) :=
            mul_le_mul_of_nonneg_left (by linarith) ht0
        _ ≤ 1 / T := by
            rw [mul_div_assoc']
            exact div_le_div_of_nonneg_right (by nlinarith) hT.le
        _ = T⁻¹ := one_div T
  have e : t * Real.log (t + α) - t * Real.log (1 + t / T) + Real.negMulLog t
      = (t * Real.log (t + α) - t * Real.log t) - t * Real.log (1 + t / T) := by
    unfold Real.negMulLog; ring
  rw [e, abs_le]
  constructor <;> linarith [hX.1, hX.2, hY.1, hY.2]

/-- `‖Ecorr α T F + cfc negMulLog F‖ ≤ α + T⁻¹` for a positive contraction `F`. -/
theorem norm_Ecorr_add_le {F : A} (hF0 : 0 ≤ F) (hF1 : F ≤ 1) {α T : ℝ} (hα : 0 < α)
    (hT : 0 < T) : ‖Ecorr α T F + cfc Real.negMulLog F‖ ≤ α + T⁻¹ := by
  have h : cfc (fun t => t * Real.log (t + α) - t * Real.log (1 + t / T) + Real.negMulLog t) F
      = Ecorr α T F + cfc Real.negMulLog F := by
    rw [cfc_add (f := fun t => t * Real.log (t + α) - t * Real.log (1 + t / T))
        (g := Real.negMulLog)
        (hf := (continuousOn_mul_log_add hF0 hα).sub (continuousOn_mul_log_one_add_div hF0 hT))
        (hg := Real.continuous_negMulLog.continuousOn),
      cfc_sub (f := fun t => t * Real.log (t + α)) (g := fun t => t * Real.log (1 + t / T))
        (hf := continuousOn_mul_log_add hF0 hα) (hg := continuousOn_mul_log_one_add_div hF0 hT)]
    rfl
  rw [← h]
  refine norm_cfc_le (by positivity) fun t ht => ?_
  rw [Real.norm_eq_abs]
  exact abs_ecorr_scalar_le (spectrum_nonneg hF0 ht) (spectrum_le_one hF1 ht) hα hT

end Resolver

end CommutingRepetition

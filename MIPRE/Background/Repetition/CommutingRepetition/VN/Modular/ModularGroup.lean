/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/Modular/ModularGroup.lean
-/
/-
# The modular group `Δ^{it} = (2 − R)^{it} R^{-it}` (stage E4.2b; Rieffel–van Daele Def. 3.2)

With `R = P + Q` from `VN/Modular/ModularOperator.lean`, the modular group is
the bounded Borel function `λ ↦ ((2−λ)/λ)^{it} = exp(i t log((2−λ)/λ))` of `R`
(defined as `1` outside `(0,2)`, which carries no spectral mass since `R` and
`2 − R` are injective).  It is a strongly continuous one-parameter unitary
group fixing `Ω` and commuting with `R`.  Source: `PLAN-tomita.md` §0.1.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.ComplexBorel
import MIPRE.Background.Repetition.CommutingRepetition.VN.Modular.ModularOperator

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace VN

namespace Modular

open scoped InnerProductSpace ComplexConjugate
open Filter Topology BorelCalc

set_option linter.unusedSectionVars false

/-! ## The functions `λ ↦ ((2−λ)/λ)^{it}` -/

/-- `log((2−λ)/λ)` on `(0,2)`, `0` elsewhere. -/
noncomputable def θ (l : ℝ) : ℝ := if l ∈ Set.Ioo (0 : ℝ) 2 then Real.log ((2 - l) / l) else 0

theorem measurable_θ : Measurable θ := by
  unfold θ
  refine Measurable.ite measurableSet_Ioo ?_ measurable_const
  exact Real.measurable_log.comp ((measurable_const.sub measurable_id).div measurable_id)

theorem θ_one : θ 1 = 0 := by
  unfold θ
  rw [if_pos ⟨by norm_num, by norm_num⟩]
  norm_num

/-- `((2−λ)/λ)^{it} = exp(i t θ(λ))`. -/
noncomputable def gDel (t : ℝ) (l : ℝ) : ℂ := Complex.exp (((t * θ l : ℝ) : ℂ) * Complex.I)

theorem norm_gDel (t l : ℝ) : ‖gDel t l‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem measurable_gDel (t : ℝ) : Measurable (gDel t) := by
  unfold gDel
  exact Complex.measurable_exp.comp
    ((Complex.measurable_ofReal.comp (measurable_const.mul measurable_θ)).mul measurable_const)

theorem cbdd_gDel (t : ℝ) : CBdd (gDel t) :=
  ⟨measurable_gDel t, 1, fun l => (norm_gDel t l).le⟩

theorem gDel_zero : gDel 0 = fun _ => 1 := by
  funext l
  simp [gDel]

theorem gDel_add (s t : ℝ) : gDel (s + t) = gDel s * gDel t := by
  funext l
  simp only [gDel, Pi.mul_apply, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem gDel_neg (t : ℝ) : gDel (-t) = fun l => conj (gDel t l) := by
  funext l
  simp only [gDel, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

theorem gDel_apply_one (t : ℝ) : gDel t 1 = 1 := by
  simp [gDel, θ_one]

theorem continuous_gDel (l : ℝ) : Continuous fun t => gDel t l := by
  unfold gDel
  fun_prop

/-! ## The modular group -/

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (M : VonNeumannAlgebra K) (Ω : K)

/-- `Δ^{it} := ((2−R)/R)^{it}` (RvD Definition 3.2). -/
noncomputable def Δit (t : ℝ) : K →L[ℂ] K := cbfc (R M Ω) (R_isSelfAdjoint M Ω) (gDel t)

theorem Δit_zero : Δit M Ω 0 = 1 := by
  rw [Δit, gDel_zero, cbfc_one]

theorem Δit_add (s t : ℝ) : Δit M Ω (s + t) = Δit M Ω s * Δit M Ω t := by
  rw [Δit, gDel_add, cbfc_mul _ _ (cbdd_gDel s) (cbdd_gDel t)]
  rfl

theorem Δit_star (t : ℝ) : star (Δit M Ω t) = Δit M Ω (-t) := by
  rw [Δit, Δit, cbfc_star _ _ (cbdd_gDel t), gDel_neg]

theorem Δit_comm (s t : ℝ) : Δit M Ω s * Δit M Ω t = Δit M Ω t * Δit M Ω s := by
  rw [← Δit_add, ← Δit_add, add_comm]

theorem Δit_neg_mul (t : ℝ) : Δit M Ω (-t) * Δit M Ω t = 1 := by
  rw [← Δit_add, neg_add_cancel, Δit_zero]

theorem Δit_mul_neg (t : ℝ) : Δit M Ω t * Δit M Ω (-t) = 1 := by
  rw [← Δit_add, add_neg_cancel, Δit_zero]

theorem star_Δit_mul_self (t : ℝ) : star (Δit M Ω t) * Δit M Ω t = 1 := by
  rw [Δit_star, Δit_neg_mul]

theorem Δit_mul_star_self (t : ℝ) : Δit M Ω t * star (Δit M Ω t) = 1 := by
  rw [Δit_star, Δit_mul_neg]

/-- `Δ^{it} Ω = Ω` (`R Ω = Ω` and `((2−1)/1)^{it} = 1`). -/
theorem Δit_Ω (t : ℝ) : Δit M Ω t Ω = Ω := by
  have hΩ : R M Ω Ω = ((1 : ℝ) : ℂ) • Ω := by rw [R_Ω]; simp
  rw [Δit, cbfc_eigen _ _ (cbdd_gDel t) hΩ, gDel_apply_one, one_smul]

theorem norm_Δit_apply (t : ℝ) (ξ : K) : ‖Δit M Ω t ξ‖ = ‖ξ‖ := by
  refine (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp ?_
  rw [Δit, norm_sq_cbfc _ _ (cbdd_gDel t)]
  simp only [norm_gDel, one_pow, MeasureTheory.integral_const, smul_eq_mul, mul_one]
  exact ν_univ_real _ _ ξ

theorem norm_Δit_le (t : ℝ) : ‖Δit M Ω t‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun ξ => by rw [norm_Δit_apply, one_mul]

theorem Δit_commute_R (t : ℝ) : Commute (Δit M Ω t) (R M Ω) :=
  commute_cbfc _ _ (Commute.refl _) (cbdd_gDel t)

/-- Strong continuity of `t ↦ Δ^{it} ξ`. -/
theorem continuous_Δit_apply (ξ : K) : Continuous fun t => Δit M Ω t ξ := by
  rw [continuous_iff_continuousAt]
  intro s
  unfold ContinuousAt Δit
  exact tendsto_cbfc _ _ (fun t => cbdd_gDel t) (cbdd_gDel s) (C := 1)
    (fun t l => (norm_gDel t l).le) (fun l => (norm_gDel s l).le)
    (fun l => (continuous_gDel l).tendsto s) ξ

end Modular

end VN

end CommutingRepetition

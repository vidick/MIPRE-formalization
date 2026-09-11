/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/Crossed/AmpCalc.lean
-/
/-
# Amplification and the functional calculi (density stage E5.3, auxiliary)

`amp y = 1 ⊗ y` on `ℓ²(ℚ, K)` is a `*`-homomorphism; it commutes with the continuous functional
calculus (as a `StarAlgHom`) and, through the identification of spectral measures
`ν_{1⊗E}(ζ) = Σ_s ν_E(ζ s)`, with the bounded Borel calculi `bfc` and `cbfc`.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.Crossed.Space
import MIPRE.Background.Repetition.CommutingRepetition.VN.ComplexBorel

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace VN

namespace Crossed

open scoped InnerProductSpace ComplexConjugate CompactlySupported
open Filter Topology MeasureTheory BorelCalc

set_option linter.unusedSectionVars false

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ## `amp` as a `*`-homomorphism -/

theorem amp_zero : amp (0 : K →L[ℂ] K) = 0 := diag_zero

theorem amp_sub (y z : K →L[ℂ] K) : amp (y - z) = amp y - amp z := by
  rw [sub_eq_add_neg, amp_add, ← neg_one_smul ℂ z, amp_smul, neg_one_smul, sub_eq_add_neg]

theorem amp_isSelfAdjoint {E : K →L[ℂ] K} (hE : IsSelfAdjoint E) :
    IsSelfAdjoint (amp E : L2Q K →L[ℂ] L2Q K) := by
  show star _ = _
  rw [← amp_star, hE.star_eq]

theorem inner_amp_right (y : K →L[ℂ] K) (f g : L2Q K) :
    ⟪f, amp y g⟫_ℂ = ∑' s, ⟪f s, y (g s)⟫_ℂ :=
  inner_diag_right (IsBddFam.const y) f g

theorem summable_inner_amp_self (y : K →L[ℂ] K) (f : L2Q K) :
    Summable fun s => ⟪f s, y (f s)⟫_ℂ := by
  refine Summable.of_norm_bounded (g := fun s => ‖y‖ * ‖f s‖ ^ 2)
    ((summable_norm_sq f).mul_left ‖y‖) fun s => ?_
  calc ‖⟪f s, y (f s)⟫_ℂ‖ ≤ ‖f s‖ * ‖y (f s)‖ := norm_inner_le_norm _ _
    _ ≤ ‖f s‖ * (‖y‖ * ‖f s‖) := by gcongr; exact y.le_opNorm _
    _ = ‖y‖ * ‖f s‖ ^ 2 := by ring

/-- `amp` as a `*`-algebra homomorphism `B(K) → B(ℓ²(ℚ, K))`. -/
noncomputable def ampHom : (K →L[ℂ] K) →⋆ₐ[ℂ] (L2Q K →L[ℂ] L2Q K) where
  toFun := amp
  map_one' := amp_one
  map_mul' := amp_mul
  map_zero' := amp_zero
  map_add' := amp_add
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, amp_smul, amp_one]
  map_star' := amp_star

theorem ampHom_apply (y : K →L[ℂ] K) : ampHom (K := K) y = amp y := rfl

theorem continuous_ampHom : Continuous (ampHom (K := K)) :=
  AddMonoidHomClass.continuous_of_bound ampHom 1 fun y => by
    rw [one_mul]; exact norm_amp_le y

/-- Amplification commutes with the continuous functional calculus. -/
theorem amp_cfc {E : K →L[ℂ] K} (hE : IsSelfAdjoint E) {f : ℝ → ℝ} (hf : Continuous f) :
    amp (cfc f E) = cfc f (amp E) := by
  have := ampHom.map_cfc f E hf.continuousOn continuous_ampHom hE (amp_isSelfAdjoint hE)
  simpa only [ampHom_apply] using this

/-! ## Spectral measures of `1 ⊗ E` -/

variable {E : K →L[ℂ] K} (hE : IsSelfAdjoint E)

theorem ν_apply_univ (ξ : K) : ν E hE ξ Set.univ = ENNReal.ofReal (‖ξ‖ ^ 2) := by
  rw [← ν_univ_toReal E hE ξ, ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- `Σ_s ν_E(ζ s)` is a finite measure (of mass `‖ζ‖²`). -/
theorem isFiniteMeasure_sum_ν (ζ : L2Q K) :
    IsFiniteMeasure (Measure.sum fun s : ℚ => ν E hE (ζ s)) := by
  constructor
  rw [Measure.sum_apply _ MeasurableSet.univ]
  simp_rw [ν_apply_univ hE]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun s => sq_nonneg _) (summable_norm_sq ζ)]
  exact ENNReal.ofReal_lt_top

/-- The spectral measure of `1 ⊗ E` at `ζ` is `Σ_s ν_E(ζ s)`. -/
theorem ν_amp (ζ : L2Q K) :
    ν (amp E) (amp_isSelfAdjoint hE) ζ = Measure.sum fun s : ℚ => ν E hE (ζ s) := by
  have := isFiniteMeasure_sum_ν hE ζ
  refine Measure.ext_of_integral_eq_on_compactlySupported fun f => ?_
  have hf : Bdd f := Bdd.of_compactlySupported f
  have h1 : ∫ x, f x ∂ν (amp E) (amp_isSelfAdjoint hE) ζ = (⟪ζ, amp (cfc f E) ζ⟫_ℂ).re := by
    rw [integral_ν _ _ _ (map_continuous f), amp_cfc hE (map_continuous f)]
    rfl
  rw [integral_sum_measure (hf.integrable _), h1, inner_amp_right,
    Complex.re_tsum (summable_inner_amp_self _ _)]
  congr 1
  funext s
  rw [integral_ν E hE _ (map_continuous f)]

/-- Amplification commutes with the bounded Borel calculus. -/
theorem amp_bfc {g : ℝ → ℝ} (hg : Bdd g) :
    amp (bfc E hE g) = bfc (amp E) (amp_isSelfAdjoint hE) g := by
  refine ext_of_inner_self fun ζ => ?_
  have := isFiniteMeasure_sum_ν hE ζ
  rw [inner_bfc_self _ _ hg, inner_amp_right]
  simp only [Q]
  rw [ν_amp hE, integral_sum_measure (hg.integrable _), Complex.ofReal_tsum]
  congr 1
  funext s
  rw [inner_bfc_self E hE hg]
  simp only [Q]

/-- Amplification commutes with the complex bounded Borel calculus. -/
theorem amp_cbfc {G : ℝ → ℂ} (hG : CBdd G) :
    amp (cbfc E hE G) = cbfc (amp E) (amp_isSelfAdjoint hE) G := by
  unfold cbfc
  rw [amp_add, amp_smul, amp_bfc hE hG.re, amp_bfc hE hG.im]

end Crossed

end VN

end CommutingRepetition

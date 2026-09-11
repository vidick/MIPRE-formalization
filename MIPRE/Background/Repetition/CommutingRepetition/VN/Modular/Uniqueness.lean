/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/Modular/Uniqueness.lean
-/
/-
# Modular data are determined by the standard subspace (density stage E5.1)

For `(M, Ω)` with `Ω` cyclic and separating, the real projection `P` onto `𝒦 = closure(M_s Ω)`
satisfies `2P = R + A` with `A = P − Q = T J` (conjugate-linear), and `2Q = R − A`. Hence any
pair `(R̃, A)` of a complex-linear and a conjugate-linear operator such that `(R̃ + A)/2` is
the identity on `𝒦` and vanishes on `𝒦^⊥` must be `(R, A)`: this is the tool that identifies
the modular operator of the dual state on a crossed product (E5.3) and of a perturbed vector
(E6.2) without computing projections onto graphs.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.Modular.PolarJ

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace VN

namespace Modular

open scoped InnerProductSpace ComplexConjugate
open ClosedSubmodule

set_option linter.unusedSectionVars false

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (M : VonNeumannAlgebra K) (Ω : K)

theorem two_smul_Pre (ξ : K) : (2 : ℂ) • Pre M Ω ξ = R M Ω ξ + Am M Ω ξ := by
  rw [R_apply, Am_apply, two_smul]; abel

theorem two_smul_Qre (ξ : K) : (2 : ℂ) • Qre M Ω ξ = R M Ω ξ - Am M Ω ξ := by
  rw [R_apply, Am_apply, two_smul]; abel

theorem sub_Pre_mem_orthogonal (ξ : K) : ξ - Pre M Ω ξ ∈ ((Kre M Ω).toSubmodule)ᗮ := by
  rw [← Pre_eq_zero_iff, map_sub, Pre_Pre, sub_self]

/-- **Uniqueness of the modular data.** If `R̃` is complex-linear, `A` conjugate-linear,
`(R̃ + A)/2` is the identity on `𝒦` and vanishes on `𝒦^⊥`, then `R̃ = R` and `A = P − Q`. -/
theorem R_eq_of_proj (R' : K →L[ℂ] K) (A : K →SL[starRingEnd ℂ] K)
    (hfix : ∀ ξ ∈ Kre M Ω, R' ξ + A ξ = (2 : ℂ) • ξ)
    (hker : ∀ ξ ∈ ((Kre M Ω).toSubmodule)ᗮ, R' ξ + A ξ = 0) :
    R' = R M Ω ∧ ∀ ξ, A ξ = Am M Ω ξ := by
  -- `(R' + A) ξ = 2 P ξ` for all `ξ`
  have hP : ∀ ξ, R' ξ + A ξ = (2 : ℂ) • Pre M Ω ξ := by
    intro ξ
    have h1 := hfix (Pre M Ω ξ) (Pre_apply_mem M Ω ξ)
    have h2 := hker (ξ - Pre M Ω ξ) (sub_Pre_mem_orthogonal M Ω ξ)
    rw [map_sub, map_sub] at h2
    have : R' ξ + A ξ = (R' (Pre M Ω ξ) + A (Pre M Ω ξ)) +
        ((R' ξ - R' (Pre M Ω ξ)) + (A ξ - A (Pre M Ω ξ))) := by abel
    rw [this, h1, h2, add_zero]
  -- `(R' − A) ξ = 2 Q ξ`, from `Q ξ = i P(−i ξ)`
  have hQ : ∀ ξ, R' ξ - A ξ = (2 : ℂ) • Qre M Ω ξ := by
    intro ξ
    have h := hP ((-Complex.I) • ξ)
    rw [map_smul, map_smulₛₗ, starRingEnd_apply, star_neg, Complex.star_def, Complex.conj_I,
      neg_neg] at h
    have h' := congrArg (fun v => Complex.I • v) h
    simp only [smul_add, smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul] at h'
    rw [Qre_eq, smul_smul, mul_comm, ← h', neg_one_smul, sub_eq_add_neg]
  refine ⟨?_, fun ξ => ?_⟩
  · ext ξ
    have := congrArg₂ (· + ·) (hP ξ) (hQ ξ)
    simp only [two_smul_Pre, two_smul_Qre] at this
    have h2 : (2 : ℂ) • R' ξ = (2 : ℂ) • R M Ω ξ := by
      rw [two_smul, two_smul]
      calc R' ξ + R' ξ = (R' ξ + A ξ) + (R' ξ - A ξ) := by abel
        _ = (R M Ω ξ + Am M Ω ξ) + (R M Ω ξ - Am M Ω ξ) := this
        _ = R M Ω ξ + R M Ω ξ := by abel
    exact smul_right_injective K (two_ne_zero) h2
  · have := congrArg₂ (· - ·) (hP ξ) (hQ ξ)
    simp only [two_smul_Pre, two_smul_Qre] at this
    have h2 : (2 : ℂ) • A ξ = (2 : ℂ) • Am M Ω ξ := by
      rw [two_smul, two_smul]
      calc A ξ + A ξ = (R' ξ + A ξ) - (R' ξ - A ξ) := by abel
        _ = (R M Ω ξ + Am M Ω ξ) - (R M Ω ξ - Am M Ω ξ) := this
        _ = Am M Ω ξ + Am M Ω ξ := by abel
    exact smul_right_injective K (two_ne_zero) h2

variable (hs : IsSeparating (M : Set (K →L[ℂ] K)) Ω) (hc : IsCyclic (M : Set (K →L[ℂ] K)) Ω)

include hs hc in
/-- With `A = T̃ J̃`: also `J̃ = J` once `T̃ = T`. -/
theorem Jm_eq_of_proj (J' : K →SL[starRingEnd ℂ] K)
    (hfix : ∀ ξ ∈ Kre M Ω, R M Ω ξ + Tm M Ω (J' ξ) = (2 : ℂ) • ξ)
    (hker : ∀ ξ ∈ ((Kre M Ω).toSubmodule)ᗮ, R M Ω ξ + Tm M Ω (J' ξ) = 0) (ξ : K) :
    J' ξ = Jm M Ω ξ := by
  have h := (R_eq_of_proj M Ω (R M Ω) ((Tm M Ω).comp J') hfix hker).2 ξ
  rw [ContinuousLinearMap.comp_apply, ← Tm_Jm M Ω hs hc] at h
  exact sub_eq_zero.mp ((Tm_eq_zero_iff M Ω hs hc).mp (by rw [map_sub, h, sub_self]))

end Modular

end VN

end CommutingRepetition

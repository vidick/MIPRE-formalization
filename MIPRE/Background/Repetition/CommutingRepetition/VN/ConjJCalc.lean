/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/ConjJCalc.lean
-/
/-
# Conjugation by `J` and the functional calculus (WP-B7, stage F)

`G ↦ J G J` is a continuous real star-algebra homomorphism of `B(L²(M))`
(conjugate-linear over `ℂ`), so it commutes with the real continuous functional
calculus of self-adjoint operators, hence with the spectral measures, the Borel
calculus and the spectral projections of `VN/BorelCalculus`,
`VN/SpectralProjection`. Used in stage G to identify the right modulus
`J E_y J` with the left one: `g(J E J) = J g(E) J`, `1_I(J E J) = J 1_I(E) J`.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.SpectralProjection
import MIPRE.Background.Repetition.CommutingRepetition.VN.Commutation

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

open scoped InnerProductSpace ComplexConjugate
open MeasureTheory BorelCalc

namespace StdTracialAlgebra

universe u

variable (M : StdTracialAlgebra.{u})

theorem inner_J_right (v w : M.H) : ⟪v, M.J w⟫_ℂ = conj ⟪M.J v, w⟫_ℂ := by
  rw [← inner_conj_symm, M.inner_J_left]

theorem inner_conjJ (G : M.H →L[ℂ] M.H) (ξ η : M.H) :
    ⟪ξ, M.conjJ G η⟫_ℂ = conj ⟪M.J ξ, G (M.J η)⟫_ℂ := by
  rw [conjJ_apply, M.inner_J_right]

theorem conjJ_conjJ (G : M.H →L[ℂ] M.H) : M.conjJ (M.conjJ G) = G := by
  ext v
  rw [conjJ_apply, conjJ_apply, M.J_J, M.J_J]

theorem conjJ_zero : M.conjJ 0 = 0 := by
  ext v
  rw [conjJ_apply, zero_apply, zero_apply, map_zero]

theorem conjJ_add (G G' : M.H →L[ℂ] M.H) : M.conjJ (G + G') = M.conjJ G + M.conjJ G' := by
  ext v
  rw [conjJ_apply, add_apply, add_apply, map_add,
    conjJ_apply, conjJ_apply]

theorem conjJ_mul (G G' : M.H →L[ℂ] M.H) : M.conjJ (G * G') = M.conjJ G * M.conjJ G' := by
  ext v
  rw [conjJ_apply, mul_apply_eq_comp, mul_apply_eq_comp, conjJ_apply,
    conjJ_apply, M.J_J]

theorem conjJ_real_smul (c : ℝ) (G : M.H →L[ℂ] M.H) : M.conjJ (c • G) = c • M.conjJ G := by
  ext v
  have e1 : ∀ w : M.H, c • w = (c : ℂ) • w := fun w =>
    @RCLike.real_smul_eq_coe_smul ℂ M.H _ _ _ _ _ c w
  rw [conjJ_apply, smul_apply, e1, map_smulₛₗ, Complex.conj_ofReal,
    smul_apply, conjJ_apply, e1]

theorem conjJ_star (G : M.H →L[ℂ] M.H) : M.conjJ (star G) = star (M.conjJ G) := by
  refine BorelCalc.ext_of_inner fun ξ η => ?_
  rw [M.inner_conjJ, ContinuousLinearMap.star_eq_adjoint G,
    ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.star_eq_adjoint (M.conjJ G),
    ContinuousLinearMap.adjoint_inner_right, conjJ_apply, M.inner_J_left, ← inner_conj_symm,
    Complex.conj_conj]

theorem conjJ_isSelfAdjoint {E : M.H →L[ℂ] M.H} (hE : IsSelfAdjoint E) :
    IsSelfAdjoint (M.conjJ E) := by
  show star (M.conjJ E) = M.conjJ E
  rw [← M.conjJ_star, hE.star_eq]

/-- `G ↦ J G J` as a unital real star-algebra homomorphism. -/
noncomputable def conjJHom : (M.H →L[ℂ] M.H) →⋆ₐ[ℝ] (M.H →L[ℂ] M.H) where
  toFun := M.conjJ
  map_one' := M.conjJ_one
  map_mul' := M.conjJ_mul
  map_zero' := M.conjJ_zero
  map_add' := M.conjJ_add
  commutes' := fun r => by
    rw [Algebra.algebraMap_eq_smul_one, M.conjJ_real_smul, M.conjJ_one]
  map_star' := M.conjJ_star

theorem conjJHom_apply (G : M.H →L[ℂ] M.H) : M.conjJHom G = M.conjJ G := rfl

theorem norm_conjJ_le (G : M.H →L[ℂ] M.H) : ‖M.conjJ G‖ ≤ ‖G‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => by
    rw [conjJ_apply, M.norm_J]
    calc ‖G (M.J v)‖ ≤ ‖G‖ * ‖M.J v‖ := G.le_opNorm _
      _ = ‖G‖ * ‖v‖ := by rw [M.norm_J]

theorem continuous_conjJHom : Continuous M.conjJHom :=
  AddMonoidHomClass.continuous_of_bound M.conjJHom 1 fun G => by
    rw [one_mul]; exact M.norm_conjJ_le G

/-- Conjugation by `J` commutes with the real continuous functional calculus. -/
theorem conjJ_cfc {E : M.H →L[ℂ] M.H} (hE : IsSelfAdjoint E) {f : ℝ → ℝ} (hf : Continuous f) :
    M.conjJ (cfc f E) = cfc f (M.conjJ E) :=
  M.conjJHom.map_cfc f E hf.continuousOn M.continuous_conjJHom hE (M.conjJ_isSelfAdjoint hE)

/-- The spectral measure of `J E J` at `ξ` is the spectral measure of `E` at `J ξ`. -/
theorem ν_conjJ {E : M.H →L[ℂ] M.H} (hE : IsSelfAdjoint E) (ξ : M.H) :
    ν (M.conjJ E) (M.conjJ_isSelfAdjoint hE) ξ = ν E hE (M.J ξ) := by
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  rw [integral_ν _ _ _ f.continuous, integral_ν _ _ _ f.continuous, ← M.conjJ_cfc hE f.continuous,
    M.inner_conjJ, Complex.conj_re]

/-- Conjugation by `J` commutes with the Borel functional calculus. -/
theorem bfc_conjJ {E : M.H →L[ℂ] M.H} (hE : IsSelfAdjoint E) (g : ℝ → ℝ) :
    bfc (M.conjJ E) (M.conjJ_isSelfAdjoint hE) g = M.conjJ (bfc E hE g) := by
  by_cases hg : Bdd g
  · refine ext_of_inner_self fun ξ => ?_
    rw [inner_bfc_self _ _ hg, M.inner_conjJ, inner_bfc_self _ _ hg, Q, Q, M.ν_conjJ hE,
      Complex.conj_ofReal]
  · rw [bfc_of_not _ _ hg, bfc_of_not _ _ hg, M.conjJ_zero]

/-- Conjugation by `J` commutes with the spectral projections. -/
theorem P_conjJ {E : M.H →L[ℂ] M.H} (hE : IsSelfAdjoint E) (I : Set ℝ) :
    P (M.conjJ E) (M.conjJ_isSelfAdjoint hE) I = M.conjJ (P E hE I) :=
  M.bfc_conjJ hE _

theorem conjJ_apply_traceVector {T : M.H →L[ℂ] M.H} (hT : T ∈ M.vnAlg) :
    M.conjJ T M.traceVector = star T M.traceVector := by
  rw [conjJ_apply, M.J_traceVector, M.J_apply_traceVector hT]

theorem conjJ_apply_traceVector_of_sa {T : M.H →L[ℂ] M.H} (hT : T ∈ M.vnAlg)
    (hsa : IsSelfAdjoint T) : M.conjJ T M.traceVector = T M.traceVector := by
  rw [M.conjJ_apply_traceVector hT, hsa.star_eq]

end StdTracialAlgebra

end CommutingRepetition

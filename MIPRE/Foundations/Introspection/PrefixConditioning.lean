/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.PrefixLaw
public import MIPRE.Foundations.Introspection.AdaptivePrefixFactor

@[expose] public section

/-! # Concrete adaptive prefix conditioning

The used and remaining coordinates are those selected by the actual CL
prefix. A residual operator is embedded with the concrete prefix projector.
Its ambient squared error is exactly the actual prefix weight times its
error on the remaining EPR register and the original auxiliary state.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): a residual operator is a block
matrix over the remaining register with entries in any algebra, the prefix projector enters as
`smulKron M (prefixProjector P k y)`, and the split is `regSplitHom (ambientSplit _)`; the exact
error identity is the local isometry `regSplit` followed by `stateSqNorm_expand_smulKron`.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical Honest
open scoped Kronecker
set_option linter.unusedSectionVars false

/-- The honest identity on the remaining register and the auxiliary algebra, split off a register
operator `Q`, is `Q ⊗ 1` read along the split. -/
theorem registerParty_kron_one {I J R 𝒜 : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype R] [DecidableEq R] [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜]
    (e : I ≃ J × R) (Q : Matrix J J ℂ) :
    regSplitHom e (smulKron (1 : Matrix R R 𝒜) Q) =
      smulKron (1 : 𝒜) (registerOp e (Q ⊗ₖ (1 : Matrix R R ℂ))) := by
  ext i i'
  simp only [regSplitHom_apply, smulKron_apply, registerOp_apply, Matrix.kroneckerMap_apply,
    Matrix.smul_apply]
  by_cases hr : (e i).2 = (e i').2
  · rw [hr, Matrix.one_apply_eq, Matrix.one_apply_eq, mul_one]
  · rw [Matrix.one_apply_ne hr, Matrix.one_apply_ne hr, mul_zero, zero_smul, smul_zero]

variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

/-- The probability of the local used-register projector is precisely the
uniform CL prefix probability, with no conditional normalization premise. -/
theorem prefixProjector_weight (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (y : ι → F) :
    stateSqNorm (registerEPR (CLChecks.prefixRegister P k y → F)) (prefixProjector P k y) =
      prefixWeight P k y := by
  have hw := hidingPrefixOp_weight P k y
  rw [hidingPrefixOp_factor P hP k y] at hw
  let e := ambientSplit (F := F) (CLChecks.prefixRegister P k y)
  have he : registerEPR (ι → F) =
      expVec (registerEPR (CLChecks.prefixRegister P k y → F))
        (registerEPR (↥((CLChecks.prefixRegister P k y)ᶜ) → F)) ∘ e.prodCongr e := by
    rw [← registerEPR_prod]
    exact (registerEPR_equiv e).symm
  rw [he, stateSqNorm_registerOp, stateSqNorm_expVec_kron, stateSqNorm_one_eq,
    registerEPR_norm, one_pow, mul_one] at hw
  exact hw

section Residual

variable {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜]

/-- Reinsert a residual operator behind its actual adaptive prefix projector. -/
def prefixResidualOp (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F)
    (M : Matrix (↥((CLChecks.prefixRegister P k y)ᶜ) → F)
      (↥((CLChecks.prefixRegister P k y)ᶜ) → F) 𝒜) :
    Matrix (ι → F) (ι → F) 𝒜 :=
  regSplitHom (ambientSplit (CLChecks.prefixRegister P k y)) (smulKron M (prefixProjector P k y))

/-- The normalizer of the reinserted residual family is exactly the ambient
honest prefix projector. -/
theorem prefixResidualOp_one (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (y : ι → F) :
    prefixResidualOp (𝒜 := 𝒜) P k y 1 = smulKron (1 : 𝒜) (hidingPrefixOp P k (some y)) := by
  rw [hidingPrefixOp_factor P hP k y]
  exact registerParty_kron_one _ _

theorem prefixProjector_eq_zero (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F)
    (hy : y ∉ prefixOutcomes P k) : prefixProjector P k y = 0 := by
  have hf (u : CLChecks.prefixRegister P k y → F) :
      (P.truncate k).eval (insertRegister (CLChecks.prefixRegister P k y) u) ≠ y := by
    intro he
    apply hy
    exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, he⟩
  ext i j
  simp [prefixProjector, readout, hf]

theorem prefixResidualOp_eq_zero (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F)
    (hy : y ∉ prefixOutcomes P k)
    (M : Matrix (↥((CLChecks.prefixRegister P k y)ᶜ) → F) _ 𝒜) :
    prefixResidualOp P k y M = 0 := by
  rw [prefixResidualOp, prefixProjector_eq_zero P k y hy, smulKron_zero_right, map_zero]

theorem prefixResidualOp_sum (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F)
    {A : Type*} [Fintype A]
    (M : A → Matrix (↥((CLChecks.prefixRegister P k y)ᶜ) → F) _ 𝒜) :
    prefixResidualOp P k y (∑ a, M a) = ∑ a, prefixResidualOp P k y (M a) := by
  rw [prefixResidualOp, smulKron_sum_left, map_sum]
  rfl

theorem prefixResidualOp_sub (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F)
    (M N : Matrix (↥((CLChecks.prefixRegister P k y)ᶜ) → F) _ 𝒜) :
    prefixResidualOp P k y (M - N) = prefixResidualOp P k y M - prefixResidualOp P k y N := by
  rw [prefixResidualOp, prefixResidualOp, prefixResidualOp, ← map_sub, smulKron_sub_left]

theorem prefixResidualOp_mul (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F)
    (M N : Matrix (↥((CLChecks.prefixRegister P k y)ᶜ) → F) _ 𝒜) :
    prefixResidualOp P k y (M * N) = prefixResidualOp P k y M * prefixResidualOp P k y N := by
  rw [prefixResidualOp, prefixResidualOp, prefixResidualOp, ← map_mul, smulKron_mul]
  have hi : prefixProjector P k y * prefixProjector P k y = prefixProjector P k y :=
    (readout_isPVM _).idem y
  rw [hi]

variable {𝒞 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [StarModule ℂ 𝒜] [Ring ℬ]
  [StarRing ℬ] [Algebra ℂ ℬ] (Ξ : BipartiteModel 𝒞 𝒜 ℬ)

/-- Exact conditional error, on the concrete complement of the used prefix
register. It holds for every prefix, including impossible ones of weight zero. -/
theorem stateSqNorm_prefixResidualOp (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (y : ι → F)
    (M : Matrix (↥((CLChecks.prefixRegister P k y)ᶜ) → F) _ 𝒜) :
    (Ξ.reg (ι → F)).stateSqNorm (prefixResidualOp P k y M) =
      prefixWeight P k y *
        (Ξ.reg (↥((CLChecks.prefixRegister P k y)ᶜ) → F)).stateSqNorm M := by
  have h := BipartiteModel.LocalIsometry.stateSqNorm_of_W_ψ
    (Ξ.regSplit_W_ψ (ambientSplit (CLChecks.prefixRegister P k y)))
    (smulKron M (prefixProjector P k y))
  rw [BipartiteModel.regSplit_ΦA_eq] at h
  rw [prefixResidualOp, h, stateSqNorm_expand_smulKron, prefixProjector_weight P hP k y]

/-- Auxiliary registers do not change the prefix distribution. -/
theorem hidingPrefixOp_registerState_weight (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (y : ι → F) (hΞ : ‖Ξ.ψ‖ = 1) :
    (Ξ.reg (ι → F)).stateSqNorm (smulKron (1 : 𝒜) (hidingPrefixOp P k (some y))) =
      prefixWeight P k y := by
  rw [← prefixResidualOp_one P hP k y, stateSqNorm_prefixResidualOp Ξ P hP,
    stateSqNorm_one_of_norm _ (by rw [BipartiteModel.norm_reg_ψ, hΞ]), mul_one]

theorem prefixResidual_distance (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (y : ι → F)
    (M N : Matrix (↥((CLChecks.prefixRegister P k y)ᶜ) → F) _ 𝒜) :
    (Ξ.reg (ι → F)).stateSqNorm
      (prefixResidualOp P k y M - prefixResidualOp P k y N) =
      prefixWeight P k y *
        (Ξ.reg (↥((CLChecks.prefixRegister P k y)ᶜ) → F)).stateSqNorm (M - N) := by
  rw [← prefixResidualOp_sub, stateSqNorm_prefixResidualOp Ξ P hP]

theorem prefixResidual_commutator (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (y : ι → F)
    (M N : Matrix (↥((CLChecks.prefixRegister P k y)ᶜ) → F) _ 𝒜) :
    (Ξ.reg (ι → F)).stateSqNorm
      (prefixResidualOp P k y M * prefixResidualOp P k y N -
        prefixResidualOp P k y N * prefixResidualOp P k y M) =
      prefixWeight P k y *
        (Ξ.reg (↥((CLChecks.prefixRegister P k y)ᶜ) → F)).stateSqNorm (M * N - N * M) := by
  rw [← prefixResidualOp_mul, ← prefixResidualOp_mul, prefixResidual_distance Ξ P hP]

/-- Full-carrier errors are exactly weighted residual errors under the actual
CL prefix law. The residual outcome alphabet may itself depend on the prefix. -/
theorem prefixResidual_distance_sum (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) {A : (ι → F) → Type*} [∀ y, Fintype (A y)]
    (M N : (y : ι → F) → A y →
      Matrix (↥((CLChecks.prefixRegister P k y)ᶜ) → F) _ 𝒜) :
    (∑ y, ∑ a, (Ξ.reg (ι → F)).stateSqNorm
      (prefixResidualOp P k y (M y a) - prefixResidualOp P k y (N y a))) =
      ∑ y, prefixWeight P k y * ∑ a,
        (Ξ.reg (↥((CLChecks.prefixRegister P k y)ᶜ) → F)).stateSqNorm (M y a - N y a) := by
  simp_rw [prefixResidual_distance Ξ P hP, Finset.mul_sum]

theorem prefixResidual_commutator_sum (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) {A B : (ι → F) → Type*}
    [∀ y, Fintype (A y)] [∀ y, Fintype (B y)]
    (M : (y : ι → F) → A y →
      Matrix (↥((CLChecks.prefixRegister P k y)ᶜ) → F) _ 𝒜)
    (N : (y : ι → F) → B y →
      Matrix (↥((CLChecks.prefixRegister P k y)ᶜ) → F) _ 𝒜) :
    (∑ y, ∑ a, ∑ b, (Ξ.reg (ι → F)).stateSqNorm
      (prefixResidualOp P k y (M y a) * prefixResidualOp P k y (N y b) -
        prefixResidualOp P k y (N y b) * prefixResidualOp P k y (M y a))) =
      ∑ y, prefixWeight P k y * ∑ a, ∑ b,
        (Ξ.reg (↥((CLChecks.prefixRegister P k y)ᶜ) → F)).stateSqNorm
          (M y a * N y b - N y b * M y a) := by
  simp_rw [prefixResidual_commutator Ξ P hP, Finset.mul_sum]

end Residual

end MIPRE.Introspection

end

end

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.PrefixLaw
import MIPRE.Foundations.Introspection.AdaptivePrefixFactor

/-! # Concrete adaptive prefix conditioning

The used and remaining coordinates are those selected by the actual CL
prefix. A residual operator is embedded with the concrete prefix projector.
Its ambient squared error is exactly the actual prefix weight times its
error on the remaining EPR register and the original auxiliary state.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical Honest
open scoped Kronecker
set_option linter.unusedSectionVars false

theorem registerParty_kron_one {I J R H : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype R] [DecidableEq R] [Fintype H] [DecidableEq H]
    (e : I ≃ J × R) (Q : Matrix J J ℂ) :
    registerOp (registerParty e H) (Q ⊗ₖ (1 : Matrix (R × H) (R × H) ℂ)) =
      (aOp (registerOp e (Q ⊗ₖ (1 : Matrix R R ℂ))) : Matrix (I × H) _ ℂ) := by
  ext ⟨i, h⟩ ⟨j, h'⟩
  simp only [registerOp_apply, registerParty, Equiv.trans_apply, Equiv.prodCongr_apply,
    Equiv.prodAssoc_apply, aOp, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Prod.mk.injEq]
  by_cases hr : (e i).2 = (e j).2 <;> by_cases hh : h = h' <;> simp [hr, hh]

variable {F ι H K : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype ι] [DecidableEq ι]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}

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

/-- Reinsert a residual operator behind its actual adaptive prefix projector. -/
def prefixResidualOp (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F)
    (M : Matrix ((↥((CLChecks.prefixRegister P k y)ᶜ) → F) × H)
      ((↥((CLChecks.prefixRegister P k y)ᶜ) → F) × H) ℂ) :
    Matrix ((ι → F) × H) ((ι → F) × H) ℂ :=
  registerOp (registerParty (ambientSplit (CLChecks.prefixRegister P k y)) H)
    (prefixProjector P k y ⊗ₖ M)

/-- The normalizer of the reinserted residual family is exactly the ambient
honest prefix projector. -/
theorem prefixResidualOp_one (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (y : ι → F) :
    prefixResidualOp (H := H) P k y 1 =
      (aOp (hidingPrefixOp P k (some y)) : Matrix ((ι → F) × H) _ ℂ) := by
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
    (M : Matrix ((↥((CLChecks.prefixRegister P k y)ᶜ) → F) × H) _ ℂ) :
    prefixResidualOp P k y M = 0 := by
  unfold prefixResidualOp
  rw [prefixProjector_eq_zero P k y hy]
  ext i j
  simp [registerOp_apply]

theorem prefixResidualOp_sum (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F)
    {A : Type*} [Fintype A]
    (M : A → Matrix ((↥((CLChecks.prefixRegister P k y)ᶜ) → F) × H) _ ℂ) :
    prefixResidualOp P k y (∑ a, M a) = ∑ a, prefixResidualOp P k y (M a) := by
  ext i j
  simp [prefixResidualOp, registerOp_apply, Matrix.kroneckerMap_apply, Matrix.sum_apply,
    Finset.mul_sum]

theorem prefixResidualOp_sub (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F)
    (M N : Matrix ((↥((CLChecks.prefixRegister P k y)ᶜ) → F) × H) _ ℂ) :
    prefixResidualOp P k y (M - N) = prefixResidualOp P k y M - prefixResidualOp P k y N := by
  unfold prefixResidualOp
  ext i j
  simp only [registerOp_apply, Matrix.kroneckerMap_apply, Matrix.sub_apply, mul_sub]

theorem prefixResidualOp_mul (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F)
    (M N : Matrix ((↥((CLChecks.prefixRegister P k y)ᶜ) → F) × H) _ ℂ) :
    prefixResidualOp P k y (M * N) = prefixResidualOp P k y M * prefixResidualOp P k y N := by
  unfold prefixResidualOp
  rw [← registerOp_mul, ← Matrix.mul_kronecker_mul]
  have hi : prefixProjector P k y * prefixProjector P k y = prefixProjector P k y :=
    (readout_isPVM _).idem y
  rw [hi]

/-- Exact conditional error, on the concrete complement of the used prefix
register. It holds for every prefix, including impossible ones of weight zero. -/
theorem stateSqNorm_prefixResidualOp (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (y : ι → F) (ξ : H × K → ℂ)
    (M : Matrix ((↥((CLChecks.prefixRegister P k y)ᶜ) → F) × H) _ ℂ) :
    stateSqNorm (registerState (ι → F) ξ) (prefixResidualOp P k y M) =
      prefixWeight P k y *
        stateSqNorm (registerState (↥((CLChecks.prefixRegister P k y)ᶜ) → F) ξ) M := by
  rw [prefixResidualOp, stateSqNorm_registerState_split]
  change stateSqNorm
    (expVec (registerEPR (CLChecks.prefixRegister P k y → F))
      (registerState (↥((CLChecks.prefixRegister P k y)ᶜ) → F) ξ))
    (prefixProjector P k y ⊗ₖ M) = _
  rw [stateSqNorm_expVec_kron, prefixProjector_weight P hP k y]

/-- Auxiliary registers do not change the prefix distribution. -/
theorem hidingPrefixOp_registerState_weight (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (y : ι → F) (ξ : H × K → ℂ) (hξ : ‖evec ξ‖ = 1) :
    stateSqNorm (registerState (ι → F) ξ)
      (aOp (hidingPrefixOp P k (some y)) : Matrix ((ι → F) × H) _ ℂ) =
      prefixWeight P k y := by
  rw [← prefixResidualOp_one P hP k y, stateSqNorm_prefixResidualOp P hP,
    stateSqNorm_one_eq, registerState_norm ξ hξ, one_pow, mul_one]

theorem prefixResidual_distance (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (y : ι → F) (ξ : H × K → ℂ)
    (M N : Matrix ((↥((CLChecks.prefixRegister P k y)ᶜ) → F) × H) _ ℂ) :
    stateSqNorm (registerState (ι → F) ξ)
      (prefixResidualOp P k y M - prefixResidualOp P k y N) =
      prefixWeight P k y *
        stateSqNorm (registerState (↥((CLChecks.prefixRegister P k y)ᶜ) → F) ξ) (M - N) := by
  rw [← prefixResidualOp_sub, stateSqNorm_prefixResidualOp P hP]

theorem prefixResidual_commutator (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (y : ι → F) (ξ : H × K → ℂ)
    (M N : Matrix ((↥((CLChecks.prefixRegister P k y)ᶜ) → F) × H) _ ℂ) :
    stateSqNorm (registerState (ι → F) ξ)
      (prefixResidualOp P k y M * prefixResidualOp P k y N -
        prefixResidualOp P k y N * prefixResidualOp P k y M) =
      prefixWeight P k y *
        stateSqNorm (registerState (↥((CLChecks.prefixRegister P k y)ᶜ) → F) ξ)
          (M * N - N * M) := by
  rw [← prefixResidualOp_mul, ← prefixResidualOp_mul, prefixResidual_distance P hP]

/-- Full-carrier errors are exactly weighted residual errors under the actual
CL prefix law. The residual outcome alphabet may itself depend on the prefix. -/
theorem prefixResidual_distance_sum (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (ξ : H × K → ℂ) {A : (ι → F) → Type*} [∀ y, Fintype (A y)]
    (M N : (y : ι → F) → A y →
      Matrix ((↥((CLChecks.prefixRegister P k y)ᶜ) → F) × H) _ ℂ) :
    (∑ y, ∑ a, stateSqNorm (registerState (ι → F) ξ)
      (prefixResidualOp P k y (M y a) - prefixResidualOp P k y (N y a))) =
      ∑ y, prefixWeight P k y * ∑ a,
        stateSqNorm (registerState (↥((CLChecks.prefixRegister P k y)ᶜ) → F) ξ)
          (M y a - N y a) := by
  simp_rw [prefixResidual_distance P hP, Finset.mul_sum]

theorem prefixResidual_commutator_sum (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (ξ : H × K → ℂ) {A B : (ι → F) → Type*}
    [∀ y, Fintype (A y)] [∀ y, Fintype (B y)]
    (M : (y : ι → F) → A y →
      Matrix ((↥((CLChecks.prefixRegister P k y)ᶜ) → F) × H) _ ℂ)
    (N : (y : ι → F) → B y →
      Matrix ((↥((CLChecks.prefixRegister P k y)ᶜ) → F) × H) _ ℂ) :
    (∑ y, ∑ a, ∑ b, stateSqNorm (registerState (ι → F) ξ)
      (prefixResidualOp P k y (M y a) * prefixResidualOp P k y (N y b) -
        prefixResidualOp P k y (N y b) * prefixResidualOp P k y (M y a))) =
      ∑ y, prefixWeight P k y * ∑ a, ∑ b,
        stateSqNorm (registerState (↥((CLChecks.prefixRegister P k y)ᶜ) → F) ξ)
          (M y a * N y b - N y b * M y a) := by
  simp_rw [prefixResidual_commutator P hP, Finset.mul_sum]

end MIPRE.Introspection

end

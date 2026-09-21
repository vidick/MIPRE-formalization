/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.PrefixConditioning

/-! # Reassembling measurements across actual adaptive CL prefixes

The CL prefix projectors give orthogonal branches even though their coordinate
splits depend on the prefix. Residual PVMs therefore assemble to a genuine PVM,
and recombining a common answer alphabet preserves exactly the weighted
residual error, with no number-of-prefixes factor.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical Honest
open scoped Kronecker
set_option linter.unusedSectionVars false

variable {F ι H K : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype ι] [DecidableEq ι]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}

theorem prefixResidualOp_conjTranspose (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F)
    (M : Matrix ((↥((CLChecks.prefixRegister P k y)ᶜ) → F) × H) _ ℂ) :
    prefixResidualOp P k y Mᴴ = (prefixResidualOp P k y M)ᴴ := by
  unfold prefixResidualOp
  rw [← registerOp_conjTranspose, Matrix.conjTranspose_kronecker]
  have hq : (prefixProjector P k y)ᴴ = prefixProjector P k y :=
    (readout_isPVM _).isSelfAdjoint y
  rw [hq]

/-- Residual operators from distinct prefixes have disjoint support in the
one ambient register, despite their different local coordinate types. -/
theorem prefixResidualOp_orthogonal (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (y z : ι → F) (hyz : y ≠ z)
    (M : Matrix ((↥((CLChecks.prefixRegister P k y)ᶜ) → F) × H) _ ℂ)
    (N : Matrix ((↥((CLChecks.prefixRegister P k z)ᶜ) → F) × H) _ ℂ) :
    prefixResidualOp P k y M * prefixResidualOp P k z N = 0 := by
  let Q (x : ι → F) : Matrix ((ι → F) × H) _ ℂ := aOp (hidingPrefixOp P k (some x))
  have hM : prefixResidualOp P k y M * Q y = prefixResidualOp P k y M := by
    dsimp only [Q]
    rw [← prefixResidualOp_one P hP, ← prefixResidualOp_mul, mul_one]
  have hN : Q z * prefixResidualOp P k z N = prefixResidualOp P k z N := by
    dsimp only [Q]
    rw [← prefixResidualOp_one P hP, ← prefixResidualOp_mul, one_mul]
  have hQ : Q y * Q z = 0 := by
    simp only [Q, hidingPrefixOp_some, ← aOp_mul]
    rw [(readout_isPVM (P.truncate k).eval).orthogonal hyz, aOp_zero]
  calc
    _ = (prefixResidualOp P k y M * Q y) * (Q z * prefixResidualOp P k z N) := by rw [hM, hN]
    _ = prefixResidualOp P k y M * (Q y * Q z) * prefixResidualOp P k z N := by
      simp only [mul_assoc]
    _ = 0 := by rw [hQ, mul_zero, zero_mul]

/-- Prefix-indexed residual PVMs give a projective joint measurement on the
ambient register. Residual answer alphabets may depend on the prefix. -/
theorem prefixResidual_isPVM (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) {A : (ι → F) → Type*} [∀ y, Fintype (A y)]
    (M : (y : ι → F) → A y →
      Matrix ((↥((CLChecks.prefixRegister P k y)ᶜ) → F) × H) _ ℂ)
    (hM : ∀ y, IsPVM (M y)) :
    IsPVM (fun p : (y : ι → F) × A y => prefixResidualOp P k p.1 (M p.1 p.2)) where
  isSelfAdjoint p := by rw [← prefixResidualOp_conjTranspose, (hM p.1).isSelfAdjoint]
  idem p := by rw [← prefixResidualOp_mul, (hM p.1).idem]
  sum_eq_one := by
    rw [Fintype.sum_sigma]
    simp_rw [← prefixResidualOp_sum, (hM _).sum_eq_one, prefixResidualOp_one P hP,
      hidingPrefixOp_some]
    rw [← aOp_sum, (readout_isPVM (P.truncate k).eval).sum_eq_one, aOp_one]

/-- If the answer alphabet is shared, the ambient PVM can forget its prefix
label and report only the common answer. -/
theorem prefixResidual_reassembled_isPVM (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) {A : Type*} [Fintype A]
    (M : (y : ι → F) → A →
      Matrix ((↥((CLChecks.prefixRegister P k y)ᶜ) → F) × H) _ ℂ)
    (hM : ∀ y, IsPVM (M y)) :
    IsPVM (fun a => ∑ y, prefixResidualOp P k y (M y a)) where
  isSelfAdjoint a := by
    rw [Matrix.conjTranspose_sum]
    simp_rw [← prefixResidualOp_conjTranspose, (hM _).isSelfAdjoint]
  idem a := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.mul_sum, Finset.sum_eq_single y]
    · rw [← prefixResidualOp_mul, (hM y).idem]
    · intro z _ hzy
      exact prefixResidualOp_orthogonal P hP k y z hzy.symm _ _
    · simp
  sum_eq_one := by
    rw [Finset.sum_comm]
    simp_rw [← prefixResidualOp_sum, (hM _).sum_eq_one, prefixResidualOp_one P hP,
      hidingPrefixOp_some]
    rw [← aOp_sum, (readout_isPVM (P.truncate k).eval).sum_eq_one, aOp_one]

/-- Orthogonal prefix branches add their squared errors exactly. No
projectivity or self-adjointness is required of the residual errors. -/
theorem stateSqNorm_sum_prefixResidualOp (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (ψ : ((ι → F) × H) × K → ℂ)
    (M : (y : ι → F) → Matrix ((↥((CLChecks.prefixRegister P k y)ᶜ) → F) × H) _ ℂ) :
    stateSqNorm ψ (∑ y, prefixResidualOp P k y (M y)) =
      ∑ y, stateSqNorm ψ (prefixResidualOp P k y (M y)) := by
  have hg : (∑ y, prefixResidualOp P k y (M y))ᴴ *
      (∑ y, prefixResidualOp P k y (M y)) =
      ∑ y, (prefixResidualOp P k y (M y))ᴴ * prefixResidualOp P k y (M y) := by
    rw [Matrix.conjTranspose_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.mul_sum]
    apply Finset.sum_eq_single y
    · intro z _ hzy
      rw [← prefixResidualOp_conjTranspose]
      exact prefixResidualOp_orthogonal P hP k y z hzy.symm _ _
    · simp
  rw [stateSqNorm_eq_qform, hg, aOp_sum, qform_sum]
  exact Finset.sum_congr rfl fun y _ => (stateSqNorm_eq_qform ψ _).symm

/-- Forgetting the prefix label preserves the exact conditional error law.
This is the concrete gluing step needed after local mixing and dilation. -/
theorem prefixResidual_reassembled_distance (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ) (ξ : H × K → ℂ)
    {A : Type*} [Fintype A]
    (M N : (y : ι → F) → A →
      Matrix ((↥((CLChecks.prefixRegister P k y)ᶜ) → F) × H) _ ℂ) :
    (∑ a, stateSqNorm (registerState (ι → F) ξ)
      ((∑ y, prefixResidualOp P k y (M y a)) - ∑ y, prefixResidualOp P k y (N y a))) =
      ∑ y, prefixWeight P k y * ∑ a,
        stateSqNorm (registerState (↥((CLChecks.prefixRegister P k y)ᶜ) → F) ξ)
          (M y a - N y a) := by
  simp_rw [← Finset.sum_sub_distrib, ← prefixResidualOp_sub,
    stateSqNorm_sum_prefixResidualOp P hP, stateSqNorm_prefixResidualOp P hP]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

end MIPRE.Introspection

end

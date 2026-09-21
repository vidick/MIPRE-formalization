/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AdaptivePrefixMeasurement
import MIPRE.Foundations.Introspection.AdaptiveZFactor

/-! # Global commutators are the actual weighted residual commutators

Only the matching prefix branch contributes to a commutator against a
prefix-supported ideal operator. This identifies the global coarse-readout
error with the exact weighted error used by adaptive mixing. No projectivity
or positivity hypothesis on the residual matrices is needed.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false

variable {F ι H K : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype ι] [DecidableEq ι]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}

/-- A global sum commutes with one prefix-supported operator exactly as its
own prefix branch does. All other products vanish by concrete prefix orthogonality. -/
theorem prefixResidual_reassembled_commutator (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ)
    (M : (y : ι → F) → Matrix ((stageRemaining P k y → F) × H) _ ℂ)
    (y : ι → F) (N : Matrix ((stageRemaining P k y → F) × H) _ ℂ) :
    (∑ z, prefixResidualOp P k z (M z)) * prefixResidualOp P k y N -
      prefixResidualOp P k y N * (∑ z, prefixResidualOp P k z (M z)) =
      prefixResidualOp P k y (M y * N - N * M y) := by
  have hl : (∑ z, prefixResidualOp P k z (M z)) * prefixResidualOp P k y N =
      prefixResidualOp P k y (M y) * prefixResidualOp P k y N := by
    rw [Finset.sum_mul]
    apply Finset.sum_eq_single y
    · intro z _ hzy
      exact prefixResidualOp_orthogonal P hP k z y hzy _ _
    · simp
  have hr : prefixResidualOp P k y N * (∑ z, prefixResidualOp P k z (M z)) =
      prefixResidualOp P k y N * prefixResidualOp P k y (M y) := by
    rw [Finset.mul_sum]
    apply Finset.sum_eq_single y
    · intro z _ hzy
      exact prefixResidualOp_orthogonal P hP k y z hzy.symm _ _
    · simp
  rw [hl, hr, ← prefixResidualOp_mul, ← prefixResidualOp_mul, ← prefixResidualOp_sub]

/-- The global commutation error equals the actual prefix-weighted local
commutation error, even when ideal outcome types depend on the prefix. -/
theorem prefixResidual_reassembled_commutator_sum (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ) (ξ : H × K → ℂ)
    {A : Type*} [Fintype A] {B : (ι → F) → Type*} [∀ y, Fintype (B y)]
    (M : (y : ι → F) → A → Matrix ((stageRemaining P k y → F) × H) _ ℂ)
    (N : (y : ι → F) → B y → Matrix ((stageRemaining P k y → F) × H) _ ℂ) :
    (∑ a, ∑ p : (y : ι → F) × B y, stateSqNorm (registerState (ι → F) ξ)
      ((∑ z, prefixResidualOp P k z (M z a)) * prefixResidualOp P k p.1 (N p.1 p.2) -
        prefixResidualOp P k p.1 (N p.1 p.2) * (∑ z, prefixResidualOp P k z (M z a)))) =
      ∑ y, prefixWeight P k y * ∑ a, ∑ b,
        stateSqNorm (registerState (stageRemaining P k y → F) ξ)
          (M y a * N y b - N y b * M y a) := by
  simp only [Fintype.sum_sigma, prefixResidual_reassembled_commutator P hP,
    stateSqNorm_prefixResidualOp P hP]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

/-- Specialization to the actual seed coarse-graining which records the CL
prefix and its next Z coordinates. This is the tested global coarse Z family,
not an independently supplied collection of prefix-local ideals. -/
theorem adaptiveZ_reassembled_commutator_sum (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ) (ξ : H × K → ℂ)
    {A : Type*} [Fintype A]
    (M : (y : ι → F) → A → Matrix ((stageRemaining P k y → F) × H) _ ℂ) :
    (∑ a, ∑ p : (y : ι → F) × (Fin (Fintype.card (P.factorOfPrefix k y)) → F),
      stateSqNorm (registerState (ι → F) ξ)
        ((∑ z, prefixResidualOp P k z (M z a)) *
            (aOp (readout (adaptiveZOutcome P k) p) : Matrix ((ι → F) × H) _ ℂ) -
          (aOp (readout (adaptiveZOutcome P k) p) : Matrix ((ι → F) × H) _ ℂ) *
            (∑ z, prefixResidualOp P k z (M z a)))) =
      ∑ y, prefixWeight P k y * ∑ a, ∑ z,
        stateSqNorm (registerState (stageRemaining P k y → F) ξ)
          (M y a * registerReadout (stageSplit P hP k y) wZ LinearMap.id z -
            registerReadout (stageSplit P hP k y) wZ LinearMap.id z * M y a) := by
  have hf (p : (y : ι → F) × (Fin (Fintype.card (P.factorOfPrefix k y)) → F)) :
      (aOp (readout (adaptiveZOutcome P k) p) : Matrix ((ι → F) × H) _ ℂ) =
        prefixResidualOp P k p.1
          (registerReadout (stageSplit P hP k p.1) wZ LinearMap.id p.2) :=
    adaptiveZ_readout_factor P hP k p.1 p.2
  simp_rw [hf]
  exact prefixResidual_reassembled_commutator_sum
    (B := fun y => Fin (Fintype.card (P.factorOfPrefix k y)) → F) P hP k ξ M
    (fun y z => registerReadout (H := H) (stageSplit P hP k y) wZ LinearMap.id z)

end MIPRE.Introspection

end

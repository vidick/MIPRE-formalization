/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.ConditionalNormalizerTests

/-! # Exact mirror transfer for the conditional ideal family

Primitive fine and prefix mirrors imply the mirror identity for the keyed
conditional ideal family. Consequently the one-party replacement estimate is
also the cross-party error needed by the hiding induction.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical
open scoped Kronecker

set_option linter.unusedSectionVars false

variable {H K I Y Z : Type*}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype Y] [DecidableEq Y]
  [Fintype Z] [DecidableEq Z]

theorem fibSum_mirror (ψ : H × K → ℂ)
    (P : I → Matrix H H ℂ) (R : I → Matrix K K ℂ)
    (h : ∀ i, aOp (P i) *ᵥ ψ = bOp (R i) *ᵥ ψ) (f : I → Z) (z : Z) :
    aOp (fibSum P f z) *ᵥ ψ = bOp (fibSum R f z) *ᵥ ψ := by
  simp only [fibSum, aOp_sum, bOp_sum, Matrix.sum_mulVec]
  exact Finset.sum_congr rfl fun i _ => h i

/-- Mirrors reverse multiplication order; commutation of the ideal prefix and
fine projectors restores the order defining the conditional ideal. -/
theorem conditionalIdeal_mirror (ψ : H × K → ℂ)
    (P : I → Matrix H H ℂ) (R : I → Matrix K K ℂ)
    (Q : Y → Matrix H H ℂ) (S : Y → Matrix K K ℂ) (f : Y → I → Z)
    (hP : ∀ i, aOp (P i) *ᵥ ψ = bOp (R i) *ᵥ ψ)
    (hQ : ∀ y, aOp (Q y) *ᵥ ψ = bOp (S y) *ᵥ ψ)
    (hc : ∀ y i, Commute (S y) (R i)) (p : Y × Z) :
    aOp (conditionalIdeal P Q f p) *ᵥ ψ =
      bOp (conditionalIdeal R S f p) *ᵥ ψ := by
  unfold conditionalIdeal
  rw [aOp_mul, ← Matrix.mulVec_mulVec, fibSum_mirror ψ P R hP,
    Matrix.mulVec_mulVec, aOp_mul_bOp, ← Matrix.mulVec_mulVec, hQ,
    Matrix.mulVec_mulVec, ← bOp_mul,
    ← (commute_fibSum_right R S hc (f p.1) p.1 p.2).eq]

/-- An exact mirror changes a cross-party distance into a same-party distance. -/
theorem xSqNorm_eq_bOp_distance_of_mirror (ψ : H × K → ℂ)
    (P : Matrix H H ℂ) (Q B : Matrix K K ℂ)
    (h : aOp P *ᵥ ψ = bOp Q *ᵥ ψ) :
    xSqNorm ψ P B = snorm ψ (bOp B - bOp Q) ^ 2 := by
  rw [xSqNorm_eq_snorm_sq]
  simp only [snorm, Matrix.sub_mulVec, h, evec_sub]
  rw [norm_sub_rev]

/-- The conditional replacement gives the cross-party ideal estimate whenever
the primitive ideal families have their exact EPR mirrors. -/
theorem conditional_coarse_ideal_replacement_mirror (ψ : H × K → ℂ)
    (hψ : ‖evec ψ‖ = 1) (M P : I → Matrix H H ℂ) (R : I → Matrix K K ℂ)
    (Q : Y → Matrix H H ℂ) (S : Y → Matrix K K ℂ)
    (B : Y × Z → Matrix K K ℂ) (f : Y → I → Z)
    (hM : IsPVM M) (hR : IsPVM R) (hS : IsPVM S)
    (hc : ∀ y i, Commute (S y) (R i))
    (hP : ∀ i, aOp (P i) *ᵥ ψ = bOp (R i) *ᵥ ψ)
    (hQ : ∀ y, aOp (Q y) *ᵥ ψ = bOp (S y) *ᵥ ψ)
    {α η ε : ℝ}
    (hfine : ∑ i, xSqNorm ψ (M i) (R i) ≤ ε)
    (hnorm : ∑ y, xSqNorm ψ (Q y) (∑ z, B (y, z)) ≤ η)
    (hconditional : ∑ p : Y × Z, snorm ψ
      (bOp (B p) - fibSum M (f p.1) p.2 ⊗ₖ (∑ z, B (p.1, z))) ^ 2 ≤ α) :
    (∑ p : Y × Z, xSqNorm ψ (conditionalIdeal P Q f p) (B p)) ≤
      3 * α + 3 * η + 3 * ε := by
  have hnorm' : ∑ y, snorm ψ (bOp ((∑ z, B (y, z)) - S y)) ^ 2 ≤ η := by
    simpa only [xSqNorm_eq_bOp_distance_of_mirror ψ _ _ _ (hQ _), bOp_sub] using hnorm
  have h := conditional_coarse_ideal_replacement ψ hψ M R S B f hM hR hS hc
    hfine hnorm' hconditional
  simpa only [xSqNorm_eq_bOp_distance_of_mirror ψ _ _ _
    (conditionalIdeal_mirror ψ P R Q S f hP hQ hc _)] using h

end MIPRE.Introspection

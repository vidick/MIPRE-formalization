/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.SubmeasurementCompletion

/-! # Retaining a classical fibre after twirling

The consistency marginal lets us retain the matching block of a nearby measurement.
An exactly consistent projective mirror moves the rightmost projector to the front,
where it is a contraction. No outcome-count factor enters the estimate.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix
open scoped ComplexOrder MatrixOrder

variable {N Y A : Type*} [Fintype N] [DecidableEq N]
  [Fintype Y] [DecidableEq Y] [Fintype A] [DecidableEq A]

/-- Multiplication on the right by a projector is contractive when it has a commuting mirror. -/
theorem snorm_right_projector_le (ψ : N → ℂ) (P R E : Matrix N N ℂ)
    (hRsa : Rᴴ = R) (hRid : R * R = R) (hPR : P *ᵥ ψ = R *ᵥ ψ)
    (hER : E * R = R * E) : snorm ψ (E * P) ^ 2 ≤ snorm ψ E ^ 2 := by
  have he : snorm ψ (E * P) = snorm ψ (R * E) := by
    rw [snorm, snorm, ← Matrix.mulVec_mulVec, hPR, Matrix.mulVec_mulVec, hER]
  rw [he]
  apply snorm_sq_mul_le_of_contraction
  rw [hRsa, hRid]
  exact proj_le_one hRsa hRid

/-- A joint PVM element is unchanged by multiplication by its own first marginal. -/
theorem joint_mul_marginal {M : Y × A → Matrix N N ℂ} (hM : IsPVM M) (y : Y) (a : A) :
    M (y, a) * (∑ b, M (y, b)) = M (y, a) := by
  rw [Finset.mul_sum]
  refine (Finset.sum_eq_single a ?_ ?_).trans (hM.idem (y, a))
  · intro b _ hba
    exact hM.orthogonal fun h => hba (Prod.mk.inj h).2.symm
  · intro h
    exact False.elim (h (mem_univ a))

/-- Keeping the matching target fibre costs twice the marginal error plus twice the original error. -/
theorem retained_fibre_dist (ψ : N → ℂ) (M T : Y × A → Matrix N N ℂ)
    (P R : Y → Matrix N N ℂ) (hM : IsPVM M) (hR : IsPVM R)
    (hPR : ∀ y, P y *ᵥ ψ = R y *ᵥ ψ)
    (hMR : ∀ y a, M (y, a) * R y = R y * M (y, a))
    (hTR : ∀ y a, T (y, a) * R y = R y * T (y, a)) :
    (∑ p : Y × A, snorm ψ (M p - T p * P p.1) ^ 2) ≤
      2 * (∑ y, snorm ψ ((∑ a, M (y, a)) - P y) ^ 2) +
      2 * (∑ p : Y × A, snorm ψ (M p - T p) ^ 2) := by
  have hfirst y : (∑ a, snorm ψ (M (y, a) - M (y, a) * P y) ^ 2) ≤
      snorm ψ ((∑ a, M (y, a)) - P y) ^ 2 := by
    have hfamily : ∑ a, (M (y, a))ᴴ * M (y, a) ≤ (1 : Matrix N N ℂ) := by
      simp_rw [hM.isSelfAdjoint, hM.idem]
      exact proj_le_one (hM.marg_left.isSelfAdjoint y) (hM.marg_left.idem y)
    have he a : M (y, a) - M (y, a) * P y =
        M (y, a) * ((∑ b, M (y, b)) - P y) := by
      rw [mul_sub, joint_mul_marginal hM]
    simp_rw [he]
    exact sum_snorm_sq_mul_le ψ _ hfamily _
  have hfirstSum := Finset.sum_le_sum fun y (_ : y ∈ univ) => hfirst y
  rw [sum_prod_eq] at hfirstSum
  have hsecond : (∑ p : Y × A, snorm ψ (M p * P p.1 - T p * P p.1) ^ 2) ≤
      ∑ p : Y × A, snorm ψ (M p - T p) ^ 2 := by
    apply Finset.sum_le_sum
    intro p _
    rw [← sub_mul]
    apply snorm_right_projector_le ψ _ (R p.1) _ (hR.isSelfAdjoint p.1) (hR.idem p.1)
      (hPR p.1)
    rw [sub_mul, hMR p.1 p.2, hTR p.1 p.2, mul_sub]
  have htri := sum_snorm_sq_triangle' ψ M (fun p => M p * P p.1) (fun p => T p * P p.1)
  linarith

end MIPRE.Introspection

end

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Commutation

/-! # Combining approximate commutations across a bipartite state

Transfer the second unitary to the other party, commute the first, and transfer back.
The POVM square-sum bound controls both transfer errors without an alphabet factor.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix
open scoped ComplexOrder MatrixOrder

variable {N A : Type*} [Fintype N] [DecidableEq N] [Fintype A]

/-- The four-link commutation argument, with an arbitrary commuting mirror `W`. -/
theorem commutator_product_bound (ψ : N → ℂ) (M : A → Matrix N N ℂ)
    (hM : ∑ a, (M a)ᴴ * M a ≤ (1 : Matrix N N ℂ))
    (U V W : Matrix N N ℂ) (hU : Uᴴ * U = 1) (hW : Wᴴ * W = 1)
    (hWU : W * U = U * W) (hWM : ∀ a, W * M a = M a * W) :
    (∑ a, snorm ψ (M a * (U * V) - (U * V) * M a) ^ 2) ≤
      4 * (∑ a, snorm ψ (M a * U - U * M a) ^ 2) +
      4 * (∑ a, snorm ψ (M a * V - V * M a) ^ 2) +
      8 * snorm ψ (V - W) ^ 2 := by
  let P₀ a := M a * U * V
  let P₁ a := M a * U * W
  let P₂ a := U * M a * W
  let P₃ a := U * M a * V
  let P₄ a := U * V * M a
  have h01 : (∑ a, snorm ψ (P₀ a - P₁ a) ^ 2) ≤ snorm ψ (V - W) ^ 2 := by
    have h := sum_snorm_sq_mul_le ψ M hM (U * (V - W))
    simp only [snorm_mul_of_isometry ψ hU] at h
    convert h using 1
    congr 1
    funext a
    congr 2
    dsimp [P₀, P₁]
    noncomm_ring
  have h12 : (∑ a, snorm ψ (P₁ a - P₂ a) ^ 2) =
      ∑ a, snorm ψ (M a * U - U * M a) ^ 2 := by
    apply Finset.sum_congr rfl
    intro a _
    have he : P₁ a - P₂ a = W * (M a * U - U * M a) := by
      dsimp [P₁, P₂]
      have h₁ : W * (M a * U) = M a * U * W := by
        rw [← mul_assoc, hWM, mul_assoc, hWU, ← mul_assoc]
      have h₂ : W * (U * M a) = U * M a * W := by
        rw [← mul_assoc, hWU, mul_assoc, hWM, ← mul_assoc]
      rw [mul_sub, h₁, h₂]
    rw [he, snorm_mul_of_isometry ψ hW]
  have h23 : (∑ a, snorm ψ (P₂ a - P₃ a) ^ 2) ≤ snorm ψ (V - W) ^ 2 := by
    have he a : P₂ a - P₃ a = U * (M a * (W - V)) := by
      dsimp [P₂, P₃]
      noncomm_ring
    simp_rw [he, snorm_mul_of_isometry ψ hU]
    exact (sum_snorm_sq_mul_le ψ M hM (W - V)).trans_eq
      (congrArg (fun x : ℝ => x ^ 2) (snorm_sub_comm ψ W V))
  have h34 : (∑ a, snorm ψ (P₃ a - P₄ a) ^ 2) =
      ∑ a, snorm ψ (M a * V - V * M a) ^ 2 := by
    have he a : P₃ a - P₄ a = U * (M a * V - V * M a) := by
      dsimp [P₃, P₄]
      noncomm_ring
    simp_rw [he, snorm_mul_of_isometry ψ hU]
  have h04 := sum_snorm_sq_triangle' ψ P₀ P₂ P₄
  have h02 := sum_snorm_sq_triangle' ψ P₀ P₁ P₂
  have h24 := sum_snorm_sq_triangle' ψ P₂ P₃ P₄
  have hend : (∑ a, snorm ψ (M a * (U * V) - (U * V) * M a) ^ 2) =
      ∑ a, snorm ψ (P₀ a - P₄ a) ^ 2 := by simp only [P₀, P₄, mul_assoc]
  rw [hend]
  linarith

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

/-- The bipartite version: `W` is the second party's mirror of Alice's `V`. -/
theorem two_sided_commutation (ψ : dA × dB → ℂ) (M : POVM A dA)
    (U V : Matrix dA dA ℂ) (W : Matrix dB dB ℂ)
    (hU : Uᴴ * U = 1) (hW : Wᴴ * W = 1) :
    (∑ a, stateSqNorm ψ ((M.mats a).val * (U * V) - (U * V) * (M.mats a).val)) ≤
      4 * (∑ a, stateSqNorm ψ ((M.mats a).val * U - U * (M.mats a).val)) +
      4 * (∑ a, stateSqNorm ψ ((M.mats a).val * V - V * (M.mats a).val)) +
      8 * xSqNorm ψ V W := by
  have h := commutator_product_bound ψ (fun a => aOp ((M.mats a).val))
    (sum_aOp_conjTranspose_mul_self_le_one M) (aOp U) (aOp V) (bOp W)
    (isometry_aOp hU) (isometry_bOp hW)
    (aOp_mul_bOp U W).symm (fun a => (aOp_mul_bOp _ W).symm)
  simpa only [← aOp_mul, ← aOp_sub, ← xSqNorm_eq_snorm_sq,
    stateSqNorm, stateNorm, norm_stateVec_eq_snorm] using h

/-- Independent conditional unitary distributions preserve the same explicit constants. -/
theorem two_sided_commutation_avg {X I J : Type*} [Fintype X] [Fintype I] [Fintype J]
    (D : X → ℝ) (hD : ∀ x, 0 ≤ D x)
    (μ : X → I → ℝ) (ν : X → J → ℝ)
    (hμ0 : ∀ x i, 0 ≤ μ x i) (hν0 : ∀ x j, 0 ≤ ν x j)
    (hμ1 : ∀ x, ∑ i, μ x i = 1) (hν1 : ∀ x, ∑ j, ν x j = 1)
    (ψ : dA × dB → ℂ) (M : X → POVM A dA)
    (U : X → I → Matrix dA dA ℂ) (V : X → J → Matrix dA dA ℂ)
    (W : X → J → Matrix dB dB ℂ)
    (hU : ∀ x i, (U x i)ᴴ * U x i = 1) (hW : ∀ x j, (W x j)ᴴ * W x j = 1) :
    (∑ x, D x * ∑ i, μ x i * ∑ j, ν x j * ∑ a,
      stateSqNorm ψ (((M x).mats a).val * (U x i * V x j) -
        (U x i * V x j) * ((M x).mats a).val)) ≤
      4 * (∑ x, D x * ∑ i, μ x i * ∑ a,
        stateSqNorm ψ (((M x).mats a).val * U x i - U x i * ((M x).mats a).val)) +
      4 * (∑ x, D x * ∑ j, ν x j * ∑ a,
        stateSqNorm ψ (((M x).mats a).val * V x j - V x j * ((M x).mats a).val)) +
      8 * (∑ x, D x * ∑ j, ν x j * xSqNorm ψ (V x j) (W x j)) := by
  have hpoint x i j := two_sided_commutation ψ (M x) (U x i) (V x j) (W x j)
    (hU x i) (hW x j)
  calc
    _ ≤ ∑ x, D x * ∑ i, μ x i * ∑ j, ν x j *
        (4 * (∑ a, stateSqNorm ψ (((M x).mats a).val * U x i -
          U x i * ((M x).mats a).val)) +
        4 * (∑ a, stateSqNorm ψ (((M x).mats a).val * V x j -
          V x j * ((M x).mats a).val)) + 8 * xSqNorm ψ (V x j) (W x j)) := by
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left _ (hD x)
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hμ0 x i)
      exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hpoint x i j) (hν0 x j)
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib]
      have hconst (x : X) (r : ℝ) : (∑ j, ν x j * r) = r := by
        rw [← Finset.sum_mul, hν1, one_mul]
      have hconst' (x : X) (r : ℝ) : (∑ i, μ x i * r) = r := by
        rw [← Finset.sum_mul, hμ1, one_mul]
      simp_rw [hconst, hconst']
      simp only [mul_left_comm (b := (4 : ℝ)), mul_left_comm (b := (8 : ℝ)),
        ← Finset.mul_sum]

end MIPRE.Introspection

end

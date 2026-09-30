/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Commutation

@[expose] public section

/-! # Combining approximate commutations across a bipartite state

Transfer the second unitary to the other party, commute the first, and transfer back.
The POVM square-sum bound controls both transfer errors without an alphabet factor.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the four-link argument for a
state model, with the family in front a column contraction (`StateModel.IsColContraction`); the
bipartite version with the mirror of Alice's `V` on the second player's side, where it commutes
with everything of the first player's.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset

section State

variable {𝒞 : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] (Ψ : StateModel 𝒞)
  {A : Type*} [Fintype A]

/-- The four-link commutation argument, with an arbitrary commuting mirror `W`. -/
theorem commutator_product_bound (M : A → 𝒞) (hM : Ψ.IsColContraction M)
    (U V W : 𝒞) (hU : star U * U = 1) (hW : star W * W = 1)
    (hWU : W * U = U * W) (hWM : ∀ a, W * M a = M a * W) :
    (∑ a, Ψ.snorm (M a * (U * V) - (U * V) * M a) ^ 2) ≤
      4 * (∑ a, Ψ.snorm (M a * U - U * M a) ^ 2) +
      4 * (∑ a, Ψ.snorm (M a * V - V * M a) ^ 2) +
      8 * Ψ.snorm (V - W) ^ 2 := by
  let P₀ a := M a * U * V
  let P₁ a := M a * U * W
  let P₂ a := U * M a * W
  let P₃ a := U * M a * V
  let P₄ a := U * V * M a
  have h01 : (∑ a, Ψ.snorm (P₀ a - P₁ a) ^ 2) ≤ Ψ.snorm (V - W) ^ 2 := by
    have h := Ψ.sum_snorm_sq_mul_le M hM (U * (V - W))
    simp only [Ψ.snorm_mul_of_isometry hU] at h
    convert h using 1
    congr 1
    funext a
    congr 2
    dsimp [P₀, P₁]
    noncomm_ring
  have h12 : (∑ a, Ψ.snorm (P₁ a - P₂ a) ^ 2) =
      ∑ a, Ψ.snorm (M a * U - U * M a) ^ 2 := by
    apply Finset.sum_congr rfl
    intro a _
    have he : P₁ a - P₂ a = W * (M a * U - U * M a) := by
      dsimp [P₁, P₂]
      have h₁ : W * (M a * U) = M a * U * W := by
        rw [← mul_assoc, hWM, mul_assoc, hWU, ← mul_assoc]
      have h₂ : W * (U * M a) = U * M a * W := by
        rw [← mul_assoc, hWU, mul_assoc, hWM, ← mul_assoc]
      rw [mul_sub, h₁, h₂]
    rw [he, Ψ.snorm_mul_of_isometry hW]
  have h23 : (∑ a, Ψ.snorm (P₂ a - P₃ a) ^ 2) ≤ Ψ.snorm (V - W) ^ 2 := by
    have he a : P₂ a - P₃ a = U * (M a * (W - V)) := by
      dsimp [P₂, P₃]
      noncomm_ring
    simp_rw [he, Ψ.snorm_mul_of_isometry hU]
    exact (Ψ.sum_snorm_sq_mul_le M hM (W - V)).trans_eq
      (congrArg (fun x : ℝ => x ^ 2) (Ψ.snorm_sub_comm W V))
  have h34 : (∑ a, Ψ.snorm (P₃ a - P₄ a) ^ 2) =
      ∑ a, Ψ.snorm (M a * V - V * M a) ^ 2 := by
    have he a : P₃ a - P₄ a = U * (M a * V - V * M a) := by
      dsimp [P₃, P₄]
      noncomm_ring
    simp_rw [he, Ψ.snorm_mul_of_isometry hU]
  have h04 := Ψ.sum_snorm_sq_triangle univ P₀ P₂ P₄
  have h02 := Ψ.sum_snorm_sq_triangle univ P₀ P₁ P₂
  have h24 := Ψ.sum_snorm_sq_triangle univ P₂ P₃ P₄
  have hend : (∑ a, Ψ.snorm (M a * (U * V) - (U * V) * M a) ^ 2) =
      ∑ a, Ψ.snorm (P₀ a - P₄ a) ^ 2 := by simp only [P₀, P₄, mul_assoc]
  rw [hend]
  linarith

end State

section Bipartite

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  (Ψ : BipartiteModel 𝒞 𝒜 ℬ) {A : Type*} [Fintype A]

/-- The bipartite version: `W` is the second party's mirror of Alice's `V`. -/
theorem two_sided_commutation (M : POVMIn A 𝒜) (U V : 𝒜) (W : ℬ)
    (hU : star U * U = 1) (hW : star W * W = 1) :
    (∑ a, Ψ.stateSqNorm (M.op a * (U * V) - (U * V) * M.op a)) ≤
      4 * (∑ a, Ψ.stateSqNorm (M.op a * U - U * M.op a)) +
      4 * (∑ a, Ψ.stateSqNorm (M.op a * V - V * M.op a)) +
      8 * Ψ.xSqNorm V W := by
  have h := commutator_product_bound Ψ.toStateModel (fun a => Ψ.πA (M.op a))
    (Ψ.isColContraction_πA M) (Ψ.πA U) (Ψ.πA V) (Ψ.πB W)
    (by rw [← map_star, ← map_mul, hU, map_one]) (by rw [← map_star, ← map_mul, hW, map_one])
    (Ψ.commute U W).eq.symm (fun a => (Ψ.commute (M.op a) W).eq.symm)
  have e : ∀ X : 𝒜, Ψ.stateSqNorm X = Ψ.snorm (Ψ.πA X) ^ 2 := fun X => rfl
  simpa only [e, BipartiteModel.xSqNorm, BipartiteModel.xNorm, map_mul, map_sub] using h

/-- Independent conditional unitary distributions preserve the same explicit constants. -/
theorem two_sided_commutation_avg {X I J : Type*} [Fintype X] [Fintype I] [Fintype J]
    (D : X → ℝ) (hD : ∀ x, 0 ≤ D x)
    (μ : X → I → ℝ) (ν : X → J → ℝ)
    (hμ0 : ∀ x i, 0 ≤ μ x i) (hν0 : ∀ x j, 0 ≤ ν x j)
    (hμ1 : ∀ x, ∑ i, μ x i = 1) (hν1 : ∀ x, ∑ j, ν x j = 1)
    (M : X → POVMIn A 𝒜) (U : X → I → 𝒜) (V : X → J → 𝒜) (W : X → J → ℬ)
    (hU : ∀ x i, star (U x i) * U x i = 1) (hW : ∀ x j, star (W x j) * W x j = 1) :
    (∑ x, D x * ∑ i, μ x i * ∑ j, ν x j * ∑ a,
      Ψ.stateSqNorm ((M x).op a * (U x i * V x j) - (U x i * V x j) * (M x).op a)) ≤
      4 * (∑ x, D x * ∑ i, μ x i * ∑ a,
        Ψ.stateSqNorm ((M x).op a * U x i - U x i * (M x).op a)) +
      4 * (∑ x, D x * ∑ j, ν x j * ∑ a,
        Ψ.stateSqNorm ((M x).op a * V x j - V x j * (M x).op a)) +
      8 * (∑ x, D x * ∑ j, ν x j * Ψ.xSqNorm (V x j) (W x j)) := by
  have hpoint x i j := two_sided_commutation Ψ (M x) (U x i) (V x j) (W x j)
    (hU x i) (hW x j)
  calc
    _ ≤ ∑ x, D x * ∑ i, μ x i * ∑ j, ν x j *
        (4 * (∑ a, Ψ.stateSqNorm ((M x).op a * U x i - U x i * (M x).op a)) +
        4 * (∑ a, Ψ.stateSqNorm ((M x).op a * V x j - V x j * (M x).op a)) +
        8 * Ψ.xSqNorm (V x j) (W x j)) := by
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

end Bipartite

end MIPRE.Introspection

end

end

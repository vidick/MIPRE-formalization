/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.IsometricStrategy
import MIPRE.Foundations.Commutation

/-! # The cost of completing isometric image measurements

The extracted ideal state need not lie exactly in the isometries' images.
Its image-complement mass is bounded by its squared distance to the actual
embedded state. Completing an image PVM at one outcome therefore adds only
a dimension-independent error, even when primitive estimates are stated on
the ideal state.
-/

noncomputable section
namespace MIPRE.Introspection
open Matrix Finset Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false

section General
variable {N A : Type*} [Fintype N] [DecidableEq N] [Fintype A]

/-- A projection annihilating one vector has at most the squared vector
distance as its mass on another. Normalization is not required. -/
theorem projector_mass_le_state_distance (ψ φ : N → ℂ) (C : Matrix N N ℂ)
    (hC : Cᴴ = C) (hCC : C * C = C) (hz : C *ᵥ ψ = 0) :
    snorm φ C ^ 2 ≤ ‖evec (ψ - φ)‖ ^ 2 := by
  have hb : Bnd C 1 := bnd_one_of_conjTranspose_mul_self_le (by
    rw [hC, hCC]
    exact proj_le_one hC hCC)
  have he : C *ᵥ (φ - ψ) = C *ᵥ φ := by rw [Matrix.mulVec_sub, hz, sub_zero]
  have hn := hb (φ - ψ)
  rw [he, one_mul, evec_sub, norm_sub_rev, ← evec_sub] at hn
  exact sq_le_sq₀ (snorm_nonneg φ C) (norm_nonneg _) |>.mpr hn

end General

section Coarse
variable {H R A B : Type*} [Fintype H] [DecidableEq H]
  [Fintype R] [DecidableEq R] [Fintype A] [Fintype B]

/-- Coarse-graining a completed image measurement is the image of the
coarse-graining, with the same complement placed at the mapped default. -/
theorem isometricPOVM_map_mats_eq (V : Matrix R H ℂ) (hV : Vᴴ * V = 1)
    (a₀ : A) (M : POVM A H) (hM : IsPVM (fun a => (M.mats a).val)) (f : A → B) (b : B) :
    (((isometricPOVM V hV a₀ M hM).map f).mats b).val =
      isometricEffect V (f a₀) (fun b => ((M.map f).mats b).val) b := by
  rw [POVM.map_mats]
  simp only [isometricPOVM_mats, isometricEffect, sum_add_distrib]
  have hs : (∑ a ∈ univ.filter (fun a => f a = b), isometricImage V (M.mats a).val) =
      isometricImage V ((M.map f).mats b).val := by
    rw [POVM.map_mats]
    simp only [isometricImage, Matrix.mul_sum, Matrix.sum_mul]
  rw [hs]
  congr 1
  simp only [sum_ite_eq', mem_filter, mem_univ, true_and]
  by_cases h : f a₀ = b
  · subst b
    simp
  · simp [h, Ne.symm h]

end Coarse

section Bipartite
variable {H K R S A : Type*}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] [Fintype A]

theorem isometricComplement_alice_mass (V : Matrix R H ℂ) (W : Matrix S K ℂ)
    (hV : Vᴴ * V = 1) (ψ : H × K → ℂ) (φ : R × S → ℂ) :
    snorm φ (aOp (isometricComplement V)) ^ 2 ≤
      ‖evec (isometricState V W ψ - φ)‖ ^ 2 := by
  apply projector_mass_le_state_distance
  · rw [aOp_conjTranspose, isometricComplement_conjTranspose]
  · rw [← aOp_mul, isometricComplement_idem V hV]
  · rw [isometricState, Matrix.mulVec_mulVec, aOp, ← Matrix.mul_kronecker_mul,
      isometricComplement_mul V hV, Matrix.zero_kronecker, Matrix.zero_mulVec]

theorem isometricComplement_bob_mass (V : Matrix R H ℂ) (W : Matrix S K ℂ)
    (hW : Wᴴ * W = 1) (ψ : H × K → ℂ) (φ : R × S → ℂ) :
    snorm φ (bOp (isometricComplement W)) ^ 2 ≤
      ‖evec (isometricState V W ψ - φ)‖ ^ 2 := by
  apply projector_mass_le_state_distance
  · rw [bOp_conjTranspose, isometricComplement_conjTranspose]
  · rw [← bOp_mul, isometricComplement_idem W hW]
  · rw [isometricState, Matrix.mulVec_mulVec, bOp, ← Matrix.mul_kronecker_mul,
      isometricComplement_mul W hW, Matrix.kronecker_zero, Matrix.zero_mulVec]

/-- Exactly one outcome receives the image complement. -/
theorem isometricEffect_alice_completion_error (V : Matrix R H ℂ) (a₀ : A)
    (M : A → Matrix H H ℂ) (φ : R × S → ℂ) :
    (∑ a, snorm φ (aOp (isometricEffect V a₀ M a - isometricImage V (M a))) ^ 2) =
      snorm φ (aOp (isometricComplement V)) ^ 2 := by
  have he (a : A) : aOp (isometricEffect V a₀ M a - isometricImage V (M a)) =
      if a = a₀ then (aOp (isometricComplement V) : Matrix (R × S) _ ℂ) else 0 := by
    by_cases h : a = a₀ <;> simp [isometricEffect, h, aOp_zero]
  simp_rw [he]
  rw [Finset.sum_eq_single a₀]
  · simp
  · intro a _ h
    simp [h, snorm]
  · simp

theorem isometricEffect_bob_completion_error (W : Matrix S K ℂ) (a₀ : A)
    (M : A → Matrix K K ℂ) (φ : R × S → ℂ) :
    (∑ a, snorm φ (bOp (isometricEffect W a₀ M a - isometricImage W (M a))) ^ 2) =
      snorm φ (bOp (isometricComplement W)) ^ 2 := by
  have he (a : A) : bOp (isometricEffect W a₀ M a - isometricImage W (M a)) =
      if a = a₀ then (bOp (isometricComplement W) : Matrix (R × S) _ ℂ) else 0 := by
    by_cases h : a = a₀ <;> simp [isometricEffect, h, bOp_zero]
  simp_rw [he]
  rw [Finset.sum_eq_single a₀]
  · simp
  · intro a _ h
    simp [h, snorm]
  · simp

/-- Primitive ideal-state image estimates survive completing the measurement
to a normalized PVM, with no factor for the number of outcomes. -/
theorem isometricEffect_alice_error_le (V : Matrix R H ℂ) (W : Matrix S K ℂ)
    (hV : Vᴴ * V = 1) (ψ : H × K → ℂ) (φ : R × S → ℂ) (a₀ : A)
    (M : A → Matrix H H ℂ) (Q : A → Matrix R R ℂ) {δ η : ℝ}
    (hδ : ∑ a, snorm φ (aOp (isometricImage V (M a) - Q a)) ^ 2 ≤ δ)
    (hη : ‖evec (isometricState V W ψ - φ)‖ ^ 2 ≤ η) :
    ∑ a, snorm φ (aOp (isometricEffect V a₀ M a - Q a)) ^ 2 ≤ 2 * δ + 2 * η := by
  have h := sum_snorm_sq_triangle' φ (fun a => aOp (isometricEffect V a₀ M a))
    (fun a => aOp (isometricImage V (M a))) (fun a => aOp (Q a))
  simp_rw [← aOp_sub] at h
  rw [isometricEffect_alice_completion_error] at h
  have hc := (isometricComplement_alice_mass V W hV ψ φ).trans hη
  linarith

theorem isometricEffect_bob_error_le (V : Matrix R H ℂ) (W : Matrix S K ℂ)
    (hW : Wᴴ * W = 1) (ψ : H × K → ℂ) (φ : R × S → ℂ) (a₀ : A)
    (M : A → Matrix K K ℂ) (Q : A → Matrix S S ℂ) {δ η : ℝ}
    (hδ : ∑ a, snorm φ (bOp (isometricImage W (M a) - Q a)) ^ 2 ≤ δ)
    (hη : ‖evec (isometricState V W ψ - φ)‖ ^ 2 ≤ η) :
    ∑ a, snorm φ (bOp (isometricEffect W a₀ M a - Q a)) ^ 2 ≤ 2 * δ + 2 * η := by
  have h := sum_snorm_sq_triangle' φ (fun a => bOp (isometricEffect W a₀ M a))
    (fun a => bOp (isometricImage W (M a))) (fun a => bOp (Q a))
  simp_rw [← bOp_sub] at h
  rw [isometricEffect_bob_completion_error] at h
  have hc := (isometricComplement_bob_mass V W hW ψ φ).trans hη
  linarith

end Bipartite
end MIPRE.Introspection
end

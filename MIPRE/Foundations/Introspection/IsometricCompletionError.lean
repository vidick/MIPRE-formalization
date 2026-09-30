/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.IsometricStrategy
public import MIPRE.Foundations.LocalIsometry
public import MIPRE.Foundations.Commutation

@[expose] public section

/-! # The cost of completing isometric image measurements

The extracted ideal state need not lie exactly in the isometries' images.
Its image-complement mass is bounded by its squared distance to the actual
embedded state. Completing an image PVM at one outcome therefore adds only
a dimension-independent error, even when primitive estimates are stated on
the ideal state.

Stated for a local isometry `Φ : LocalIsometry M M'` of bipartite models (Phase 4 of
`planning/mipco-track.md`): the ideal state is the target's state `M'.ψ`, the embedded state is
`Φ.W M.ψ`, the image of an operator is `Φ.ΦA`, its complement `1 - Φ.ΦA 1`, and the completed
measurement is the transport `Φ.transportOpA` (`MIPRE/Foundations/LocalIsometry.lean`).
-/

noncomputable section
namespace MIPRE.Introspection
open Finset Classical
set_option linter.unusedSectionVars false

section General

variable {𝒞 : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] (Ψ : StateModel 𝒞)

/-- A projection annihilating one vector has at most the squared vector
distance as its mass on the state. Normalization is not required. -/
theorem projector_mass_le_state_distance (v : Ψ.H) (C : 𝒞) (hC : star C = C) (hCC : C * C = C)
    (hz : Ψ.π C v = 0) : Ψ.snorm C ^ 2 ≤ ‖v - Ψ.ψ‖ ^ 2 := by
  have hb := Ψ.bnd_one_of_isStarProjection ⟨hCC, hC⟩
  have he : Ψ.π C (Ψ.ψ - v) = Ψ.π C Ψ.ψ := by rw [map_sub, hz, sub_zero]
  have hn := hb (Ψ.ψ - v)
  rw [he, one_mul, norm_sub_rev] at hn
  exact sq_le_sq₀ (Ψ.snorm_nonneg C) (norm_nonneg _) |>.mpr hn

end General

variable {𝒞 𝒜 ℬ 𝒞' 𝒜' ℬ' : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [Ring 𝒞'] [StarRing 𝒞'] [Algebra ℂ 𝒞']
  [Ring 𝒜'] [StarRing 𝒜'] [Algebra ℂ 𝒜'] [Ring ℬ'] [StarRing ℬ'] [Algebra ℂ ℬ']
  {M : BipartiteModel 𝒞 𝒜 ℬ} {M' : BipartiteModel 𝒞' 𝒜' ℬ'}
  (Φ : BipartiteModel.LocalIsometry M M')

section Coarse

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder 𝒜'] [StarOrderedRing 𝒜']

/-- Coarse-graining a completed image measurement is the image of the
coarse-graining, with the same complement placed at the mapped default. -/
theorem transportA_map_op (a₀ : A) (P : POVMIn A 𝒜) (hP : IsPVMIn P.op) (f : A → B) (b : B) :
    ((Φ.transportA a₀ P hP).map f).op b = Φ.transportOpA (f a₀) (P.map f).op b := by
  rw [POVMIn.map_op]
  simp only [BipartiteModel.LocalIsometry.transportA_op,
    BipartiteModel.LocalIsometry.transportOpA, sum_add_distrib]
  rw [← map_sum, ← POVMIn.map_op]
  congr 1
  simp only [sum_ite_eq', mem_filter, mem_univ, true_and]
  by_cases h : f a₀ = b
  · subst b
    simp
  · simp [h, Ne.symm h]

end Coarse

theorem isometricComplement_alice_mass :
    M'.snorm (M'.πA (1 - Φ.ΦA 1)) ^ 2 ≤ ‖Φ.W M.ψ - M'.ψ‖ ^ 2 := by
  apply projector_mass_le_state_distance M'.toStateModel (Φ.W M.ψ)
  · rw [← map_star, Φ.star_compl_ΦA_one]
  · rw [← map_mul, Φ.compl_ΦA_one_mul_self]
  · exact Φ.π_πA_compl M.ψ

theorem isometricComplement_bob_mass :
    M'.snorm (M'.πB (1 - Φ.ΦB 1)) ^ 2 ≤ ‖Φ.W M.ψ - M'.ψ‖ ^ 2 :=
  isometricComplement_alice_mass Φ.swap

/-- Exactly one outcome receives the image complement. -/
theorem isometricEffect_alice_completion_error {A : Type*} [Fintype A] [DecidableEq A] (a₀ : A)
    (P : A → 𝒜) :
    (∑ a, M'.snorm (M'.πA (Φ.transportOpA a₀ P a - Φ.ΦA (P a))) ^ 2) =
      M'.snorm (M'.πA (1 - Φ.ΦA 1)) ^ 2 := by
  have he (a : A) : Φ.transportOpA a₀ P a - Φ.ΦA (P a) = if a = a₀ then 1 - Φ.ΦA 1 else 0 := by
    simp only [BipartiteModel.LocalIsometry.transportOpA, add_sub_cancel_left]
  simp_rw [he]
  rw [Finset.sum_eq_single a₀]
  · simp
  · intro a _ h
    simp [h, map_zero, M'.snorm_zero]
  · simp

theorem isometricEffect_bob_completion_error {B : Type*} [Fintype B] [DecidableEq B] (b₀ : B)
    (Q : B → ℬ) :
    (∑ b, M'.snorm (M'.πB (Φ.swap.transportOpA b₀ Q b - Φ.ΦB (Q b))) ^ 2) =
      M'.snorm (M'.πB (1 - Φ.ΦB 1)) ^ 2 :=
  isometricEffect_alice_completion_error Φ.swap b₀ Q

/-- Primitive ideal-state image estimates survive completing the measurement
to a normalized PVM, with no factor for the number of outcomes. -/
theorem isometricEffect_alice_error_le {A : Type*} [Fintype A] [DecidableEq A] (a₀ : A)
    (P : A → 𝒜) (Q : A → 𝒜') {δ η : ℝ}
    (hδ : ∑ a, M'.snorm (M'.πA (Φ.ΦA (P a) - Q a)) ^ 2 ≤ δ)
    (hη : ‖Φ.W M.ψ - M'.ψ‖ ^ 2 ≤ η) :
    ∑ a, M'.snorm (M'.πA (Φ.transportOpA a₀ P a - Q a)) ^ 2 ≤ 2 * δ + 2 * η := by
  have h := M'.sum_snorm_sq_triangle univ (fun a => M'.πA (Φ.transportOpA a₀ P a))
    (fun a => M'.πA (Φ.ΦA (P a))) (fun a => M'.πA (Q a))
  simp_rw [← map_sub] at h
  rw [isometricEffect_alice_completion_error] at h
  have hc := (isometricComplement_alice_mass Φ).trans hη
  linarith

theorem isometricEffect_bob_error_le {B : Type*} [Fintype B] [DecidableEq B] (b₀ : B)
    (Q : B → ℬ) (R : B → ℬ') {δ η : ℝ}
    (hδ : ∑ b, M'.snorm (M'.πB (Φ.ΦB (Q b) - R b)) ^ 2 ≤ δ)
    (hη : ‖Φ.W M.ψ - M'.ψ‖ ^ 2 ≤ η) :
    ∑ b, M'.snorm (M'.πB (Φ.swap.transportOpA b₀ Q b - R b)) ^ 2 ≤ 2 * δ + 2 * η :=
  isometricEffect_alice_error_le Φ.swap b₀ Q R hδ hη

end MIPRE.Introspection
end

end

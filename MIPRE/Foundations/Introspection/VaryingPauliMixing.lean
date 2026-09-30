/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.PauliMixing

@[expose] public section

/-! # Pauli mixing in question-dependent coordinate presentations

The number of sampled coordinates and both ancillary spaces can depend on the
question. This is the form used after splitting a retained register from its
complement. The register's ambient embeddings are not part of this statement.

In a bipartite model (Phase 4 of `planning/mipco-track.md`) the ancillary state of each question
is a model `Ξ x`, over algebras that may depend on the question too.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Weyl Classical

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A] {n : X → ℕ}
  {𝒞 𝒜 ℬ : X → Type*} [∀ x, Ring (𝒞 x)] [∀ x, StarRing (𝒞 x)] [∀ x, Algebra ℂ (𝒞 x)]
  [∀ x, Ring (𝒜 x)] [∀ x, StarRing (𝒜 x)] [∀ x, Algebra ℂ (𝒜 x)] [∀ x, StarModule ℂ (𝒜 x)]
  [∀ x, PartialOrder (𝒜 x)] [∀ x, StarOrderedRing (𝒜 x)] [∀ x, StarProper (𝒜 x)]
  [∀ x, Ring (ℬ x)] [∀ x, StarRing (ℬ x)] [∀ x, Algebra ℂ (ℬ x)] [∀ x, StarModule ℂ (ℬ x)]

/-- Averaged mixing when the retained register and its complement vary with the question. -/
theorem exists_pauli_mixing_varying
    (D : X → ℝ) (hD0 : ∀ x, 0 ≤ D x) (hD1 : ∑ x, D x = 1)
    (L : (x : X) → (Fin (n x) → F) →ₗ[F] (Fin (n x) → F))
    (Ξ : (x : X) → BipartiteModel (𝒞 x) (𝒜 x) (ℬ x)) (hΞ : ∀ x, ‖(Ξ x).ψ‖ = 1)
    (M : (x : X) → POVMIn ((Fin (n x) → F) × A) (Matrix (Fin (n x) → F) (Fin (n x) → F) (𝒜 x)))
    (hM : ∀ x, IsPVMIn (M x).op)
    {δ : ℝ} (hδ : ∑ x, D x * mixingError (L x) (Ξ x) (M x) ≤ δ) :
    ∃ Q : (x : X) → (Fin (n x) → F) → POVMIn A (𝒜 x),
      (∑ x, D x * ∑ p : (Fin (n x) → F) × A, ((Ξ x).reg (Fin (n x) → F)).stateSqNorm
        ((M x).op p - smulKron ((Q x p.1).op p.2) (synOf wZ (L x) p.1))) ≤
      2 * δ + 4 * Real.sqrt δ := by
  choose Q hQ using fun x => exists_pauli_mixing (L x) (Ξ x) (hΞ x) (M x) (hM x)
  refine ⟨Q, ?_⟩
  have hsum := Finset.sum_le_sum fun x (_ : x ∈ univ) =>
    mul_le_mul_of_nonneg_left (hQ x) (hD0 x)
  have hroot := (sum_weighted_sqrt_le D (fun x => mixingError (L x) (Ξ x) (M x)) hD0 hD1
    (fun x => mixingError_nonneg (L x) (Ξ x) (M x))).trans (Real.sqrt_le_sqrt hδ)
  have heq : (∑ x, D x * (2 * mixingError (L x) (Ξ x) (M x) +
      4 * Real.sqrt (mixingError (L x) (Ξ x) (M x)))) =
      2 * (∑ x, D x * mixingError (L x) (Ξ x) (M x)) +
      4 * ∑ x, D x * Real.sqrt (mixingError (L x) (Ξ x) (M x)) := by
    simp only [mul_add, Finset.sum_add_distrib, mul_left_comm (b := (2 : ℝ)),
      mul_left_comm (b := (4 : ℝ)), ← Finset.mul_sum]
  rw [heq] at hsum
  linarith

/-- A convenient universal constant for three error hypotheses bounded by `ε ≤ 1`. -/
theorem mixing_error_sqrt_bound {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    2 * (18 * ε) + 4 * Real.sqrt (18 * ε) ≤ 56 * Real.sqrt ε := by
  have hroot0 := Real.sqrt_nonneg ε
  have hroot1 := Real.sq_sqrt hε0
  have hroot18 := Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 18) hε0)
  have hle : ε ≤ Real.sqrt ε := by nlinarith [sq_nonneg (Real.sqrt ε - 1)]
  have h18 : Real.sqrt (18 * ε) ≤ 5 * Real.sqrt ε := by
    nlinarith [Real.sqrt_nonneg (18 * ε)]
  linarith

/-- The three readout hypotheses yield a dimension-independent `56 sqrt ε` bound. -/
theorem exists_pauli_mixing_sqrt
    (D : X → ℝ) (hD0 : ∀ x, 0 ≤ D x) (hD1 : ∑ x, D x = 1)
    (L : (x : X) → (Fin (n x) → F) →ₗ[F] (Fin (n x) → F))
    (Ξ : (x : X) → BipartiteModel (𝒞 x) (𝒜 x) (ℬ x)) (hΞ : ∀ x, ‖(Ξ x).ψ‖ = 1)
    (M : (x : X) → POVMIn ((Fin (n x) → F) × A) (Matrix (Fin (n x) → F) (Fin (n x) → F) (𝒜 x)))
    (hM : ∀ x, IsPVMIn (M x).op)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hmarg : ∑ x, D x * readoutMarginalError (L x) ((Ξ x).reg (Fin (n x) → F)) (M x).op ≤ ε)
    (hZ : ∑ x, D x * readoutCommutatorError ((Ξ x).reg (Fin (n x) → F)) (M x).op wZ
      LinearMap.id ≤ ε)
    (hX : ∑ x, D x * readoutCommutatorError ((Ξ x).reg (Fin (n x) → F)) (M x).op wX
      (CL.lperp (L x)) ≤ ε) :
    ∃ Q : (x : X) → (Fin (n x) → F) → POVMIn A (𝒜 x),
      (∑ x, D x * ∑ p : (Fin (n x) → F) × A, ((Ξ x).reg (Fin (n x) → F)).stateSqNorm
        ((M x).op p - smulKron ((Q x p.1).op p.2) (synOf wZ (L x) p.1))) ≤
      56 * Real.sqrt ε := by
  have hδ : ∑ x, D x * mixingError (L x) (Ξ x) (M x) ≤ 18 * ε := by
    simp only [mixingError, mul_add, Finset.sum_add_distrib,
      mul_left_comm (b := (2 : ℝ)), mul_left_comm (b := (8 : ℝ)), ← Finset.mul_sum]
    linarith
  obtain ⟨Q, hQ⟩ := exists_pauli_mixing_varying D hD0 hD1 L Ξ hΞ M hM hδ
  exact ⟨Q, hQ.trans (mixing_error_sqrt_bound hε0 hε1)⟩

end MIPRE.Introspection

end

end

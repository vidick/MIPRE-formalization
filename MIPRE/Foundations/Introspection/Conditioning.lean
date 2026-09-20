/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Expanded

/-! # Conditioning on a classical question register

Exact squared-norm identities behind `lem:conditional` and
`lem:commutation-simplification`. The question-indexed versions allow different
tensor decompositions for different outcomes; they introduce no dimension factor.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix
open scoped Kronecker

variable {V W H K : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

/-- A product operator's squared state norm factors over a product state. -/
theorem stateSqNorm_expVec_kron (ψ : V × W → ℂ) (ξ : H × K → ℂ)
    (Q : Matrix V V ℂ) (A : Matrix H H ℂ) :
    stateSqNorm (expVec ψ ξ) (Q ⊗ₖ A) = stateSqNorm ψ Q * stateSqNorm ξ A := by
  unfold stateSqNorm stateNorm stateVec
  change ‖evec _‖ ^ 2 = ‖evec _‖ ^ 2 * ‖evec _‖ ^ 2
  rw [mulVec_kron_expVec, norm_evec_expVec, mul_pow]

/-- The identity's squared state norm is the squared norm of the state. -/
theorem stateSqNorm_one_eq (ψ : V × W → ℂ) :
    stateSqNorm ψ (1 : Matrix V V ℂ) = ‖evec ψ‖ ^ 2 := by
  simp only [stateSqNorm, stateNorm, stateVec, Matrix.one_kronecker_one,
    Matrix.one_mulVec]
  rfl

/-- Selecting a question fibre is exactly averaging with its Born weight. -/
theorem conditional_sqNorm (ψ : V × W → ℂ) (ξ : H × K → ℂ)
    (hψ : ‖evec ψ‖ = 1) (hξ : ‖evec ξ‖ = 1)
    (Q : Matrix V V ℂ) (A B : Matrix H H ℂ) :
    stateSqNorm (expVec ψ ξ) (Q ⊗ₖ A - Q ⊗ₖ B) =
      stateSqNorm (expVec ψ ξ) (Q ⊗ₖ (1 : Matrix H H ℂ)) *
        stateSqNorm (expVec ψ ξ) ((1 : Matrix V V ℂ) ⊗ₖ A -
          (1 : Matrix V V ℂ) ⊗ₖ B) := by
  have hsub (P : Matrix V V ℂ) : P ⊗ₖ A - P ⊗ₖ B = P ⊗ₖ (A - B) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.kroneckerMap_apply]
    ring
  rw [hsub Q, hsub 1, stateSqNorm_expVec_kron, stateSqNorm_expVec_kron,
    stateSqNorm_expVec_kron, stateSqNorm_one_eq, stateSqNorm_one_eq, hψ, hξ]
  ring

/-- A common projector factors out of a commutator. -/
theorem kron_projector_commutator (Q : Matrix V V ℂ) (hQ : Q * Q = Q)
    (A B : Matrix H H ℂ) :
    (Q ⊗ₖ A) * (Q ⊗ₖ B) - (Q ⊗ₖ B) * (Q ⊗ₖ A) =
      Q ⊗ₖ (A * B) - Q ⊗ₖ (B * A) := by
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hQ]

/-- Removing the shared question projector preserves precisely the conditional error. -/
theorem conditional_commutator (ψ : V × W → ℂ) (ξ : H × K → ℂ)
    (hψ : ‖evec ψ‖ = 1) (hξ : ‖evec ξ‖ = 1)
    (Q : Matrix V V ℂ) (hQ : Q * Q = Q) (A B : Matrix H H ℂ) :
    stateSqNorm (expVec ψ ξ)
        ((Q ⊗ₖ A) * (Q ⊗ₖ B) - (Q ⊗ₖ B) * (Q ⊗ₖ A)) =
      stateSqNorm (expVec ψ ξ) (Q ⊗ₖ (1 : Matrix H H ℂ)) *
        stateSqNorm (expVec ψ ξ)
          (((1 : Matrix V V ℂ) ⊗ₖ A) * ((1 : Matrix V V ℂ) ⊗ₖ B) -
            ((1 : Matrix V V ℂ) ⊗ₖ B) * ((1 : Matrix V V ℂ) ⊗ₖ A)) := by
  rw [kron_projector_commutator Q hQ, kron_projector_commutator 1 (one_mul 1)]
  exact conditional_sqNorm ψ ξ hψ hξ Q (A * B) (B * A)

section VaryingRegisters

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
  {V W H K : X → Type*}
  [∀ x, Fintype (V x)] [∀ x, DecidableEq (V x)]
  [∀ x, Fintype (W x)] [∀ x, DecidableEq (W x)]
  [∀ x, Fintype (H x)] [∀ x, DecidableEq (H x)]
  [∀ x, Fintype (K x)] [∀ x, DecidableEq (K x)]

/-- Conditioning with outcome-dependent tensor decompositions, summing every answer. -/
theorem conditional_sqNorm_sum
    (ψ : (x : X) → V x × W x → ℂ) (ξ : (x : X) → H x × K x → ℂ)
    (hψ : ∀ x, ‖evec (ψ x)‖ = 1) (hξ : ∀ x, ‖evec (ξ x)‖ = 1)
    (Q : (x : X) → Matrix (V x) (V x) ℂ)
    (A B : (x : X) → Y → Matrix (H x) (H x) ℂ) :
    (∑ x, ∑ y, stateSqNorm (expVec (ψ x) (ξ x))
      (Q x ⊗ₖ A x y - Q x ⊗ₖ B x y)) =
    ∑ x, stateSqNorm (expVec (ψ x) (ξ x)) (Q x ⊗ₖ (1 : Matrix (H x) _ ℂ)) *
      ∑ y, stateSqNorm (expVec (ψ x) (ξ x))
        ((1 : Matrix (V x) _ ℂ) ⊗ₖ A x y - (1 : Matrix (V x) _ ℂ) ⊗ₖ B x y) := by
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => conditional_sqNorm (ψ x) (ξ x) (hψ x) (hξ x)
    (Q x) (A x y) (B x y)

/-- The commutation-simplification identity with varying question and answer registers. -/
theorem conditional_commutator_sum
    (ψ : (x : X) → V x × W x → ℂ) (ξ : (x : X) → H x × K x → ℂ)
    (hψ : ∀ x, ‖evec (ψ x)‖ = 1) (hξ : ∀ x, ‖evec (ξ x)‖ = 1)
    (Q : (x : X) → Matrix (V x) (V x) ℂ) (hQ : ∀ x, Q x * Q x = Q x)
    (A : (x : X) → Y → Matrix (H x) (H x) ℂ)
    (B : (x : X) → Z → Matrix (H x) (H x) ℂ) :
    (∑ x, ∑ y, ∑ z, stateSqNorm (expVec (ψ x) (ξ x))
      ((Q x ⊗ₖ A x y) * (Q x ⊗ₖ B x z) - (Q x ⊗ₖ B x z) * (Q x ⊗ₖ A x y))) =
    ∑ x, stateSqNorm (expVec (ψ x) (ξ x)) (Q x ⊗ₖ (1 : Matrix (H x) _ ℂ)) *
      ∑ y, ∑ z, stateSqNorm (expVec (ψ x) (ξ x))
        (((1 : Matrix (V x) _ ℂ) ⊗ₖ A x y) * ((1 : Matrix (V x) _ ℂ) ⊗ₖ B x z) -
          ((1 : Matrix (V x) _ ℂ) ⊗ₖ B x z) * ((1 : Matrix (V x) _ ℂ) ⊗ₖ A x y)) := by
  apply Finset.sum_congr rfl
  intro x _
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  exact Finset.sum_congr rfl fun z _ => conditional_commutator (ψ x) (ξ x) (hψ x) (hξ x)
    (Q x) (hQ x) (A x y) (B x z)

end VaryingRegisters

end MIPRE.Introspection

end

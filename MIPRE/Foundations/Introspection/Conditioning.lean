/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Expanded
public import MIPRE.Foundations.AncillaModel

@[expose] public section

/-! # Conditioning on a classical question register

Exact squared-norm identities behind `lem:conditional` and
`lem:commutation-simplification`. The question-indexed versions allow different
tensor decompositions for different outcomes; they introduce no dimension factor.

In a bipartite model (Phase 4 of `planning/mipco-track.md`) the auxiliary state is a model `Ξ`,
and the question register a vector `ψ` of `ℂ^{V × W}` adjoined to it
(`BipartiteModel.expand`): a product operator `Q ⊗ A` of the matrix analysis is `smulKron A Q`.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix
open scoped Kronecker ComplexOrder

set_option linter.unusedSectionVars false

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- The identity's squared state norm is the squared norm of the state. -/
theorem stateSqNorm_one_eq (ψ : V × W → ℂ) :
    stateSqNorm ψ (1 : Matrix V V ℂ) = ‖evec ψ‖ ^ 2 := by
  simp only [stateSqNorm, stateNorm, stateVec, Matrix.one_kronecker_one,
    Matrix.one_mulVec]
  rfl

section Model

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [StarModule ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]
  (Ξ : BipartiteModel 𝒞 𝒜 ℬ)

/-- A product operator's squared state norm factors over a product state. -/
theorem stateSqNorm_expand_smulKron (ψ : V × W → ℂ) (Q : Matrix V V ℂ) (A : 𝒜) :
    (Ξ.expand ψ).stateSqNorm (smulKron A Q) = stateSqNorm ψ Q * Ξ.stateSqNorm A := by
  rw [BipartiteModel.stateSqNorm_eq_bornProb_one, star_smulKron, smulKron_mul,
    ← smulKron_one_one (R := ℬ),
    BipartiteModel.bornProb_expand_smulKron Ξ ψ _ _ (Matrix.posSemidef_conjTranspose_mul_self Q)
      PosSemidef.one,
    BipartiteModel.stateSqNorm_eq_bornProb_one, stateSqNorm_eq, MIPRE.bornProb]

/-- The squared norm of the identity on a unit state. -/
theorem stateSqNorm_one_of_norm (hΞ : ‖Ξ.ψ‖ = 1) : Ξ.stateSqNorm 1 = 1 := by
  rw [BipartiteModel.stateSqNorm, BipartiteModel.stateNorm, map_one, Ξ.snorm_one hΞ, one_pow]

/-- Selecting a question fibre is exactly averaging with its Born weight. -/
theorem conditional_sqNorm (ψ : V × W → ℂ) (hψ : ‖evec ψ‖ = 1) (hΞ : ‖Ξ.ψ‖ = 1)
    (Q : Matrix V V ℂ) (A B : 𝒜) :
    (Ξ.expand ψ).stateSqNorm (smulKron A Q - smulKron B Q) =
      (Ξ.expand ψ).stateSqNorm (smulKron 1 Q) *
        (Ξ.expand ψ).stateSqNorm (smulKron A 1 - smulKron B 1) := by
  rw [smulKron_sub_left, smulKron_sub_left, stateSqNorm_expand_smulKron,
    stateSqNorm_expand_smulKron, stateSqNorm_expand_smulKron, stateSqNorm_one_eq,
    stateSqNorm_one_of_norm Ξ hΞ, hψ]
  ring

/-- A common projector factors out of a commutator. -/
theorem smulKron_projector_commutator (Q : Matrix V V ℂ) (hQ : Q * Q = Q) (A B : 𝒜) :
    smulKron A Q * smulKron B Q - smulKron B Q * smulKron A Q =
      smulKron (A * B) Q - smulKron (B * A) Q := by
  rw [smulKron_mul, smulKron_mul, hQ]

/-- Removing the shared question projector preserves precisely the conditional error. -/
theorem conditional_commutator (ψ : V × W → ℂ) (hψ : ‖evec ψ‖ = 1) (hΞ : ‖Ξ.ψ‖ = 1)
    (Q : Matrix V V ℂ) (hQ : Q * Q = Q) (A B : 𝒜) :
    (Ξ.expand ψ).stateSqNorm (smulKron A Q * smulKron B Q - smulKron B Q * smulKron A Q) =
      (Ξ.expand ψ).stateSqNorm (smulKron 1 Q) *
        (Ξ.expand ψ).stateSqNorm (smulKron A 1 * smulKron B 1 - smulKron B 1 * smulKron A 1) := by
  rw [smulKron_projector_commutator Q hQ, smulKron_projector_commutator 1 (one_mul 1)]
  exact conditional_sqNorm Ξ ψ hψ hΞ Q (A * B) (B * A)

end Model

section VaryingRegisters

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z] {V W : X → Type*}
  [∀ x, Fintype (V x)] [∀ x, DecidableEq (V x)] [∀ x, Fintype (W x)] [∀ x, DecidableEq (W x)]
  {𝒞 𝒜 ℬ : X → Type*} [∀ x, Ring (𝒞 x)] [∀ x, StarRing (𝒞 x)] [∀ x, Algebra ℂ (𝒞 x)]
  [∀ x, Ring (𝒜 x)] [∀ x, StarRing (𝒜 x)] [∀ x, Algebra ℂ (𝒜 x)] [∀ x, StarModule ℂ (𝒜 x)]
  [∀ x, Ring (ℬ x)] [∀ x, StarRing (ℬ x)] [∀ x, Algebra ℂ (ℬ x)]

/-- Conditioning with outcome-dependent tensor decompositions, summing every answer. -/
theorem conditional_sqNorm_sum (Ξ : (x : X) → BipartiteModel (𝒞 x) (𝒜 x) (ℬ x))
    (ψ : (x : X) → V x × W x → ℂ) (hψ : ∀ x, ‖evec (ψ x)‖ = 1) (hΞ : ∀ x, ‖(Ξ x).ψ‖ = 1)
    (Q : (x : X) → Matrix (V x) (V x) ℂ) (A B : (x : X) → Y → 𝒜 x) :
    (∑ x, ∑ y, ((Ξ x).expand (ψ x)).stateSqNorm (smulKron (A x y) (Q x) - smulKron (B x y) (Q x))) =
    ∑ x, ((Ξ x).expand (ψ x)).stateSqNorm (smulKron 1 (Q x)) *
      ∑ y, ((Ξ x).expand (ψ x)).stateSqNorm (smulKron (A x y) 1 - smulKron (B x y) 1) := by
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => conditional_sqNorm (Ξ x) (ψ x) (hψ x) (hΞ x)
    (Q x) (A x y) (B x y)

/-- The commutation-simplification identity with varying question and answer registers. -/
theorem conditional_commutator_sum (Ξ : (x : X) → BipartiteModel (𝒞 x) (𝒜 x) (ℬ x))
    (ψ : (x : X) → V x × W x → ℂ) (hψ : ∀ x, ‖evec (ψ x)‖ = 1) (hΞ : ∀ x, ‖(Ξ x).ψ‖ = 1)
    (Q : (x : X) → Matrix (V x) (V x) ℂ) (hQ : ∀ x, Q x * Q x = Q x)
    (A : (x : X) → Y → 𝒜 x) (B : (x : X) → Z → 𝒜 x) :
    (∑ x, ∑ y, ∑ z, ((Ξ x).expand (ψ x)).stateSqNorm
      (smulKron (A x y) (Q x) * smulKron (B x z) (Q x) -
        smulKron (B x z) (Q x) * smulKron (A x y) (Q x))) =
    ∑ x, ((Ξ x).expand (ψ x)).stateSqNorm (smulKron 1 (Q x)) *
      ∑ y, ∑ z, ((Ξ x).expand (ψ x)).stateSqNorm
        (smulKron (A x y) 1 * smulKron (B x z) 1 - smulKron (B x z) 1 * smulKron (A x y) 1) := by
  apply Finset.sum_congr rfl
  intro x _
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  exact Finset.sum_congr rfl fun z _ => conditional_commutator (Ξ x) (ψ x) (hψ x) (hΞ x)
    (Q x) (hQ x) (A x y) (B x z)

end VaryingRegisters

end MIPRE.Introspection

end

end

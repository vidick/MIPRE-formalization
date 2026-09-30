/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.ConditionalNormalizerStep
public import MIPRE.Foundations.Introspection.ConditionalNormalizerIdealMirror

@[expose] public section

/-! # The next hiding step on an EPR seed with arbitrary auxiliaries

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the EPR seed beside an
arbitrary auxiliary state is the register model `Ξ.reg (ι → F)` of an arbitrary model `Ξ`, whose
players hold the matrices over `ι → F` with entries in `Ξ`'s algebras, and an honest register
operator `P`, a complex matrix, acts as `smulKron 1 P` for either player. The honest operators are
symmetric, so the mirror identity of the register model (`BipartiteModel.reg_mirror`) makes each of
them an exact mirror of itself, and the step is `hideCoarseOp_step_of_normalizer` in the register
model. Register families are embedded, with their coarse-grainings and conditional ideals, by
`fibSumIn_smulKron_one` and `conditionalIdeal_smulKron_one` (`ConditionalNormalizerStep.lean`).
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical

set_option linter.unusedSectionVars false

namespace Honest

variable {F ι A PauliAnswer : Type*}
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype PauliAnswer] {ℓ : ℕ}

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]

/-- Exact ideal mirrors persist with any bipartite auxiliary model. -/
theorem hideCoarseOp_registerState_mirror (P : CL.CLFun F ι ℓ) (k : ℕ)
    (h : P.SupportedOn univ) (Ξ : BipartiteModel 𝒞 𝒜 ℬ) (i : Option (HideLabel F ι)) :
    (Ξ.reg (ι → F)).π ((Ξ.reg (ι → F)).πA (smulKron 1 (hideCoarseOp P k h i)))
        (Ξ.reg (ι → F)).ψ =
      (Ξ.reg (ι → F)).π ((Ξ.reg (ι → F)).πB (smulKron 1 (hideCoarseOp P k h i)))
        (Ξ.reg (ι → F)).ψ := by
  have he := Ξ.reg_mirror (hideCoarseOp P k h i)
  rwa [hideCoarseOp_transpose] at he

theorem hidingPrefixOp_registerState_mirror (P : CL.CLFun F ι ℓ) (k : ℕ)
    (Ξ : BipartiteModel 𝒞 𝒜 ℬ) (y : Option (ι → F)) :
    (Ξ.reg (ι → F)).π ((Ξ.reg (ι → F)).πA (smulKron 1 (hidingPrefixOp P k y)))
        (Ξ.reg (ι → F)).ψ =
      (Ξ.reg (ι → F)).π ((Ξ.reg (ι → F)).πB (smulKron 1 (hidingPrefixOp P k y)))
        (Ξ.reg (ι → F)).ψ := by
  have he := Ξ.reg_mirror (hidingPrefixOp P k y)
  rwa [hidingPrefixOp_transpose] at he

/-- The next honest prefix commutes with the current coarse Hide measurement, both embedded in the
matrices over any algebra. -/
theorem hidingPrefixOp_aux_commute {R : Type*} [Ring R] [Algebra ℂ R] (P : CL.CLFun F ι ℓ)
    (k : ℕ) (h : P.SupportedOn univ) (y : Option (ι → F)) (i : Option (HideLabel F ι)) :
    Commute (smulKron (1 : R) (hidingPrefixOp P (k + 1) y)) (smulKron 1 (hideCoarseOp P k h i)) :=
  commute_smulKron_one (hidingPrefixOp_commute_coarse P k h (hideLabelCoarse P k) y i)

/-- The paired normalizer bound implies rigidity of the actual next coarse
Hide measurement on the full seed/auxiliary carrier. All ideal mirrors and
conditional product identities are supplied by the honest construction. -/
theorem hideCoarseOp_aux_step_of_normalizer [StarModule ℂ 𝒜] [PartialOrder ℬ]
    [StarOrderedRing ℬ] [StarProper ℬ] (P : CL.CLFun F ι ℓ) (k : ℕ)
    (hk : k + 1 < ℓ) (h : P.SupportedOn univ)
    (Ξ : BipartiteModel 𝒞 𝒜 ℬ) (hΞ : ‖Ξ.ψ‖ = 1)
    (N : POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) ℬ))
    (hN : IsPVMIn N.op) {δ : ℝ}
    (hpaired : ∑ p, (Ξ.reg (ι → F)).snorm
      ((Ξ.reg (ι → F)).πB ((N.map (TypedEstimates.hidingNextLater P k)).op p) -
        (Ξ.reg (ι → F)).πB (conditionalIdeal (fun i => smulKron 1 (hideCoarseOp P k h i))
          (fun y => smulKron 1 (hidingPrefixOp P (k + 1) y))
          (TypedEstimates.hidingNextGuarded P k) p)) ^ 2 ≤ δ) :
    (∑ z, (Ξ.reg (ι → F)).xSqNorm (smulKron 1 (hideCoarseOp P (k + 1) h z))
      ((N.map (TypedEstimates.hidingCoarse P (k + 1))).op z)) ≤ δ :=
  hideCoarseOp_step_of_normalizer P k hk h (Ξ.reg (ι → F))
    (by rw [BipartiteModel.norm_reg_ψ, hΞ]) N hN
    (hideCoarseOp_registerState_mirror P k h Ξ) (hidingPrefixOp_registerState_mirror P (k + 1) Ξ)
    hpaired

end Honest

end MIPRE.Introspection

end

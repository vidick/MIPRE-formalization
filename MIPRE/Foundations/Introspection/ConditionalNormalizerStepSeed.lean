/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.ConditionalNormalizerStep
public import MIPRE.Foundations.Introspection.ConditionalNormalizerIdealMirror
public import MIPRE.Foundations.Introspection.HidingNormalizer

@[expose] public section

/-! # An actual adjacent hiding rigidity step on the EPR seed

All ideal measurements, commutation facts, exact mirrors, and label identities
are explicit. The remaining quantitative inputs are the preceding fine error,
the next prefix marginal error, and the actual parsed game's failure.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the EPR seed is the register
model `Ξ.reg (ι → F)` of a model `Ξ` --- the seed alone being the instance in which `Ξ` is trivial
--- the strategy is a pair of POVM families of matrices over `ι → F` with entries in `Ξ`'s algebras,
and an honest register operator `P` acts as `smulKron 1 P`. The exact mirrors of the honest
operators are the mirror identity of the register model (`BipartiteModel.reg_mirror`), the honest
operators being symmetric.
-/

noncomputable section

namespace MIPRE.Introspection.TypedEstimates

open Finset Matrix Classical Honest

set_option linter.unusedSectionVars false

variable {PauliType PauliAnswer F ι κ A : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype A] {ℓ : ℕ}

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]

/-- A single actual adjacent hiding test propagates fine honest rigidity to
the next level with error `6 |E| ε + 3 η + 3 εfine`. This theorem assumes no
ideal commutation, exact-mirror, or accepted-answer contract. -/
theorem hiding_next_seed_rigidity [StarModule ℂ 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
    [StarProper 𝒜] [StarModule ℂ ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ] [StarProper ℬ]
    (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
      PauliAnswer → PauliAnswer → Bool)
    (Ξ : BipartiteModel 𝒞 𝒜 ℬ) (hΞ : ‖Ξ.ψ‖ = 1)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) 𝒜))
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) ℬ))
    {ε η εfine : ℝ}
    (hfail : 1 - (Ξ.reg (ι → F)).povmValue (parsedGame E X Z P L projectPauli D DP) MA MB ≤ ε)
    (w : Bool) (k j : Fin ℓ) (hk : k.val + 1 = j.val)
    (hL : (L w).SupportedOn univ)
    (hMA : IsPVMIn (MA (QuestionType.hide w k, 0)).op)
    (hMB : IsPVMIn (MB (QuestionType.hide w j, 0)).op)
    (hfine : ∑ i, (Ξ.reg (ι → F)).xSqNorm
      (((MA (QuestionType.hide w k, 0)).map (hidingCoarse (L w) k.val)).op i)
      (smulKron 1 (hideCoarseOp (L w) k.val hL i)) ≤ εfine)
    (hnorm : ∑ y, (Ξ.reg (ι → F)).snorm ((Ξ.reg (ι → F)).πB
      ((∑ z, ((MB (QuestionType.hide w j, 0)).map
        (hidingNextLater (L w) k.val)).op (y, z)) -
          smulKron 1 (hidingPrefixOp (L w) j.val y))) ^ 2 ≤ η) :
    (∑ z, (Ξ.reg (ι → F)).xSqNorm (smulKron 1 (hideCoarseOp (L w) j.val hL z))
      (((MB (QuestionType.hide w j, 0)).map (hidingCoarse (L w) j.val)).op z)) ≤
        6 * (TypeGraph.edges E X Z ℓ).card * ε + 3 * η + 3 * εfine := by
  have hunit : ‖(Ξ.reg (ι → F)).ψ‖ = 1 := by rw [BipartiteModel.norm_reg_ψ, hΞ]
  have hnorm' : ∑ y, (Ξ.reg (ι → F)).snorm ((Ξ.reg (ι → F)).πB
      ((∑ z, ((MB (QuestionType.hide w j, 0)).map
        (hidingNextLater (L w) k.val)).op (y, z)) -
          smulKron 1 (hidingPrefixOp (L w) (k.val + 1) y))) ^ 2 ≤ η := by
    simpa only [hk] using hnorm
  have hpaired := hiding_next_normalizer_estimate E X Z P L projectPauli D DP
    (Ξ.reg (ι → F)) hunit MA MB hfail w k j hk hL hMA hMB
    (fun i => smulKron 1 (hideCoarseOp (L w) k.val hL i))
    (fun y => smulKron 1 (hidingPrefixOp (L w) (k.val + 1) y))
    (hideCoarseOp_isPVM (L w) k.val hL).toIn.smulKron_one
    (hidingPrefixOp_isPVM (L w) (k.val + 1)).toIn.smulKron_one
    (fun y i => commute_smulKron_one
      (hidingPrefixOp_commute_coarse (L w) k.val hL (hideLabelCoarse (L w) k.val) y i))
    hfine hnorm'
  have hstep := hideCoarseOp_step_of_normalizer (L w) k.val (by omega) hL
    (Ξ.reg (ι → F)) hunit (MB (QuestionType.hide w j, 0)) hMB
    (fun i => by
      have he := Ξ.reg_mirror (hideCoarseOp (L w) k.val hL i)
      rwa [hideCoarseOp_transpose] at he)
    (fun y => by
      have he := Ξ.reg_mirror (hidingPrefixOp (L w) (k.val + 1) y)
      rwa [hidingPrefixOp_transpose] at he)
    hpaired
  simpa only [hk] using hstep

end MIPRE.Introspection.TypedEstimates

end

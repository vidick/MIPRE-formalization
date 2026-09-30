/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.ConditionalNormalizerStepAux
public import MIPRE.Foundations.Introspection.HidingNormalizer
public import MIPRE.Foundations.Introspection.HidingNormalizerPrefix

@[expose] public section

/-! # A concrete adjacent hiding rigidity step in the actual parsed game

The state has the extracted EPR seed and an arbitrary normalized auxiliary
state. Only the preceding fine estimate and the Introspect-prefix estimate
are induction inputs. The actual game supplies the conditional relation and
propagates the required normalizer through its hiding/Read/Introspect chain.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the state is the register
model `Ξ.reg (ι → F)` of a normalized auxiliary model, and the honest operators enter as
`smulKron 1 _`.
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

/-- The actual next Hide measurement is rigid with no dimension or answer
alphabet factor. All ideal commutation, mirror, and accepted-answer facts are
proved from the construction. The remaining inputs are the preceding fine
rigidity and the Introspect-prefix estimate from sampling/Pauli extraction. -/
theorem hiding_next_register_rigidity [StarModule ℂ 𝒜] [PartialOrder 𝒜]
    [StarOrderedRing 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]
    [StarProper ℬ]
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
    {ε δ εfine : ℝ}
    (hfail : 1 - (Ξ.reg (ι → F)).povmValue (parsedGame E X Z P L projectPauli D DP) MA MB ≤ ε)
    (w : Bool) (k j : Fin ℓ) (hk : k.val + 1 = j.val)
    (hL : (L w).SupportedOn univ)
    (hMA : IsPVMIn (MA (QuestionType.hide w k, 0)).op)
    (hMB : IsPVMIn (MB (QuestionType.hide w j, 0)).op)
    (hfine : ∑ i, (Ξ.reg (ι → F)).xSqNorm
      (((MA (QuestionType.hide w k, 0)).map (hidingCoarse (L w) k.val)).op i)
      (smulKron 1 (hideCoarseOp (L w) k.val hL i)) ≤ εfine)
    (hintro : ∑ y, (Ξ.reg (ι → F)).snorm ((Ξ.reg (ι → F)).πB
      (((MB (QuestionType.introspect w, 0)).map
        (reportedPrefix (L w) j.val .introspect)).op y -
          smulKron 1 (hidingPrefixOp (L w) j.val y))) ^ 2 ≤ δ) :
    (∑ z, (Ξ.reg (ι → F)).xSqNorm (smulKron 1 (hideCoarseOp (L w) j.val hL z))
      (((MB (QuestionType.hide w j, 0)).map (hidingCoarse (L w) j.val)).op z)) ≤
        (6 + 48 * ((ℓ - j.val + 1 : ℕ) : ℝ) ^ 2) * (TypeGraph.edges E X Z ℓ).card * ε +
          6 * δ + 3 * εfine := by
  have hunit : ‖(Ξ.reg (ι → F)).ψ‖ = 1 := by rw [BipartiteModel.norm_reg_ψ, hΞ]
  let Q (y : Option (ι → F)) : Matrix (ι → F) (ι → F) ℬ :=
    smulKron 1 (hidingPrefixOp (L w) (k.val + 1) y)
  have hi : ∑ y, (Ξ.reg (ι → F)).snorm ((Ξ.reg (ι → F)).πB
      (((MB (QuestionType.introspect w, 0)).map
        (reportedPrefix (L w) (k.val + 1) .introspect)).op y - Q y)) ^ 2 ≤ δ := by
    simpa only [Q, hk] using hintro
  have hn := hidingNormalizer_estimate E X Z P L projectPauli D DP
    (Ξ.reg (ι → F)) hunit MA MB hfail w k j hk hL Q hi
  have hp := hiding_next_normalizer_estimate E X Z P L projectPauli D DP
    (Ξ.reg (ι → F)) hunit MA MB hfail w k j hk hL hMA hMB
    (fun i => smulKron 1 (hideCoarseOp (L w) k.val hL i)) Q
    (hideCoarseOp_isPVM (L w) k.val hL).toIn.smulKron_one
    (hidingPrefixOp_isPVM (L w) (k.val + 1)).toIn.smulKron_one
    (hidingPrefixOp_aux_commute (L w) k.val hL) hfine hn
  have hs := hideCoarseOp_aux_step_of_normalizer (L w) k.val (by omega) hL Ξ hΞ
    (MB (QuestionType.hide w j, 0)) hMB hp
  rw [hk] at hs
  exact hs.trans_eq (by ring)

end MIPRE.Introspection.TypedEstimates

end

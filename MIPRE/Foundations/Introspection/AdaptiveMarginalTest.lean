/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.ProductStageZTests
public import MIPRE.Foundations.Introspection.AdaptivePrefixMarginal

@[expose] public section

/-! # The actual game controls Alice's next-prefix marginal

Bob's prefix rigidity follows from Sample and primitive Z extraction. The
actual Introspect consistency loop and the exact EPR mirror transfer this
estimate to Alice, with no assumed Alice prefix rigidity or alphabet loss.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the extracted register state is
the register model `Ξ.reg (ι → F)` of a normalized auxiliary model `Ξ`, and the exact mirror is the
register model's (`Honest.hidingPrefixOp_registerState_mirror`).
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

/-- Every Alice Introspect-prefix marginal is controlled by the actual
consistency and Sample tests and the primitive Bob-Z error. Malformed and
unattainable outcomes remain in the complete option-valued alphabet. -/
theorem introspect_prefix_register_rigidity_alice [StarModule ℂ 𝒜] [PartialOrder 𝒜]
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
    {ε η : ℝ}
    (hfail : 1 - (Ξ.reg (ι → F)).povmValue (parsedGame E X Z P L projectPauli D DP) MA MB ≤ ε)
    (q : κ → ZMod 2) (hq : ∀ z, (P Z).eval z = q)
    (w : Bool) (hL : (L w).SupportedOn univ)
    (hS : IsPVMIn (MA (QuestionType.sample w, 0)).op)
    (hZ : ∑ z, (Ξ.reg (ι → F)).snorm ((Ξ.reg (ι → F)).πB
      (((MB (QuestionType.pauli Z, q)).map (pauliProjection projectPauli)).op z -
        smulKron 1 (readout (some : (ι → F) → Option (ι → F)) z))) ^ 2 ≤ η)
    (j : ℕ) :
    (∑ y, (Ξ.reg (ι → F)).stateSqNorm
      (((MA (QuestionType.introspect w, 0)).map (reportedPrefix (L w) j .introspect)).op y -
        smulKron 1 (hidingPrefixOp (L w) j y))) ≤
      8 * η + 28 * (TypeGraph.edges E X Z ℓ).card * ε := by
  have hBob := introspect_prefix_register_rigidity_bob E X Z P L projectPauli D DP
    Ξ hΞ MA MB hfail q hq w hL hS hZ j
  have hψ : ‖(Ξ.reg (ι → F)).ψ‖ = 1 := by rw [BipartiteModel.norm_reg_ψ, hΞ]
  have hloop := aux_agreement_estimate E X Z P
    (questionCheck L X Z projectPauli D DP) (Ξ.reg (ι → F)) hψ MA MB hfail
    .introspect .introspect w w (TypeGraph.adj_self E X Z (QuestionType.introspect w))
    (reportedPrefix (L w) j .introspect) (reportedPrefix (L w) j .introspect)
    (fun a b hab => congrArg (reportedPrefix (L w) j .introspect)
      (TypedPredicate.check_consistency L X Z projectPauli D (fun p s => DP p s 0 0) hab))
  have ht := same_side_via_common_other (Ξ.reg (ι → F))
    (fun y => ((MA (QuestionType.introspect w, 0)).map (reportedPrefix (L w) j .introspect)).op y)
    (fun y => smulKron 1 (hidingPrefixOp (L w) j y))
    (fun y => ((MB (QuestionType.introspect w, 0)).map (reportedPrefix (L w) j .introspect)).op y)
  simp only [xSqNorm_eq_bOp_distance_of_mirror _ _ _ _
    (hidingPrefixOp_registerState_mirror (L w) j Ξ _), ← map_sub] at ht
  linarith only [ht, hloop, hBob]

end MIPRE.Introspection.TypedEstimates
end

end

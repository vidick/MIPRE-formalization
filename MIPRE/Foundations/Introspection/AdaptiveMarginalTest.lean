/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.ProductStageZTests
import MIPRE.Foundations.Introspection.AdaptivePrefixMarginal

/-! # The actual game controls Alice's next-prefix marginal

Bob's prefix rigidity follows from Sample and primitive Z extraction. The
actual Introspect consistency loop and the exact EPR mirror transfer this
estimate to Alice, with no assumed Alice prefix rigidity or alphabet loss.
-/

noncomputable section
namespace MIPRE.Introspection.TypedEstimates

open Finset Matrix Classical Honest
set_option linter.unusedSectionVars false

variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype A]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}

set_option backward.isDefEq.respectTransparency false in
/-- Every Alice Introspect-prefix marginal is controlled by the actual
consistency and Sample tests and the primitive Bob-Z error. Malformed and
unattainable outcomes remain in the complete option-valued alphabet. -/
theorem introspect_prefix_register_rigidity_alice
    (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
      PauliAnswer → PauliAnswer → Bool)
    (ξ : H × K → ℂ) (hξ : star ξ ⬝ᵥ ξ = 1)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H))
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × K))
    {ε η : ℝ}
    (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP)
      (registerState (ι → F) ξ) MA MB ≤ ε)
    (q : κ → ZMod 2) (hq : ∀ z, (P Z).eval z = q)
    (w : Bool) (hL : (L w).SupportedOn univ)
    (hS : IsPVM (fun a => ((MA (QuestionType.sample w, 0)).mats a).val))
    (hZ : ∑ z, snorm (registerState (ι → F) ξ) (bOp
      ((((MB (QuestionType.pauli Z, q)).map (pauliProjection projectPauli)).mats z).val -
        (aOp (readout (some : (ι → F) → Option (ι → F)) z) :
          Matrix ((ι → F) × K) _ ℂ))) ^ 2 ≤ η)
    (j : ℕ) :
    (∑ y, stateSqNorm (registerState (ι → F) ξ)
      ((((MA (QuestionType.introspect w, 0)).map
        (reportedPrefix (L w) j .introspect)).mats y).val -
          (aOp (hidingPrefixOp (L w) j y) : Matrix ((ι → F) × H) _ ℂ))) ≤
      8 * η + 28 * (TypeGraph.edges E X Z ℓ).card * ε := by
  have hBob := introspect_prefix_register_rigidity_bob E X Z P L projectPauli D DP
    ξ hξ MA MB hfail q hq w hL hS hZ j
  have hψ : star (registerState (ι → F) ξ) ⬝ᵥ registerState (ι → F) ξ = 1 := by
    rw [dotProduct_star_self, registerState_norm ξ (norm_evec_eq_one_of_unit hξ)]
    norm_num
  have hloop := aux_agreement_estimate E X Z P
    (questionCheck L X Z projectPauli D DP) (registerState (ι → F) ξ) hψ MA MB hfail
    .introspect .introspect w w (TypeGraph.adj_self E X Z (QuestionType.introspect w))
    (reportedPrefix (L w) j .introspect) (reportedPrefix (L w) j .introspect)
    (fun a b hab => congrArg (reportedPrefix (L w) j .introspect)
      (TypedPredicate.check_consistency L X Z projectPauli D (fun p s => DP p s 0 0) hab))
  have ht := same_side_via_common_other (registerState (ι → F) ξ)
    (fun y => (((MA (QuestionType.introspect w, 0)).map
      (reportedPrefix (L w) j .introspect)).mats y).val)
    (fun y => (aOp (hidingPrefixOp (L w) j y) : Matrix ((ι → F) × H) _ ℂ))
    (fun y => (((MB (QuestionType.introspect w, 0)).map
      (reportedPrefix (L w) j .introspect)).mats y).val)
  have hmirror (y : Option (ι → F)) :
      aOp (aOp (hidingPrefixOp (L w) j y) : Matrix ((ι → F) × H) _ ℂ) *ᵥ
        registerState (ι → F) ξ =
      bOp (aOp (hidingPrefixOp (L w) j y) : Matrix ((ι → F) × K) _ ℂ) *ᵥ
        registerState (ι → F) ξ :=
    coarseZ_registerState_mirror (fun z => some (((L w).truncate j).eval z)) y ξ
  simp only [xSqNorm_eq_bOp_distance_of_mirror _ _ _ _ (hmirror _), ← bOp_sub] at ht
  linarith only [ht, hloop, hBob]

end MIPRE.Introspection.TypedEstimates
end

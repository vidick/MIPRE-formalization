/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AdaptivePlayerSwap
import MIPRE.Foundations.Introspection.ProductStageZTests

/-! # The tested Pauli loop supplies the second primitive Z estimate

The actual constant Pauli-Z loop compares both players' complete projected
answer alphabets. Combining it with Bob's extracted Z guarantee and the
exact computational-readout mirror yields Alice's Z guarantee. No additional
extraction hypothesis is needed when starting Bob's induction.
-/

noncomputable section
namespace MIPRE.Introspection.TypedEstimates
open Finset Matrix Classical
set_option linter.unusedSectionVars false

variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype A]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}

set_option backward.isDefEq.respectTransparency false in
/-- Actual loop consistency transfers the primitive Z estimate to Alice,
including the malformed Pauli outcome. -/
theorem introAliceZError_le_of_bob
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
    (q : κ → ZMod 2) (hq : ∀ z, (P Z).eval z = q)
    {ε η : ℝ}
    (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP)
      (registerState (ι → F) ξ) MA MB ≤ ε)
    (hZ : introBobZError projectPauli Z q ξ MB ≤ η) :
    introAliceZError projectPauli Z q ξ MA ≤
      4 * (TypeGraph.edges E X Z ℓ).card * ε + 2 * η := by
  have hψ : star (registerState (ι → F) ξ) ⬝ᵥ registerState (ι → F) ξ = 1 := by
    rw [dotProduct_star_self, registerState_norm ξ (norm_evec_eq_one_of_unit hξ)]
    norm_num
  have hloop := constant_edge_agreement_estimate E X Z P
    (questionCheck L X Z projectPauli D DP) (registerState (ι → F) ξ) hψ MA MB hfail
    (QuestionType.pauli Z) (QuestionType.pauli Z) q q hq hq
    (TypeGraph.adj_self E X Z (QuestionType.pauli Z))
    (pauliProjection projectPauli) (pauliProjection projectPauli)
    (fun a b hab => congrArg (pauliProjection projectPauli)
      (TypedPredicate.check_consistency L X Z projectPauli D (fun p s => DP p s q q) hab))
  have ht := sampling_replace_bob (registerState (ι → F) ξ)
    (fun z => (((MA (QuestionType.pauli Z, q)).map (pauliProjection projectPauli)).mats z).val)
    (fun z => (((MB (QuestionType.pauli Z, q)).map (pauliProjection projectPauli)).mats z).val)
    (fun z => (aOp (readout (some : (ι → F) → Option (ι → F)) z) :
      Matrix ((ι → F) × K) _ ℂ)) hloop hZ
  simp only [xSqNorm_eq_stateSqNorm_of_mirror _ _ _ _
    (coarseZ_registerState_mirror (some : (ι → F) → Option (ι → F)) _ ξ)] at ht
  have heq : introAliceZError projectPauli Z q ξ MA =
      ∑ z, stateSqNorm (registerState (ι → F) ξ)
        ((aOp (readout (some : (ι → F) → Option (ι → F)) z) :
          Matrix ((ι → F) × H) _ ℂ) -
          (((MA (QuestionType.pauli Z, q)).map (pauliProjection projectPauli)).mats z).val) := by
    unfold introAliceZError
    apply Finset.sum_congr rfl
    intro z _
    simp only [stateSqNorm, stateNorm, norm_stateVec_eq_snorm, aOp_sub]
    rw [snorm_sub_comm]
  rw [heq]
  linarith

end MIPRE.Introspection.TypedEstimates
end

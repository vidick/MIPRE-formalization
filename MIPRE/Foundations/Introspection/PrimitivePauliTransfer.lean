/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.AdaptivePlayerSwap
public import MIPRE.Foundations.Introspection.ProductStageZTests

@[expose] public section

/-! # The tested Pauli loop supplies the second primitive Z estimate

The actual constant Pauli-Z loop compares both players' complete projected
answer alphabets. Combining it with Bob's extracted Z guarantee and the
exact computational-readout mirror yields Alice's Z guarantee. No additional
extraction hypothesis is needed when starting Bob's induction.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the register state is the
register model `Ξ.reg (ι → F)` of a normalized auxiliary model `Ξ`, the strategy is a pair of
POVM families of matrices over `ι → F` with entries in `Ξ`'s algebras, and the honest
computational readout enters as `smulKron 1 _` for either player. Its exact mirror is the vector
identity `coarseZ_registerState_mirror`, which turns the cross-party distance to the readout on
Bob's side into Alice's same-side error (`xSqNorm_eq_stateSqNorm_of_mirror`).
-/

noncomputable section
namespace MIPRE.Introspection.TypedEstimates
open Finset Matrix Classical
set_option linter.unusedSectionVars false

variable {PauliType PauliAnswer F ι κ A : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype A] {ℓ : ℕ}
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]

/-- Actual loop consistency transfers the primitive Z estimate to Alice,
including the malformed Pauli outcome. -/
theorem introAliceZError_le_of_bob [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarProper 𝒜]
    [PartialOrder ℬ] [StarOrderedRing ℬ] [StarProper ℬ]
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
    (q : κ → ZMod 2) (hq : ∀ z, (P Z).eval z = q)
    {ε η : ℝ}
    (hfail : 1 - (Ξ.reg (ι → F)).povmValue (parsedGame E X Z P L projectPauli D DP) MA MB ≤ ε)
    (hZ : introBobZError projectPauli Z q Ξ MB ≤ η) :
    introAliceZError projectPauli Z q Ξ MA ≤
      4 * (TypeGraph.edges E X Z ℓ).card * ε + 2 * η := by
  have hψ : ‖(Ξ.reg (ι → F)).ψ‖ = 1 := by rw [BipartiteModel.norm_reg_ψ, hΞ]
  have hloop := constant_edge_agreement_estimate E X Z P
    (questionCheck L X Z projectPauli D DP) (Ξ.reg (ι → F)) hψ MA MB hfail
    (QuestionType.pauli Z) (QuestionType.pauli Z) q q hq hq
    (TypeGraph.adj_self E X Z (QuestionType.pauli Z))
    (pauliProjection projectPauli) (pauliProjection projectPauli)
    (fun a b hab => congrArg (pauliProjection projectPauli)
      (TypedPredicate.check_consistency L X Z projectPauli D (fun p s => DP p s q q) hab))
  have ht := sampling_replace_bob (Ξ.reg (ι → F))
    (fun z => ((MA (QuestionType.pauli Z, q)).map (pauliProjection projectPauli)).op z)
    (fun z => ((MB (QuestionType.pauli Z, q)).map (pauliProjection projectPauli)).op z)
    (fun z => smulKron 1 (readout (some : (ι → F) → Option (ι → F)) z)) hloop hZ
  simp only [xSqNorm_eq_stateSqNorm_of_mirror _ _ _ _
    (coarseZ_registerState_mirror (some : (ι → F) → Option (ι → F)) _ Ξ)] at ht
  have heq : introAliceZError projectPauli Z q Ξ MA =
      ∑ z, (Ξ.reg (ι → F)).stateSqNorm
        (smulKron 1 (readout (some : (ι → F) → Option (ι → F)) z) -
          ((MA (QuestionType.pauli Z, q)).map (pauliProjection projectPauli)).op z) :=
    Finset.sum_congr rfl fun _ _ => (Ξ.reg (ι → F)).stateSqNorm_sub_comm _ _
  rw [heq]
  linarith

end MIPRE.Introspection.TypedEstimates
end

end

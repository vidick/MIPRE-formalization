/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.AdaptiveMarginalGame
public import MIPRE.Foundations.Introspection.AdaptiveZTest
public import MIPRE.Foundations.Introspection.AdaptiveXTest
public import MIPRE.Foundations.Introspection.AdaptiveStageBudget

@[expose] public section

/-! # An adaptive dilation from the actual parsed game tests

The three mixing errors are derived from the current game's failure,
primitive Z extraction, and the fixed hiding approximation. Deterministic
answer refinement retains all malformed mass. The common-ancilla residual
projectors are then constructed by the proved mixing and dilation theorem.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the extracted register state is
the register model `Ξ.reg (ι → F)` of a normalized auxiliary model `Ξ`, the product form is one of
POVMs in the matrices over the remaining registers with entries in its first algebra, and the
common ancilla is the dilation ancilla `DilationAncilla _ K` of `exists_adaptive_prefix_dilation`,
whose size `K` the theorem returns.
-/

noncomputable section
namespace MIPRE.Introspection.TypedEstimates
open Finset Matrix Classical Weyl
set_option linter.unusedSectionVars false

variable {PauliType PauliAnswer F ι κ A : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype A] {ℓ : ℕ}
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [StarModule ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [StarModule ℂ ℬ]
  [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarProper 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ]
  [StarProper ℬ]

variable
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
  {ε η δ : ℝ} (hε : 0 ≤ ε) (hη : 0 ≤ η) (hδ : 0 ≤ δ)
  (hfail : 1 - (Ξ.reg (ι → F)).povmValue (parsedGame E X Z P L projectPauli D DP) MA MB ≤ ε)
  (q : κ → ZMod 2) (hq : ∀ z, (P Z).eval z = q)
  (w : Bool) (hL : (L w).SupportedOn univ) (j : Fin ℓ)
  (hSA : IsPVMIn (MA (QuestionType.sample w, 0)).op)
  (hSB : IsPVMIn (MB (QuestionType.sample w, 0)).op)
  (hZ : ∑ z, (Ξ.reg (ι → F)).snorm ((Ξ.reg (ι → F)).πB
    (((MB (QuestionType.pauli Z, q)).map (pauliProjection projectPauli)).op z -
      smulKron 1 (readout (some : (ι → F) → Option (ι → F)) z))) ^ 2 ≤ η)
  (hHide : IsPVMIn (MA (QuestionType.hide w j, 0)).op)
  (hRead : IsPVMIn (MB (QuestionType.read w, 0)).op)
  (hfine : ∑ i, (Ξ.reg (ι → F)).xSqNorm
    (((MA (QuestionType.hide w j, 0)).map (hidingCoarse (L w) j.val)).op i)
    (smulKron 1 (Honest.hideCoarseOp (L w) j.val hL i)) ≤ δ)
  (M : (y : ι → F) → POVMIn (Option ((ι → F) × A))
    (Matrix (stageRemaining (L w) j.val y → F) (stageRemaining (L w) j.val y → F) 𝒜))
  (hform : ∀ a, ((MA (QuestionType.introspect w, 0)).map introspectPair).op a =
    ∑ y, prefixResidualOp (L w) j.val y ((M y).op a))
  (hsupport : ∀ y x a, (L w).outputPrefix j.val x ≠ y → (M y).op (some (x, a)) = 0)

include hΞ hε hη hδ hfail hq hSA hSB hZ hHide hRead hfine hform hsupport

/-- All three errors required by mixing follow from the actual tests and
the current structural prefix invariant, under one explicit budget. -/
theorem introspect_refined_stage_bounds :
    let budget := adaptiveStageBudget (ℓ - j.val)
      ((TypeGraph.edges E X Z ℓ).card * ε) η δ
    let R := fun y p => (stageAnswerRefinementPOVM (L w) j.val y (M y)).op p
    prefixStageMarginalError (L w) hL j.val Ξ R ≤ budget ∧
    prefixStageCommutatorError (L w) hL j.val Ξ R
      (fun _ => wZ) (fun _ => LinearMap.id) ≤ budget ∧
    prefixStageCommutatorError (L w) hL j.val Ξ R
      (fun _ => wX) (fun y => CL.lperp (coordinateLinear (CLChecks.stageLinear (L w) j.val y)))
      ≤ budget := by
  dsimp only
  simp only [stageAnswerRefinementPOVM_mats]
  have he : 0 ≤ (TypeGraph.edges E X Z ℓ).card * ε := mul_nonneg (Nat.cast_nonneg _) hε
  have hm := introspect_adaptive_marginal E X Z P L projectPauli D DP Ξ hΞ MA MB
    hfail q hq w hL hSA hZ j.val (fun y a => (M y).op a) hform hsupport
  have hz := introspect_adaptiveZ_commutator E X Z P L projectPauli D DP Ξ hΞ MA MB
    hfail q hq w hSB hZ hL j.val (fun y a => (M y).op a) hform
  have hx := introspect_adaptiveX_commutator E X Z P L projectPauli D DP Ξ hΞ MA MB
    hfail w hL j hHide hRead hfine (fun y a => (M y).op a) hform
  refine ⟨hm.trans ?_, ?_, ?_⟩
  · simpa only [mul_assoc] using marginal_le_adaptiveStageBudget (ℓ - j.val) he hη hδ
  · rw [stageAnswerRefinement_commutator]
    apply hz.trans
    simpa only [mul_assoc] using
      (Z_le_adaptiveStageBudget (z := η) (ℓ - j.val) he hδ)
  · rw [stageAnswerRefinement_commutator]
    apply hx.trans
    simpa only [mul_assoc] using
      (X_le_adaptiveStageBudget (h := δ) (ℓ - j.val) he hη)

-- The structural `DecidableEq` instance of the dilation ancilla over the option-valued answer
-- alphabet exceeds the default instance size; with it, the statement's instance is the one
-- `exists_adaptive_prefix_dilation` produces.
set_option synthInstance.maxSize 512 in
/-- Actual game tests construct the common-ancilla adaptive projectors.
Only the current prefix product form and its answer support are structural
inputs; none of the three analytic mixing estimates is assumed. -/
theorem exists_game_adaptive_prefix_dilation
    (hM : ∀ y, IsPVMIn (M y).op)
    (hsmall : adaptiveStageBudget (ℓ - j.val)
      ((TypeGraph.edges E X Z ℓ).card * ε) η δ ≤ 1) :
    ∃ (K : ℕ) (R : AdaptiveDilationFamily (L w) j.val 𝒜
        (DilationAncilla (Option ((ι → F) × A)) K) (Option ((ι → F) × A)))
      (hR : ∀ y z, IsPVMIn (R y z)),
      (∑ p, ((Ξ.reg (ι → F)).expandA
          (Sum.inl (none, 0) : DilationAncilla (Option ((ι → F) × A)) K)).stateSqNorm
        ((diagonal fun _ => (adaptiveOldJointPOVM (L w) hL j.val
          (fun y => stageAnswerRefinementPOVM (L w) j.val y (M y))).op p) -
            (adaptiveReplacementPOVM (L w) hL j.val R hR).op p)) ≤
        2 * Real.sqrt (56 * Real.sqrt (adaptiveStageBudget (ℓ - j.val)
          ((TypeGraph.edges E X Z ℓ).card * ε) η δ)) := by
  have hb := introspect_refined_stage_bounds E X Z P L projectPauli D DP Ξ hΞ MA MB
    hε hη hδ hfail q hq w hL j hSA hSB hZ hHide hRead hfine M hform hsupport
  have hb0 := adaptiveStageBudget_nonneg (ℓ - j.val)
    (mul_nonneg (Nat.cast_nonneg (TypeGraph.edges E X Z ℓ).card) hε) hη hδ
  obtain ⟨K, R, hR, hd⟩ := exists_adaptive_prefix_dilation Ξ (L w) hL j.val hΞ
    (none : Option ((ι → F) × A))
    (fun y => stageAnswerRefinementPOVM (L w) j.val y (M y))
    (fun y => stageAnswerRefinementPOVM_isPVM (L w) j.val y (M y) (hM y))
    hb0 hsmall hb.1 hb.2.1 hb.2.2
  exact ⟨K, R, hR, adaptiveReplacement_distance Ξ (L w) hL j.val _ _ R hR hd⟩

end MIPRE.Introspection.TypedEstimates
end

end

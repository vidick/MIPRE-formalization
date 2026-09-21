/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AdaptiveMarginalGame
import MIPRE.Foundations.Introspection.AdaptiveZTest
import MIPRE.Foundations.Introspection.AdaptiveXTest
import MIPRE.Foundations.Introspection.AdaptiveStageBudget

/-! # An adaptive dilation from the actual parsed game tests

The three mixing errors are derived from the current game's failure,
primitive Z extraction, and the fixed hiding approximation. Deterministic
answer refinement retains all malformed mass. The common-ancilla residual
projectors are then constructed by the proved mixing and dilation theorem.
-/

noncomputable section
namespace MIPRE.Introspection.TypedEstimates
open Finset Matrix Classical Weyl
set_option linter.unusedSectionVars false

variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype A]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}

variable
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
  {ε η δ : ℝ} (hε : 0 ≤ ε) (hη : 0 ≤ η) (hδ : 0 ≤ δ)
  (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP)
    (registerState (ι → F) ξ) MA MB ≤ ε)
  (q : κ → ZMod 2) (hq : ∀ z, (P Z).eval z = q)
  (w : Bool) (hL : (L w).SupportedOn univ) (j : Fin ℓ)
  (hSA : IsPVM (fun a => ((MA (QuestionType.sample w, 0)).mats a).val))
  (hSB : IsPVM (fun a => ((MB (QuestionType.sample w, 0)).mats a).val))
  (hZ : ∑ z, snorm (registerState (ι → F) ξ) (bOp
    ((((MB (QuestionType.pauli Z, q)).map (pauliProjection projectPauli)).mats z).val -
      (aOp (readout (some : (ι → F) → Option (ι → F)) z) :
        Matrix ((ι → F) × K) _ ℂ))) ^ 2 ≤ η)
  (hHide : IsPVM (fun a => ((MA (QuestionType.hide w j, 0)).mats a).val))
  (hRead : IsPVM (fun a => ((MB (QuestionType.read w, 0)).mats a).val))
  (hfine : ∑ i, xSqNorm (registerState (ι → F) ξ)
    ((((MA (QuestionType.hide w j, 0)).map (hidingCoarse (L w) j.val)).mats i).val)
    (aOp (Honest.hideCoarseOp (L w) j.val hL i) : Matrix ((ι → F) × K) _ ℂ) ≤ δ)
  (M : (y : ι → F) → POVM (Option ((ι → F) × A))
    ((stageRemaining (L w) j.val y → F) × H))
  (hform : ∀ a, (((MA (QuestionType.introspect w, 0)).map introspectPair).mats a).val =
    ∑ y, prefixResidualOp (L w) j.val y ((M y).mats a).val)
  (hsupport : ∀ y x a, (L w).outputPrefix j.val x ≠ y →
    ((M y).mats (some (x, a))).val = 0)

include hξ hε hη hδ hfail hq hSA hSB hZ hHide hRead hfine hform hsupport

set_option backward.isDefEq.respectTransparency false in
/-- All three errors required by mixing follow from the actual tests and
the current structural prefix invariant, under one explicit budget. -/
theorem introspect_refined_stage_bounds :
    let budget := adaptiveStageBudget (ℓ - j.val)
      ((TypeGraph.edges E X Z ℓ).card * ε) η δ
    let R := fun y p => ((stageAnswerRefinementPOVM (L w) j.val y (M y)).mats p).val
    prefixStageMarginalError (L w) hL j.val ξ R ≤ budget ∧
    prefixStageCommutatorError (L w) hL j.val ξ R
      (fun _ => wZ) (fun _ => LinearMap.id) ≤ budget ∧
    prefixStageCommutatorError (L w) hL j.val ξ R
      (fun _ => wX) (fun y => CL.lperp (coordinateLinear (CLChecks.stageLinear (L w) j.val y)))
      ≤ budget := by
  dsimp only
  simp only [stageAnswerRefinementPOVM_mats]
  have he : 0 ≤ (TypeGraph.edges E X Z ℓ).card * ε := mul_nonneg (Nat.cast_nonneg _) hε
  have hm := introspect_adaptive_marginal E X Z P L projectPauli D DP ξ hξ MA MB
    hfail q hq w hL hSA hZ j.val (fun y a => ((M y).mats a).val) hform hsupport
  have hz := introspect_adaptiveZ_commutator E X Z P L projectPauli D DP ξ hξ MA MB
    hfail q hq w hSB hZ hL j.val (fun y a => ((M y).mats a).val) hform
  have hx := introspect_adaptiveX_commutator E X Z P L projectPauli D DP ξ hξ MA MB
    hfail w hL j hHide hRead hfine (fun y a => ((M y).mats a).val) hform
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

set_option backward.isDefEq.respectTransparency false in
/-- Actual game tests construct the common-ancilla adaptive projectors.
Only the current prefix product form and its answer support are structural
inputs; none of the three analytic mixing estimates is assumed. -/
theorem exists_game_adaptive_prefix_dilation
    (hM : ∀ y, IsPVM (fun a => ((M y).mats a).val))
    (hsmall : adaptiveStageBudget (ℓ - j.val)
      ((TypeGraph.edges E X Z ℓ).card * ε) η δ ≤ 1) :
    ∃ (R : AdaptiveDilationFamily (L w) j.val H (Option ((ι → F) × A)))
      (hR : ∀ y z, IsPVM (R y z)),
      (∑ p, stateSqNorm (extVecA (registerState (ι → F) ξ) (none : Option ((ι → F) × A)))
        (aOp ((adaptiveOldJointPOVM (L w) hL j.val
          (fun y => stageAnswerRefinementPOVM (L w) j.val y (M y))
          (fun y => stageAnswerRefinementPOVM_isPVM (L w) j.val y (M y) (hM y))).mats p).val -
            ((adaptiveReplacementPOVM (L w) hL j.val R hR).mats p).val)) ≤
        2 * Real.sqrt (56 * Real.sqrt (adaptiveStageBudget (ℓ - j.val)
          ((TypeGraph.edges E X Z ℓ).card * ε) η δ)) := by
  have hb := introspect_refined_stage_bounds E X Z P L projectPauli D DP ξ hξ MA MB
    hε hη hδ hfail q hq w hL j hSA hSB hZ hHide hRead hfine M hform hsupport
  have hb0 := adaptiveStageBudget_nonneg (ℓ - j.val)
    (mul_nonneg (Nat.cast_nonneg (TypeGraph.edges E X Z ℓ).card) hε) hη hδ
  obtain ⟨R, hR, hd⟩ := exists_adaptive_prefix_dilation (L w) hL j.val ξ
    (norm_evec_eq_one_of_unit hξ) (none : Option ((ι → F) × A))
    (fun y => stageAnswerRefinementPOVM (L w) j.val y (M y))
    (fun y => stageAnswerRefinementPOVM_isPVM (L w) j.val y (M y) (hM y))
    hb0 hsmall hb.1 hb.2.1 hb.2.2
  exact ⟨R, hR, adaptiveReplacement_distance (L w) hL j.val ξ none _ _ R hR hd⟩

end MIPRE.Introspection.TypedEstimates
end

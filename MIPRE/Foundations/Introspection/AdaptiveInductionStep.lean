/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AdaptiveInductionInvariant
import MIPRE.Foundations.Introspection.AdaptiveSelectedMeasurement
import MIPRE.Foundations.Introspection.AdaptiveGameStage
import MIPRE.Foundations.Introspection.StrategyReplacementErrors

/-! # A successor of the actual Introspect induction

The current game's tests construct the replacement. Canonicalization and
decoder recovery discharge the selected-measurement identity, and decoding
gives the next structural invariant. The fixed hiding and primitive Z
errors can be reused on the enlarged auxiliary space.
-/

noncomputable section
namespace MIPRE.Introspection
open Finset Matrix Classical Weyl
set_option linter.unusedSectionVars false

variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype A] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K] {ℓ : ℕ}

/-- The actual question-indexed family after inserting the decoded
replacement, with the original family retained at every other question. -/
def introSuccessorFamily (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ) (k : ℕ)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H)) (w : Bool)
    (R : AdaptiveDilationFamily P k H (Option ((ι → F) × A)))
    (hR : ∀ y z, IsPVM (R y z)) :=
  registeredReplacement MA (QuestionType.introspect w, 0)
    ((adaptiveReplacementPOVM P hP k R hR).map
      (fun p => restoreIntroAnswer (nextOptionDecoder P k (advanceStageAnswer P k p))))

theorem introSuccessorFamily_isPVM (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H)) (w : Bool)
    (R : AdaptiveDilationFamily P k H (Option ((ι → F) × A)))
    (hR : ∀ y z, IsPVM (R y z))
    (hMA : ∀ q, IsPVM (fun a => ((MA q).mats a).val))
    (q : CL.Detyping.Question (QuestionType PauliType ℓ) κ) :
    IsPVM (fun a => ((introSuccessorFamily P hP k MA w R hR q).mats a).val) := by
  apply registeredReplacement_isPVM _ _ _ hMA
  exact isPVM_povm_map _ (adaptiveReplacementPOVM_isPVM P hP k R hR) _

/-- The returned raw selected measurement carries the complete next
option-valued product form, including valid-answer support. -/
def introSuccessorInvariant (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ) (k : ℕ)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H)) (w : Bool)
    (R : AdaptiveDilationFamily P k H (Option ((ι → F) × A)))
    (hR : ∀ y z, IsPVM (R y z)) :
    IntroPrefixInvariant P (k + 1)
      ((introSuccessorFamily P hP k MA w R hR (QuestionType.introspect w, 0)).map
        TypedEstimates.introspectPair) where
  residual := nextPrefixDecodedPOVM P hP k none R hR (nextOptionDecoder P k)
  projective := nextPrefixDecodedPOVM_option_isPVM P hP k R hR
  form := registeredReplacement_nextOption_mats P hP k R hR MA (QuestionType.introspect w, 0)
  support := nextPrefixDecodedPOVM_some_support P hP k R hR

namespace TypedEstimates

/-- The primitive Bob-Z error in the common registered state. -/
def introBobZError (projectPauli : PauliAnswer → ι → F) (Z : PauliType)
    (q : κ → ZMod 2) (ξ : H × K → ℂ)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × K)) : ℝ :=
  ∑ z, snorm (registerState (ι → F) ξ) (bOp
    ((((MB (QuestionType.pauli Z, q)).map (pauliProjection projectPauli)).mats z).val -
      (aOp (readout (some : (ι → F) → Option (ι → F)) z) :
        Matrix ((ι → F) × K) _ ℂ))) ^ 2

theorem introBobZError_extVecA (projectPauli : PauliAnswer → ι → F) (Z : PauliType)
    (q : κ → ZMod 2) (ξ : H × K → ℂ)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × K)) :
    introBobZError projectPauli Z q (extVecA ξ (none : Option ((ι → F) × A))) MB =
      introBobZError projectPauli Z q ξ MB :=
  pauliBobError_registeredExtension ξ none projectPauli MB Z q (readout some)

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The actual current tests produce a projective next family and its
complete prefix invariant. No selected-measurement or mixing-error bound
is assumed: those are derived from the supplied current invariant. -/
theorem exists_intro_successor
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
    (hMA : ∀ q, IsPVM (fun a => ((MA q).mats a).val))
    (hMB : ∀ q, IsPVM (fun a => ((MB q).mats a).val))
    (q : κ → ZMod 2) (hq : ∀ z, (P Z).eval z = q)
    (w : Bool) (hL : (L w).SupportedOn univ) (j : Fin ℓ)
    (I : IntroPrefixInvariant (L w) j.val
      ((MA (QuestionType.introspect w, 0)).map introspectPair))
    {ε η δ : ℝ} (hε : 0 ≤ ε) (hη : 0 ≤ η) (hδ : 0 ≤ δ)
    (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP)
      (registerState (ι → F) ξ) MA MB ≤ ε)
    (hZ : introBobZError projectPauli Z q ξ MB ≤ η)
    (hhide : hidingAliceError L w hL ξ MA j ≤ δ)
    (hsmall : adaptiveStageBudget (ℓ - j.val)
      ((TypeGraph.edges E X Z ℓ).card * ε) η δ ≤ 1) :
    ∃ (MA' : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
        POVM (ParsedAnswer (ι → F) A PauliAnswer)
          ((ι → F) × (H × Option ((ι → F) × A))))
      (_ : IntroPrefixInvariant (L w) (j.val + 1)
        ((MA' (QuestionType.introspect w, 0)).map introspectPair)),
      (∀ t, IsPVM (fun a => ((MA' t).mats a).val)) ∧
      1 - povmValue (parsedGame E X Z P L projectPauli D DP)
        (registerState (ι → F) (extVecA ξ (none : Option ((ι → F) × A)))) MA' MB ≤
          ε + adaptiveStepLoss (adaptiveStageBudget (ℓ - j.val)
            ((TypeGraph.edges E X Z ℓ).card * ε) η δ) ∧
      (∀ t, t ≠ (QuestionType.introspect w, 0) → MA' t = registeredExtendPOVM (MA t)) ∧
      (∀ i : Fin ℓ, hidingAliceError L w hL
        (extVecA ξ (none : Option ((ι → F) × A))) MA' i = hidingAliceError L w hL ξ MA i) := by
  obtain ⟨R, hR, hd⟩ := exists_game_adaptive_prefix_dilation E X Z P L projectPauli D DP
    ξ hξ MA MB hε hη hδ hfail q hq w hL j
    (hMA _) (hMB _) hZ (hMA _) (hMB _) hhide
    I.residual I.form I.support I.projective hsmall
  let J := adaptiveOldJointPOVM (L w) hL j.val
    (fun y => stageAnswerRefinementPOVM (L w) j.val y (I.residual y))
    (fun y => stageAnswerRefinementPOVM_isPVM (L w) j.val y (I.residual y) (I.projective y))
  let N := adaptiveReplacementPOVM (L w) hL j.val R hR
  let f := fun p : AdaptiveStageAnswer (L w) j.val (Option ((ι → F) × A)) =>
    restoreIntroAnswer (PauliAnswer := PauliAnswer)
      (nextOptionDecoder (L w) j.val (advanceStageAnswer (L w) j.val p))
  have hselected : canonicalizeIntro MA w (QuestionType.introspect w, 0) = J.map f :=
    canonicalizeIntro_adaptive_selected (L w) hL j.val MA w
      I.residual I.projective I.form I.support
  have hv := replaceExtended_value (parsedGame E X Z P L projectPauli D DP)
    (registerState (ι → F) ξ) (registerState_norm ξ (norm_evec_eq_one_of_unit hξ))
    (none : Option ((ι → F) × A)) (canonicalizeIntro MA w) MB
    (QuestionType.introspect w, 0) J N f hselected
    (adaptiveOldJointPOVM_isPVM (L w) hL j.val _ _) (adaptiveReplacementPOVM_isPVM _ _ _ R hR)
    hMB hd
  rw [← registeredReplacement_value_eq (parsedGame E X Z P L projectPauli D DP)
      ξ none (canonicalizeIntro MA w) MB (QuestionType.introspect w, 0) (N.map f),
    canonicalizeIntro_value, registeredReplacement_canonicalizeIntro] at hv
  refine ⟨introSuccessorFamily (L w) hL j.val MA w R hR,
    introSuccessorInvariant (L w) hL j.val MA w R hR,
    introSuccessorFamily_isPVM (L w) hL j.val MA w R hR hMA, ?_, ?_, ?_⟩
  · have hloss := (abs_sub_le_iff.mp hv).1
    change 1 - povmValue (parsedGame E X Z P L projectPauli D DP)
      (registerState (ι → F) (extVecA ξ (none : Option ((ι → F) × A))))
      (registeredReplacement MA (QuestionType.introspect w, 0) (N.map f)) MB ≤ _
    unfold adaptiveStepLoss
    linarith
  · intro t ht
    exact registeredReplacement_other_eq MA (QuestionType.introspect w, 0) t (N.map f) ht
  · intro i
    exact hidingAliceError_registeredReplacement L w w hL ξ none MA (N.map f) i

end TypedEstimates
end MIPRE.Introspection
end

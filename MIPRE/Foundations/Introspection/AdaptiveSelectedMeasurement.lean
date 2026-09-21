/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AdaptiveDecodedInvariant
import MIPRE.Foundations.Introspection.IntrospectCanonicalization

/-! # The actual selected measurement before an adaptive replacement

The local updating decoder recovers the old option-valued measurement on
each prefix branch. Reassembly therefore recovers the full ambient option
measurement. Canonicalization turns this into exactly the raw selected
measurement required by the quantitative replacement theorem. No malformed
effect is assumed to vanish.
-/

noncomputable section
namespace MIPRE.Introspection
open Finset Matrix Classical
set_option linter.unusedSectionVars false

variable {F ι H A B C : Type*}
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype H] [DecidableEq H]
  [Fintype A] [Fintype B] [Fintype C] [DecidableEq C] {ℓ : ℕ}

/-- A dependent answer decoder commutes with the concrete prefix assembly. -/
theorem adaptiveOldJointPOVM_map_mats (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ)
    (M : (y : ι → F) → POVM ((Fin (Fintype.card (P.factorOfPrefix k y)) → F) × B)
      ((stageRemaining P k y → F) × H))
    (hM : ∀ y, IsPVM (fun p => ((M y).mats p).val))
    (f : AdaptiveStageAnswer P k B → C) (c : C) :
    (((adaptiveOldJointPOVM P hP k M hM).map f).mats c).val =
      ∑ y, prefixResidualOp P k y
        (((M y).map (fun p => f ⟨y, p⟩)).mats c).val := by
  simp only [adaptiveOldJointPOVM, POVM.map_mats, IsPVM.toPOVM_mats,
    Finset.sum_filter, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro y _
  rw [prefixResidualOp_sum]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : f ⟨y, p⟩ = c
  · simp only [hp, if_true]
  · simp only [hp, if_false]
    ext i j
    simp [prefixResidualOp, registerOp_apply]

set_option backward.isDefEq.respectTransparency false in
/-- Decoding the refined actual joint measurement recovers the complete
old option-valued POVM, including its malformed effect. -/
theorem adaptiveRefinedJoint_decode (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ)
    (M : (y : ι → F) → POVM (Option ((ι → F) × A))
      ((stageRemaining P k y → F) × H))
    (hM : ∀ y, IsPVM (fun a => ((M y).mats a).val))
    (N : POVM (Option ((ι → F) × A)) ((ι → F) × H))
    (hform : ∀ a, (N.mats a).val = ∑ y, prefixResidualOp P k y ((M y).mats a).val)
    (hsupport : ∀ y x a, P.outputPrefix k x ≠ y → ((M y).mats (some (x, a))).val = 0) :
    (adaptiveOldJointPOVM P hP k
      (fun y => stageAnswerRefinementPOVM P k y (M y))
      (fun y => stageAnswerRefinementPOVM_isPVM P k y (M y) (hM y))).map
        (fun p => stageAnswerDecode P k p.1 p.2.1 p.2.2) = N := by
  apply POVM.ext'
  intro a
  trans ∑ y, prefixResidualOp P k y
    (((stageAnswerRefinementPOVM P k y (M y)).map
      (fun p => stageAnswerDecode P k y p.1 p.2)).mats a).val
  · exact adaptiveOldJointPOVM_map_mats P hP k
      (fun y => stageAnswerRefinementPOVM P k y (M y))
      (fun y => stageAnswerRefinementPOVM_isPVM P k y (M y) (hM y))
      (fun p => stageAnswerDecode P k p.1 p.2.1 p.2.2) a
  · have hlocal (y : ι → F) :
        (stageAnswerRefinementPOVM P k y (M y)).map
          (fun p => stageAnswerDecode P k y p.1 p.2) = M y :=
      stageAnswerRefinementPOVM_decode_recover hP k y (M y) (hsupport y)
    simp only [hlocal]
    exact (hform a).symm

/-- The same exact recovery uses only the advanced prefix and the retained
answer, which is the decoder interface of the next-strategy theorem. -/
theorem adaptiveRefinedJoint_next_decode (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ)
    (M : (y : ι → F) → POVM (Option ((ι → F) × A))
      ((stageRemaining P k y → F) × H))
    (hM : ∀ y, IsPVM (fun a => ((M y).mats a).val))
    (N : POVM (Option ((ι → F) × A)) ((ι → F) × H))
    (hform : ∀ a, (N.mats a).val = ∑ y, prefixResidualOp P k y ((M y).mats a).val)
    (hsupport : ∀ y x a, P.outputPrefix k x ≠ y → ((M y).mats (some (x, a))).val = 0) :
    (adaptiveOldJointPOVM P hP k
      (fun y => stageAnswerRefinementPOVM P k y (M y))
      (fun y => stageAnswerRefinementPOVM_isPVM P k y (M y) (hM y))).map
        (fun p => nextOptionDecoder P k (advanceStageAnswer P k p)) = N := by
  simp only [nextOptionDecoder_advanceStageAnswer hP]
  exact adaptiveRefinedJoint_decode P hP k M hM N hform hsupport

variable {PauliType PauliAnswer κ T : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Fintype κ] [DecidableEq κ] [Fintype T] [DecidableEq T]

/-- The raw normalized Introspect POVM is exactly the refined old joint
PVM followed by the actual updating decoder and raw-answer restoration. -/
theorem canonicalizeIntro_adaptive_selected (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H)) (w : Bool)
    (M : (y : ι → F) → POVM (Option ((ι → F) × A))
      ((stageRemaining P k y → F) × H))
    (hM : ∀ y, IsPVM (fun a => ((M y).mats a).val))
    (hform : ∀ a, (((MA (QuestionType.introspect w, 0)).map
      TypedEstimates.introspectPair).mats a).val =
        ∑ y, prefixResidualOp P k y ((M y).mats a).val)
    (hsupport : ∀ y x a, P.outputPrefix k x ≠ y → ((M y).mats (some (x, a))).val = 0) :
    canonicalizeIntro MA w (QuestionType.introspect w, 0) =
      (adaptiveOldJointPOVM P hP k
        (fun y => stageAnswerRefinementPOVM P k y (M y))
        (fun y => stageAnswerRefinementPOVM_isPVM P k y (M y) (hM y))).map
          (fun p => restoreIntroAnswer (nextOptionDecoder P k (advanceStageAnswer P k p))) := by
  rw [canonicalizeIntro_factor]
  have hd := adaptiveRefinedJoint_next_decode P hP k M hM
    ((MA (QuestionType.introspect w, 0)).map TypedEstimates.introspectPair) hform hsupport
  rw [← hd, POVM.map_map]

/-- Normalization preserves the option-valued prefix form used to derive
the analytic stage bounds from the current actual game. -/
theorem canonicalizeIntro_prefix_form (P : CL.CLFun F ι ℓ) (k : ℕ)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H)) (w : Bool)
    (M : (y : ι → F) → Option ((ι → F) × A) →
      Matrix ((stageRemaining P k y → F) × H) ((stageRemaining P k y → F) × H) ℂ)
    (hform : ∀ a, (((MA (QuestionType.introspect w, 0)).map
      TypedEstimates.introspectPair).mats a).val = ∑ y, prefixResidualOp P k y (M y a))
    (a : Option ((ι → F) × A)) :
    (((canonicalizeIntro MA w (QuestionType.introspect w, 0)).map
      TypedEstimates.introspectPair).mats a).val = ∑ y, prefixResidualOp P k y (M y a) := by
  rw [canonicalizeIntro_recover]
  exact hform a

/-- Canonicalization at the selected question is overwritten by the actual
replacement. All other old questions are retained identically. -/
theorem registeredReplacement_canonicalizeIntro
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H)) (w : Bool)
    (R : POVM (ParsedAnswer (ι → F) A PauliAnswer) (((ι → F) × H) × T)) :
    registeredReplacement (canonicalizeIntro MA w) (QuestionType.introspect w, 0) R =
      registeredReplacement MA (QuestionType.introspect w, 0) R := by
  funext q
  by_cases hq : q = (QuestionType.introspect w, 0)
  · subst q
    simp only [registeredReplacement_at]
  · rw [registeredReplacement_other (canonicalizeIntro MA w) _ q R hq,
      registeredReplacement_other MA _ q R hq, canonicalizeIntro_other MA w q hq]

end MIPRE.Introspection
end

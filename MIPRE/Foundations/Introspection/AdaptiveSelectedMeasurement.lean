/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.AdaptiveDecodedInvariant
public import MIPRE.Foundations.Introspection.IntrospectCanonicalization

@[expose] public section

/-! # The actual selected measurement before an adaptive replacement

The local updating decoder recovers the old option-valued measurement on
each prefix branch. Reassembly therefore recovers the full ambient option
measurement. Canonicalization turns this into exactly the raw selected
measurement required by the quantitative replacement theorem. No malformed
effect is assumed to vanish.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the residual measurements are
POVMs of block matrices over the remaining coordinates of each prefix with entries in an ordered
`⋆`-algebra `𝒜`, and the old joint measurement `adaptiveOldJointPOVM` and the selected measurement
are POVMs in `Matrix (ι → F) (ι → F) 𝒜`, the first player's algebra of the register model
`Ξ.reg (ι → F)`. The product form is an identity of operators `.op`. The old joint measurement no
longer carries a projectivity proof, so the recovery identities hold for any residual POVMs and
take no projectivity hypothesis (the matrix versions needed one only to build that proof). The
replacement `R` is a POVM in `Matrix T T (Matrix (ι → F) (ι → F) 𝒜)`, as in
`registeredReplacement`.
-/

noncomputable section
namespace MIPRE.Introspection
open Finset Matrix Classical
set_option linter.unusedSectionVars false

variable {F ι A B C : Type*}
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι]
  [Fintype A] [Fintype B] [Fintype C] [DecidableEq C] {ℓ : ℕ}
variable {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] [StarModule ℂ 𝒜] [PartialOrder 𝒜]
  [StarOrderedRing 𝒜] [StarProper 𝒜]

/-- A dependent answer decoder commutes with the concrete prefix assembly. -/
theorem adaptiveOldJointPOVM_map_mats (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ)
    (M : (y : ι → F) → POVMIn ((Fin (Fintype.card (P.factorOfPrefix k y)) → F) × B)
      (Matrix (stageRemaining P k y → F) (stageRemaining P k y → F) 𝒜))
    (f : AdaptiveStageAnswer P k B → C) (c : C) :
    ((adaptiveOldJointPOVM P hP k M).map f).op c =
      ∑ y, prefixResidualOp P k y (((M y).map (fun p => f ⟨y, p⟩)).op c) := by
  simp only [adaptiveOldJointPOVM, POVMIn.map_op, prefixResidualPOVM_op,
    Finset.sum_filter, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro y _
  rw [prefixResidualOp_sum]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : f ⟨y, p⟩ = c
  · rw [ite_eq_left hp, ite_eq_left hp]
  · rw [ite_eq_right hp, ite_eq_right hp, prefixResidualOp, smulKron_zero_left, map_zero]

/-- Decoding the refined actual joint measurement recovers the complete
old option-valued POVM, including its malformed effect. -/
theorem adaptiveRefinedJoint_decode (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ)
    (M : (y : ι → F) → POVMIn (Option ((ι → F) × A))
      (Matrix (stageRemaining P k y → F) (stageRemaining P k y → F) 𝒜))
    (N : POVMIn (Option ((ι → F) × A)) (Matrix (ι → F) (ι → F) 𝒜))
    (hform : ∀ a, N.op a = ∑ y, prefixResidualOp P k y ((M y).op a))
    (hsupport : ∀ y x a, P.outputPrefix k x ≠ y → (M y).op (some (x, a)) = 0) :
    (adaptiveOldJointPOVM P hP k
      (fun y => stageAnswerRefinementPOVM P k y (M y))).map
        (fun p => stageAnswerDecode P k p.1 p.2.1 p.2.2) = N := by
  apply POVMIn.ext'
  intro a
  trans ∑ y, prefixResidualOp P k y
    (((stageAnswerRefinementPOVM P k y (M y)).map
      (fun p => stageAnswerDecode P k y p.1 p.2)).op a)
  · exact adaptiveOldJointPOVM_map_mats P hP k
      (fun y => stageAnswerRefinementPOVM P k y (M y))
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
    (M : (y : ι → F) → POVMIn (Option ((ι → F) × A))
      (Matrix (stageRemaining P k y → F) (stageRemaining P k y → F) 𝒜))
    (N : POVMIn (Option ((ι → F) × A)) (Matrix (ι → F) (ι → F) 𝒜))
    (hform : ∀ a, N.op a = ∑ y, prefixResidualOp P k y ((M y).op a))
    (hsupport : ∀ y x a, P.outputPrefix k x ≠ y → (M y).op (some (x, a)) = 0) :
    (adaptiveOldJointPOVM P hP k
      (fun y => stageAnswerRefinementPOVM P k y (M y))).map
        (fun p => nextOptionDecoder P k (advanceStageAnswer P k p)) = N := by
  simp only [nextOptionDecoder_advanceStageAnswer hP]
  exact adaptiveRefinedJoint_decode P hP k M N hform hsupport

variable {PauliType PauliAnswer κ T : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Fintype κ] [DecidableEq κ] [Fintype T] [DecidableEq T]

/-- The raw normalized Introspect POVM is exactly the refined old joint
PVM followed by the actual updating decoder and raw-answer restoration. -/
theorem canonicalizeIntro_adaptive_selected (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) 𝒜)) (w : Bool)
    (M : (y : ι → F) → POVMIn (Option ((ι → F) × A))
      (Matrix (stageRemaining P k y → F) (stageRemaining P k y → F) 𝒜))
    (hform : ∀ a, ((MA (QuestionType.introspect w, 0)).map
      TypedEstimates.introspectPair).op a =
        ∑ y, prefixResidualOp P k y ((M y).op a))
    (hsupport : ∀ y x a, P.outputPrefix k x ≠ y → (M y).op (some (x, a)) = 0) :
    canonicalizeIntro MA w (QuestionType.introspect w, 0) =
      (adaptiveOldJointPOVM P hP k
        (fun y => stageAnswerRefinementPOVM P k y (M y))).map
          (fun p => restoreIntroAnswer (nextOptionDecoder P k (advanceStageAnswer P k p))) := by
  rw [canonicalizeIntro_factor]
  have hd := adaptiveRefinedJoint_next_decode P hP k M
    ((MA (QuestionType.introspect w, 0)).map TypedEstimates.introspectPair) hform hsupport
  rw [← hd, POVMIn.map_map]

/-- Canonicalization at the selected question is overwritten by the actual
replacement. All other old questions are retained identically. -/
theorem registeredReplacement_canonicalizeIntro
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) 𝒜)) (w : Bool)
    (R : POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix T T (Matrix (ι → F) (ι → F) 𝒜))) :
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

end

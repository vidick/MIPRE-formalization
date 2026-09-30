/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.AdaptiveInductionInvariant
public import MIPRE.Foundations.Introspection.AdaptiveSelectedMeasurement
public import MIPRE.Foundations.Introspection.AdaptiveGameStage
public import MIPRE.Foundations.Introspection.StrategyReplacementErrors

@[expose] public section

/-! # A successor of the actual Introspect induction

The current game's tests construct the replacement. Canonicalization and
decoder recovery discharge the selected-measurement identity, and decoding
gives the next structural invariant. The fixed hiding and primitive Z
errors can be reused on the enlarged auxiliary space.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the register state is the
register model `Ξ.reg (ι → F)` of a normalized auxiliary model `Ξ`, and the successor lives on the
register model `(Ξ.expandA t₀).reg (ι → F)` of its one-sided extension by the dilation ancilla
`DilationAncilla (Option ((ι → F) × A)) K` in its fixed state `t₀ = inl (none, 0)`. The size `K`
is chosen by the dilation (`exists_game_adaptive_prefix_dilation`), so the successor theorem
returns it. The successor family is the registered replacement, a family of POVMs in
`Matrix (ι → F) (ι → F) (Matrix T T 𝒜)`, and its invariant is the decoded next-prefix invariant
over that algebra. The primitive Z errors of both players (`introAliceZError`, defined here next
to `introBobZError`) and their hiding errors are transported exactly to the extended model
(`StrategyReplacementErrors`); the successor theorem records these equalities for the iteration.
-/

noncomputable section
namespace MIPRE.Introspection
open Finset Matrix Classical Weyl
set_option linter.unusedSectionVars false

variable {PauliType PauliAnswer F ι κ A : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype A] {ℓ : ℕ}
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]

section Successor
variable [StarModule ℂ 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarProper 𝒜]
variable {T : Type*} [Fintype T] [DecidableEq T]

/-- The actual question-indexed family after inserting the decoded
replacement, with the original family retained at every other question. -/
def introSuccessorFamily (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ) (k : ℕ)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) 𝒜)) (w : Bool)
    (R : AdaptiveDilationFamily P k 𝒜 T (Option ((ι → F) × A)))
    (hR : ∀ y z, IsPVMIn (R y z)) :
    CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) (Matrix T T 𝒜)) :=
  registeredReplacement MA (QuestionType.introspect w, 0)
    ((adaptiveReplacementPOVM P hP k R hR).map
      (fun p => restoreIntroAnswer (nextOptionDecoder P k (advanceStageAnswer P k p))))

theorem introSuccessorFamily_isPVM (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) 𝒜)) (w : Bool)
    (R : AdaptiveDilationFamily P k 𝒜 T (Option ((ι → F) × A)))
    (hR : ∀ y z, IsPVMIn (R y z))
    (hMA : ∀ q, IsPVMIn (MA q).op)
    (q : CL.Detyping.Question (QuestionType PauliType ℓ) κ) :
    IsPVMIn (introSuccessorFamily P hP k MA w R hR q).op :=
  registeredReplacement_isPVM _ _ _ hMA
    (POVMIn.isPVMIn_map (adaptiveReplacementPOVM_isPVM P hP k R hR) _) q

/-- The returned raw selected measurement carries the complete next
option-valued product form, including valid-answer support. -/
def introSuccessorInvariant (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ) (k : ℕ)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) 𝒜)) (w : Bool)
    (R : AdaptiveDilationFamily P k 𝒜 T (Option ((ι → F) × A)))
    (hR : ∀ y z, IsPVMIn (R y z)) :
    IntroPrefixInvariant P (k + 1)
      ((introSuccessorFamily P hP k MA w R hR (QuestionType.introspect w, 0)).map
        TypedEstimates.introspectPair) where
  residual := nextPrefixDecodedPOVM P hP k none R hR (nextOptionDecoder P k)
  projective := nextPrefixDecodedPOVM_option_isPVM P hP k R hR
  form := registeredReplacement_nextOption_mats P hP k R hR MA (QuestionType.introspect w, 0)
  support := nextPrefixDecodedPOVM_some_support P hP k R hR

end Successor

namespace TypedEstimates

section Bob
variable [PartialOrder ℬ] [StarOrderedRing ℬ] [StarProper ℬ]

/-- The primitive Bob-Z error in the common register model. -/
def introBobZError (projectPauli : PauliAnswer → ι → F) (Z : PauliType)
    (q : κ → ZMod 2) (Ξ : BipartiteModel 𝒞 𝒜 ℬ)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) ℬ)) : ℝ :=
  ∑ z, (Ξ.reg (ι → F)).snorm ((Ξ.reg (ι → F)).πB
    (((MB (QuestionType.pauli Z, q)).map (pauliProjection projectPauli)).op z -
      smulKron 1 (readout (some : (ι → F) → Option (ι → F)) z))) ^ 2

/-- The primitive Bob-Z error is unchanged by a first-player ancilla in a fixed state. -/
theorem introBobZError_extVecA {T : Type*} [Fintype T] [DecidableEq T]
    (projectPauli : PauliAnswer → ι → F) (Z : PauliType)
    (q : κ → ZMod 2) (Ξ : BipartiteModel 𝒞 𝒜 ℬ) (t₀ : T)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) ℬ)) :
    introBobZError projectPauli Z q (Ξ.expandA t₀) MB =
      introBobZError projectPauli Z q Ξ MB :=
  pauliBobError_registeredExtension Ξ t₀ projectPauli MB Z q (readout some)

end Bob

section Alice
variable [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarProper 𝒜]

/-- Alice's primitive computational-basis error, with malformed Pauli
answers kept as the separate option outcome. -/
def introAliceZError (projectPauli : PauliAnswer → ι → F) (Z : PauliType)
    (q : κ → ZMod 2) (Ξ : BipartiteModel 𝒞 𝒜 ℬ)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) 𝒜)) : ℝ :=
  ∑ z, (Ξ.reg (ι → F)).stateSqNorm
    (((MA (QuestionType.pauli Z, q)).map (pauliProjection projectPauli)).op z -
      smulKron 1 (readout (some : (ι → F) → Option (ι → F)) z))

end Alice

variable [StarModule ℂ 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarProper 𝒜]
  [StarModule ℂ ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ] [StarProper ℬ]

-- The structural `DecidableEq` instance of the dilation ancilla over the option-valued answer
-- alphabet exceeds the default instance size; with it, the statement's instance is the one
-- `exists_game_adaptive_prefix_dilation` produces.
set_option synthInstance.maxSize 512 in
/-- The actual current tests produce a projective next family and its
complete prefix invariant. No selected-measurement or mixing-error bound
is assumed: those are derived from the supplied current invariant. The
primitive Z errors and the hiding errors of both players are unchanged on
the extended model. -/
theorem exists_intro_successor
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
    (hMA : ∀ q, IsPVMIn (MA q).op)
    (hMB : ∀ q, IsPVMIn (MB q).op)
    (q : κ → ZMod 2) (hq : ∀ z, (P Z).eval z = q)
    (w : Bool) (hL : (L w).SupportedOn univ) (j : Fin ℓ)
    (I : IntroPrefixInvariant (L w) j.val
      ((MA (QuestionType.introspect w, 0)).map introspectPair))
    {ε η δ : ℝ} (hε : 0 ≤ ε) (hη : 0 ≤ η) (hδ : 0 ≤ δ)
    (hfail : 1 - (Ξ.reg (ι → F)).povmValue (parsedGame E X Z P L projectPauli D DP) MA MB ≤ ε)
    (hZ : introBobZError projectPauli Z q Ξ MB ≤ η)
    (hhide : hidingAliceError L w hL Ξ MA j ≤ δ)
    (hsmall : adaptiveStageBudget (ℓ - j.val)
      ((TypeGraph.edges E X Z ℓ).card * ε) η δ ≤ 1) :
    ∃ (K : ℕ) (MA' : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
        POVMIn (ParsedAnswer (ι → F) A PauliAnswer)
          (Matrix (ι → F) (ι → F) (Matrix (DilationAncilla (Option ((ι → F) × A)) K)
            (DilationAncilla (Option ((ι → F) × A)) K) 𝒜)))
      (_ : IntroPrefixInvariant (L w) (j.val + 1)
        ((MA' (QuestionType.introspect w, 0)).map introspectPair)),
      (∀ t, IsPVMIn (MA' t).op) ∧
      1 - ((Ξ.expandA (Sum.inl (none, 0) : DilationAncilla (Option ((ι → F) × A)) K)).reg
          (ι → F)).povmValue (parsedGame E X Z P L projectPauli D DP) MA' MB ≤
        ε + adaptiveStepLoss (adaptiveStageBudget (ℓ - j.val)
          ((TypeGraph.edges E X Z ℓ).card * ε) η δ) ∧
      (∀ t, t ≠ (QuestionType.introspect w, 0) → MA' t = registeredExtendPOVM (MA t)) ∧
      (∀ i : Fin ℓ, hidingAliceError L w hL
        (Ξ.expandA (Sum.inl (none, 0) : DilationAncilla (Option ((ι → F) × A)) K)) MA' i =
          hidingAliceError L w hL Ξ MA i) ∧
      introAliceZError projectPauli Z q
          (Ξ.expandA (Sum.inl (none, 0) : DilationAncilla (Option ((ι → F) × A)) K)) MA' =
        introAliceZError projectPauli Z q Ξ MA ∧
      introBobZError projectPauli Z q
          (Ξ.expandA (Sum.inl (none, 0) : DilationAncilla (Option ((ι → F) × A)) K)) MB =
        introBobZError projectPauli Z q Ξ MB ∧
      (∀ i : Fin ℓ, hidingBobError L w hL
        (Ξ.expandA (Sum.inl (none, 0) : DilationAncilla (Option ((ι → F) × A)) K)) MB i =
          hidingBobError L w hL Ξ MB i) := by
  obtain ⟨K, R, hR, hd⟩ := exists_game_adaptive_prefix_dilation E X Z P L projectPauli D DP
    Ξ hΞ MA MB hε hη hδ hfail q hq w hL j
    (hMA _) (hMB _) hZ (hMA _) (hMB _) hhide
    I.residual I.form I.support I.projective hsmall
  let t₀ : DilationAncilla (Option ((ι → F) × A)) K := Sum.inl (none, 0)
  let J := adaptiveOldJointPOVM (L w) hL j.val
    (fun y => stageAnswerRefinementPOVM (L w) j.val y (I.residual y))
  let N := adaptiveReplacementPOVM (L w) hL j.val R hR
  let f := fun p : AdaptiveStageAnswer (L w) j.val (Option ((ι → F) × A)) =>
    restoreIntroAnswer (PauliAnswer := PauliAnswer)
      (nextOptionDecoder (L w) j.val (advanceStageAnswer (L w) j.val p))
  have hselected : canonicalizeIntro MA w (QuestionType.introspect w, 0) = J.map f :=
    canonicalizeIntro_adaptive_selected (L w) hL j.val MA w I.residual I.form I.support
  have hv := replaceExtended_value (Ξ.reg (ι → F)) (parsedGame E X Z P L projectPauli D DP)
    (by rw [BipartiteModel.norm_reg_ψ, hΞ]) t₀ (canonicalizeIntro MA w) MB
    (QuestionType.introspect w, 0) J N f hselected
    (adaptiveOldJointPOVM_isPVM (L w) hL j.val _
      (fun y => stageAnswerRefinementPOVM_isPVM (L w) j.val y (I.residual y) (I.projective y)))
    (adaptiveReplacementPOVM_isPVM _ _ _ R hR) hMB hd
  rw [← registeredReplacement_value_eq Ξ (parsedGame E X Z P L projectPauli D DP)
      t₀ (canonicalizeIntro MA w) MB (QuestionType.introspect w, 0) (N.map f),
    canonicalizeIntro_value, registeredReplacement_canonicalizeIntro] at hv
  refine ⟨K, introSuccessorFamily (L w) hL j.val MA w R hR,
    introSuccessorInvariant (L w) hL j.val MA w R hR,
    introSuccessorFamily_isPVM (L w) hL j.val MA w R hR hMA, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hloss := (abs_sub_le_iff.mp hv).1
    change 1 - ((Ξ.expandA t₀).reg (ι → F)).povmValue (parsedGame E X Z P L projectPauli D DP)
      (registeredReplacement MA (QuestionType.introspect w, 0) (N.map f)) MB ≤ _
    unfold adaptiveStepLoss
    linarith
  · intro t ht
    exact registeredReplacement_other_eq MA (QuestionType.introspect w, 0) t (N.map f) ht
  · intro i
    exact hidingAliceError_registeredReplacement L w w hL Ξ t₀ MA (N.map f) i
  · exact pauliAliceError_registeredReplacement Ξ t₀ projectPauli MA (N.map f) w Z q
      (readout some)
  · exact introBobZError_extVecA projectPauli Z q Ξ t₀ MB
  · intro i
    exact hidingBobError_registeredExtension L w hL Ξ t₀ MB i

end TypedEstimates
end MIPRE.Introspection
end

end

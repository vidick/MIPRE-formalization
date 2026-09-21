/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AdaptivePlayerSwap

/-! # Actual Bob iteration and the error transport between the two blocks

The checked Alice construction is applied with the players exchanged and
the Pauli predicate transposed. Returning to the original player order leaves
Alice's entire measurement family literally unchanged. The additional local
registers belong only to Bob's auxiliary state.
-/

noncomputable section
namespace MIPRE.Introspection
open Finset Matrix Classical
set_option linter.unusedSectionVars false

universe u

section State
variable {H : Type*} {K Ω : Type u}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype Ω] [DecidableEq Ω]

/-- The actual auxiliary state after adding only Bob-local fixed registers. -/
def introBobIterationState (ξ : H × K → ℂ) (a₀ : Ω) (n : ℕ) :
    H × introIterationAux K Ω n → ℂ :=
  swapVec (introIterationState (swapVec ξ) a₀ n)

@[simp] theorem introBobIterationState_zero (ξ : H × K → ℂ) (a₀ : Ω) :
    introBobIterationState ξ a₀ 0 = ξ := rfl

theorem introBobIterationState_unit (ξ : H × K → ℂ)
    (hξ : star ξ ⬝ᵥ ξ = 1) (a₀ : Ω) (n : ℕ) :
    star (introBobIterationState ξ a₀ n) ⬝ᵥ introBobIterationState ξ a₀ n = 1 := by
  rw [introBobIterationState, swapVec_dotProduct]
  exact introIterationState_unit (swapVec ξ) (by rwa [swapVec_dotProduct]) a₀ n

end State

namespace TypedEstimates

section Preserve
variable {PauliType PauliAnswer κ K : Type*} {F ι A H : Type u}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype A]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}

theorem introAliceZError_registeredExtend (projectPauli : PauliAnswer → ι → F)
    (Z : PauliType) (q : κ → ZMod 2) (ξ : H × K → ℂ)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H)) :
    introAliceZError projectPauli Z q (extVecA ξ (none : Option ((ι → F) × A)))
      (fun t => registeredExtendPOVM (MA t)) = introAliceZError projectPauli Z q ξ MA := by
  unfold introAliceZError
  apply Finset.sum_congr rfl
  intro z _
  rw [← registeredExtendPOVM_map, registeredExtendPOVM_mats,
    ← registeredExtendOp_aOp, ← registeredExtendOp_sub, stateSqNorm_registeredExtendOp]

/-- Alice's primitive Z error survives all of Alice's inert Pauli extensions. -/
theorem introAliceZError_introIterationExtend (projectPauli : PauliAnswer → ι → F)
    (Z : PauliType) (q : κ → ZMod 2) (ξ : H × K → ℂ)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H)) (n : ℕ) :
    introAliceZError projectPauli Z q
      (introIterationState ξ (none : Option ((ι → F) × A)) n)
      (fun t => introIterationExtend (Option ((ι → F) × A)) (MA t) n) =
        introAliceZError projectPauli Z q ξ MA := by
  induction n with
  | zero => rfl
  | succ n ih =>
      exact (introAliceZError_registeredExtend projectPauli Z q
        (introIterationState ξ (none : Option ((ι → F) × A)) n)
        (fun t => introIterationExtend (Option ((ι → F) × A)) (MA t) n)).trans ih

/-- The actual Alice-iteration family needs only its exact untouched Pauli
question identity to preserve the primitive input for Bob's block. -/
theorem introAliceZError_of_iteration_other (projectPauli : PauliAnswer → ι → F)
    (Z : PauliType) (q : κ → ZMod 2) (ξ : H × K → ℂ)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H)) (n : ℕ)
    (MN : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer)
        ((ι → F) × introIterationAux H (Option ((ι → F) × A)) n))
    (hother : MN (QuestionType.pauli Z, q) =
      introIterationExtend (Option ((ι → F) × A)) (MA (QuestionType.pauli Z, q)) n) :
    introAliceZError projectPauli Z q
      (introIterationState ξ (none : Option ((ι → F) × A)) n) MN =
        introAliceZError projectPauli Z q ξ MA := by
  have h := introAliceZError_introIterationExtend projectPauli Z q ξ MA n
  simpa only [introAliceZError, hother] using h

/-- Bob's hiding errors are exactly unchanged during Alice's complete block. -/
theorem hidingBobError_introIterationState (L : Bool → CL.CLFun F ι ℓ)
    (w : Bool) (hL : (L w).SupportedOn univ) (ξ : H × K → ℂ)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × K)) (n : ℕ) (j : Fin ℓ) :
    hidingBobError L w hL (introIterationState ξ (none : Option ((ι → F) × A)) n) MB j =
      hidingBobError L w hL ξ MB j := by
  induction n with
  | zero => rfl
  | succ n ih =>
      exact (hidingBobError_registeredExtension L w hL
        (introIterationState ξ (none : Option ((ι → F) × A)) n) none MB j).trans ih

end Preserve

section Iteration
variable {PauliType PauliAnswer κ H : Type*} {F ι A K : Type u}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype A]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}

set_option backward.isDefEq.respectTransparency false in
/-- The actual finite Bob induction in the original game and player order.
Alice's full measurement family is retained, so any previously completed
Alice terminal form remains true without an additional transport premise. -/
theorem exists_intro_bob_iteration
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
    (w : Bool) (hL : (L w).SupportedOn univ)
    {initial η δ : ℝ} (hi0 : 0 ≤ initial) (hη0 : 0 ≤ η) (hδ0 : 0 ≤ δ)
    (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP)
      (registerState (ι → F) ξ) MA MB ≤ initial)
    (hZ : introAliceZError projectPauli Z q ξ MA ≤ η)
    (hhide : ∀ j : Fin ℓ, hidingBobError L w hL ξ MB j ≤ δ)
    (hi : initial ≤ adaptiveSmallThreshold ℓ (TypeGraph.edges E X Z ℓ).card ℓ)
    (hη : η ≤ adaptiveSmallThreshold ℓ (TypeGraph.edges E X Z ℓ).card ℓ)
    (hδ : δ ≤ adaptiveSmallThreshold ℓ (TypeGraph.edges E X Z ℓ).card ℓ)
    (n : ℕ) (hn : n ≤ ℓ) :
    ∃ (MN : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
        POVM (ParsedAnswer (ι → F) A PauliAnswer)
          ((ι → F) × introIterationAux K (Option ((ι → F) × A)) n))
      (_ : IntroPrefixInvariant (L w) n
        ((MN (QuestionType.introspect w, 0)).map introspectPair)),
      (∀ t, IsPVM (fun a => ((MN t).mats a).val)) ∧
      1 - povmValue (parsedGame E X Z P L projectPauli D DP)
        (registerState (ι → F)
          (introBobIterationState ξ (none : Option ((ι → F) × A)) n)) MA MN ≤
            adaptiveFailureBudget ℓ (TypeGraph.edges E X Z ℓ).card η δ initial n ∧
      (∀ t, t ≠ (QuestionType.introspect w, 0) →
        MN t = introIterationExtend (Option ((ι → F) × A)) (MB t) n) ∧
      (∀ j : Fin ℓ, hidingBobError L w hL
        (introBobIterationState ξ (none : Option ((ι → F) × A)) n) MN j =
          hidingBobError L w hL ξ MB j) := by
  have hu : star (swapVec ξ) ⬝ᵥ swapVec ξ = 1 := by rwa [swapVec_dotProduct]
  have hf : 1 - povmValue (parsedGame E X Z P L projectPauli D (transposePauliPredicate DP))
      (registerState (ι → F) (swapVec ξ)) MB MA ≤ initial := by
    rw [parsedGame_value_swap]
    exact hfail
  have hz : introBobZError projectPauli Z q (swapVec ξ) MA ≤ η :=
    (introBobZError_swap projectPauli Z q ξ MA).trans_le hZ
  have hh (j : Fin ℓ) : hidingAliceError L w hL (swapVec ξ) MB j ≤ δ :=
    (hidingAliceError_swap L w hL ξ MB j).trans_le (hhide j)
  obtain ⟨MN, IN, hMN, hfailN, hotherN, hhideN⟩ := exists_intro_iteration
    E X Z P L projectPauli D (transposePauliPredicate DP) (swapVec ξ) hu
    MB MA hMB hMA q hq w hL hi0 hη0 hδ0 hf hz hh hi hη hδ n hn
  refine ⟨MN, IN, hMN, ?_, hotherN, ?_⟩
  · have hv := parsedGame_value_swap E X Z P L projectPauli D (transposePauliPredicate DP)
      (introIterationState (swapVec ξ) (none : Option ((ι → F) × A)) n) MN MA
    simp only [transposePauliPredicate_transpose] at hv
    change 1 - povmValue (parsedGame E X Z P L projectPauli D DP)
      (registerState (ι → F)
        (swapVec (introIterationState (swapVec ξ) (none : Option ((ι → F) × A)) n)))
      MA MN ≤ _
    rw [hv]
    exact hfailN
  · intro j
    exact (hidingBobError_swap L w hL
      (introIterationState (swapVec ξ) (none : Option ((ι → F) × A)) n) MN j).trans
      ((hhideN j).trans (hidingAliceError_swap L w hL ξ MB j))

end Iteration
end TypedEstimates
end MIPRE.Introspection
end

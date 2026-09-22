/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AdaptiveBobIteration

/-! # Both actual introspection measurements reach terminal form

Alice's false-role block is followed by Bob's true-role block. The second
block leaves the completed Alice measurement unchanged. All its primitive
inputs are transported from the original strategy, and a single numerical
recurrence accounts for the full `2 * ℓ` replacements.
-/

noncomputable section
namespace MIPRE.Introspection
open Finset Matrix Classical
set_option linter.unusedSectionVars false

/-- Restarting the failure recurrence is exactly continuing it. -/
theorem adaptiveFailureBudget_add (r : ℕ) (edges z h initial : ℝ) (m n : ℕ) :
    adaptiveFailureBudget r edges z h initial (m + n) =
      adaptiveFailureBudget r edges z h
        (adaptiveFailureBudget r edges z h initial m) n := by
  induction n with
  | zero => simp only [Nat.add_zero, adaptiveFailureBudget]
  | succ n ih =>
      rw [Nat.add_succ, adaptiveFailureBudget_step, adaptiveFailureBudget_step, ih]

universe u
variable {F ι A H K : Type u}
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype A]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

/-- The explicit product-ancilla extension used by the two blocks. -/
def introTwoSidedState (ξ : H × K → ℂ) (n : ℕ) :
    introIterationAux H (Option ((ι → F) × A)) n ×
      introIterationAux K (Option ((ι → F) × A)) n → ℂ :=
  introBobIterationState
    (introIterationState ξ (none : Option ((ι → F) × A)) n) none n

theorem introTwoSidedState_unit (ξ : H × K → ℂ) (hξ : star ξ ⬝ᵥ ξ = 1) (n : ℕ) :
    star (introTwoSidedState (F := F) (ι := ι) (A := A) ξ n) ⬝ᵥ
      introTwoSidedState ξ n = 1 :=
  introBobIterationState_unit _ (introIterationState_unit ξ hξ none n) none n

namespace TypedEstimates

variable {PauliType PauliAnswer κ : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Fintype κ] [DecidableEq κ] {ℓ : ℕ}

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- Two concrete projective measurement families with both terminal prefix
invariants, from actual game success and fixed primitive errors. No future
measurement, structural invariant, or stage-success premise is assumed. -/
theorem exists_intro_two_sided_iteration
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
    (hL : ∀ w, (L w).SupportedOn univ)
    {initial η δ : ℝ} (hi0 : 0 ≤ initial) (hη0 : 0 ≤ η) (hδ0 : 0 ≤ δ)
    (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP)
      (registerState (ι → F) ξ) MA MB ≤ initial)
    (hZA : introAliceZError projectPauli Z q ξ MA ≤ η)
    (hZB : introBobZError projectPauli Z q ξ MB ≤ η)
    (hhideA : ∀ j : Fin ℓ, hidingAliceError L false (hL false) ξ MA j ≤ δ)
    (hhideB : ∀ j : Fin ℓ, hidingBobError L true (hL true) ξ MB j ≤ δ)
    (hi : initial ≤ adaptiveSmallThreshold ℓ (TypeGraph.edges E X Z ℓ).card (2 * ℓ))
    (hη : η ≤ adaptiveSmallThreshold ℓ (TypeGraph.edges E X Z ℓ).card (2 * ℓ))
    (hδ : δ ≤ adaptiveSmallThreshold ℓ (TypeGraph.edges E X Z ℓ).card (2 * ℓ)) :
    ∃ (MAN : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
        POVM (ParsedAnswer (ι → F) A PauliAnswer)
          ((ι → F) × introIterationAux H (Option ((ι → F) × A)) ℓ))
      (MBN : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
        POVM (ParsedAnswer (ι → F) A PauliAnswer)
          ((ι → F) × introIterationAux K (Option ((ι → F) × A)) ℓ))
      (_ : IntroPrefixInvariant (L false) ℓ
        ((MAN (QuestionType.introspect false, 0)).map introspectPair))
      (_ : IntroPrefixInvariant (L true) ℓ
        ((MBN (QuestionType.introspect true, 0)).map introspectPair)),
      (∀ t, IsPVM (fun a => ((MAN t).mats a).val)) ∧
      (∀ t, IsPVM (fun a => ((MBN t).mats a).val)) ∧
      1 - povmValue (parsedGame E X Z P L projectPauli D DP)
        (registerState (ι → F) (introTwoSidedState ξ ℓ)) MAN MBN ≤
          adaptiveFailureBudget ℓ (TypeGraph.edges E X Z ℓ).card η δ initial (2 * ℓ) := by
  have he : (0 : ℝ) ≤ (TypeGraph.edges E X Z ℓ).card := Nat.cast_nonneg _
  have hlevels : ℓ ≤ 2 * ℓ := by omega
  have ht := adaptiveSmallThreshold_antitone ℓ he hlevels
  obtain ⟨MAN, IA, hMAN, hfA, hoA, _⟩ := exists_intro_iteration
    E X Z P L projectPauli D DP ξ hξ MA MB hMA hMB q hq false (hL false)
    hi0 hη0 hδ0 hfail hZB hhideA (hi.trans ht) (hη.trans ht) (hδ.trans ht) ℓ le_rfl
  have hmid : adaptiveFailureBudget ℓ (TypeGraph.edges E X Z ℓ).card η δ initial ℓ ≤
      adaptiveSmallThreshold ℓ (TypeGraph.edges E X Z ℓ).card ℓ := by
    simpa only [show 2 * ℓ - ℓ = ℓ by omega] using
      adaptiveFailureBudget_le_threshold ℓ (2 * ℓ) he hi hη hδ ℓ hlevels
  have hzA : introAliceZError projectPauli Z q
      (introIterationState ξ (none : Option ((ι → F) × A)) ℓ) MAN ≤ η := by
    rw [introAliceZError_of_iteration_other projectPauli Z q ξ MA ℓ MAN
      (hoA (QuestionType.pauli Z, q) (by
        intro hh
        have hh' := congrArg Prod.fst hh
        cases hh'))]
    exact hZA
  have hhB (j : Fin ℓ) : hidingBobError L true (hL true)
      (introIterationState ξ (none : Option ((ι → F) × A)) ℓ) MB j ≤ δ := by
    rw [hidingBobError_introIterationState]
    exact hhideB j
  obtain ⟨MBN, IB, hMBN, hfB, _, _⟩ := exists_intro_bob_iteration
    E X Z P L projectPauli D DP
    (introIterationState ξ (none : Option ((ι → F) × A)) ℓ)
    (introIterationState_unit ξ hξ none ℓ) MAN MB hMAN hMB q hq true (hL true)
    (adaptiveFailureBudget_nonneg ℓ ℓ _ η δ hi0) hη0 hδ0 hfA hzA hhB
    hmid (hη.trans ht) (hδ.trans ht) ℓ le_rfl
  refine ⟨MAN, MBN, IA, IB, hMAN, hMBN, ?_⟩
  have hsum := adaptiveFailureBudget_add ℓ (TypeGraph.edges E X Z ℓ).card η δ initial ℓ ℓ
  rw [← two_mul] at hsum
  exact hfB.trans_eq hsum.symm

end TypedEstimates
end MIPRE.Introspection
end

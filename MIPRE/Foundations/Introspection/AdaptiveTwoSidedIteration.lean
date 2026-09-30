/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.AdaptiveBobIteration

@[expose] public section

/-! # Both actual introspection measurements reach terminal form

Alice's false-role block is followed by Bob's true-role block. The second
block leaves the completed Alice measurement unchanged. All its primitive
inputs are transported from the original strategy, and a single numerical
recurrence accounts for the full `2 * ℓ` replacements.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): Alice's block returns a model
`N₁` over the second player's algebra, Bob's block, run on `N₁.Ξ`, a model `N₂` over `N₁`'s first
player's algebra, and the final model is `N₂.Ξ.swap`, which reduces to the original one. The matrix
version's product state `introTwoSidedState` has no counterpart.
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

namespace TypedEstimates

universe u v

variable {PauliType PauliAnswer κ : Type*} {F ι A : Type}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype A] {ℓ : ℕ}
variable {𝒞 𝒜 ℬ : Type u} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [StarModule ℂ 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarProper 𝒜]
  [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [StarModule ℂ ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]
  [StarProper ℬ]

/-- Two concrete projective measurement families with both terminal prefix
invariants, from actual game success and fixed primitive errors, in a model reducing to the
original one. No future measurement, structural invariant, or stage-success premise is
assumed. -/
theorem exists_intro_two_sided_iteration
    (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
      PauliAnswer → PauliAnswer → Bool)
    (Ξ : BipartiteModel.{v} 𝒞 𝒜 ℬ) (hΞ : ‖Ξ.ψ‖ = 1)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) 𝒜))
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) ℬ))
    (hMA : ∀ q, IsPVMIn (MA q).op) (hMB : ∀ q, IsPVMIn (MB q).op)
    (q : κ → ZMod 2) (hq : ∀ z, (P Z).eval z = q)
    (hL : ∀ w, (L w).SupportedOn univ)
    {initial η δ : ℝ} (hi0 : 0 ≤ initial) (hη0 : 0 ≤ η) (hδ0 : 0 ≤ δ)
    (hfail : 1 - (Ξ.reg (ι → F)).povmValue (parsedGame E X Z P L projectPauli D DP) MA MB ≤
      initial)
    (hZA : introAliceZError projectPauli Z q Ξ MA ≤ η)
    (hZB : introBobZError projectPauli Z q Ξ MB ≤ η)
    (hhideA : ∀ j : Fin ℓ, hidingAliceError L false (hL false) Ξ MA j ≤ δ)
    (hhideB : ∀ j : Fin ℓ, hidingBobError L true (hL true) Ξ MB j ≤ δ)
    (hi : initial ≤ adaptiveSmallThreshold ℓ (TypeGraph.edges E X Z ℓ).card (2 * ℓ))
    (hη : η ≤ adaptiveSmallThreshold ℓ (TypeGraph.edges E X Z ℓ).card (2 * ℓ))
    (hδ : δ ≤ adaptiveSmallThreshold ℓ (TypeGraph.edges E X Z ℓ).card (2 * ℓ)) :
    ∃ (N₁ : ModelOver.{u, v} ℬ) (N₂ : ModelOver.{u, v} N₁.𝒜)
      (MAN : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
        POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) N₁.𝒜))
      (MBN : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
        POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) N₂.𝒜))
      (_ : IntroPrefixInvariant (L false) ℓ
        ((MAN (QuestionType.introspect false, 0)).map introspectPair))
      (_ : IntroPrefixInvariant (L true) ℓ
        ((MBN (QuestionType.introspect true, 0)).map introspectPair)),
      ‖N₂.Ξ.ψ‖ = 1 ∧ (∀ t, IsPVMIn (MAN t).op) ∧ (∀ t, IsPVMIn (MBN t).op) ∧
      1 - (N₂.Ξ.swap.reg (ι → F)).povmValue (parsedGame E X Z P L projectPauli D DP)
          MAN MBN ≤
        adaptiveFailureBudget ℓ (TypeGraph.edges E X Z ℓ).card η δ initial (2 * ℓ) ∧
      N₂.Ξ.swap.POVMReduces Ξ := by
  have he : (0 : ℝ) ≤ (TypeGraph.edges E X Z ℓ).card := Nat.cast_nonneg _
  have hlevels : ℓ ≤ 2 * ℓ := by omega
  have ht := adaptiveSmallThreshold_antitone ℓ he hlevels
  obtain ⟨N₁, MAN, IA, hN₁, hMAN, hfA, hzA, _, _, hhB, hred₁⟩ := exists_intro_iteration
    E X Z P L projectPauli D DP Ξ hΞ MA MB hMA hMB q hq false (hL false)
    hi0 hη0 hδ0 hfail hZB hhideA (hi.trans ht) (hη.trans ht) (hδ.trans ht) ℓ le_rfl
  have hmid : adaptiveFailureBudget ℓ (TypeGraph.edges E X Z ℓ).card η δ initial ℓ ≤
      adaptiveSmallThreshold ℓ (TypeGraph.edges E X Z ℓ).card ℓ := by
    simpa only [show 2 * ℓ - ℓ = ℓ by omega] using
      adaptiveFailureBudget_le_threshold ℓ (2 * ℓ) he hi hη hδ ℓ hlevels
  obtain ⟨N₂, MBN, IB, hN₂, hMBN, hfB, _, _, _, _, hred₂⟩ := exists_intro_bob_iteration
    E X Z P L projectPauli D DP N₁.Ξ hN₁ MAN MB hMAN hMB q hq true (hL true)
    (adaptiveFailureBudget_nonneg ℓ ℓ _ η δ hi0) hη0 hδ0 hfA (hzA.trans_le hZA)
    (fun j => (hhB true (hL true) j).trans_le (hhideB j)) hmid (hη.trans ht) (hδ.trans ht)
    ℓ le_rfl
  refine ⟨N₁, N₂, MAN, MBN, IA, IB, hN₂, hMAN, hMBN, ?_,
    BipartiteModel.POVMReduces.trans hred₂ hred₁⟩
  have hsum := adaptiveFailureBudget_add ℓ (TypeGraph.edges E X Z ℓ).card η δ initial ℓ ℓ
  rw [← two_mul] at hsum
  exact hfB.trans_eq hsum.symm

end TypedEstimates
end MIPRE.Introspection
end

end

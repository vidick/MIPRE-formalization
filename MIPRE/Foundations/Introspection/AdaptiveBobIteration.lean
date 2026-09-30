/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.AdaptivePlayerSwap

@[expose] public section

/-! # Actual Bob iteration and the error transport between the two blocks

The checked Alice construction is applied with the players exchanged and
the Pauli predicate transposed. Returning to the original player order leaves
Alice's entire measurement family literally unchanged. The additional local
registers belong only to Bob's side.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the Alice iteration runs on the
swapped model `Ξ.swap`, and returns a model `N` over the first player's algebra; the Bob-extended
model is `N.Ξ.swap`, and it reduces to `Ξ` because `N.Ξ` reduces to `Ξ.swap`
(`BipartiteModel.POVMReduces.swap`). Every error of the two players moves across the exchange with
no loss (`AdaptivePlayerSwap`), so the matrix version's explicit Bob state and its transport lemmas
have no counterpart.
-/

noncomputable section
namespace MIPRE.Introspection.TypedEstimates
open Finset Matrix Classical
set_option linter.unusedSectionVars false

universe u v

variable {PauliType PauliAnswer κ : Type*} {F ι A : Type}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype A] {ℓ : ℕ}
variable {𝒞 𝒜 ℬ : Type u} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [StarModule ℂ 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarProper 𝒜]
  [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [StarModule ℂ ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]
  [StarProper ℬ]

/-- The actual finite Bob induction in the original game and player order.
Alice's full measurement family is retained, so any previously completed
Alice terminal form remains true without an additional transport premise. The Bob-extended
model `N.Ξ.swap` reduces to the original model, and every primitive error of either player is
unchanged. -/
theorem exists_intro_bob_iteration
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
    (w : Bool) (hL : (L w).SupportedOn univ)
    {initial η δ : ℝ} (hi0 : 0 ≤ initial) (hη0 : 0 ≤ η) (hδ0 : 0 ≤ δ)
    (hfail : 1 - (Ξ.reg (ι → F)).povmValue (parsedGame E X Z P L projectPauli D DP) MA MB ≤
      initial)
    (hZ : introAliceZError projectPauli Z q Ξ MA ≤ η)
    (hhide : ∀ j : Fin ℓ, hidingBobError L w hL Ξ MB j ≤ δ)
    (hi : initial ≤ adaptiveSmallThreshold ℓ (TypeGraph.edges E X Z ℓ).card ℓ)
    (hη : η ≤ adaptiveSmallThreshold ℓ (TypeGraph.edges E X Z ℓ).card ℓ)
    (hδ : δ ≤ adaptiveSmallThreshold ℓ (TypeGraph.edges E X Z ℓ).card ℓ)
    (n : ℕ) (hn : n ≤ ℓ) :
    ∃ (N : ModelOver.{u, v} 𝒜)
      (MN : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
        POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) N.𝒜))
      (_ : IntroPrefixInvariant (L w) n
        ((MN (QuestionType.introspect w, 0)).map introspectPair)),
      ‖N.Ξ.ψ‖ = 1 ∧ (∀ t, IsPVMIn (MN t).op) ∧
      1 - (N.Ξ.swap.reg (ι → F)).povmValue (parsedGame E X Z P L projectPauli D DP) MA MN ≤
        adaptiveFailureBudget ℓ (TypeGraph.edges E X Z ℓ).card η δ initial n ∧
      introAliceZError projectPauli Z q N.Ξ.swap MA = introAliceZError projectPauli Z q Ξ MA ∧
      introBobZError projectPauli Z q N.Ξ.swap MN = introBobZError projectPauli Z q Ξ MB ∧
      (∀ (w' : Bool) (hL' : (L w').SupportedOn univ) (j : Fin ℓ),
        hidingAliceError L w' hL' N.Ξ.swap MA j = hidingAliceError L w' hL' Ξ MA j) ∧
      (∀ j : Fin ℓ, hidingBobError L w hL N.Ξ.swap MN j = hidingBobError L w hL Ξ MB j) ∧
      N.Ξ.swap.POVMReduces Ξ := by
  have hf : 1 - (Ξ.swap.reg (ι → F)).povmValue
      (parsedGame E X Z P L projectPauli D (transposePauliPredicate DP)) MB MA ≤ initial := by
    rw [parsedGame_value_swap]
    exact hfail
  obtain ⟨N, MN, IN, hNψ, hMN, hfailN, hzAN, hzBN, hhideN, hhideBN, hredN⟩ :=
    exists_intro_iteration E X Z P L projectPauli D (transposePauliPredicate DP) Ξ.swap hΞ
      MB MA hMB hMA q hq w hL hi0 hη0 hδ0 hf
      ((introBobZError_swap Ξ projectPauli Z q MA).trans_le hZ)
      (fun j => (hidingAliceError_swap Ξ L w hL MB j).trans_le (hhide j)) hi hη hδ n hn
  refine ⟨N, MN, IN, hNψ, hMN, ?_, ?_, ?_, fun w' hL' j => ?_, fun j => ?_, hredN.swap⟩
  · rw [← transposePauliPredicate_transpose DP, parsedGame_value_swap]
    exact hfailN
  · rw [introAliceZError_swap, hzBN, introBobZError_swap]
  · rw [introBobZError_swap, hzAN, introAliceZError_swap]
  · rw [hidingAliceError_swap, hhideBN w' hL', hidingBobError_swap]
  · rw [hidingBobError_swap, hhideN, hidingAliceError_swap]

end MIPRE.Introspection.TypedEstimates
end

end

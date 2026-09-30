/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.AdaptiveMarginalTest
public import MIPRE.Foundations.Introspection.AdaptiveAnswerMarginal

@[expose] public section

/-! # The actual game supplies the refined stage marginal bound

The actual full Introspect measurement is refined deterministically. Its
malformed mass is retained and charged to the actual reported-prefix error,
which comes from the Sample tests and primitive Bob-Z extraction.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the extracted register state is
the register model `Ξ.reg (ι → F)` of a normalized auxiliary model `Ξ`, and the measurements are
POVMs in its algebras (the postprocessing identity in any ordered `⋆`-ring).
-/

noncomputable section
namespace MIPRE.Introspection.TypedEstimates
open Finset Matrix Classical
set_option linter.unusedSectionVars false

variable {PauliType PauliAnswer F ι κ A : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype A] [DecidableEq A] {ℓ : ℕ}
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]

theorem fullAnswerPrefix_introspectPair (P : CL.CLFun F ι ℓ) (k : ℕ)
    (a : ParsedAnswer (ι → F) A PauliAnswer) :
    fullAnswerPrefix P k (introspectPair a) = reportedPrefix P k .introspect a := by
  cases a <;> rfl

/-- Actual POVM postprocessing gives precisely the tested prefix map,
including all malformed constructors. -/
theorem fullAnswerPrefix_introspect_marginal {R : Type*} [Ring R] [StarRing R] [PartialOrder R]
    [StarOrderedRing R] (P : CL.CLFun F ι ℓ) (k : ℕ)
    (M : POVMIn (ParsedAnswer (ι → F) A PauliAnswer) R) (v : Option (ι → F)) :
    fibSumIn (M.map introspectPair).op (fullAnswerPrefix P k) v =
      (M.map (reportedPrefix P k .introspect)).op v := by
  rw [fibSumIn, ← POVMIn.map_op, POVMIn.map_map]
  simp only [fullAnswerPrefix_introspectPair]

/-- The real refined stage marginal is at most `16η + 56|E|ε`.
The product form and old-prefix support are the current induction
invariant; the marginal estimate itself follows from actual game tests. -/
theorem introspect_adaptive_marginal [StarModule ℂ 𝒜] [PartialOrder 𝒜]
    [StarOrderedRing 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]
    [StarProper ℬ]
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
    {ε η : ℝ}
    (hfail : 1 - (Ξ.reg (ι → F)).povmValue (parsedGame E X Z P L projectPauli D DP) MA MB ≤ ε)
    (q : κ → ZMod 2) (hq : ∀ z, (P Z).eval z = q)
    (w : Bool) (hL : (L w).SupportedOn univ)
    (hS : IsPVMIn (MA (QuestionType.sample w, 0)).op)
    (hZ : ∑ z, (Ξ.reg (ι → F)).snorm ((Ξ.reg (ι → F)).πB
      (((MB (QuestionType.pauli Z, q)).map (pauliProjection projectPauli)).op z -
        smulKron 1 (readout (some : (ι → F) → Option (ι → F)) z))) ^ 2 ≤ η)
    (j : ℕ)
    (M : (y : ι → F) → Option ((ι → F) × A) →
      Matrix (stageRemaining (L w) j y → F) (stageRemaining (L w) j y → F) 𝒜)
    (hform : ∀ a, ((MA (QuestionType.introspect w, 0)).map introspectPair).op a =
      ∑ y, prefixResidualOp (L w) j y (M y a))
    (hsupport : ∀ y x a, (L w).outputPrefix j x ≠ y → M y (some (x, a)) = 0) :
    prefixStageMarginalError (L w) hL j Ξ
      (fun y => stageAnswerRefinement (L w) j y (M y)) ≤
      16 * η + 56 * (TypeGraph.edges E X Z ℓ).card * ε := by
  have hm := stageAnswerRefinement_marginal_le_reported (L w) hL j Ξ M
    (fun a => ((MA (QuestionType.introspect w, 0)).map introspectPair).op a)
    hform hsupport
  simp only [fullAnswerPrefix_introspect_marginal] at hm
  have hg := introspect_prefix_register_rigidity_alice E X Z P L projectPauli D DP
    Ξ hΞ MA MB hfail q hq w hL hS hZ (j + 1)
  calc
    _ ≤ _ := hm
    _ ≤ 2 * (8 * η + 28 * (TypeGraph.edges E X Z ℓ).card * ε) :=
      mul_le_mul_of_nonneg_left hg (by norm_num)
    _ = _ := by ring

end MIPRE.Introspection.TypedEstimates
end

end

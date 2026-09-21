/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AdaptiveMarginalTest
import MIPRE.Foundations.Introspection.AdaptiveAnswerMarginal

/-! # The actual game supplies the refined stage marginal bound

The actual full Introspect measurement is refined deterministically. Its
malformed mass is retained and charged to the actual reported-prefix error,
which comes from the Sample tests and primitive Bob-Z extraction.
-/

noncomputable section
namespace MIPRE.Introspection.TypedEstimates
open Finset Matrix Classical
set_option linter.unusedSectionVars false

variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype A] [DecidableEq A] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K] {ℓ : ℕ}

theorem fullAnswerPrefix_introspectPair (P : CL.CLFun F ι ℓ) (k : ℕ)
    (a : ParsedAnswer (ι → F) A PauliAnswer) :
    fullAnswerPrefix P k (introspectPair a) = reportedPrefix P k .introspect a := by
  cases a <;> rfl

/-- Actual POVM postprocessing gives precisely the tested prefix map,
including all malformed constructors. -/
theorem fullAnswerPrefix_introspect_marginal (P : CL.CLFun F ι ℓ) (k : ℕ)
    (M : POVM (ParsedAnswer (ι → F) A PauliAnswer) H) (v : Option (ι → F)) :
    fibSum (fun a => ((M.map introspectPair).mats a).val) (fullAnswerPrefix P k) v =
      ((M.map (reportedPrefix P k .introspect)).mats v).val := by
  rw [fibSum, ← POVM.map_mats, POVM.map_map]
  simp only [fullAnswerPrefix_introspectPair]

set_option backward.isDefEq.respectTransparency false in
/-- The real refined stage marginal is at most `16η + 56|E|ε`.
The product form and old-prefix support are the current induction
invariant; the marginal estimate itself follows from actual game tests. -/
theorem introspect_adaptive_marginal
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
    {ε η : ℝ}
    (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP)
      (registerState (ι → F) ξ) MA MB ≤ ε)
    (q : κ → ZMod 2) (hq : ∀ z, (P Z).eval z = q)
    (w : Bool) (hL : (L w).SupportedOn univ)
    (hS : IsPVM (fun a => ((MA (QuestionType.sample w, 0)).mats a).val))
    (hZ : ∑ z, snorm (registerState (ι → F) ξ) (bOp
      ((((MB (QuestionType.pauli Z, q)).map (pauliProjection projectPauli)).mats z).val -
        (aOp (readout (some : (ι → F) → Option (ι → F)) z) :
          Matrix ((ι → F) × K) _ ℂ))) ^ 2 ≤ η)
    (j : ℕ)
    (M : (y : ι → F) → Option ((ι → F) × A) →
      Matrix ((stageRemaining (L w) j y → F) × H) _ ℂ)
    (hform : ∀ a, (((MA (QuestionType.introspect w, 0)).map introspectPair).mats a).val =
      ∑ y, prefixResidualOp (L w) j y (M y a))
    (hsupport : ∀ y x a, (L w).outputPrefix j x ≠ y → M y (some (x, a)) = 0) :
    prefixStageMarginalError (L w) hL j ξ
      (fun y => stageAnswerRefinement (L w) j y (M y)) ≤
      16 * η + 56 * (TypeGraph.edges E X Z ℓ).card * ε := by
  have hm := stageAnswerRefinement_marginal_le_reported (L w) hL j ξ M
    (fun a => (((MA (QuestionType.introspect w, 0)).map introspectPair).mats a).val)
    hform hsupport
  simp only [fullAnswerPrefix_introspect_marginal] at hm
  have hg := introspect_prefix_register_rigidity_alice E X Z P L projectPauli D DP
    ξ hξ MA MB hfail q hq w hL hS hZ (j + 1)
  calc
    _ ≤ _ := hm
    _ ≤ 2 * (8 * η + 28 * (TypeGraph.edges E X Z ℓ).card * ε) :=
      mul_le_mul_of_nonneg_left hg (by norm_num)
    _ = _ := by ring

end MIPRE.Introspection.TypedEstimates
end

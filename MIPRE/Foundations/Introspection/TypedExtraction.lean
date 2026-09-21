/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.TypedEstimates
import MIPRE.Foundations.Introspection.FinalExtraction
import MIPRE.Foundations.Introspection.ValueStability
import MIPRE.Foundations.Introspection.StateStability

/-! # Final extraction from the actual typed introspection game

This is the last game calculation in `introspection.tex`: the cross-introspection
edge has probability exactly `1 / |E|`, accepts precisely the original predicate
on pair answers, and rejects all other constructors. Consequently terminal
readout measurements yield an actual original-game strategy with failure at
most `|E|` times the typed-game failure. The tensor-product form is the output
required of the hiding induction; no separate acceptance premise is assumed.
-/

noncomputable section

namespace MIPRE.Introspection.TypedExtraction

open Finset Matrix Classical
open scoped Kronecker

variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Fintype PauliType] [DecidableEq PauliType]
  [Field F] [Fintype F] [DecidableEq F] [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype A] [DecidableEq A]
  [Fintype PauliAnswer] [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  {ℓ : ℕ}

set_option linter.unusedSectionVars false

/-- An accepted cross-introspection answer has the pair constructor on each side. -/
theorem cross_check (L : Bool → CL.CLFun F ι ℓ) (X Z : PauliType)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → PauliAnswer → PauliAnswer → Bool)
    (a b : ParsedAnswer (ι → F) A PauliAnswer) :
    TypedPredicate.check L X Z projectPauli D DP
      (QuestionType.introspect false) (QuestionType.introspect true) a b =
        match a, b with
        | .pair x a, .pair y b => D x y a b
        | _, _ => false := by
  cases a <;> cases b <;>
    simp [TypedPredicate.check, TypedPredicate.fits, TypedPredicate.directed,
      QuestionType.introspect]

/-- A sum supported on the pair answers is exactly a sum over their two components. -/
theorem sum_pairs {R : Type*} [AddCommMonoid R]
    (f : ParsedAnswer (ι → F) A PauliAnswer → R)
    (hp : ∀ p, f (.pauli p) = 0) (hr : ∀ x y a, f (.read x y a) = 0)
    (hh : ∀ x y z, f (.hide x y z) = 0) :
    ∑ a, f a = ∑ xa : (ι → F) × A, f (.pair xa.1 xa.2) := by
  symm
  refine Fintype.sum_of_injective (fun xa : (ι → F) × A =>
    (ParsedAnswer.pair xa.1 xa.2 : ParsedAnswer (ι → F) A PauliAnswer)) ?_ _ f ?_ ?_
  · intro x y h
    cases x; cases y
    simpa using h
  · intro a ha
    cases a with
    | pauli p => exact hp p
    | read x y a => exact hr x y a
    | hide x y z => exact hh x y z
    | pair x a => exact (ha ⟨(x, a), rfl⟩).elim
  · intro xa
    rfl

/-- Embed the terminal question/answer PVM into the full parsed alphabet. -/
def pairReadout (f : (ι → F) → (ι → F)) (Q : (ι → F) → A → Matrix H H ℂ) :
    ParsedAnswer (ι → F) A PauliAnswer → Matrix ((ι → F) × H) ((ι → F) × H) ℂ
  | .pair y a => conditionalReadout f Q (y, a)
  | _ => 0

/-- The terminal pair effects and zero effects on other constructors form a genuine PVM. -/
theorem pairReadout_isPVM (f : (ι → F) → (ι → F)) (Q : (ι → F) → A → Matrix H H ℂ)
    (hQ : ∀ y, IsPVM (Q y)) : IsPVM (pairReadout (PauliAnswer := PauliAnswer) f Q) where
  isSelfAdjoint a := by
    cases a <;> simp only [pairReadout, conjTranspose_zero]
    exact (conditionalReadout_isPVM f Q hQ).isSelfAdjoint _
  idem a := by
    cases a <;> simp only [pairReadout, zero_mul]
    exact (conditionalReadout_isPVM f Q hQ).idem _
  sum_eq_one := by
    rw [sum_pairs _ (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)]
    exact (conditionalReadout_isPVM f Q hQ).sum_eq_one

variable (E : PauliType → PauliType → Bool) (X Z : PauliType)
  (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
  (projectPauli : PauliAnswer → ι → F)
  (D : (ι → F) → (ι → F) → A → A → Bool)
  (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
    PauliAnswer → PauliAnswer → Bool)

/-- On the concrete game edge, only pair answers contribute to the conditional value. -/
theorem condWin_cross_eq (ψ : H × K → ℂ)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) H)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) K) :
    condWin (TypedEstimates.parsedGame E X Z P L projectPauli D DP) ψ MA MB
      (QuestionType.introspect false, 0) (QuestionType.introspect true, 0) =
        ∑ xa : (ι → F) × A, ∑ yb : (ι → F) × A,
          (if D xa.1 yb.1 xa.2 yb.2 then 1 else 0) *
            bornProb ψ (((MA (QuestionType.introspect false, 0)).mats (.pair xa.1 xa.2)).val)
              (((MB (QuestionType.introspect true, 0)).mats (.pair yb.1 yb.2)).val) := by
  unfold condWin
  change (∑ a, ∑ b, (if TypedPredicate.check L X Z projectPauli D
    (fun p s => DP p s 0 0) (QuestionType.introspect false)
      (QuestionType.introspect true) a b then (1 : ℝ) else 0) * _) = _
  simp_rw [cross_check]
  rw [sum_pairs]
  · apply sum_congr rfl
    intro xa _
    rw [sum_pairs]
    all_goals simp
  · intro p
    simp
  · intro x y a
    simp
  · intro x y z
    simp

/-- The actual typed game's success bounds the conditional cross-test failure. -/
theorem cross_failure_le (ψ : H × K → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) H)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) K)
    {ε : ℝ}
    (hfail : 1 - povmValue (TypedEstimates.parsedGame E X Z P L projectPauli D DP)
      ψ MA MB ≤ ε) :
    condFail (TypedEstimates.parsedGame E X Z P L projectPauli D DP) ψ MA MB
      (QuestionType.introspect false, 0) (QuestionType.introspect true, 0) ≤
        (TypeGraph.edges E X Z ℓ).card * ε := by
  have hμ := TypedPresentation.mu_cross_introspect E X Z P
    (TypedEstimates.questionCheck L X Z projectPauli D DP)
  have hc : (0 : ℝ) < (TypeGraph.edges E X Z ℓ).card := by
    exact_mod_cast (TypeGraph.edges_nonempty E X Z ℓ).card_pos
  have hpos : 0 < (TypedEstimates.parsedGame E X Z P L projectPauli D DP).μ
      (QuestionType.introspect false, 0) (QuestionType.introspect true, 0) := by
    rw [TypedEstimates.parsedGame, hμ]
    positivity
  have h := condFail_le_div hψ hfail hpos
  change _ ≤ ε / (TypedPresentation.game E X Z ℓ P
    (TypedEstimates.questionCheck L X Z projectPauli D DP)).μ _ _ at h
  rw [hμ, div_inv_eq_mul, mul_comm] at h
  exact h

/-- Terminal tensor-product pair effects identify the conditional value exactly.
No premise about the other parsed constructors is needed: the decider rejects them. -/
theorem condWin_cross_readout (ξ : H × K → ℂ)
    (QA : (ι → F) → A → Matrix H H ℂ) (QB : (ι → F) → A → Matrix K K ℂ)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H))
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × K))
    (hA : ∀ y a, ((MA (QuestionType.introspect false, 0)).mats (.pair y a)).val =
      conditionalReadout (L false).eval QA (y, a))
    (hB : ∀ y a, ((MB (QuestionType.introspect true, 0)).mats (.pair y a)).val =
      conditionalReadout (L true).eval QB (y, a)) :
    condWin (TypedEstimates.parsedGame E X Z P L projectPauli D DP)
      (registerState (ι → F) ξ) MA MB
      (QuestionType.introspect false, 0) (QuestionType.introspect true, 0) =
        readoutAcceptance (L false).eval (L true).eval ξ QA QB D := by
  rw [condWin_cross_eq]
  simp_rw [hA, hB]
  rfl

/-- **The final extraction step from the actual game.** Given the product forms
produced by the hiding induction, near-perfect typed play constructs a legal
original strategy on exactly the auxiliary spaces, with explicit loss `|E| ε`. -/
theorem exists_strategy_of_terminal_form
    (G : Game (ι → F) (ι → F) A A)
    (hμ : ∀ x y, G.μ x y = CL.clDist (L false).eval (L true).eval x y)
    (hD : G.D = D) {dA dB : ℕ}
    (ξ : Fin dA × Fin dB → ℂ) (hξ : star ξ ⬝ᵥ ξ = 1)
    (QA : (ι → F) → A → Matrix (Fin dA) (Fin dA) ℂ)
    (QB : (ι → F) → A → Matrix (Fin dB) (Fin dB) ℂ)
    (hQA : ∀ x, IsPVM (QA x)) (hQB : ∀ y, IsPVM (QB y))
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × Fin dA))
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × Fin dB))
    (hA : ∀ y a, ((MA (QuestionType.introspect false, 0)).mats (.pair y a)).val =
      conditionalReadout (L false).eval QA (y, a))
    (hB : ∀ y a, ((MB (QuestionType.introspect true, 0)).mats (.pair y a)).val =
      conditionalReadout (L true).eval QB (y, a))
    {ε : ℝ} (hfail :
      1 - povmValue (TypedEstimates.parsedGame E X Z P L projectPauli D DP)
        (registerState (ι → F) ξ) MA MB ≤ ε) :
    ∃ S : TensorProductStrategy G, S.dA = dA ∧ S.dB = dB ∧
      1 - (TypeGraph.edges E X Z ℓ).card * ε ≤ S.value := by
  have hξnorm : ‖evec ξ‖ = 1 := by
    have hn := norm_evec_sq ξ
    rw [hξ, Complex.one_re] at hn
    nlinarith [norm_nonneg (evec ξ)]
  have hstate : star (registerState (ι → F) ξ) ⬝ᵥ registerState (ι → F) ξ = 1 := by
    rw [dotProduct_star_self, registerState_norm ξ hξnorm]
    norm_num
  have hfail' := cross_failure_le E X Z P L projectPauli D DP
    (registerState (ι → F) ξ) hstate MA MB hfail
  rw [condFail, condWin_cross_readout E X Z P L projectPauli D DP ξ QA QB MA MB hA hB]
    at hfail'
  obtain ⟨S, hdA, hdB, hval⟩ := exists_strategy_of_readoutAcceptance G
    (L false).eval (L true).eval
    (fun x y => (hμ x y).trans (sampled_dist_eq_clDist _ _ x y).symm)
    ξ hξ QA QB hQA hQB
  refine ⟨S, hdA, hdB, ?_⟩
  rw [hval, hD]
  linarith

/-- **Quantitative terminal extraction.** The induction need only approximate
the pair readouts in summed squared state distance. Its two errors cost exactly
`2 sqrt(deltaA) + 2 sqrt(deltaB)` after the cross-test's `|E| epsilon` loss.
The actual measurements may have effects on all malformed constructors. -/
theorem exists_strategy_of_approx_terminal_form
    (G : Game (ι → F) (ι → F) A A)
    (hμ : ∀ x y, G.μ x y = CL.clDist (L false).eval (L true).eval x y)
    (hD : G.D = D) {dA dB : ℕ}
    (ξ : Fin dA × Fin dB → ℂ) (hξ : star ξ ⬝ᵥ ξ = 1)
    (QA : (ι → F) → A → Matrix (Fin dA) (Fin dA) ℂ)
    (QB : (ι → F) → A → Matrix (Fin dB) (Fin dB) ℂ)
    (hQA : ∀ x, IsPVM (QA x)) (hQB : ∀ y, IsPVM (QB y))
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × Fin dA))
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × Fin dB))
    (hMA : IsPVM (fun a => ((MA (QuestionType.introspect false, 0)).mats a).val))
    (hMB : IsPVM (fun b => ((MB (QuestionType.introspect true, 0)).mats b).val))
    {ε δA δB : ℝ} (hfail :
      1 - povmValue (TypedEstimates.parsedGame E X Z P L projectPauli D DP)
        (registerState (ι → F) ξ) MA MB ≤ ε)
    (hA : ∑ a, stateSqNorm (registerState (ι → F) ξ)
      (((MA (QuestionType.introspect false, 0)).mats a).val -
        pairReadout (L false).eval QA a) ≤ δA)
    (hB : ∑ b, ‖stateVecB (registerState (ι → F) ξ)
      (((MB (QuestionType.introspect true, 0)).mats b).val -
        pairReadout (L true).eval QB b)‖ ^ 2 ≤ δB) :
    ∃ S : TensorProductStrategy G, S.dA = dA ∧ S.dB = dB ∧
      1 - ((TypeGraph.edges E X Z ℓ).card * ε +
        2 * Real.sqrt δA + 2 * Real.sqrt δB) ≤ S.value := by
  have hξnorm : ‖evec ξ‖ = 1 := by
    have hn := norm_evec_sq ξ
    rw [hξ, Complex.one_re] at hn
    nlinarith [norm_nonneg (evec ξ)]
  let ψ := registerState (ι → F) ξ
  have hn : ‖evec ψ‖ = 1 := registerState_norm ξ hξnorm
  have hu : star ψ ⬝ᵥ ψ = 1 := by rw [dotProduct_star_self, hn]; norm_num
  let Dt := TypedEstimates.questionCheck L X Z projectPauli D DP
    (QuestionType.introspect false, (0 : κ → ZMod 2)) (QuestionType.introspect true, 0)
  let IA := pairReadout (PauliAnswer := PauliAnswer) (L false).eval QA
  let IB := pairReadout (PauliAnswer := PauliAnswer) (L true).eval QB
  have hIA : IsPVM IA := pairReadout_isPVM _ _ hQA
  have hIB : IsPVM IB := pairReadout_isPVM _ _ hQB
  have hid : testAcceptance ψ Dt IA IB =
      readoutAcceptance (L false).eval (L true).eval ξ QA QB D := by
    exact condWin_cross_readout E X Z P L projectPauli D DP ξ QA QB
      (fun _ => hIA.toPOVM) (fun _ => hIB.toPOVM) (fun _ _ => rfl) (fun _ _ => rfl)
  have hc := testAcceptance_stability ψ hn Dt
    (fun a => ((MA (QuestionType.introspect false, 0)).mats a).val) IA
    (fun b => ((MB (QuestionType.introspect true, 0)).mats b).val) IB
    hMA hIA hMB hIB hA hB
  rw [hid] at hc
  have hf := cross_failure_le E X Z P L projectPauli D DP ψ hu MA MB hfail
  change 1 - testAcceptance ψ Dt _ _ ≤ _ at hf
  obtain ⟨S, hdA, hdB, hval⟩ := exists_strategy_of_readoutAcceptance G
    (L false).eval (L true).eval
    (fun x y => (hμ x y).trans (sampled_dist_eq_clDist _ _ x y).symm)
    ξ hξ QA QB hQA hQB
  refine ⟨S, hdA, hdB, ?_⟩
  rw [hval, hD]
  have hc' := (abs_le.mp hc).2
  linarith

/-- The complete final extraction calculation after Pauli state approximation
and hiding measurement approximation. All three errors are paid explicitly. -/
theorem exists_strategy_of_state_and_terminal_approx
    (G : Game (ι → F) (ι → F) A A)
    (hμ : ∀ x y, G.μ x y = CL.clDist (L false).eval (L true).eval x y)
    (hD : G.D = D) {dA dB : ℕ}
    (ξ : Fin dA × Fin dB → ℂ) (hξ : star ξ ⬝ᵥ ξ = 1)
    (ψ : ((ι → F) × Fin dA) × ((ι → F) × Fin dB) → ℂ) (hψ : ‖evec ψ‖ = 1)
    (QA : (ι → F) → A → Matrix (Fin dA) (Fin dA) ℂ)
    (QB : (ι → F) → A → Matrix (Fin dB) (Fin dB) ℂ)
    (hQA : ∀ x, IsPVM (QA x)) (hQB : ∀ y, IsPVM (QB y))
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × Fin dA))
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × Fin dB))
    (hMA : ∀ q, IsPVM (fun a => ((MA q).mats a).val))
    (hMB : ∀ q, IsPVM (fun b => ((MB q).mats b).val))
    {ε η δA δB : ℝ} (hfail :
      1 - povmValue (TypedEstimates.parsedGame E X Z P L projectPauli D DP) ψ MA MB ≤ ε)
    (hstate : ‖evec (ψ - registerState (ι → F) ξ)‖ ^ 2 ≤ η)
    (hA : ∑ a, stateSqNorm (registerState (ι → F) ξ)
      (((MA (QuestionType.introspect false, 0)).mats a).val -
        pairReadout (L false).eval QA a) ≤ δA)
    (hB : ∑ b, ‖stateVecB (registerState (ι → F) ξ)
      (((MB (QuestionType.introspect true, 0)).mats b).val -
        pairReadout (L true).eval QB b)‖ ^ 2 ≤ δB) :
    ∃ S : TensorProductStrategy G, S.dA = dA ∧ S.dB = dB ∧
      1 - ((TypeGraph.edges E X Z ℓ).card * (ε + 2 * Real.sqrt η) +
        2 * Real.sqrt δA + 2 * Real.sqrt δB) ≤ S.value := by
  have hn : ‖evec ξ‖ = 1 := by
    have h := norm_evec_sq ξ
    rw [hξ, Complex.one_re] at h
    nlinarith [norm_nonneg (evec ξ)]
  have hfail' := povmValue_failure_transfer
    (TypedEstimates.parsedGame E X Z P L projectPauli D DP) ψ (registerState (ι → F) ξ)
    hψ (registerState_norm ξ hn) MA MB hMA hMB hfail hstate
  exact exists_strategy_of_approx_terminal_form E X Z P L projectPauli D DP
    G hμ hD ξ hξ QA QB hQA hQB MA MB (hMA _) (hMB _) hfail' hA hB

end MIPRE.Introspection.TypedExtraction

end

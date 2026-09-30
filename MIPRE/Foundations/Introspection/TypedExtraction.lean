/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.TypedEstimates
public import MIPRE.Foundations.Introspection.FinalExtraction
public import MIPRE.Foundations.Introspection.ValueStability
public import MIPRE.Foundations.Introspection.StateStability

@[expose] public section

/-! # Final extraction from the actual typed introspection game

This is the last game calculation in `introspection.tex`: the cross-introspection
edge has probability exactly `1 / |E|`, accepts precisely the original predicate
on pair answers, and rejects all other constructors. Consequently terminal
readout measurements yield an actual original-game strategy with failure at
most `|E|` times the typed-game failure. The tensor-product form is the output
required of the hiding induction; no separate acceptance premise is assumed.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the typed game is played in a
model `Ψ`, the terminal measurements in the register model `Ξ.reg (ι → F)`, where the product form
of a readout is `conditionalReadout` (`smulKron` of the auxiliary operator and the question
readout). The extracted strategy is a projective strategy of the auxiliary model `Ξ` itself, which
replaces the matrix statement's equality of local dimensions; the actual state of the last theorem
is a unit vector `φ` of the register model's space, played in `(Ξ.reg (ι → F)).withState φ`.
-/

noncomputable section

namespace MIPRE.Introspection.TypedExtraction

open Finset Matrix Classical

variable {PauliType PauliAnswer F ι κ A : Type*}
  [Fintype PauliType] [DecidableEq PauliType]
  [Field F] [Fintype F] [DecidableEq F] [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype A] [DecidableEq A]
  [Fintype PauliAnswer] {ℓ : ℕ}

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
def pairReadout {R : Type*} [Ring R] [Algebra ℂ R] (f : (ι → F) → (ι → F))
    (Q : (ι → F) → A → R) : ParsedAnswer (ι → F) A PauliAnswer → Matrix (ι → F) (ι → F) R
  | .pair y a => conditionalReadout f Q (y, a)
  | _ => 0

/-- The terminal pair effects and zero effects on other constructors form a genuine PVM. -/
theorem pairReadout_isPVM {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
    (f : (ι → F) → (ι → F)) (Q : (ι → F) → A → R) (hQ : ∀ y, IsPVMIn (Q y)) :
    IsPVMIn (pairReadout (PauliAnswer := PauliAnswer) f Q) where
  star_eq a := by
    cases a <;> simp only [pairReadout, star_zero]
    exact (conditionalReadout_isPVM f Q hQ).star_eq _
  idem a := by
    cases a <;> simp only [pairReadout, zero_mul]
    exact (conditionalReadout_isPVM f Q hQ).idem _
  sum_eq_one := by
    rw [sum_pairs _ (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)]
    exact (conditionalReadout_isPVM f Q hQ).sum_eq_one
  orthogonal {a b} h := by
    cases a <;> cases b <;> simp only [pairReadout, zero_mul, mul_zero]
    refine (conditionalReadout_isPVM f Q hQ).orthogonal fun he => h ?_
    simp only [Prod.mk.injEq] at he
    rw [he.1, he.2]

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ]

variable (E : PauliType → PauliType → Bool) (X Z : PauliType)
  (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
  (projectPauli : PauliAnswer → ι → F)
  (D : (ι → F) → (ι → F) → A → A → Bool)
  (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
    PauliAnswer → PauliAnswer → Bool)

/-- On the concrete game edge, only pair answers contribute to the conditional value. -/
theorem condWin_cross_eq (Ψ : BipartiteModel 𝒞 𝒜 ℬ)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) 𝒜)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) ℬ) :
    Ψ.condWin (TypedEstimates.parsedGame E X Z P L projectPauli D DP) MA MB
      (QuestionType.introspect false, 0) (QuestionType.introspect true, 0) =
        ∑ xa : (ι → F) × A, ∑ yb : (ι → F) × A,
          (if D xa.1 yb.1 xa.2 yb.2 then 1 else 0) *
            Ψ.bornProb ((MA (QuestionType.introspect false, 0)).op (.pair xa.1 xa.2))
              ((MB (QuestionType.introspect true, 0)).op (.pair yb.1 yb.2)) := by
  unfold BipartiteModel.condWin
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
theorem cross_failure_le (Ψ : BipartiteModel 𝒞 𝒜 ℬ) (hΨ : ‖Ψ.ψ‖ = 1)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) 𝒜)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) ℬ)
    {ε : ℝ}
    (hfail : 1 - Ψ.povmValue (TypedEstimates.parsedGame E X Z P L projectPauli D DP)
      MA MB ≤ ε) :
    Ψ.condFail (TypedEstimates.parsedGame E X Z P L projectPauli D DP) MA MB
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
  have h := Ψ.condFail_le_div hΨ hfail hpos
  change _ ≤ ε / (TypedPresentation.game E X Z ℓ P
    (TypedEstimates.questionCheck L X Z projectPauli D DP)).μ _ _ at h
  rw [hμ, div_inv_eq_mul, mul_comm] at h
  exact h

variable [StarProper 𝒜] [StarProper ℬ]

/-- Terminal pair effects of product form identify the conditional value exactly, in the
register model. No premise about the other parsed constructors is needed: the decider rejects
them. -/
theorem condWin_cross_readout (Ξ : BipartiteModel 𝒞 𝒜 ℬ)
    (QA : (ι → F) → A → 𝒜) (QB : (ι → F) → A → ℬ)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) 𝒜))
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) ℬ))
    (hA : ∀ y a, (MA (QuestionType.introspect false, 0)).op (.pair y a) =
      conditionalReadout (L false).eval QA (y, a))
    (hB : ∀ y a, (MB (QuestionType.introspect true, 0)).op (.pair y a) =
      conditionalReadout (L true).eval QB (y, a)) :
    (Ξ.reg (ι → F)).condWin (TypedEstimates.parsedGame E X Z P L projectPauli D DP) MA MB
      (QuestionType.introspect false, 0) (QuestionType.introspect true, 0) =
        readoutAcceptance (L false).eval (L true).eval Ξ QA QB D := by
  rw [condWin_cross_eq]
  simp_rw [hA, hB]
  rfl

/-- **The final extraction step from the actual game.** Given the product forms
produced by the hiding induction, near-perfect typed play constructs a legal
original strategy in exactly the auxiliary model, with explicit loss `|E| ε`. -/
theorem exists_strategy_of_terminal_form
    (G : Game (ι → F) (ι → F) A A)
    (hμ : ∀ x y, G.μ x y = CL.clDist (L false).eval (L true).eval x y)
    (hD : G.D = D) (Ξ : BipartiteModel 𝒞 𝒜 ℬ) (hΞ : ‖Ξ.ψ‖ = 1)
    (QA : (ι → F) → A → 𝒜) (QB : (ι → F) → A → ℬ)
    (hQA : ∀ x, IsPVMIn (QA x)) (hQB : ∀ y, IsPVMIn (QB y))
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) 𝒜))
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) ℬ))
    (hA : ∀ y a, (MA (QuestionType.introspect false, 0)).op (.pair y a) =
      conditionalReadout (L false).eval QA (y, a))
    (hB : ∀ y a, (MB (QuestionType.introspect true, 0)).op (.pair y a) =
      conditionalReadout (L true).eval QB (y, a))
    {ε : ℝ} (hfail :
      1 - (Ξ.reg (ι → F)).povmValue (TypedEstimates.parsedGame E X Z P L projectPauli D DP)
        MA MB ≤ ε) :
    ∃ S : Ξ.ProjStrat G, 1 - (TypeGraph.edges E X Z ℓ).card * ε ≤ S.value := by
  have hstate : ‖(Ξ.reg (ι → F)).ψ‖ = 1 := by rw [BipartiteModel.norm_reg_ψ, hΞ]
  have hfail' := cross_failure_le E X Z P L projectPauli D DP
    (Ξ.reg (ι → F)) hstate MA MB hfail
  rw [BipartiteModel.condFail,
    condWin_cross_readout E X Z P L projectPauli D DP Ξ QA QB MA MB hA hB] at hfail'
  obtain ⟨S, hval⟩ := exists_strategy_of_readoutAcceptance G
    (L false).eval (L true).eval
    (fun x y => (hμ x y).trans (sampled_dist_eq_clDist _ _ x y).symm)
    Ξ hΞ QA QB hQA hQB
  refine ⟨S, ?_⟩
  rw [hval, hD]
  linarith

variable [StarModule ℂ 𝒜] [StarModule ℂ ℬ]

/-- **Quantitative terminal extraction.** The induction need only approximate
the pair readouts in summed squared state distance. Its two errors cost exactly
`2 sqrt(deltaA) + 2 sqrt(deltaB)` after the cross-test's `|E| epsilon` loss.
The actual measurements may have effects on all malformed constructors. -/
theorem exists_strategy_of_approx_terminal_form
    (G : Game (ι → F) (ι → F) A A)
    (hμ : ∀ x y, G.μ x y = CL.clDist (L false).eval (L true).eval x y)
    (hD : G.D = D) (Ξ : BipartiteModel 𝒞 𝒜 ℬ) (hΞ : ‖Ξ.ψ‖ = 1)
    (QA : (ι → F) → A → 𝒜) (QB : (ι → F) → A → ℬ)
    (hQA : ∀ x, IsPVMIn (QA x)) (hQB : ∀ y, IsPVMIn (QB y))
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) 𝒜))
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) ℬ))
    (hMA : IsPVMIn (MA (QuestionType.introspect false, 0)).op)
    (hMB : IsPVMIn (MB (QuestionType.introspect true, 0)).op)
    {ε δA δB : ℝ} (hfail :
      1 - (Ξ.reg (ι → F)).povmValue (TypedEstimates.parsedGame E X Z P L projectPauli D DP)
        MA MB ≤ ε)
    (hA : ∑ a, (Ξ.reg (ι → F)).stateSqNorm
      ((MA (QuestionType.introspect false, 0)).op a - pairReadout (L false).eval QA a) ≤ δA)
    (hB : ∑ b, (Ξ.reg (ι → F)).swap.stateSqNorm
      ((MB (QuestionType.introspect true, 0)).op b - pairReadout (L true).eval QB b) ≤ δB) :
    ∃ S : Ξ.ProjStrat G,
      1 - ((TypeGraph.edges E X Z ℓ).card * ε +
        2 * Real.sqrt δA + 2 * Real.sqrt δB) ≤ S.value := by
  have hn : ‖(Ξ.reg (ι → F)).ψ‖ = 1 := by rw [BipartiteModel.norm_reg_ψ, hΞ]
  let Dt := TypedEstimates.questionCheck L X Z projectPauli D DP
    (QuestionType.introspect false, (0 : κ → ZMod 2)) (QuestionType.introspect true, 0)
  let IA := pairReadout (PauliAnswer := PauliAnswer) (L false).eval QA
  let IB := pairReadout (PauliAnswer := PauliAnswer) (L true).eval QB
  have hIA : IsPVMIn IA := pairReadout_isPVM _ _ hQA
  have hIB : IsPVMIn IB := pairReadout_isPVM _ _ hQB
  have hid : testAcceptance (Ξ.reg (ι → F)) Dt IA IB =
      readoutAcceptance (L false).eval (L true).eval Ξ QA QB D := by
    exact condWin_cross_readout E X Z P L projectPauli D DP Ξ QA QB
      (fun _ => hIA.toPOVMIn) (fun _ => hIB.toPOVMIn) (fun _ _ => rfl) (fun _ _ => rfl)
  have hc := testAcceptance_stability (Ξ.reg (ι → F)) hn Dt
    (fun a => (MA (QuestionType.introspect false, 0)).op a) IA
    (fun b => (MB (QuestionType.introspect true, 0)).op b) IB
    hMA hIA hMB hIB hA hB
  rw [hid] at hc
  have hf := cross_failure_le E X Z P L projectPauli D DP (Ξ.reg (ι → F)) hn MA MB hfail
  change 1 - testAcceptance (Ξ.reg (ι → F)) Dt _ _ ≤ _ at hf
  obtain ⟨S, hval⟩ := exists_strategy_of_readoutAcceptance G
    (L false).eval (L true).eval
    (fun x y => (hμ x y).trans (sampled_dist_eq_clDist _ _ x y).symm)
    Ξ hΞ QA QB hQA hQB
  refine ⟨S, ?_⟩
  rw [hval, hD]
  have hc' := (abs_le.mp hc).2
  linarith

/-- The complete final extraction calculation after Pauli state approximation
and hiding measurement approximation. All three errors are paid explicitly. -/
theorem exists_strategy_of_state_and_terminal_approx
    (G : Game (ι → F) (ι → F) A A)
    (hμ : ∀ x y, G.μ x y = CL.clDist (L false).eval (L true).eval x y)
    (hD : G.D = D) (Ξ : BipartiteModel 𝒞 𝒜 ℬ) (hΞ : ‖Ξ.ψ‖ = 1)
    (φ : (Ξ.reg (ι → F)).H) (hφ : ‖φ‖ = 1)
    (QA : (ι → F) → A → 𝒜) (QB : (ι → F) → A → ℬ)
    (hQA : ∀ x, IsPVMIn (QA x)) (hQB : ∀ y, IsPVMIn (QB y))
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) 𝒜))
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) ℬ))
    (hMA : ∀ q, IsPVMIn (MA q).op) (hMB : ∀ q, IsPVMIn (MB q).op)
    {ε η δA δB : ℝ} (hfail :
      1 - ((Ξ.reg (ι → F)).withState φ).povmValue
        (TypedEstimates.parsedGame E X Z P L projectPauli D DP) MA MB ≤ ε)
    (hstate : ‖φ - (Ξ.reg (ι → F)).ψ‖ ^ 2 ≤ η)
    (hA : ∑ a, (Ξ.reg (ι → F)).stateSqNorm
      ((MA (QuestionType.introspect false, 0)).op a - pairReadout (L false).eval QA a) ≤ δA)
    (hB : ∑ b, (Ξ.reg (ι → F)).swap.stateSqNorm
      ((MB (QuestionType.introspect true, 0)).op b - pairReadout (L true).eval QB b) ≤ δB) :
    ∃ S : Ξ.ProjStrat G,
      1 - ((TypeGraph.edges E X Z ℓ).card * (ε + 2 * Real.sqrt η) +
        2 * Real.sqrt δA + 2 * Real.sqrt δB) ≤ S.value := by
  have hn : ‖(Ξ.reg (ι → F)).ψ‖ = 1 := by rw [BipartiteModel.norm_reg_ψ, hΞ]
  have hfail' := povmValue_failure_transfer ((Ξ.reg (ι → F)).withState φ)
    (TypedEstimates.parsedGame E X Z P L projectPauli D DP) (Ξ.reg (ι → F)).ψ hφ hn
    MA MB hMA hMB hfail hstate
  exact exists_strategy_of_approx_terminal_form E X Z P L projectPauli D DP
    G hμ hD Ξ hΞ QA QB hQA hQB MA MB (hMA _) (hMB _) hfail' hA hB

end MIPRE.Introspection.TypedExtraction

end

end

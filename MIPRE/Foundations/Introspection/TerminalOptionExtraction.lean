/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.AdaptiveTerminalInvariant
public import MIPRE.Foundations.Introspection.TypedExtraction

@[expose] public section

/-! # Extracting ordinary answers from terminal option-valued measurements

The adaptive invariant retains malformed answers as `none`. Mapping this
outcome to a fixed valid answer preserves projectivity and cannot decrease
the accepted mass of the original predicate. Applied to both concrete
terminal invariants, this constructs an original-game strategy directly
from the actual typed game, with no zero-malformed-mass assumption.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the completion of a
malformed outcome is a coarse-graining of a POVM in any ordered `⋆`-ring, and the acceptance
comparison is between Born probabilities of an auxiliary model `Ξ`. The terminal measurements are
played in the register model `Ξ.reg (ι → F)`, where their valid effects are the
`conditionalReadout`s of the auxiliary POVMs `terminalAuxPOVM` in the players' algebras `𝒜` and
`ℬ`; the extracted strategy is a projective strategy of `Ξ` itself, which replaces the matrix
statement's equality of local dimensions.
-/

noncomputable section
namespace MIPRE.Introspection
open Finset Matrix Classical
set_option linter.unusedSectionVars false

section Completion
variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- Replace a malformed auxiliary outcome by a fixed ordinary answer. -/
def completeOptionPOVM {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
    (a₀ : A) (Q : POVMIn (Option A) R) : POVMIn A R :=
  Q.map (fun a => a.getD a₀)

theorem completeOptionPOVM_isPVM {R : Type*} [Ring R] [StarRing R] [PartialOrder R]
    [StarOrderedRing R] (a₀ : A) (Q : POVMIn (Option A) R) (hQ : IsPVMIn Q.op) :
    IsPVMIn (completeOptionPOVM a₀ Q).op :=
  POVMIn.isPVMIn_map hQ (fun a => a.getD a₀)

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ]

/-- Accepted valid outcomes remain accepted after completion; all newly
accepted malformed outcomes contribute nonnegative Born probabilities. -/
theorem option_valid_acceptance_le_complete (Ψ : BipartiteModel 𝒞 𝒜 ℬ)
    (Q : POVMIn (Option A) 𝒜) (R : POVMIn (Option B) ℬ)
    (a₀ : A) (b₀ : B) (D : A → B → Bool) :
    (∑ a, ∑ b, (if D a b then (1 : ℝ) else 0) *
      Ψ.bornProb (Q.op (some a)) (R.op (some b))) ≤
      ∑ a, ∑ b, (if D a b then (1 : ℝ) else 0) *
        Ψ.bornProb ((completeOptionPOVM a₀ Q).op a) ((completeOptionPOVM b₀ R).op b) := by
  have hn (a : Option A) (b : Option B) :
      0 ≤ (if D (a.getD a₀) (b.getD b₀) then (1 : ℝ) else 0) *
        Ψ.bornProb (Q.op a) (R.op b) :=
    mul_nonneg (by split_ifs <;> norm_num) (Ψ.bornProb_nonneg (Q.op_nonneg a) (R.op_nonneg b))
  have hrow (a : Option A) :
      (∑ b : B, (if D (a.getD a₀) b then (1 : ℝ) else 0) *
        Ψ.bornProb (Q.op a) (R.op (some b))) ≤
      ∑ b : Option B, (if D (a.getD a₀) (b.getD b₀) then (1 : ℝ) else 0) *
        Ψ.bornProb (Q.op a) (R.op b) := by
    rw [Fintype.sum_option]
    exact le_add_of_nonneg_left (hn a none)
  unfold completeOptionPOVM
  rw [Ψ.sum_weight_bornProb_map]
  calc
    _ ≤ ∑ a : A, ∑ b : Option B,
        (if D a (b.getD b₀) then (1 : ℝ) else 0) * Ψ.bornProb (Q.op (some a)) (R.op b) :=
      Finset.sum_le_sum (fun a _ => hrow (some a))
    _ ≤ ∑ a : Option A, ∑ b : Option B,
        (if D (a.getD a₀) (b.getD b₀) then (1 : ℝ) else 0) * Ψ.bornProb (Q.op a) (R.op b) := by
      rw [Fintype.sum_option]
      exact le_add_of_nonneg_left (Finset.sum_nonneg (fun b _ => hn none b))

end Completion

section Readout
variable {I X Y A B : Type*}
  [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B]
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ]

/-- The actual question law converts the valid part of the readout test
into a lower bound on the completed ordinary-answer strategy. -/
theorem readoutAcceptance_le_completedValue (G : Game X Y A B)
    (f : I → X) (g : I → Y)
    (hμ : ∀ x y, G.μ x y = SampledGame.dist f g x y)
    (Ξ : BipartiteModel 𝒞 𝒜 ℬ) (Q : X → POVMIn (Option A) 𝒜) (R : Y → POVMIn (Option B) ℬ)
    (a₀ : A) (b₀ : B) :
    readoutAcceptance f g Ξ (fun x a => (Q x).op (some a))
      (fun y b => (R y).op (some b)) G.D ≤
        Ξ.povmValue G (fun x => completeOptionPOVM a₀ (Q x))
          (fun y => completeOptionPOVM b₀ (R y)) := by
  have he : readoutAcceptance f g Ξ (fun x a => (Q x).op (some a))
      (fun y b => (R y).op (some b)) G.D =
      ∑ x, ∑ y, G.μ x y * ∑ a, ∑ b, (if G.D x y a b then (1 : ℝ) else 0) *
        Ξ.bornProb ((Q x).op (some a)) ((R y).op (some b)) := by
    unfold readoutAcceptance
    simp_rw [bornProb_conditionalReadout f g Ξ]
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [hμ]
    ring
  rw [he]
  unfold BipartiteModel.povmValue BipartiteModel.condWin
  exact Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ =>
    mul_le_mul_of_nonneg_left
      (option_valid_acceptance_le_complete Ξ (Q x) (R y) a₀ b₀ (G.D x y))
      (G.μ_nonneg x y)))

end Readout

section Terminal
variable {F ι A PauliAnswer : Type*}
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]
  [Fintype PauliAnswer] {ℓ : ℕ}

/-- A valid full-option outcome has a unique parsed-answer preimage. -/
theorem introspectPair_map_some {R : Type*} [Ring R] [StarRing R] [PartialOrder R]
    [StarOrderedRing R] (N : POVMIn (ParsedAnswer (ι → F) A PauliAnswer) R)
    (y : ι → F) (a : A) :
    (N.map TypedEstimates.introspectPair).op (some (y, a)) = N.op (.pair y a) := by
  rw [POVMIn.map_op]
  refine Finset.sum_eq_single (f := fun b => N.op b)
    (ParsedAnswer.pair y a) ?_ ?_
  · intro b hb hba
    have he : TypedEstimates.introspectPair b = some (y, a) := (mem_filter.mp hb).2
    cases b with
    | pauli p => cases he
    | read x z b => cases he
    | hide x z t => cases he
    | pair x b =>
      have h := Option.some.inj he
      have hx : x = y := congrArg Prod.fst h
      have hb : b = a := congrArg Prod.snd h
      subst x
      subst b
      exact False.elim (hba rfl)
  · intro h
    exact False.elim (h (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩))

variable {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] [PartialOrder 𝒜]
  [StarOrderedRing 𝒜] [StarProper 𝒜]

/-- The valid parsed effects of an actual terminal invariant have the
precise conditional readout form, regardless of malformed effects. -/
theorem IntroPrefixInvariant.terminal_parsed_pair
    {P : CL.CLFun F ι ℓ}
    {N : POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) 𝒜)}
    (I : IntroPrefixInvariant P ℓ (N.map TypedEstimates.introspectPair))
    (hP : P.ExactlyOn univ)
    (y : ι → F) (a : A) :
    N.op (.pair y a) = conditionalReadout P.eval
      (fun y a => (terminalAuxPOVM hP I y).op (some a)) (y, a) := by
  rw [← introspectPair_map_some]
  exact I.terminal_some hP y a

end Terminal

namespace TypedExtraction
variable {PauliType PauliAnswer F ι κ A : Type*}
  [Fintype PauliType] [DecidableEq PauliType]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype A] [DecidableEq A] [Nonempty A] [Fintype PauliAnswer] {ℓ : ℕ}
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [StarProper 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ] [StarProper ℬ]

/-- Both concrete terminal invariants construct an ordinary-answer original
strategy, a projective strategy of the auxiliary model. Completing malformed
outcomes costs no additional failure. -/
theorem exists_strategy_of_terminal_invariants
    (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
    (hL : ∀ w, (L w).ExactlyOn univ)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
      PauliAnswer → PauliAnswer → Bool)
    (G : Game (ι → F) (ι → F) A A)
    (hμ : ∀ x y, G.μ x y = CL.clDist (L false).eval (L true).eval x y)
    (hD : G.D = D) (Ξ : BipartiteModel 𝒞 𝒜 ℬ) (hΞ : ‖Ξ.ψ‖ = 1)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) 𝒜))
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) ℬ))
    (IA : IntroPrefixInvariant (L false) ℓ
      ((MA (QuestionType.introspect false, 0)).map TypedEstimates.introspectPair))
    (IB : IntroPrefixInvariant (L true) ℓ
      ((MB (QuestionType.introspect true, 0)).map TypedEstimates.introspectPair))
    {ε : ℝ} (hfail :
      1 - (Ξ.reg (ι → F)).povmValue (TypedEstimates.parsedGame E X Z P L projectPauli D DP)
        MA MB ≤ ε) :
    ∃ S : Ξ.ProjStrat G, 1 - (TypeGraph.edges E X Z ℓ).card * ε ≤ S.value := by
  let a₀ : A := Classical.choice inferInstance
  let QA := terminalAuxPOVM (hL false) IA
  let QB := terminalAuxPOVM (hL true) IB
  let RA := fun y => completeOptionPOVM a₀ (QA y)
  let RB := fun y => completeOptionPOVM a₀ (QB y)
  have hRA (y : ι → F) : IsPVMIn (RA y).op :=
    completeOptionPOVM_isPVM a₀ (QA y) (terminalAuxPOVM_isPVM (hL false) IA y)
  have hRB (y : ι → F) : IsPVMIn (RB y).op :=
    completeOptionPOVM_isPVM a₀ (QB y) (terminalAuxPOVM_isPVM (hL true) IB y)
  let S : Ξ.ProjStrat G :=
    { PA := RA, PB := RB, projA := hRA, projB := hRB, ψ_unit := hΞ }
  refine ⟨S, ?_⟩
  have hstate : ‖(Ξ.reg (ι → F)).ψ‖ = 1 := by rw [BipartiteModel.norm_reg_ψ, hΞ]
  have hf := cross_failure_le E X Z P L projectPauli D DP
    (Ξ.reg (ι → F)) hstate MA MB hfail
  have hc := condWin_cross_readout E X Z P L projectPauli D DP Ξ
    (fun y a => (QA y).op (some a)) (fun y a => (QB y).op (some a)) MA MB
    (fun y a => IA.terminal_parsed_pair (hL false) y a)
    (fun y a => IB.terminal_parsed_pair (hL true) y a)
  rw [BipartiteModel.condFail, hc] at hf
  have hv := readoutAcceptance_le_completedValue G (L false).eval (L true).eval
    (fun x y => (hμ x y).trans (sampled_dist_eq_clDist _ _ x y).symm)
    Ξ QA QB a₀ a₀
  rw [hD] at hv
  change 1 - (TypeGraph.edges E X Z ℓ).card * ε ≤ Ξ.povmValue G RA RB
  exact (by linarith : 1 - (TypeGraph.edges E X Z ℓ).card * ε ≤
    readoutAcceptance (L false).eval (L true).eval Ξ
      (fun y a => (QA y).op (some a))
      (fun y a => (QB y).op (some a)) D).trans hv

end TypedExtraction
end MIPRE.Introspection
end

end

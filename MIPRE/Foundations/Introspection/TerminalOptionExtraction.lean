/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AdaptiveTerminalInvariant
import MIPRE.Foundations.Introspection.TypedExtraction

/-! # Extracting ordinary answers from terminal option-valued measurements

The adaptive invariant retains malformed answers as `none`. Mapping this
outcome to a fixed valid answer preserves projectivity and cannot decrease
the accepted mass of the original predicate. Applied to both concrete
terminal invariants, this constructs an original-game strategy directly
from the actual typed game, with no zero-malformed-mass assumption.
-/

noncomputable section
namespace MIPRE.Introspection
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false

section Completion
variable {A B H K : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K]

/-- Replace a malformed auxiliary outcome by a fixed ordinary answer. -/
def completeOptionPOVM (a₀ : A) (Q : POVM (Option A) H) : POVM A H :=
  Q.map (fun a => a.getD a₀)

theorem completeOptionPOVM_isPVM (a₀ : A) (Q : POVM (Option A) H)
    (hQ : IsPVM (fun a => (Q.mats a).val)) :
    IsPVM (fun a => ((completeOptionPOVM a₀ Q).mats a).val) :=
  isPVM_povm_map Q hQ (fun a => a.getD a₀)

/-- Accepted valid outcomes remain accepted after completion; all newly
accepted malformed outcomes contribute nonnegative Born probabilities. -/
theorem option_valid_acceptance_le_complete (ψ : H × K → ℂ)
    (Q : POVM (Option A) H) (R : POVM (Option B) K)
    (a₀ : A) (b₀ : B) (D : A → B → Bool) :
    (∑ a, ∑ b, (if D a b then (1 : ℝ) else 0) *
      bornProb ψ (Q.mats (some a)).val (R.mats (some b)).val) ≤
      ∑ a, ∑ b, (if D a b then (1 : ℝ) else 0) *
        bornProb ψ ((completeOptionPOVM a₀ Q).mats a).val
          ((completeOptionPOVM b₀ R).mats b).val := by
  have hn (a : Option A) (b : Option B) :
      0 ≤ (if D (a.getD a₀) (b.getD b₀) then (1 : ℝ) else 0) *
        bornProb ψ (Q.mats a).val (R.mats b).val :=
    mul_nonneg (by split_ifs <;> norm_num)
      (bornProb_nonneg ψ (Q.posSemidef a) (R.posSemidef b))
  have hrow (a : Option A) :
      (∑ b : B, (if D (a.getD a₀) b then (1 : ℝ) else 0) *
        bornProb ψ (Q.mats a).val (R.mats (some b)).val) ≤
      ∑ b : Option B, (if D (a.getD a₀) (b.getD b₀) then (1 : ℝ) else 0) *
        bornProb ψ (Q.mats a).val (R.mats b).val := by
    rw [Fintype.sum_option]
    exact le_add_of_nonneg_left (hn a none)
  unfold completeOptionPOVM
  rw [sum_weight_bornProb_map]
  calc
    _ ≤ ∑ a : A, ∑ b : Option B,
        (if D a (b.getD b₀) then (1 : ℝ) else 0) *
          bornProb ψ (Q.mats (some a)).val (R.mats b).val :=
      Finset.sum_le_sum (fun a _ => hrow (some a))
    _ ≤ ∑ a : Option A, ∑ b : Option B,
        (if D (a.getD a₀) (b.getD b₀) then (1 : ℝ) else 0) *
          bornProb ψ (Q.mats a).val (R.mats b).val := by
      rw [Fintype.sum_option]
      exact le_add_of_nonneg_left (Finset.sum_nonneg (fun b _ => hn none b))

end Completion

section Readout
variable {I X Y A B H K : Type*}
  [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K]

/-- The actual question law converts the valid part of the readout test
into a lower bound on the completed ordinary-answer strategy. -/
theorem readoutAcceptance_le_completedValue (G : Game X Y A B)
    (f : I → X) (g : I → Y)
    (hμ : ∀ x y, G.μ x y = SampledGame.dist f g x y)
    (ξ : H × K → ℂ) (Q : X → POVM (Option A) H) (R : Y → POVM (Option B) K)
    (a₀ : A) (b₀ : B) :
    readoutAcceptance f g ξ (fun x a => ((Q x).mats (some a)).val)
      (fun y b => ((R y).mats (some b)).val) G.D ≤
        povmValue G ξ (fun x => completeOptionPOVM a₀ (Q x))
          (fun y => completeOptionPOVM b₀ (R y)) := by
  have he : readoutAcceptance f g ξ (fun x a => ((Q x).mats (some a)).val)
      (fun y b => ((R y).mats (some b)).val) G.D =
      ∑ x, ∑ y, G.μ x y * ∑ a, ∑ b, (if G.D x y a b then (1 : ℝ) else 0) *
        bornProb ξ ((Q x).mats (some a)).val ((R y).mats (some b)).val := by
    unfold readoutAcceptance
    simp_rw [bornProb_conditionalReadout f g ξ _ _
      (fun x a => (Q x).posSemidef (some a))
      (fun y b => (R y).posSemidef (some b))]
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
  unfold povmValue condWin
  exact Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ =>
    mul_le_mul_of_nonneg_left
      (option_valid_acceptance_le_complete ξ (Q x) (R y) a₀ b₀ (G.D x y))
      (G.μ_nonneg x y)))

end Readout

section Terminal
variable {F ι A H PauliAnswer : Type*}
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]
  [Fintype H] [DecidableEq H] [Fintype PauliAnswer] {ℓ : ℕ}

/-- A valid full-option outcome has a unique parsed-answer preimage. -/
theorem introspectPair_map_some (N : POVM (ParsedAnswer (ι → F) A PauliAnswer) H)
    (y : ι → F) (a : A) :
    ((N.map TypedEstimates.introspectPair).mats (some (y, a))).val =
      (N.mats (.pair y a)).val := by
  rw [POVM.map_mats]
  refine Finset.sum_eq_single (f := fun b => (N.mats b).val)
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

/-- The valid parsed effects of an actual terminal invariant have the
precise conditional readout form, regardless of malformed effects. -/
theorem IntroPrefixInvariant.terminal_parsed_pair
    {P : CL.CLFun F ι ℓ}
    {N : POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H)}
    (I : IntroPrefixInvariant P ℓ (N.map TypedEstimates.introspectPair))
    (hP : P.ExactlyOn univ)
    (y : ι → F) (a : A) :
    (N.mats (.pair y a)).val = conditionalReadout P.eval
      (fun y a => ((terminalAuxPOVM hP I y).mats (some a)).val) (y, a) := by
  rw [← introspectPair_map_some]
  exact I.terminal_some hP y a

end Terminal

namespace TypedExtraction
variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Fintype PauliType] [DecidableEq PauliType]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype A] [DecidableEq A] [Nonempty A] [Fintype PauliAnswer]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}

/-- Both concrete terminal invariants construct an ordinary-answer original
strategy. Completing malformed outcomes costs no additional failure. -/
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
    (hD : G.D = D) (ξ : H × K → ℂ) (hξ : star ξ ⬝ᵥ ξ = 1)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H))
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × K))
    (IA : IntroPrefixInvariant (L false) ℓ
      ((MA (QuestionType.introspect false, 0)).map TypedEstimates.introspectPair))
    (IB : IntroPrefixInvariant (L true) ℓ
      ((MB (QuestionType.introspect true, 0)).map TypedEstimates.introspectPair))
    {ε : ℝ} (hfail :
      1 - povmValue (TypedEstimates.parsedGame E X Z P L projectPauli D DP)
        (registerState (ι → F) ξ) MA MB ≤ ε) :
    ∃ S : TensorProductStrategy G,
      S.dA = Fintype.card H ∧ S.dB = Fintype.card K ∧
        1 - (TypeGraph.edges E X Z ℓ).card * ε ≤ S.value := by
  let a₀ : A := Classical.choice inferInstance
  let QA := terminalAuxPOVM (hL false) IA
  let QB := terminalAuxPOVM (hL true) IB
  let RA := fun y => completeOptionPOVM a₀ (QA y)
  let RB := fun y => completeOptionPOVM a₀ (QB y)
  have hRA (y : ι → F) : IsPVM (fun a => ((RA y).mats a).val) :=
    completeOptionPOVM_isPVM a₀ (QA y) (terminalAuxPOVM_isPVM (hL false) IA y)
  have hRB (y : ι → F) : IsPVM (fun a => ((RB y).mats a).val) :=
    completeOptionPOVM_isPVM a₀ (QB y) (terminalAuxPOVM_isPVM (hL true) IB y)
  let S := TensorProductStrategy.ofPVM G ξ hξ RA RB hRA hRB
  refine ⟨S, rfl, rfl, ?_⟩
  have hstate : star (registerState (ι → F) ξ) ⬝ᵥ registerState (ι → F) ξ = 1 := by
    rw [dotProduct_star_self, registerState_norm ξ (norm_evec_eq_one_of_unit hξ)]
    norm_num
  have hf := cross_failure_le E X Z P L projectPauli D DP
    (registerState (ι → F) ξ) hstate MA MB hfail
  have hc := condWin_cross_readout E X Z P L projectPauli D DP ξ
    (fun y a => ((QA y).mats (some a)).val)
    (fun y a => ((QB y).mats (some a)).val) MA MB
    (fun y a => IA.terminal_parsed_pair (hL false) y a)
    (fun y a => IB.terminal_parsed_pair (hL true) y a)
  rw [condFail, hc] at hf
  have hv := readoutAcceptance_le_completedValue G (L false).eval (L true).eval
    (fun x y => (hμ x y).trans (sampled_dist_eq_clDist _ _ x y).symm)
    ξ QA QB a₀ a₀
  rw [hD] at hv
  change 1 - (TypeGraph.edges E X Z ℓ).card * ε ≤
    (TensorProductStrategy.ofPVM G ξ hξ RA RB hRA hRB).value
  rw [TensorProductStrategy.value_ofPVM]
  exact (by linarith : 1 - (TypeGraph.edges E X Z ℓ).card * ε ≤
    readoutAcceptance (L false).eval (L true).eval ξ
      (fun y a => ((QA y).mats (some a)).val)
      (fun y a => ((QB y).mats (some a)).val) D).trans hv

end TypedExtraction
end MIPRE.Introspection
end

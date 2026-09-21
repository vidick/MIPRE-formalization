/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.HidingRigidityOrientation

/-! # Finite iteration of the actual hiding rigidity step

Write `e = |E| epsilon`. The actual same-type loop and adjacent hiding edge
give `A_k <= 4e + 2B_k` and `B_(k+1) <= 6B_k + C`, where
`C = (18 + 48 ell^2)e + 6delta`. The closed bound has no dependence on the
question or answer alphabet. The base and Introspect-prefix errors are the
explicit inputs, to be supplied by the Pauli-X and Pauli-Z tests.
-/

noncomputable section

namespace MIPRE.Introspection.TypedEstimates

open Finset Matrix Classical Honest
open scoped Kronecker

set_option linter.unusedSectionVars false

def hidingStepBudget (ℓ : ℕ) (e δ : ℝ) : ℝ := (18 + 48*(ℓ:ℝ)^2)*e + 6*δ

def hidingIterationBudget (ℓ : ℕ) (e δ β : ℝ) (k : ℕ) : ℝ :=
  (6:ℝ)^k*β + ((6:ℝ)^k-1)/5*hidingStepBudget ℓ e δ

@[simp] theorem hidingIterationBudget_zero (ℓ : ℕ) (e δ β : ℝ) :
    hidingIterationBudget ℓ e δ β 0 = β := by simp [hidingIterationBudget]

theorem hidingIterationBudget_succ (ℓ : ℕ) (e δ β : ℝ) (k : ℕ) :
    hidingIterationBudget ℓ e δ β (k+1) =
      6*hidingIterationBudget ℓ e δ β k + hidingStepBudget ℓ e δ := by
  unfold hidingIterationBudget
  rw [pow_succ]
  ring

def hidingUniformBudget (ℓ : ℕ) (e δ β : ℝ) : ℝ :=
  (6:ℝ)^ℓ * (β + hidingStepBudget ℓ e δ)

theorem hidingStepBudget_nonneg (ℓ : ℕ) {e δ : ℝ} (he : 0 ≤ e) (hδ : 0 ≤ δ) :
    0 ≤ hidingStepBudget ℓ e δ := by unfold hidingStepBudget; positivity

theorem hidingIterationBudget_le_uniform {ℓ k : ℕ} (hk : k ≤ ℓ)
    {e δ β : ℝ} (he : 0 ≤ e) (hδ : 0 ≤ δ) (hβ : 0 ≤ β) :
    hidingIterationBudget ℓ e δ β k ≤ hidingUniformBudget ℓ e δ β := by
  have hC := hidingStepBudget_nonneg ℓ he hδ
  have hp : (6:ℝ)^k ≤ (6:ℝ)^ℓ := by
    exact_mod_cast (Nat.pow_le_pow_right (by decide : 1 ≤ 6) hk)
  have hc : ((6:ℝ)^k-1)/5 ≤ (6:ℝ)^k := by
    have hz : 0 ≤ (6:ℝ)^k := by positivity
    linarith
  calc
    hidingIterationBudget ℓ e δ β k ≤ (6:ℝ)^k*β + (6:ℝ)^k*hidingStepBudget ℓ e δ :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hc hC)
    _ = (6:ℝ)^k*(β+hidingStepBudget ℓ e δ) := by ring
    _ ≤ hidingUniformBudget ℓ e δ β := mul_le_mul_of_nonneg_right hp (add_nonneg hβ hC)

variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype A]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}

def hidingIntroPrefixError (L : Bool → CL.CLFun F ι ℓ) (w : Bool) (ξ : H × K → ℂ)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × K)) (j : Fin ℓ) : ℝ :=
  ∑ y, snorm (registerState (ι → F) ξ) (bOp
    ((((MB (QuestionType.introspect w, 0)).map
      (reportedPrefix (L w) j.val .introspect)).mats y).val -
        (aOp (hidingPrefixOp (L w) j.val y) : Matrix ((ι → F) × K) _ ℂ)))^2

theorem hidingIntroPrefixError_nonneg (L : Bool → CL.CLFun F ι ℓ) (w : Bool) (ξ : H × K → ℂ)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × K)) (j : Fin ℓ) :
    0 ≤ hidingIntroPrefixError L w ξ MB j :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

variable
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
    {ε : ℝ} (hε : 0 ≤ ε)
    (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP)
      (registerState (ι → F) ξ) MA MB ≤ ε)
    (w : Bool) (hL : (L w).SupportedOn univ)
    (hMA : ∀ j : Fin ℓ, IsPVM (fun a => ((MA (QuestionType.hide w j, 0)).mats a).val))
    (hMB : ∀ j : Fin ℓ, IsPVM (fun b => ((MB (QuestionType.hide w j, 0)).mats b).val))

include hξ hε hfail hMA hMB

/-- A single recurrence step uses actual tests in their given orientation. -/
theorem hiding_register_recurrence (k j : Fin ℓ) (hk : k.val+1=j.val) {δ : ℝ}
    (hintro : hidingIntroPrefixError L w ξ MB j ≤ δ) :
    hidingBobError L w hL ξ MB j ≤ 6*hidingBobError L w hL ξ MB k +
      hidingStepBudget ℓ ((TypeGraph.edges E X Z ℓ).card*ε) δ := by
  have hnext := hiding_next_register_rigidity E X Z P L projectPauli D DP ξ hξ
    MA MB hfail w k j hk hL (hMA k) (hMB j)
    (show _ ≤ hidingAliceError L w hL ξ MA k from le_rfl) hintro
  have hloop := hiding_register_orientation E X Z P L projectPauli D DP ξ hξ
    MA MB hfail w hL k
  have hn : ℓ-j.val+1 ≤ ℓ := by omega
  have hn' : ((ℓ-j.val+1:ℕ):ℝ) ≤ (ℓ:ℝ) := by exact_mod_cast hn
  have hsq : (((ℓ-j.val+1:ℕ):ℝ))^2 ≤ (ℓ:ℝ)^2 := by nlinarith [sq_nonneg (((ℓ-j.val+1:ℕ):ℝ)-(ℓ:ℝ))]
  have he : 0 ≤ ((TypeGraph.edges E X Z ℓ).card:ℝ)*ε := mul_nonneg (Nat.cast_nonneg _) hε
  have hb := mul_le_mul_of_nonneg_right
    (show (6:ℝ)+48*((ℓ-j.val+1:ℕ):ℝ)^2 ≤ 6+48*(ℓ:ℝ)^2 by linarith) he
  change hidingBobError L w hL ξ MB j ≤ _ at hnext
  dsimp only [hidingStepBudget]
  nlinarith

/-- Finite induction over every real hiding level, starting with Bob's
actual level-zero estimate and the actual Introspect-prefix estimates. -/
theorem hiding_register_iteration (hℓ : 0 < ℓ) {δ β : ℝ}
    (hbase : hidingBobError L w hL ξ MB ⟨0,hℓ⟩ ≤ β)
    (hintro : ∀ j : Fin ℓ, hidingIntroPrefixError L w ξ MB j ≤ δ) (j : Fin ℓ) :
    hidingBobError L w hL ξ MB j ≤
      hidingIterationBudget ℓ ((TypeGraph.edges E X Z ℓ).card*ε) δ β j.val ∧
    hidingAliceError L w hL ξ MA j ≤ 4*(TypeGraph.edges E X Z ℓ).card*ε +
      2*hidingIterationBudget ℓ ((TypeGraph.edges E X Z ℓ).card*ε) δ β j.val := by
  have hb : ∀ n (hn : n < ℓ), hidingBobError L w hL ξ MB ⟨n,hn⟩ ≤
      hidingIterationBudget ℓ ((TypeGraph.edges E X Z ℓ).card*ε) δ β n := by
    intro n
    induction n with
    | zero => intro hn; simpa only [hidingIterationBudget_zero] using hbase
    | succ n ih =>
      intro hn
      have hprev := ih (by omega)
      have hstep := hiding_register_recurrence E X Z P L projectPauli D DP ξ hξ
        MA MB hε hfail w hL hMA hMB ⟨n,by omega⟩ ⟨n+1,hn⟩ rfl (hintro ⟨n+1,hn⟩)
      rw [hidingIterationBudget_succ]
      linarith
  have hj := hb j.val j.isLt
  have ha := hiding_register_orientation E X Z P L projectPauli D DP ξ hξ MA MB hfail w hL j
  exact ⟨hj,by linarith⟩

/-- One explicit bound holds at every level, with no extra nonnegativity
premises on the supplied base and prefix budgets. -/
theorem hiding_register_iteration_uniform (hℓ : 0 < ℓ) {δ β : ℝ}
    (hbase : hidingBobError L w hL ξ MB ⟨0,hℓ⟩ ≤ β)
    (hintro : ∀ j : Fin ℓ, hidingIntroPrefixError L w ξ MB j ≤ δ) (j : Fin ℓ) :
    hidingBobError L w hL ξ MB j ≤ hidingUniformBudget ℓ ((TypeGraph.edges E X Z ℓ).card*ε) δ β ∧
    hidingAliceError L w hL ξ MA j ≤ 4*(TypeGraph.edges E X Z ℓ).card*ε +
      2*hidingUniformBudget ℓ ((TypeGraph.edges E X Z ℓ).card*ε) δ β := by
  have hj := hiding_register_iteration E X Z P L projectPauli D DP ξ hξ MA MB hε hfail
    w hL hMA hMB hℓ hbase hintro j
  have hβ := (hidingBobError_nonneg L w hL ξ MB ⟨0,hℓ⟩).trans hbase
  have hδ := (hidingIntroPrefixError_nonneg L w ξ MB ⟨0,hℓ⟩).trans (hintro ⟨0,hℓ⟩)
  have hu := hidingIterationBudget_le_uniform j.isLt.le
    (mul_nonneg (Nat.cast_nonneg (TypeGraph.edges E X Z ℓ).card) hε) hδ hβ
  exact ⟨hj.1.trans hu,by linarith [hj.2]⟩

end MIPRE.Introspection.TypedEstimates

end

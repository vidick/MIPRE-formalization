/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AdaptiveInductionStep
import MIPRE.Foundations.Introspection.AdaptiveIterationBudget

/-! # Finite iteration of the actual Alice Introspect replacement

The auxiliary carrier and state are explicit at every level. Starting with
the original projective family, each successor is constructed from the
current game's tests. The numerical inverse threshold discharges every
smallness premise. All other questions retain their iterated identity
extensions, and all fixed hiding errors are preserved exactly.
-/

noncomputable section
namespace MIPRE.Introspection
open Finset Matrix Classical
set_option linter.unusedSectionVars false

universe u

/-- The original auxiliary space with one fresh local register per step. -/
def introIterationAux (H Ω : Type u) : ℕ → Type u
  | 0 => H
  | n + 1 => introIterationAux H Ω n × Ω

instance introIterationAuxFintype (H Ω : Type u) [Fintype H] [Fintype Ω] :
    (n : ℕ) → Fintype (introIterationAux H Ω n)
  | 0 => inferInstanceAs (Fintype H)
  | n + 1 =>
      letI : Fintype (introIterationAux H Ω n) := introIterationAuxFintype H Ω n
      inferInstanceAs (Fintype (introIterationAux H Ω n × Ω))

instance introIterationAuxDecidableEq (H Ω : Type u) [DecidableEq H] [DecidableEq Ω] :
    (n : ℕ) → DecidableEq (introIterationAux H Ω n)
  | 0 => inferInstanceAs (DecidableEq H)
  | n + 1 =>
      letI : DecidableEq (introIterationAux H Ω n) := introIterationAuxDecidableEq H Ω n
      inferInstanceAs (DecidableEq (introIterationAux H Ω n × Ω))

variable {H Ω : Type u} {K : Type*}
  [Fintype H] [DecidableEq H] [Fintype Ω] [DecidableEq Ω]
  [Fintype K] [DecidableEq K]

/-- Each added register is in the same fixed basis state on Alice's side. -/
def introIterationState (ξ : H × K → ℂ) (a₀ : Ω) :
    (n : ℕ) → introIterationAux H Ω n × K → ℂ
  | 0 => ξ
  | n + 1 => extVecA (introIterationState ξ a₀ n) a₀

@[simp] theorem introIterationState_zero (ξ : H × K → ℂ) (a₀ : Ω) :
    introIterationState ξ a₀ 0 = ξ := rfl

theorem introIterationState_succ (ξ : H × K → ℂ) (a₀ : Ω) (n : ℕ) :
    introIterationState ξ a₀ (n + 1) = extVecA (introIterationState ξ a₀ n) a₀ := rfl

theorem introIterationState_unit (ξ : H × K → ℂ) (hξ : star ξ ⬝ᵥ ξ = 1)
    (a₀ : Ω) (n : ℕ) :
    star (introIterationState ξ a₀ n) ⬝ᵥ introIterationState ξ a₀ n = 1 := by
  induction n with
  | zero => exact hξ
  | succ n ih => exact extVecA_unit (introIterationState ξ a₀ n) ih a₀

variable {I B : Type*} [Fintype I] [DecidableEq I] [Fintype B] [DecidableEq B]

/-- The exact repeated identity extension of an untouched measurement. -/
def introIterationExtend (Ω : Type u) [Fintype Ω] [DecidableEq Ω]
    (M : POVM B (I × H)) : (n : ℕ) → POVM B (I × introIterationAux H Ω n)
  | 0 => M
  | n + 1 => registeredExtendPOVM (introIterationExtend Ω M n)

@[simp] theorem introIterationExtend_zero (M : POVM B (I × H)) :
    introIterationExtend Ω M 0 = M := rfl

theorem introIterationExtend_succ (M : POVM B (I × H)) (n : ℕ) :
    introIterationExtend Ω M (n + 1) =
      registeredExtendPOVM (introIterationExtend Ω M n) := rfl

namespace TypedEstimates

variable {PauliType PauliAnswer κ : Type*} {F ι A : Type u}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype A] {ℓ : ℕ}

/-- The primitive Bob-Z approximation is unchanged throughout the actual
Alice iteration, on the original EPR register and extended auxiliary state. -/
theorem introBobZError_introIterationState (projectPauli : PauliAnswer → ι → F)
    (Z : PauliType) (q : κ → ZMod 2) (ξ : H × K → ℂ)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × K)) (n : ℕ) :
    introBobZError projectPauli Z q
      (introIterationState ξ (none : Option ((ι → F) × A)) n) MB =
        introBobZError projectPauli Z q ξ MB := by
  induction n with
  | zero => rfl
  | succ n ih =>
      exact (introBobZError_extVecA projectPauli Z q
        (introIterationState ξ (none : Option ((ι → F) × A)) n) MB).trans ih

set_option backward.isDefEq.respectTransparency false in
/-- A concrete projective strategy family exists after every finite Alice
stage. The original primitive bounds and explicit positive threshold suffice;
no future structural invariant, future error bound, or stage-smallness
conclusion is assumed. The full option-valued invariant includes malformed
answers and the support of all valid answers. -/
theorem exists_intro_iteration
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
    (w : Bool) (hL : (L w).SupportedOn univ)
    {initial η δ : ℝ} (hi0 : 0 ≤ initial) (hη0 : 0 ≤ η) (hδ0 : 0 ≤ δ)
    (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP)
      (registerState (ι → F) ξ) MA MB ≤ initial)
    (hZ : introBobZError projectPauli Z q ξ MB ≤ η)
    (hhide : ∀ j : Fin ℓ, hidingAliceError L w hL ξ MA j ≤ δ)
    (hi : initial ≤ adaptiveSmallThreshold ℓ (TypeGraph.edges E X Z ℓ).card ℓ)
    (hη : η ≤ adaptiveSmallThreshold ℓ (TypeGraph.edges E X Z ℓ).card ℓ)
    (hδ : δ ≤ adaptiveSmallThreshold ℓ (TypeGraph.edges E X Z ℓ).card ℓ)
    (n : ℕ) (hn : n ≤ ℓ) :
    ∃ (MN : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
        POVM (ParsedAnswer (ι → F) A PauliAnswer)
          ((ι → F) × introIterationAux H (Option ((ι → F) × A)) n))
      (_ : IntroPrefixInvariant (L w) n
        ((MN (QuestionType.introspect w, 0)).map introspectPair)),
      (∀ t, IsPVM (fun a => ((MN t).mats a).val)) ∧
      1 - povmValue (parsedGame E X Z P L projectPauli D DP)
        (registerState (ι → F)
          (introIterationState ξ (none : Option ((ι → F) × A)) n)) MN MB ≤
            adaptiveFailureBudget ℓ (TypeGraph.edges E X Z ℓ).card η δ initial n ∧
      (∀ t, t ≠ (QuestionType.introspect w, 0) →
        MN t = introIterationExtend (Option ((ι → F) × A)) (MA t) n) ∧
      (∀ j : Fin ℓ, hidingAliceError L w hL
        (introIterationState ξ (none : Option ((ι → F) × A)) n) MN j =
          hidingAliceError L w hL ξ MA j) := by
  induction n with
  | zero =>
      refine ⟨MA, initialIntroPrefixInvariant (L w)
        ((MA (QuestionType.introspect w, 0)).map introspectPair)
        (isPVM_povm_map _ (hMA _) introspectPair), hMA, ?_, ?_, ?_⟩
      · exact hfail
      · intro t _
        rfl
      · intro j
        rfl
  | succ n ih =>
      have hn' : n ≤ ℓ := (Nat.le_succ n).trans hn
      obtain ⟨MN, IN, hMN, hfailN, hotherN, hhideN⟩ := ih hn'
      let j : Fin ℓ := ⟨n, by omega⟩
      have he : (0 : ℝ) ≤ (TypeGraph.edges E X Z ℓ).card := Nat.cast_nonneg _
      have hb : 0 ≤ adaptiveFailureBudget ℓ (TypeGraph.edges E X Z ℓ).card
          η δ initial n :=
        adaptiveFailureBudget_nonneg ℓ n _ η δ hi0
      have hdepth : adaptiveStageBudget (ℓ - j.val)
          ((TypeGraph.edges E X Z ℓ).card *
            adaptiveFailureBudget ℓ (TypeGraph.edges E X Z ℓ).card η δ initial n) η δ ≤
          adaptiveStageBudget ℓ
            ((TypeGraph.edges E X Z ℓ).card *
              adaptiveFailureBudget ℓ (TypeGraph.edges E X Z ℓ).card η δ initial n) η δ :=
        adaptiveStageBudget_mono_depth (Nat.sub_le ℓ j.val) (mul_nonneg he hb)
      have hsmall := hdepth.trans
        (adaptiveStageBudget_le_one_of_threshold ℓ ℓ he hi hη hδ n hn')
      have hZn : introBobZError projectPauli Z q
          (introIterationState ξ (none : Option ((ι → F) × A)) n) MB ≤ η := by
        rw [introBobZError_introIterationState]
        exact hZ
      have hhn : hidingAliceError L w hL
          (introIterationState ξ (none : Option ((ι → F) × A)) n) MN j ≤ δ := by
        rw [hhideN j]
        exact hhide j
      obtain ⟨MS, IS, hMS, hfailS, hotherS, hhideS⟩ := exists_intro_successor
        E X Z P L projectPauli D DP
        (introIterationState ξ (none : Option ((ι → F) × A)) n)
        (introIterationState_unit ξ hξ none n) MN MB hMN hMB q hq w hL j IN
        hb hη0 hδ0 hfailN hZn hhn hsmall
      refine ⟨MS, IS, hMS, ?_, ?_, ?_⟩
      · exact hfailS.trans (by
          rw [adaptiveFailureBudget_step]
          exact add_le_add_left (adaptiveStepLoss_mono hdepth) _)
      · intro t ht
        exact (hotherS t ht).trans (congrArg
          (fun N => registeredExtendPOVM (T := Option ((ι → F) × A)) N) (hotherN t ht))
      · intro i
        exact (hhideS i).trans (hhideN i)

end TypedEstimates
end MIPRE.Introspection
end

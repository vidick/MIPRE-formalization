/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.PauliAuxEstimates
import MIPRE.Foundations.Introspection.HidingBaseOperators

/-! # The actual Pauli-X/first-hiding test -/

noncomputable section

namespace MIPRE.Introspection.TypedEstimates

open Finset Matrix Classical

set_option linter.unusedSectionVars false

variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype A]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}

theorem hidingCoarse_zero_hide (P : CL.CLFun F ι ℓ) (y yp x : ι → F) :
    hidingCoarse (A := A) (PauliAnswer := PauliAnswer) P 0 (.hide y yp x) =
      some (0, CL.proj (P.factorOfPrefix 0 0) yp, CL.proj (P.factorOfPrefix 0 0)ᶜ x) := by
  have hr : CLChecks.prefixRegister P 1 y = P.factorOfPrefix 0 0 := by
    cases P <;> simp [CLChecks.prefixRegister]
  simp only [hidingCoarse, CL.CLFun.outputPrefix_zero, hr]

/-- This implication is over the complete parsed alphabet; acceptance excludes
every malformed constructor before the Pauli-X comparison is used. -/
theorem hiding_first_accepts
    (L : Bool → CL.CLFun F ι ℓ) (X Z : PauliType)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → PauliAnswer → PauliAnswer → Bool)
    (w : Bool) (k : Fin ℓ) (hk : k.val = 0)
    (a b : ParsedAnswer (ι → F) A PauliAnswer)
    (hab : TypedPredicate.check L X Z projectPauli D DP (.inl X)
      (.inr (.hide k, w)) a b = true) :
    Option.map (Honest.firstHideAnswer (L w)) (pauliProjection projectPauli a) =
      hidingCoarse (L w) 0 b := by
  have hf := TypedPredicate.check_formats L X Z projectPauli D DP hab
  cases a <;> cases b <;> simp only [TypedPredicate.fits, Bool.false_eq_true, and_false,
    false_and] at hf
  rename_i a y yp x
  have hc := TypedPredicate.check_hiding_pauli L X Z projectPauli D DP w k hk hab
  rw [pauliProjection, Option.map_some, hidingCoarse_zero_hide]
  exact congrArg some (Prod.ext rfl (Prod.ext hc.1.symm hc.2))

/-- Actual game failure controls the first hiding coarse family against the
tested coarse Pauli-X family, on either player's full local carrier. -/
theorem hiding_first_agreement_estimate
    (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
      PauliAnswer → PauliAnswer → Bool)
    (ψ : H × K → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) H)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) K)
    {ε : ℝ} (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP) ψ MA MB ≤ ε)
    (w : Bool) (k : Fin ℓ) (hk : k.val = 0)
    (qX : κ → ZMod 2) (hqX : ∀ z, (P X).eval z = qX) :
    (∑ z, xSqNorm ψ
      ((((MA (.inl X, qX)).map (fun a =>
        Option.map (Honest.firstHideAnswer (L w)) (pauliProjection projectPauli a))).mats z).val)
      ((((MB (QuestionType.hide w k, 0)).map (hidingCoarse (L w) 0)).mats z).val)) ≤
        2 * (TypeGraph.edges E X Z ℓ).card * ε := by
  have hℓ : 0 < ℓ := by simpa only [hk] using k.isLt
  have heq : k = ⟨0, hℓ⟩ := Fin.ext hk
  have hedge : TypeGraph.Adj E X Z (.inl X) (.inr (.hide k, w)) := by
    subst k
    exact TypeGraph.adj_pauliX_hide_first E X Z hℓ w
  exact pauli_aux_agreement_estimate E X Z P (questionCheck L X Z projectPauli D DP)
    ψ hψ MA MB hfail X qX hqX (.hide k) w hedge
    (fun a => Option.map (Honest.firstHideAnswer (L w)) (pauliProjection projectPauli a))
    (hidingCoarse (L w) 0)
    (hiding_first_accepts L X Z projectPauli D (fun p r => DP p r qX 0) w k hk)

end MIPRE.Introspection.TypedEstimates

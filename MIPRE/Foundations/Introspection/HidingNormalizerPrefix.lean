/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.HidingMaps
import MIPRE.Foundations.Introspection.TypedPrefixChainBob

/-! # The actual hiding normalizer is the propagated question prefix -/

noncomputable section

namespace MIPRE.Introspection.TypedEstimates

open Finset Matrix Classical

variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Field F] [Fintype F] [DecidableEq F] [Fintype ι] [DecidableEq ι]
  [Fintype PauliAnswer] [Fintype A] [Fintype K] [DecidableEq K] {ℓ : ℕ}

/-- The actual conditional marginal, including its malformed-answer outcome. -/
def hidingNormalizer (P : CL.CLFun F ι ℓ) (k : ℕ)
    (N : POVM (ParsedAnswer (ι → F) A PauliAnswer) K) (y : Option (ι → F)) :
    Matrix K K ℂ := ∑ z, ((N.map (hidingNextLater P k)).mats (y, z)).val

/-- Summing the tested later outcomes gives exactly its reported prefix PVM;
the dummy outcome is included on both sides of the identity. -/
theorem hidingNormalizer_eq_reportedPrefix (P : CL.CLFun F ι ℓ) (k : ℕ) (j : Fin ℓ)
    (N : POVM (ParsedAnswer (ι → F) A PauliAnswer) K) (y : Option (ι → F)) :
    hidingNormalizer P k N y =
      ((N.map (reportedPrefix P (k + 1) (.hide j))).mats y).val := by
  have hc : (hidingNextCondition P k : ParsedAnswer (ι → F) A PauliAnswer → _) =
      reportedPrefix P (k + 1) (.hide j) := by
    funext a
    cases a <;> rfl
  rw [← hc]
  have hg : (fun a : ParsedAnswer (ι → F) A PauliAnswer =>
      (hidingNextCondition P k a, (hidingNextLater P k a).2)) = hidingNextLater P k := by
    funext a
    cases a <;> rfl
  have hm := POVM.sum_mats_map_prod N (hidingNextCondition P k)
    (fun a => (hidingNextLater P k a).2) y
  simp only [hg] at hm
  convert hm using 1
  unfold hidingNormalizer
  apply Finset.sum_congr rfl
  intro z _
  simp only [POVM.map_mats, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : hidingNextLater P k a = (y, z)
  · simp only [if_pos h]
  · simp only [if_neg h]

variable [Fintype PauliType] [DecidableEq PauliType]
  [Fintype κ] [DecidableEq κ] [Fintype H] [DecidableEq H]

/-- The actual prefix chain discharges the later hiding normalizer estimate
from the single Introspect-prefix estimate. No assumption about later hiding
operators or a supplied conditional marginal is needed. -/
theorem hidingNormalizer_estimate
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
    {ε δ : ℝ} (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP) ψ MA MB ≤ ε)
    (w : Bool) (k j : Fin ℓ) (hk : k.val + 1 = j.val)
    (hL : (L w).SupportedOn univ) (Q : Option (ι → F) → Matrix K K ℂ)
    (hintro : ∑ y, snorm ψ (bOp
      ((((MB (QuestionType.introspect w, 0)).map
        (reportedPrefix (L w) (k.val + 1) .introspect)).mats y).val - Q y)) ^ 2 ≤ δ) :
    (∑ y, snorm ψ (bOp
      (hidingNormalizer (L w) k.val (MB (QuestionType.hide w j, 0)) y - Q y)) ^ 2) ≤
      2 * (((ℓ - j.val + 1 : ℕ) : ℝ) ^ 2 *
        (8 * (TypeGraph.edges E X Z ℓ).card * ε)) + 2 * δ := by
  have hchain := hiding_introspect_prefix_estimate_bob E X Z P L projectPauli D DP
    ψ hψ MA MB hfail w hL j (k.val + 1) (by omega)
  let R (y : Option (ι → F)) :=
    (((MB (QuestionType.introspect w, 0)).map
      (reportedPrefix (L w) (k.val + 1) .introspect)).mats y).val
  have ht := sum_snorm_sq_triangle' ψ
    (fun y => bOp (hidingNormalizer (L w) k.val (MB (QuestionType.hide w j, 0)) y))
    (fun y => bOp (R y)) (fun y => bOp (Q y))
  simp only [← bOp_sub] at ht
  have hstep : (∑ y, snorm ψ (bOp
      (hidingNormalizer (L w) k.val (MB (QuestionType.hide w j, 0)) y - R y)) ^ 2) ≤
      ((ℓ - j.val + 1 : ℕ) : ℝ) ^ 2 * (8 * (TypeGraph.edges E X Z ℓ).card * ε) := by
    simpa only [hidingNormalizer_eq_reportedPrefix (L w) k.val j, R] using hchain
  exact ht.trans (add_le_add (mul_le_mul_of_nonneg_left hstep (by norm_num))
    (mul_le_mul_of_nonneg_left hintro (by norm_num)))

end MIPRE.Introspection.TypedEstimates

end

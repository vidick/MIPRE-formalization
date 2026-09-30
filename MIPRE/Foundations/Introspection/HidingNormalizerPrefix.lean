/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.HidingMaps
public import MIPRE.Foundations.Introspection.TypedPrefixChainBob

@[expose] public section

/-! # The actual hiding normalizer is the propagated question prefix

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the normalizer is an element of
the second player's algebra, and the estimate is in the second player's state norm of the model.
-/

noncomputable section

namespace MIPRE.Introspection.TypedEstimates

open Finset Classical

variable {PauliType PauliAnswer F ι κ A : Type*}
  [Field F] [Fintype F] [DecidableEq F] [Fintype ι] [DecidableEq ι]
  [Fintype PauliAnswer] [Fintype A] {ℓ : ℕ}

section Normalizer

variable {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]

/-- The actual conditional marginal, including its malformed-answer outcome. -/
def hidingNormalizer (P : CL.CLFun F ι ℓ) (k : ℕ)
    (N : POVMIn (ParsedAnswer (ι → F) A PauliAnswer) R) (y : Option (ι → F)) : R :=
  ∑ z, (N.map (hidingNextLater P k)).op (y, z)

/-- Summing the tested later outcomes gives exactly its reported prefix PVM;
the dummy outcome is included on both sides of the identity. -/
theorem hidingNormalizer_eq_reportedPrefix (P : CL.CLFun F ι ℓ) (k : ℕ) (j : Fin ℓ)
    (N : POVMIn (ParsedAnswer (ι → F) A PauliAnswer) R) (y : Option (ι → F)) :
    hidingNormalizer P k N y = (N.map (reportedPrefix P (k + 1) (.hide j))).op y := by
  have hc : (hidingNextCondition P k : ParsedAnswer (ι → F) A PauliAnswer → _) =
      reportedPrefix P (k + 1) (.hide j) := by
    funext a
    cases a <;> rfl
  rw [← hc]
  have hg : (fun a : ParsedAnswer (ι → F) A PauliAnswer =>
      (hidingNextCondition P k a, (hidingNextLater P k a).2)) = hidingNextLater P k := by
    funext a
    cases a <;> rfl
  have hm := POVMIn.sum_op_map_prod N (hidingNextCondition P k)
    (fun a => (hidingNextLater P k a).2) y
  simp only [hg] at hm
  unfold hidingNormalizer
  convert hm

end Normalizer

variable [Fintype PauliType] [DecidableEq PauliType] [Fintype κ] [DecidableEq κ]
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ]

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
    (Ψ : BipartiteModel 𝒞 𝒜 ℬ) (hΨ : ‖Ψ.ψ‖ = 1)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) 𝒜)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) ℬ)
    {ε δ : ℝ} (hfail : 1 - Ψ.povmValue (parsedGame E X Z P L projectPauli D DP) MA MB ≤ ε)
    (w : Bool) (k j : Fin ℓ) (hk : k.val + 1 = j.val)
    (hL : (L w).SupportedOn univ) (Q : Option (ι → F) → ℬ)
    (hintro : ∑ y, Ψ.snorm (Ψ.πB
      (((MB (QuestionType.introspect w, 0)).map
        (reportedPrefix (L w) (k.val + 1) .introspect)).op y - Q y)) ^ 2 ≤ δ) :
    (∑ y, Ψ.snorm (Ψ.πB
      (hidingNormalizer (L w) k.val (MB (QuestionType.hide w j, 0)) y - Q y)) ^ 2) ≤
      2 * (((ℓ - j.val + 1 : ℕ) : ℝ) ^ 2 *
        (8 * (TypeGraph.edges E X Z ℓ).card * ε)) + 2 * δ := by
  have hchain := hiding_introspect_prefix_estimate_bob E X Z P L projectPauli D DP
    Ψ hΨ MA MB hfail w hL j (k.val + 1) (by omega)
  let R (y : Option (ι → F)) :=
    ((MB (QuestionType.introspect w, 0)).map
      (reportedPrefix (L w) (k.val + 1) .introspect)).op y
  have ht := Ψ.sum_snorm_sq_triangle univ
    (fun y => Ψ.πB (hidingNormalizer (L w) k.val (MB (QuestionType.hide w j, 0)) y))
    (fun y => Ψ.πB (R y)) (fun y => Ψ.πB (Q y))
  simp only [← map_sub] at ht
  have hstep : (∑ y, Ψ.snorm (Ψ.πB
      (hidingNormalizer (L w) k.val (MB (QuestionType.hide w j, 0)) y - R y)) ^ 2) ≤
      ((ℓ - j.val + 1 : ℕ) : ℝ) ^ 2 * (8 * (TypeGraph.edges E X Z ℓ).card * ε) := by
    simpa only [hidingNormalizer_eq_reportedPrefix (L w) k.val j, R] using hchain
  exact ht.trans (add_le_add (mul_le_mul_of_nonneg_left hstep (by norm_num))
    (mul_le_mul_of_nonneg_left hintro (by norm_num)))

end MIPRE.Introspection.TypedEstimates

end

end

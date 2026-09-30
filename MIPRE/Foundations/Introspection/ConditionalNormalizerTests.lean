/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.ConditionalNormalizer
public import MIPRE.Foundations.Introspection.HidingRigidity

@[expose] public section

/-! # Conditional ideal replacement from an actual tested relation

The conditional approximation is derived from the acceptance probability and
concrete answer maps. It is not an additional rigidity premise.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`).
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical

set_option linter.unusedSectionVars false

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] (Ψ : BipartiteModel 𝒞 𝒜 ℬ)
variable {I O Y Z : Type*} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
  [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]

/-- Replace the actual marginal in a tested conditional relation by its ideal
commuting prefix, with constant six on the test's conditional failure. -/
theorem conditional_coarse_ideal_of_test (hΨ : ‖Ψ.ψ‖ = 1)
    (M : POVMIn I 𝒜) (N : POVMIn O ℬ)
    (P : I → ℬ) (Q : Y → ℬ)
    (f : Y → I → Z) (g : O → Y × Z) (test : I → O → Bool)
    (hM : IsPVMIn M.op) (hN : IsPVMIn N.op)
    (hP : IsPVMIn P) (hQ : IsPVMIn Q) (hc : ∀ y i, Commute (Q y) (P i))
    {δ η ε : ℝ}
    (hfine : ∑ i, Ψ.xSqNorm (M.op i) (P i) ≤ ε)
    (hnorm : ∑ y, Ψ.snorm (Ψ.πB ((∑ z, (N.map g).op (y, z)) - Q y)) ^ 2 ≤ η)
    (hwin : 1 - δ ≤ ∑ i, ∑ o,
      (if test i o = true then (1 : ℝ) else 0) * Ψ.bornProb (M.op i) (N.op o))
    (hcheck : ∀ i o, test i o = true → f (g o).1 i = (g o).2) :
    (∑ p : Y × Z, Ψ.snorm
      (Ψ.πB ((N.map g).op p) - Ψ.πB (conditionalIdeal P Q f p)) ^ 2) ≤
      6 * δ + 3 * η + 3 * ε := by
  have hconditional := conditional_coarse_consistency Ψ hΨ M N hN f g test hwin hcheck
  have hmapped (y : Y) (z : Z) : (M.map (f y)).op z = fibSumIn M.op (f y) z :=
    POVMIn.map_op (f y) M z
  have h := conditional_coarse_ideal_replacement Ψ hΨ M.op P Q (fun p => (N.map g).op p) f
    hM hP hQ hc hfine hnorm
    (by simpa only [conditionalCoarseDistance, hmapped] using hconditional)
  linarith

end MIPRE.Introspection

end

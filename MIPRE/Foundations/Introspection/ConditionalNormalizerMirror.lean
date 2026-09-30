/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.ConditionalNormalizerTests

@[expose] public section

/-! # Exact mirror transfer for the conditional ideal family

Primitive fine and prefix mirrors imply the mirror identity for the keyed
conditional ideal family. Consequently the one-party replacement estimate is
also the cross-party error needed by the hiding induction.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): an exact mirror of the first
player's operator `P` by the second player's `R` is the identity of vectors
`π (πA P) ψ = π (πB R) ψ`, the form in which the register model supplies it
(`BipartiteModel.reg_mirror`, `mirror_expand`); in the tensor-product model it is
`aOp P *ᵥ ψ = bOp R *ᵥ ψ`. Coarse-graining is `fibSumIn`, and `A ⊗ B` is `πA A * πB B`.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Classical

set_option linter.unusedSectionVars false

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] (Ψ : BipartiteModel 𝒞 𝒜 ℬ)
variable {I Y Z : Type*} [Fintype I] [DecidableEq I] [Fintype Y] [DecidableEq Y]
  [Fintype Z] [DecidableEq Z]

/-- Exact mirrors are preserved by coarse-graining both families along the same map. -/
theorem fibSum_mirror (P : I → 𝒜) (R : I → ℬ)
    (h : ∀ i, Ψ.π (Ψ.πA (P i)) Ψ.ψ = Ψ.π (Ψ.πB (R i)) Ψ.ψ) (f : I → Z) (z : Z) :
    Ψ.π (Ψ.πA (fibSumIn P f z)) Ψ.ψ = Ψ.π (Ψ.πB (fibSumIn R f z)) Ψ.ψ := by
  simp only [fibSumIn, map_sum, _root_.sum_apply]
  exact Finset.sum_congr rfl fun i _ => h i

/-- Mirrors reverse multiplication order; commutation of the ideal prefix and
fine projectors restores the order defining the conditional ideal. -/
theorem conditionalIdeal_mirror (P : I → 𝒜) (R : I → ℬ) (Q : Y → 𝒜) (S : Y → ℬ)
    (f : Y → I → Z)
    (hP : ∀ i, Ψ.π (Ψ.πA (P i)) Ψ.ψ = Ψ.π (Ψ.πB (R i)) Ψ.ψ)
    (hQ : ∀ y, Ψ.π (Ψ.πA (Q y)) Ψ.ψ = Ψ.π (Ψ.πB (S y)) Ψ.ψ)
    (hc : ∀ y i, Commute (S y) (R i)) (p : Y × Z) :
    Ψ.π (Ψ.πA (conditionalIdeal P Q f p)) Ψ.ψ =
      Ψ.π (Ψ.πB (conditionalIdeal R S f p)) Ψ.ψ := by
  have hAB (a : 𝒜) (b : ℬ) (v : Ψ.H) :
      Ψ.π (Ψ.πA a) (Ψ.π (Ψ.πB b) v) = Ψ.π (Ψ.πB b) (Ψ.π (Ψ.πA a) v) := by
    rw [← mul_apply_eq_comp, ← map_mul, (Ψ.commute a b).eq, map_mul,
      mul_apply_eq_comp]
  unfold conditionalIdeal
  rw [(commute_fibSum_right R S hc (f p.1) p.1 p.2).eq]
  simp only [map_mul, mul_apply_eq_comp]
  rw [fibSum_mirror Ψ P R hP, hAB, hQ]

/-- An exact mirror changes a cross-party distance into a same-party distance. -/
theorem xSqNorm_eq_bOp_distance_of_mirror (P : 𝒜) (Q B : ℬ)
    (h : Ψ.π (Ψ.πA P) Ψ.ψ = Ψ.π (Ψ.πB Q) Ψ.ψ) :
    Ψ.xSqNorm P B = Ψ.snorm (Ψ.πB B - Ψ.πB Q) ^ 2 := by
  rw [BipartiteModel.xSqNorm, BipartiteModel.xNorm, StateModel.snorm, StateModel.snorm, Op.snorm,
    Op.snorm, map_sub, map_sub, _root_.sub_apply, _root_.sub_apply, h,
    norm_sub_rev]

/-- The conditional replacement gives the cross-party ideal estimate whenever
the primitive ideal families have their exact EPR mirrors. -/
theorem conditional_coarse_ideal_replacement_mirror [PartialOrder 𝒜] [StarOrderedRing 𝒜]
    [PartialOrder ℬ] [StarOrderedRing ℬ] (hΨ : ‖Ψ.ψ‖ = 1)
    (M P : I → 𝒜) (R : I → ℬ) (Q : Y → 𝒜) (S : Y → ℬ)
    (B : Y × Z → ℬ) (f : Y → I → Z)
    (hM : IsPVMIn M) (hR : IsPVMIn R) (hS : IsPVMIn S)
    (hc : ∀ y i, Commute (S y) (R i))
    (hP : ∀ i, Ψ.π (Ψ.πA (P i)) Ψ.ψ = Ψ.π (Ψ.πB (R i)) Ψ.ψ)
    (hQ : ∀ y, Ψ.π (Ψ.πA (Q y)) Ψ.ψ = Ψ.π (Ψ.πB (S y)) Ψ.ψ)
    {α η ε : ℝ}
    (hfine : ∑ i, Ψ.xSqNorm (M i) (R i) ≤ ε)
    (hnorm : ∑ y, Ψ.xSqNorm (Q y) (∑ z, B (y, z)) ≤ η)
    (hconditional : ∑ p : Y × Z, Ψ.snorm
      (Ψ.πB (B p) - Ψ.πA (fibSumIn M (f p.1) p.2) * Ψ.πB (∑ z, B (p.1, z))) ^ 2 ≤ α) :
    (∑ p : Y × Z, Ψ.xSqNorm (conditionalIdeal P Q f p) (B p)) ≤
      3 * α + 3 * η + 3 * ε := by
  have hnorm' : ∑ y, Ψ.snorm (Ψ.πB ((∑ z, B (y, z)) - S y)) ^ 2 ≤ η := by
    simpa only [xSqNorm_eq_bOp_distance_of_mirror Ψ _ _ _ (hQ _), map_sub] using hnorm
  have h := conditional_coarse_ideal_replacement Ψ hΨ M R S B f hM hR hS hc
    hfine hnorm' hconditional
  simpa only [xSqNorm_eq_bOp_distance_of_mirror Ψ _ _ _
    (conditionalIdeal_mirror Ψ P R Q S f hP hQ hc _)] using h

end MIPRE.Introspection

end

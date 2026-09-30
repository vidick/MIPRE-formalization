/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.ConditionalNormalizerMirror
public import MIPRE.Foundations.Introspection.ConditionalNormalizerIdeal

@[expose] public section

/-! # Retaining the next hiding label without an alphabet-size loss

We first transfer the paired same-party estimate to the exact ideal mirror.
Coarse-graining is then applied to cross-party PVM consistency, where positivity
gives a dimension-independent contraction.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): an exact mirror is the vector
identity `π (πA P) ψ = π (πB R) ψ` of `ConditionalNormalizerMirror.lean`, coarse-graining is
`fibSumIn`, and the measurements are families and POVMs in the players' algebras. In the honest
step the players' algebras are the matrices over `ι → F` with entries in two algebras `𝒜` and `ℬ`
--- the register model `Ξ.reg (ι → F)` is one such model, and supplies the two mirrors by
`BipartiteModel.reg_mirror` --- and an honest register operator `P`, a complex matrix, acts as
`smulKron 1 P` for either player (`conditionalIdeal_smulKron_one`).
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical

set_option linter.unusedSectionVars false

section Lift

variable {R α : Type*} [Ring R] [Algebra ℂ R] [Fintype α] [DecidableEq α]
variable {I Y Z : Type*} [Fintype I] [DecidableEq I] [Fintype Y] [DecidableEq Y]
  [Fintype Z] [DecidableEq Z]

/-- Coarse-graining commutes with the embedding `P ↦ 1 ⊗ P` of register operators. -/
theorem fibSumIn_smulKron_one (P : I → Matrix α α ℂ) (f : I → Z) (z : Z) :
    fibSumIn (fun i => smulKron (1 : R) (P i)) f z = smulKron 1 (fibSumIn P f z) :=
  (smulKron_sum_right _ _ _).symm

/-- Commuting register operators embed as commuting operators. -/
theorem commute_smulKron_one {P Q : Matrix α α ℂ} (h : Commute P Q) :
    Commute (smulKron (1 : R) P) (smulKron 1 Q) := by
  show _ * _ = _ * _
  rw [smulKron_mul, smulKron_mul, h.eq]

/-- The conditional ideal of embedded register families is the embedded conditional ideal. -/
theorem conditionalIdeal_smulKron_one (P : I → Matrix α α ℂ) (Q : Y → Matrix α α ℂ)
    (f : Y → I → Z) (p : Y × Z) :
    conditionalIdeal (fun i => smulKron (1 : R) (P i)) (fun y => smulKron 1 (Q y)) f p =
      smulKron 1 (conditionalIdeal P Q f p) := by
  rw [conditionalIdeal, fibSumIn_smulKron_one, smulKron_mul, one_mul, conditionalIdeal]

end Lift

section Retain

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] (Ψ : BipartiteModel 𝒞 𝒜 ℬ)
variable {I W : Type*} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

/-- Exact mirror transfer followed by cross-party coarse consistency loses
no constant. No same-party coarse-distance contraction is used. -/
theorem mirror_retained_distance_le (hΨ : ‖Ψ.ψ‖ = 1)
    (P : I → 𝒜) (Q B : I → ℬ)
    (hP : IsPVMIn P) (hB : IsPVMIn B)
    (hmirror : ∀ i, Ψ.π (Ψ.πA (P i)) Ψ.ψ = Ψ.π (Ψ.πB (Q i)) Ψ.ψ) (r : I → W) :
    (∑ w, Ψ.xSqNorm (fibSumIn P r w) (fibSumIn B r w)) ≤
      ∑ i, Ψ.snorm (Ψ.πB (B i) - Ψ.πB (Q i)) ^ 2 := by
  have h := Ψ.sum_xSqNorm_fibSum_le hΨ hP hB r
  simpa only [xSqNorm_eq_bOp_distance_of_mirror Ψ _ _ _ (hmirror _)] using h

end Retain

section Conditional

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] (Ψ : BipartiteModel 𝒞 𝒜 ℬ)
variable {I Y Z W : Type*} [Fintype I] [DecidableEq I] [Fintype Y] [DecidableEq Y]
  [Fintype Z] [DecidableEq Z] [Fintype W] [DecidableEq W]

/-- The full ideal replacement remains valid after retaining any desired
part of the paired conditional outcome, using primitive ideal mirrors. -/
theorem conditional_coarse_ideal_replacement_retained [PartialOrder 𝒜] [StarOrderedRing 𝒜]
    [PartialOrder ℬ] [StarOrderedRing ℬ] (hΨ : ‖Ψ.ψ‖ = 1)
    (M P : I → 𝒜) (R : I → ℬ) (Q : Y → 𝒜) (S : Y → ℬ)
    (B : Y × Z → ℬ) (f : Y → I → Z) (r : Y × Z → W)
    (hM : IsPVMIn M) (hP : IsPVMIn P) (hR : IsPVMIn R)
    (hQ : IsPVMIn Q) (hS : IsPVMIn S) (hB : IsPVMIn B)
    (hcA : ∀ y i, Commute (Q y) (P i)) (hcB : ∀ y i, Commute (S y) (R i))
    (hmirrorP : ∀ i, Ψ.π (Ψ.πA (P i)) Ψ.ψ = Ψ.π (Ψ.πB (R i)) Ψ.ψ)
    (hmirrorQ : ∀ y, Ψ.π (Ψ.πA (Q y)) Ψ.ψ = Ψ.π (Ψ.πB (S y)) Ψ.ψ)
    {α η ε : ℝ}
    (hfine : ∑ i, Ψ.xSqNorm (M i) (R i) ≤ ε)
    (hnorm : ∑ y, Ψ.snorm (Ψ.πB ((∑ z, B (y, z)) - S y)) ^ 2 ≤ η)
    (hconditional : ∑ p : Y × Z, Ψ.snorm
      (Ψ.πB (B p) - Ψ.πA (fibSumIn M (f p.1) p.2) * Ψ.πB (∑ z, B (p.1, z))) ^ 2 ≤ α) :
    (∑ w, Ψ.xSqNorm (fibSumIn (conditionalIdeal P Q f) r w) (fibSumIn B r w)) ≤
      3 * α + 3 * η + 3 * ε := by
  exact (mirror_retained_distance_le Ψ hΨ (conditionalIdeal P Q f)
    (conditionalIdeal R S f) B (conditionalIdeal_isPVM P Q f hP hQ hcA) hB
    (conditionalIdeal_mirror Ψ P R Q S f hmirrorP hmirrorQ hcB) r).trans
      (conditional_coarse_ideal_replacement Ψ hΨ M R S B f hM hR hS hcB
        hfine hnorm hconditional)

end Conditional

namespace Honest

variable {F ι A PauliAnswer : Type*}
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype PauliAnswer] {ℓ : ℕ}

/-- The same retention map acts correctly on the entire parsed alphabet,
including every malformed answer constructor. -/
theorem hideNextRetain_parsed (P : CL.CLFun F ι ℓ) (k : ℕ)
    (a : ParsedAnswer (ι → F) A PauliAnswer) :
    hideNextRetain (TypedEstimates.hidingNextLater P k a) =
      TypedEstimates.hidingCoarse P (k + 1) a := by
  cases a <;> rfl

/-- Retaining the next label of the paired measurement is the next coarse measurement, for a POVM
in any ordered `⋆`-ring. -/
theorem hideNextRetain_mapped (P : CL.CLFun F ι ℓ) (k : ℕ)
    {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
    (N : POVMIn (ParsedAnswer (ι → F) A PauliAnswer) R) (z : Option (HideLabel F ι)) :
    fibSumIn (N.map (TypedEstimates.hidingNextLater P k)).op hideNextRetain z =
      (N.map (TypedEstimates.hidingCoarse P (k + 1))).op z := by
  rw [fibSumIn, ← POVMIn.map_op, POVMIn.map_map]
  simp only [hideNextRetain_parsed]

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]

/-- The actual next hiding measurement is close to the next honest fine
family. The paired bound is the normalizer estimate; the only state-specific
inputs here are exact mirrors of the primitive ideal families. -/
theorem hideCoarseOp_step_of_normalizer [StarModule ℂ 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ]
    [StarProper ℬ] (P : CL.CLFun F ι ℓ) (k : ℕ)
    (hk : k + 1 < ℓ) (h : P.SupportedOn univ)
    (Ψ : BipartiteModel 𝒞 (Matrix (ι → F) (ι → F) 𝒜) (Matrix (ι → F) (ι → F) ℬ))
    (hΨ : ‖Ψ.ψ‖ = 1)
    (N : POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) ℬ))
    (hN : IsPVMIn N.op)
    (hmfine : ∀ i, Ψ.π (Ψ.πA (smulKron 1 (hideCoarseOp P k h i))) Ψ.ψ =
      Ψ.π (Ψ.πB (smulKron 1 (hideCoarseOp P k h i))) Ψ.ψ)
    (hmprefix : ∀ y, Ψ.π (Ψ.πA (smulKron 1 (hidingPrefixOp P (k + 1) y))) Ψ.ψ =
      Ψ.π (Ψ.πB (smulKron 1 (hidingPrefixOp P (k + 1) y))) Ψ.ψ)
    {δ : ℝ}
    (hpaired : ∑ p, Ψ.snorm
      (Ψ.πB ((N.map (TypedEstimates.hidingNextLater P k)).op p) -
        Ψ.πB (conditionalIdeal (fun i => smulKron 1 (hideCoarseOp P k h i))
          (fun y => smulKron 1 (hidingPrefixOp P (k + 1) y))
          (TypedEstimates.hidingNextGuarded P k) p)) ^ 2 ≤ δ) :
    (∑ z, Ψ.xSqNorm (smulKron 1 (hideCoarseOp P (k + 1) h z))
      ((N.map (TypedEstimates.hidingCoarse P (k + 1))).op z)) ≤ δ := by
  let C := conditionalIdeal (hideCoarseOp P k h) (hidingPrefixOp P (k + 1))
    (TypedEstimates.hidingNextGuarded P k)
  have hc := hidingPrefixOp_commute_coarse P k h (hideLabelCoarse P k)
  have hC : IsPVMIn C := conditionalIdeal_isPVM _ _ _
    (hideCoarseOp_isPVM P k h).toIn (hidingPrefixOp_isPVM P (k + 1)).toIn hc
  have hm (p) : Ψ.π (Ψ.πA (smulKron 1 (C p))) Ψ.ψ = Ψ.π (Ψ.πB (smulKron 1 (C p))) Ψ.ψ := by
    have he := conditionalIdeal_mirror Ψ _ _ _ _ (TypedEstimates.hidingNextGuarded P k)
      hmfine hmprefix (fun y i => commute_smulKron_one (hc y i)) p
    rwa [conditionalIdeal_smulKron_one, conditionalIdeal_smulKron_one] at he
  have hret := mirror_retained_distance_le Ψ hΨ (fun p => smulKron 1 (C p))
    (fun p => smulKron 1 (C p)) (N.map (TypedEstimates.hidingNextLater P k)).op
    hC.smulKron_one (POVMIn.isPVMIn_map hN _) hm hideNextRetain
  have hp : (∑ p, Ψ.snorm (Ψ.πB ((N.map (TypedEstimates.hidingNextLater P k)).op p) -
      Ψ.πB (smulKron 1 (C p))) ^ 2) ≤ δ := by
    simpa only [conditionalIdeal_smulKron_one, C] using hpaired
  have hret' := hret.trans hp
  simpa only [fibSumIn_smulKron_one, C, ← fibSum_eq_fibSumIn,
    hideCoarseOp_conditionalIdeal_step P k hk h, hideNextRetain_mapped] using hret'

end Honest

end MIPRE.Introspection

end

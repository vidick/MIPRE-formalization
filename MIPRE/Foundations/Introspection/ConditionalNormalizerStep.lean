/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.ConditionalNormalizerMirror
import MIPRE.Foundations.Introspection.ConditionalNormalizerIdeal

/-! # Retaining the next hiding label without an alphabet-size loss

We first transfer the paired same-party estimate to the exact ideal mirror.
Coarse-graining is then applied to cross-party PVM consistency, where positivity
gives a dimension-independent contraction.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical
open scoped Kronecker

set_option linter.unusedSectionVars false

section Retain

variable {H K I W : Type*}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

/-- Exact mirror transfer followed by cross-party coarse consistency loses
no constant. No same-party coarse-distance contraction is used. -/
theorem mirror_retained_distance_le (ψ : H × K → ℂ) (hψ : ‖evec ψ‖ = 1)
    (P : I → Matrix H H ℂ) (Q B : I → Matrix K K ℂ)
    (hP : IsPVM P) (hB : IsPVM B)
    (hmirror : ∀ i, aOp (P i) *ᵥ ψ = bOp (Q i) *ᵥ ψ) (r : I → W) :
    (∑ w, xSqNorm ψ (fibSum P r w) (fibSum B r w)) ≤
      ∑ i, snorm ψ (bOp (B i) - bOp (Q i)) ^ 2 := by
  have h := sum_xSqNorm_fibSum_le hψ hP hB r
  simpa only [xSqNorm_eq_bOp_distance_of_mirror ψ _ _ _ (hmirror _)] using h

end Retain

section Conditional

variable {H K I Y Z W : Type*}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype Y] [DecidableEq Y]
  [Fintype Z] [DecidableEq Z] [Fintype W] [DecidableEq W]

/-- The full ideal replacement remains valid after retaining any desired
part of the paired conditional outcome, using primitive ideal mirrors. -/
theorem conditional_coarse_ideal_replacement_retained (ψ : H × K → ℂ)
    (hψ : ‖evec ψ‖ = 1) (M P : I → Matrix H H ℂ) (R : I → Matrix K K ℂ)
    (Q : Y → Matrix H H ℂ) (S : Y → Matrix K K ℂ)
    (B : Y × Z → Matrix K K ℂ) (f : Y → I → Z) (r : Y × Z → W)
    (hM : IsPVM M) (hP : IsPVM P) (hR : IsPVM R)
    (hQ : IsPVM Q) (hS : IsPVM S) (hB : IsPVM B)
    (hcA : ∀ y i, Commute (Q y) (P i)) (hcB : ∀ y i, Commute (S y) (R i))
    (hmirrorP : ∀ i, aOp (P i) *ᵥ ψ = bOp (R i) *ᵥ ψ)
    (hmirrorQ : ∀ y, aOp (Q y) *ᵥ ψ = bOp (S y) *ᵥ ψ)
    {α η ε : ℝ}
    (hfine : ∑ i, xSqNorm ψ (M i) (R i) ≤ ε)
    (hnorm : ∑ y, snorm ψ (bOp ((∑ z, B (y, z)) - S y)) ^ 2 ≤ η)
    (hconditional : ∑ p : Y × Z, snorm ψ
      (bOp (B p) - fibSum M (f p.1) p.2 ⊗ₖ (∑ z, B (p.1, z))) ^ 2 ≤ α) :
    (∑ w, xSqNorm ψ (fibSum (conditionalIdeal P Q f) r w) (fibSum B r w)) ≤
      3 * α + 3 * η + 3 * ε := by
  exact (mirror_retained_distance_le ψ hψ (conditionalIdeal P Q f)
    (conditionalIdeal R S f) B (conditionalIdeal_isPVM P Q f hP hQ hcA) hB
    (conditionalIdeal_mirror ψ P R Q S f hmirrorP hmirrorQ hcB) r).trans
      (conditional_coarse_ideal_replacement ψ hψ M R S B f hM hR hS hcB
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

theorem hideNextRetain_mapped (P : CL.CLFun F ι ℓ) (k : ℕ)
    {K : Type*} [Fintype K] [DecidableEq K]
    (N : POVM (ParsedAnswer (ι → F) A PauliAnswer) K) (z : Option (HideLabel F ι)) :
    fibSum (fun p => ((N.map (TypedEstimates.hidingNextLater P k)).mats p).val)
      hideNextRetain z = ((N.map (TypedEstimates.hidingCoarse P (k + 1))).mats z).val := by
  rw [fibSum, ← POVM.map_mats, POVM.map_map]
  simp only [hideNextRetain_parsed]

set_option backward.isDefEq.respectTransparency false in
/-- The actual next hiding measurement is close to the next honest fine
family. The paired bound is the normalizer estimate; the only state-specific
inputs here are exact mirrors of the primitive ideal families. -/
theorem hideCoarseOp_step_of_normalizer (P : CL.CLFun F ι ℓ) (k : ℕ)
    (hk : k + 1 < ℓ) (h : P.SupportedOn univ)
    (ψ : (ι → F) × (ι → F) → ℂ) (hψ : ‖evec ψ‖ = 1)
    (N : POVM (ParsedAnswer (ι → F) A PauliAnswer) (ι → F))
    (hN : IsPVM (fun a => (N.mats a).val))
    (hmfine : ∀ i, aOp (hideCoarseOp P k h i) *ᵥ ψ = bOp (hideCoarseOp P k h i) *ᵥ ψ)
    (hmprefix : ∀ y, aOp (hidingPrefixOp P (k + 1) y) *ᵥ ψ =
      bOp (hidingPrefixOp P (k + 1) y) *ᵥ ψ)
    {δ : ℝ}
    (hpaired : ∑ p, snorm ψ
      (bOp (((N.map (TypedEstimates.hidingNextLater P k)).mats p).val) -
        bOp (conditionalIdeal (hideCoarseOp P k h) (hidingPrefixOp P (k + 1))
          (TypedEstimates.hidingNextGuarded P k) p)) ^ 2 ≤ δ) :
    (∑ z, xSqNorm ψ (hideCoarseOp P (k + 1) h z)
      (((N.map (TypedEstimates.hidingCoarse P (k + 1))).mats z).val)) ≤ δ := by
  let C := conditionalIdeal (hideCoarseOp P k h) (hidingPrefixOp P (k + 1))
    (TypedEstimates.hidingNextGuarded P k)
  have hc := hidingPrefixOp_commute_coarse P k h (hideLabelCoarse P k)
  have hC : IsPVM C := conditionalIdeal_isPVM _ _ _
    (hideCoarseOp_isPVM P k h) (hidingPrefixOp_isPVM P (k + 1)) hc
  have hm : ∀ p, aOp (C p) *ᵥ ψ = bOp (C p) *ᵥ ψ :=
    conditionalIdeal_mirror ψ _ _ _ _ _ hmfine hmprefix hc
  have hret := mirror_retained_distance_le ψ hψ C C
    (fun p => ((N.map (TypedEstimates.hidingNextLater P k)).mats p).val) hC
    (isPVM_povm_map N hN (TypedEstimates.hidingNextLater P k)) hm hideNextRetain
  have hret' := hret.trans hpaired
  simpa only [C, hideCoarseOp_conditionalIdeal_step P k hk h, hideNextRetain_mapped] using hret'

end Honest

end MIPRE.Introspection

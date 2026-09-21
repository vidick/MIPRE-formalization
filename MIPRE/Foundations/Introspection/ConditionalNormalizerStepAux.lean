/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.ConditionalNormalizerStep
import MIPRE.Foundations.Introspection.ConditionalNormalizerIdealMirror

/-! # The next hiding step on an EPR seed with arbitrary auxiliaries -/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical
open scoped Kronecker

set_option linter.unusedSectionVars false

section Extend

variable {V H I Y Z : Type*}
  [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]
  [Fintype I] [DecidableEq I] [Fintype Y] [DecidableEq Y]
  [Fintype Z] [DecidableEq Z]

theorem fibSum_aOp (P : I → Matrix V V ℂ) (f : I → Z) (z : Z) :
    fibSum (fun i => (aOp (P i) : Matrix (V × H) _ ℂ)) f z = aOp (fibSum P f z) :=
  (aOp_sum _ _).symm

theorem conditionalIdeal_aOp (P : I → Matrix V V ℂ) (Q : Y → Matrix V V ℂ)
    (f : Y → I → Z) (p : Y × Z) :
    conditionalIdeal (fun i => (aOp (P i) : Matrix (V × H) _ ℂ))
      (fun y => aOp (Q y)) f p = aOp (conditionalIdeal P Q f p) := by
  rw [conditionalIdeal, fibSum_aOp, ← aOp_mul, conditionalIdeal]

end Extend

namespace Honest

variable {F ι A PauliAnswer H K : Type*}
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype PauliAnswer]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}

/-- Exact ideal mirrors persist with any bipartite auxiliary state. -/
theorem hideCoarseOp_registerState_mirror (P : CL.CLFun F ι ℓ) (k : ℕ)
    (h : P.SupportedOn univ) (ξ : H × K → ℂ) (i : Option (HideLabel F ι)) :
    aOp (aOp (hideCoarseOp P k h i) : Matrix ((ι → F) × H) _ ℂ) *ᵥ registerState (ι → F) ξ =
      bOp (aOp (hideCoarseOp P k h i) : Matrix ((ι → F) × K) _ ℂ) *ᵥ
        registerState (ι → F) ξ := by
  have he := mirror_expVec (registerEPR (ι → F)) ξ (hideCoarseOp P k h i)
    (hideCoarseOp P k h i) (congrArg evec (hideCoarseOp_epr_mirror P k h i))
  exact congrArg WithLp.ofLp he

theorem hidingPrefixOp_registerState_mirror (P : CL.CLFun F ι ℓ) (k : ℕ)
    (ξ : H × K → ℂ) (y : Option (ι → F)) :
    aOp (aOp (hidingPrefixOp P k y) : Matrix ((ι → F) × H) _ ℂ) *ᵥ registerState (ι → F) ξ =
      bOp (aOp (hidingPrefixOp P k y) : Matrix ((ι → F) × K) _ ℂ) *ᵥ
        registerState (ι → F) ξ := by
  have he := mirror_expVec (registerEPR (ι → F)) ξ (hidingPrefixOp P k y)
    (hidingPrefixOp P k y) (congrArg evec (hidingPrefixOp_epr_mirror P k y))
  exact congrArg WithLp.ofLp he

theorem hidingPrefixOp_aux_commute (P : CL.CLFun F ι ℓ) (k : ℕ)
    (h : P.SupportedOn univ) (y : Option (ι → F)) (i : Option (HideLabel F ι)) :
    Commute (aOp (hidingPrefixOp P (k + 1) y) : Matrix ((ι → F) × H) _ ℂ)
      (aOp (hideCoarseOp P k h i)) := by
  show _ * _ = _ * _
  rw [← aOp_mul, ← aOp_mul]
  exact congrArg aOp (hidingPrefixOp_commute_coarse P k h (hideLabelCoarse P k) y i).eq

set_option backward.isDefEq.respectTransparency false in
/-- The paired normalizer bound implies rigidity of the actual next coarse
Hide measurement on the full seed/auxiliary carrier. All ideal mirrors and
conditional product identities are supplied by the honest construction. -/
theorem hideCoarseOp_aux_step_of_normalizer (P : CL.CLFun F ι ℓ) (k : ℕ)
    (hk : k + 1 < ℓ) (h : P.SupportedOn univ)
    (ξ : H × K → ℂ) (hξ : ‖evec ξ‖ = 1)
    (N : POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × K))
    (hN : IsPVM (fun a => (N.mats a).val)) {δ : ℝ}
    (hpaired : ∑ p, snorm (registerState (ι → F) ξ)
      (bOp (((N.map (TypedEstimates.hidingNextLater P k)).mats p).val) -
        bOp (conditionalIdeal
          (fun i => (aOp (hideCoarseOp P k h i) : Matrix ((ι → F) × K) _ ℂ))
          (fun y => aOp (hidingPrefixOp P (k + 1) y))
          (TypedEstimates.hidingNextGuarded P k) p)) ^ 2 ≤ δ) :
    (∑ z, xSqNorm (registerState (ι → F) ξ)
      (aOp (hideCoarseOp P (k + 1) h z) : Matrix ((ι → F) × H) _ ℂ)
      (((N.map (TypedEstimates.hidingCoarse P (k + 1))).mats z).val)) ≤ δ := by
  let C := conditionalIdeal (hideCoarseOp P k h) (hidingPrefixOp P (k + 1))
    (TypedEstimates.hidingNextGuarded P k)
  have hc := hidingPrefixOp_commute_coarse P k h (hideLabelCoarse P k)
  have hC : IsPVM C := conditionalIdeal_isPVM _ _ _
    (hideCoarseOp_isPVM P k h) (hidingPrefixOp_isPVM P (k + 1)) hc
  have hseed (p) : aOp (C p) *ᵥ registerEPR (ι → F) = bOp (C p) *ᵥ registerEPR (ι → F) :=
    conditionalIdeal_mirror _ _ _ _ _ _ (hideCoarseOp_epr_mirror P k h)
      (hidingPrefixOp_epr_mirror P (k + 1)) hc p
  have hm (p) :
      aOp (aOp (C p) : Matrix ((ι → F) × H) _ ℂ) *ᵥ registerState (ι → F) ξ =
        bOp (aOp (C p) : Matrix ((ι → F) × K) _ ℂ) *ᵥ registerState (ι → F) ξ :=
    congrArg WithLp.ofLp (mirror_expVec (registerEPR (ι → F)) ξ (C p) (C p)
      (congrArg evec (hseed p)))
  have hret := mirror_retained_distance_le (registerState (ι → F) ξ)
    (registerState_norm ξ hξ)
    (fun p => (aOp (C p) : Matrix ((ι → F) × H) _ ℂ))
    (fun p => (aOp (C p) : Matrix ((ι → F) × K) _ ℂ))
    (fun p => ((N.map (TypedEstimates.hidingNextLater P k)).mats p).val)
    hC.aOp (isPVM_povm_map N hN (TypedEstimates.hidingNextLater P k)) hm hideNextRetain
  have hp : (∑ p, snorm (registerState (ι → F) ξ)
      (bOp (((N.map (TypedEstimates.hidingNextLater P k)).mats p).val) -
        bOp (aOp (C p) : Matrix ((ι → F) × K) _ ℂ)) ^ 2) ≤ δ := by
    simpa only [conditionalIdeal_aOp, C] using hpaired
  have hret' := hret.trans hp
  simpa only [fibSum_aOp, C, hideCoarseOp_conditionalIdeal_step P k hk h,
    hideNextRetain_mapped] using hret'

end Honest

end MIPRE.Introspection

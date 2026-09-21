/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.ConditionalNormalizerStepAux
import MIPRE.Foundations.Introspection.HonestPauliRegister

/-! # The ideal first hiding family is the full Pauli-X coarsening -/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical Weyl
open scoped Kronecker

set_option linter.unusedSectionVars false

/-- An ideal mirror identifies same-side replacement error with fine
cross-party consistency, before any coarse-graining is performed. -/
theorem xSqNorm_eq_stateSqNorm_of_mirror
    {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
    (ψ : H × K → ℂ) (M P : Matrix H H ℂ) (Q : Matrix K K ℂ)
    (hmirror : aOp P *ᵥ ψ = bOp Q *ᵥ ψ) :
    xSqNorm ψ M Q = stateSqNorm ψ (P - M) := by
  calc
    _ = snorm ψ (bOp Q - aOp M) ^ 2 := by rw [xSqNorm_eq_snorm_sq, snorm_sub_comm]
    _ = snorm ψ (aOp P - aOp M) ^ 2 := by simp only [snorm, Matrix.sub_mulVec, hmirror]
    _ = _ := by rw [stateSqNorm, stateNorm, norm_stateVec_eq_snorm, aOp_sub]

namespace Honest

variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

/-- The complete Pauli-X family, including zero at the malformed outcome. -/
def pauliXReadout : Option (ι → F) → Matrix (ι → F) (ι → F) ℂ := synOf wX some

theorem pauliXReadout_isPVM : IsPVM (pauliXReadout (F := F) (ι := ι)) :=
  isPVM_synOf isWeylFamily_wX some

@[simp] theorem pauliXReadout_none : pauliXReadout (F := F) (ι := ι) none = 0 := by
  simp [pauliXReadout, synOf]

@[simp] theorem pauliXReadout_some (x : ι → F) : pauliXReadout (some x) = proj wX x := by
  simp [pauliXReadout, synOf, Finset.sum_filter]

theorem hideLabelCoarse_firstHideAnswer (P : CL.CLFun F ι ℓ) (x : ι → F) :
    hideLabelCoarse P 0 (firstHideAnswer P x) = some (firstHideAnswer P x) := by
  have hd := dualReadout_first_supported P x
  have hr : CLChecks.prefixRegister P 1 (0 : ι → F) = P.factorOfPrefix 0 0 := by
    cases P <;> simp [CLChecks.prefixRegister]
  simp only [hideLabelCoarse, hideLabelAnswer, TypedEstimates.hidingCoarse, firstHideAnswer,
    CL.CLFun.outputPrefix_zero, hr, hd, CL.proj_proj_self]

/-- The ideal full-register first Hide family equals the tested coarsening
of ideal Pauli-X, with a complete dummy outcome. -/
theorem pauliXReadout_firstHide (P : CL.CLFun F ι ℓ) (h : P.SupportedOn univ)
    (z : Option (HideLabel F ι)) :
    fibSum (pauliXReadout (F := F) (ι := ι)) (Option.map (firstHideAnswer P)) z =
      hideCoarseOp P 0 h z := by
  have hfirst : hideOp P 0 h = fibSum (proj wX) (firstHideAnswer P) := by
    funext a
    exact hideOp_zero_eq_firstHideOp P h a
  have hf : hideLabelCoarse P 0 ∘ firstHideAnswer P =
      fun x => some (firstHideAnswer P x) := funext (hideLabelCoarse_firstHideAnswer P)
  calc
    _ = fibSum (proj wX) (fun x => some (firstHideAnswer P x)) z :=
      coarseOp_comp some (Option.map (firstHideAnswer P)) (proj wX) z
    _ = fibSum (fibSum (proj wX) (firstHideAnswer P)) (hideLabelCoarse P 0) z := by
      rw [← hf]
      exact (coarseOp_comp (firstHideAnswer P) (hideLabelCoarse P 0) (proj wX) z).symm
    _ = _ := by rw [hideCoarseOp, hfirst]

theorem pauliXReadout_registerState_mirror
    {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
    (ξ : H × K → ℂ) (x : Option (ι → F)) :
    aOp (aOp (pauliXReadout x) : Matrix ((ι → F) × H) _ ℂ) *ᵥ registerState (ι → F) ξ =
      bOp (aOp (pauliXReadout x) : Matrix ((ι → F) × K) _ ℂ) *ᵥ registerState (ι → F) ξ := by
  have hseed : stateVec (registerEPR (ι → F)) (pauliXReadout x) =
      stateVecB (registerEPR (ι → F)) (pauliXReadout x) :=
    stateVec_epr_synOf wX_transpose some x
  exact congrArg WithLp.ofLp (mirror_expVec _ ξ _ _ hseed)

end Honest

end MIPRE.Introspection

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.ConditionalNormalizerStepAux
public import MIPRE.Foundations.Introspection.HonestPauliRegister

@[expose] public section

/-! # The ideal first hiding family is the full Pauli-X coarsening

The two statements about a state are made in a bipartite model (Phase 4 of
`planning/mipco-track.md`): an ideal mirror is a vector identity, and the register mirror is
`BipartiteModel.reg_mirror`. The honest register operators stay concrete.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical Weyl

set_option linter.unusedSectionVars false

/-- An ideal mirror identifies same-side replacement error with fine
cross-party consistency, before any coarse-graining is performed. -/
theorem xSqNorm_eq_stateSqNorm_of_mirror
    {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
    [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] (Ψ : BipartiteModel 𝒞 𝒜 ℬ)
    (M P : 𝒜) (Q : ℬ) (hmirror : Ψ.π (Ψ.πA P) Ψ.ψ = Ψ.π (Ψ.πB Q) Ψ.ψ) :
    Ψ.xSqNorm M Q = Ψ.stateSqNorm (P - M) := by
  unfold BipartiteModel.xSqNorm BipartiteModel.xNorm BipartiteModel.stateSqNorm
    BipartiteModel.stateNorm
  rw [Ψ.snorm_sub_comm]
  congr 1
  simp only [StateModel.snorm, Op.snorm, map_sub, ContinuousLinearMap.sub_apply, hmirror]

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
    {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
    [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] (Ξ : BipartiteModel 𝒞 𝒜 ℬ)
    (x : Option (ι → F)) :
    (Ξ.reg (ι → F)).π ((Ξ.reg (ι → F)).πA (smulKron 1 (pauliXReadout x))) (Ξ.reg (ι → F)).ψ =
      (Ξ.reg (ι → F)).π ((Ξ.reg (ι → F)).πB (smulKron 1 (pauliXReadout x)))
        (Ξ.reg (ι → F)).ψ := by
  have he := Ξ.reg_mirror (pauliXReadout x)
  rwa [pauliXReadout, synOf_transpose_of_symmetric _ wX_transpose] at he

end Honest

end MIPRE.Introspection

end

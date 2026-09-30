/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.HidingBaseTests
public import MIPRE.Foundations.Introspection.HidingRigidityOrientation

@[expose] public section

/-! # Initializing hiding rigidity from the extracted Pauli-X family

The fine Pauli-X replacement estimate is first converted to cross-party
consistency using its exact EPR mirror. Projective coarse-graining therefore
costs nothing. The actual Pauli-X/first-hiding edge then identifies the first
hiding family, with error `2 deltaX + 4 |E| epsilon` on a full EPR-plus-auxiliary
state. No first-hiding rigidity hypothesis is used.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the EPR-plus-auxiliary state is
the register model `Ξ.reg (ι → F)` of a normalized auxiliary model, and the honest families enter
as `smulKron 1 _`.
-/

noncomputable section

namespace MIPRE.Introspection.TypedEstimates

open Finset Matrix Classical

set_option linter.unusedSectionVars false

variable {PauliType PauliAnswer F ι κ A : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype A] {ℓ : ℕ}

theorem pauliX_firstHide_mapped {R : Type*} [Ring R] [StarRing R] [PartialOrder R]
    [StarOrderedRing R] (P : CL.CLFun F ι ℓ)
    (projectPauli : PauliAnswer → ι → F)
    (M : POVMIn (ParsedAnswer (ι → F) A PauliAnswer) R)
    (z : Option (Honest.HideLabel F ι)) :
    fibSumIn (fun x => (M.map (pauliProjection projectPauli)).op x)
      (Option.map (Honest.firstHideAnswer P)) z =
      (M.map (fun a => Option.map (Honest.firstHideAnswer P)
        (pauliProjection projectPauli a))).op z := by
  rw [fibSumIn, ← POVMIn.map_op, POVMIn.map_map]

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [StarModule ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [StarModule ℂ ℬ]
  [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarProper 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ]
  [StarProper ℬ]

variable
  (E : PauliType → PauliType → Bool) (X Z : PauliType)
  (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
  (projectPauli : PauliAnswer → ι → F)
  (D : (ι → F) → (ι → F) → A → A → Bool)
  (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
    PauliAnswer → PauliAnswer → Bool)
  (Ξ : BipartiteModel 𝒞 𝒜 ℬ) (hΞ : ‖Ξ.ψ‖ = 1)
  (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
    POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) 𝒜))
  (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
    POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) ℬ))
  {ε : ℝ} (hfail : 1 - (Ξ.reg (ι → F)).povmValue
    (parsedGame E X Z P L projectPauli D DP) MA MB ≤ ε)

include hΞ hfail

/-- A cross-party extracted Pauli-X guarantee initializes the actual hiding
chain. Only the Pauli-X measurement needs projectivity at this step. -/
theorem hiding_first_register_rigidity_cross
    (w : Bool) (k : Fin ℓ) (hk : k.val = 0) (hL : (L w).SupportedOn univ)
    (qX : κ → ZMod 2) (hqX : ∀ z, (P X).eval z = qX)
    (hMA : IsPVMIn (MA (.inl X, qX)).op) {δX : ℝ}
    (hPauli : ∑ x, (Ξ.reg (ι → F)).xSqNorm
      (((MA (.inl X, qX)).map (pauliProjection projectPauli)).op x)
      (smulKron 1 (Honest.pauliXReadout x)) ≤ δX) :
    hidingBobError L w hL Ξ MB k ≤ 4 * (TypeGraph.edges E X Z ℓ).card * ε + 2 * δX := by
  have hunit : ‖(Ξ.reg (ι → F)).ψ‖ = 1 := by rw [BipartiteModel.norm_reg_ψ, hΞ]
  have hcoarse := (Ξ.reg (ι → F)).sum_xSqNorm_fibSum_le hunit
    (POVMIn.isPVMIn_map hMA (pauliProjection projectPauli))
    ((Honest.pauliXReadout_isPVM (F := F) (ι := ι)).toIn.smulKron_one (R := ℬ))
    (Option.map (Honest.firstHideAnswer (L w)))
  have hc := hcoarse.trans hPauli
  simp only [pauliX_firstHide_mapped, fibSumIn_smulKron_one, ← fibSum_eq_fibSumIn,
    Honest.pauliXReadout_firstHide (L w) hL] at hc
  have htest := hiding_first_agreement_estimate E X Z P L projectPauli D DP
    (Ξ.reg (ι → F)) hunit MA MB hfail w k hk qX hqX
  let M := (MA (.inl X, qX)).map (fun a =>
    Option.map (Honest.firstHideAnswer (L w)) (pauliProjection projectPauli a))
  have hc' : ∑ z, (Ξ.reg (ι → F)).stateSqNorm
      (smulKron (1 : 𝒜) (Honest.hideCoarseOp (L w) 0 hL z) - M.op z) ≤ δX := by
    calc
      _ = ∑ z, (Ξ.reg (ι → F)).xSqNorm (M.op z)
          (smulKron (1 : ℬ) (Honest.hideCoarseOp (L w) 0 hL z)) := by
        apply Finset.sum_congr rfl
        intro z _
        exact (xSqNorm_eq_stateSqNorm_of_mirror _ _ _ _
          (Honest.hideCoarseOp_registerState_mirror (L w) 0 hL Ξ z)).symm
      _ ≤ δX := hc
  have ht := (Ξ.reg (ι → F)).sum_xSqNorm_le_of_two_step
    (fun z => smulKron (1 : 𝒜) (Honest.hideCoarseOp (L w) 0 hL z))
    (fun z => M.op z)
    (fun z => ((MB (QuestionType.hide w k, 0)).map (hidingCoarse (L w) 0)).op z)
    hc' htest
  simpa only [hidingBobError, hk] using ht.trans_eq (by ring)

/-- The usual same-party extracted Pauli-X replacement estimate suffices:
the ideal X projectors are exact mirrors on the EPR register, independently
of the auxiliary state. -/
theorem hiding_first_register_rigidity
    (w : Bool) (k : Fin ℓ) (hk : k.val = 0) (hL : (L w).SupportedOn univ)
    (qX : κ → ZMod 2) (hqX : ∀ z, (P X).eval z = qX)
    (hMA : IsPVMIn (MA (.inl X, qX)).op) {δX : ℝ}
    (hPauli : ∑ x, (Ξ.reg (ι → F)).stateSqNorm
      (((MA (.inl X, qX)).map (pauliProjection projectPauli)).op x -
        smulKron 1 (Honest.pauliXReadout x)) ≤ δX) :
    hidingBobError L w hL Ξ MB k ≤ 4 * (TypeGraph.edges E X Z ℓ).card * ε + 2 * δX := by
  apply hiding_first_register_rigidity_cross E X Z P L projectPauli D DP Ξ hΞ MA MB hfail
    w k hk hL qX hqX hMA
  simpa only [xSqNorm_eq_stateSqNorm_of_mirror _ _ _ _
    (Honest.pauliXReadout_registerState_mirror Ξ _), BipartiteModel.stateSqNorm_sub_comm]
    using hPauli

end MIPRE.Introspection.TypedEstimates

end

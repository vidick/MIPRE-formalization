/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.HidingBaseTests
import MIPRE.Foundations.Introspection.HidingRigidityOrientation

/-! # Initializing hiding rigidity from the extracted Pauli-X family

The fine Pauli-X replacement estimate is first converted to cross-party
consistency using its exact EPR mirror. Projective coarse-graining therefore
costs nothing. The actual Pauli-X/first-hiding edge then identifies the first
hiding family, with error `2 deltaX + 4 |E| epsilon` on a full EPR-plus-auxiliary
state. No first-hiding rigidity hypothesis is used.
-/

noncomputable section

namespace MIPRE.Introspection.TypedEstimates

open Finset Matrix Classical

set_option linter.unusedSectionVars false

variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype A]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}

theorem pauliX_firstHide_mapped (P : CL.CLFun F ι ℓ)
    (projectPauli : PauliAnswer → ι → F)
    (M : POVM (ParsedAnswer (ι → F) A PauliAnswer) H)
    (z : Option (Honest.HideLabel F ι)) :
    fibSum (fun x => ((M.map (pauliProjection projectPauli)).mats x).val)
      (Option.map (Honest.firstHideAnswer P)) z =
      ((M.map (fun a => Option.map (Honest.firstHideAnswer P)
        (pauliProjection projectPauli a))).mats z).val := by
  rw [fibSum, ← POVM.map_mats, POVM.map_map]

variable
  (E : PauliType → PauliType → Bool) (X Z : PauliType)
  (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
  (projectPauli : PauliAnswer → ι → F)
  (D : (ι → F) → (ι → F) → A → A → Bool)
  (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
    PauliAnswer → PauliAnswer → Bool)
  (ξ : H × K → ℂ) (hξ : star ξ ⬝ᵥ ξ = 1)
  (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
    POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H))
  (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
    POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × K))
  {ε : ℝ} (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP)
    (registerState (ι → F) ξ) MA MB ≤ ε)

include hξ hfail

/-- A cross-party extracted Pauli-X guarantee initializes the actual hiding
chain. Only the Pauli-X measurement needs projectivity at this step. -/
theorem hiding_first_register_rigidity_cross
    (w : Bool) (k : Fin ℓ) (hk : k.val = 0) (hL : (L w).SupportedOn univ)
    (qX : κ → ZMod 2) (hqX : ∀ z, (P X).eval z = qX)
    (hMA : IsPVM (fun a => ((MA (.inl X, qX)).mats a).val)) {δX : ℝ}
    (hPauli : ∑ x, xSqNorm (registerState (ι → F) ξ)
      ((((MA (.inl X, qX)).map (pauliProjection projectPauli)).mats x).val)
      (aOp (Honest.pauliXReadout x) : Matrix ((ι → F) × K) _ ℂ) ≤ δX) :
    hidingBobError L w hL ξ MB k ≤ 4 * (TypeGraph.edges E X Z ℓ).card * ε + 2 * δX := by
  have hseed : star (registerEPR (ι → F)) ⬝ᵥ registerEPR (ι → F) = 1 := by
    rw [registerEPR_eq_weyl]
    exact Weyl.epr_unit
  have hunit := expVec_unit hseed hξ
  have hcoarse := sum_xSqNorm_fibSum_le (norm_evec_eq_one_of_unit hunit)
    (isPVM_povm_map (MA (.inl X, qX)) hMA (pauliProjection projectPauli))
    (Honest.pauliXReadout_isPVM (F := F) (ι := ι)).aOp
    (Option.map (Honest.firstHideAnswer (L w)))
  have hc := hcoarse.trans hPauli
  simp only [pauliX_firstHide_mapped, fibSum_aOp, Honest.pauliXReadout_firstHide (L w) hL] at hc
  have htest := hiding_first_agreement_estimate E X Z P L projectPauli D DP
    (registerState (ι → F) ξ) hunit MA MB hfail w k hk qX hqX
  let M := (MA (.inl X, qX)).map (fun a =>
    Option.map (Honest.firstHideAnswer (L w)) (pauliProjection projectPauli a))
  have hc' : ∑ z, stateSqNorm (registerState (ι → F) ξ)
      ((aOp (Honest.hideCoarseOp (L w) 0 hL z) : Matrix ((ι → F) × H) _ ℂ) -
        (M.mats z).val) ≤ δX := by
    calc
      _ = ∑ z, xSqNorm (registerState (ι → F) ξ) (M.mats z).val
          (aOp (Honest.hideCoarseOp (L w) 0 hL z) : Matrix ((ι → F) × K) _ ℂ) := by
        apply Finset.sum_congr rfl
        intro z _
        exact (xSqNorm_eq_stateSqNorm_of_mirror _ _ _ _
          (Honest.hideCoarseOp_registerState_mirror (L w) 0 hL ξ z)).symm
      _ ≤ δX := hc
  have ht := sum_xSqNorm_le_of_two_step
    (fun z => (aOp (Honest.hideCoarseOp (L w) 0 hL z) : Matrix ((ι → F) × H) _ ℂ))
    (fun z => (M.mats z).val)
    (fun z => (((MB (QuestionType.hide w k, 0)).map (hidingCoarse (L w) 0)).mats z).val)
    hc' htest
  simpa only [hidingBobError, hk] using ht.trans_eq (by ring)

/-- The usual same-party extracted Pauli-X replacement estimate suffices:
the ideal X projectors are exact mirrors on the EPR register, independently
of the auxiliary state. -/
theorem hiding_first_register_rigidity
    (w : Bool) (k : Fin ℓ) (hk : k.val = 0) (hL : (L w).SupportedOn univ)
    (qX : κ → ZMod 2) (hqX : ∀ z, (P X).eval z = qX)
    (hMA : IsPVM (fun a => ((MA (.inl X, qX)).mats a).val)) {δX : ℝ}
    (hPauli : ∑ x, stateSqNorm (registerState (ι → F) ξ)
      (((((MA (.inl X, qX)).map (pauliProjection projectPauli)).mats x).val) -
        (aOp (Honest.pauliXReadout x) : Matrix ((ι → F) × H) _ ℂ)) ≤ δX) :
    hidingBobError L w hL ξ MB k ≤ 4 * (TypeGraph.edges E X Z ℓ).card * ε + 2 * δX := by
  apply hiding_first_register_rigidity_cross E X Z P L projectPauli D DP ξ hξ MA MB hfail
    w k hk hL qX hqX hMA
  simpa only [xSqNorm_eq_stateSqNorm_of_mirror _ _ _ _
    (Honest.pauliXReadout_registerState_mirror ξ _), stateSqNorm_sub_comm] using hPauli

end MIPRE.Introspection.TypedEstimates

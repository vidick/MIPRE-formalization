/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.ReadRigidity
import MIPRE.Foundations.Introspection.HidingInduction

/-! # The actual Read joint measurement supplies the dual commutator

The two marginals are Introspect's full question/answer and one fixed
prefix/dual readout. Their consistency follows from the actual reading test
and hiding rigidity, respectively. Commutation is derived at this coarse
alphabet; no fine commutator is subsequently coarse-grained.
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

def introFullPair : ParsedAnswer (ι → F) A PauliAnswer → Option ((ι → F) × A)
  | .pair y a => some (y, a)
  | _ => none

def readFullPair : ParsedAnswer (ι → F) A PauliAnswer → Option ((ι → F) × A)
  | .read y _ a => some (y, a)
  | _ => none

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

theorem introspect_read_full_estimate (w : Bool) :
    (∑ z, xSqNorm (registerState (ι → F) ξ)
      ((((MA (QuestionType.introspect w, 0)).map introFullPair).mats z).val)
      ((((MB (QuestionType.read w, 0)).map readFullPair).mats z).val)) ≤
      2 * (TypeGraph.edges E X Z ℓ).card * ε := by
  have hseed : star (registerEPR (ι → F)) ⬝ᵥ registerEPR (ι → F) = 1 := by
    rw [registerEPR_eq_weyl]
    exact Weyl.epr_unit
  apply aux_agreement_estimate E X Z P (questionCheck L X Z projectPauli D DP)
    (registerState (ι → F) ξ) (expVec_unit hseed hξ) MA MB hfail .introspect .read w w
    (TypeGraph.adj_introspect_read E X Z w)
  intro a b hab
  have hf := TypedPredicate.check_formats L X Z projectPauli D (fun p s => DP p s 0 0) hab
  cases a <;> cases b <;> simp [TypedPredicate.fits] at hf
  rename_i y a z zp b
  have he := TypedPredicate.check_reading L X Z projectPauli D (fun p s => DP p s 0 0) w hab
  exact congrArg some (Prod.ext he.1 he.2)

/-- The actual Read measurement supplies both tested marginals of the joint
measurement used for the X/dual half of product-form induction. -/
theorem introspect_dual_commutator (w : Bool) (hL : (L w).SupportedOn univ)
    (j : Fin ℓ)
    (hMA : IsPVM (fun a => ((MA (QuestionType.hide w j, 0)).mats a).val))
    (hMB : IsPVM (fun a => ((MB (QuestionType.read w, 0)).mats a).val)) {δ : ℝ}
    (hfine : ∑ i, xSqNorm (registerState (ι → F) ξ)
      ((((MA (QuestionType.hide w j, 0)).map (hidingCoarse (L w) j.val)).mats i).val)
      (aOp (Honest.hideCoarseOp (L w) j.val hL i) : Matrix ((ι → F) × K) _ ℂ) ≤ δ) :
    (∑ a, ∑ z, stateSqNorm (registerState (ι → F) ξ)
      (((((MA (QuestionType.introspect w, 0)).map introFullPair).mats a).val) *
          aOp (Honest.readDualOp (L w) j.val hL z) -
        aOp (Honest.readDualOp (L w) j.val hL z) *
          ((((MA (QuestionType.introspect w, 0)).map introFullPair).mats a).val))) ≤
      16 * ((32 * ((ℓ - j.val : ℕ) : ℝ) ^ 2 + 6) *
        (TypeGraph.edges E X Z ℓ).card * ε + 4 * δ) := by
  let M := (MA (QuestionType.introspect w, 0)).map introFullPair
  let R : POVM (Option ((ι → F) × (ι → F))) ((ι → F) × H) :=
    (Honest.readDualOp_isPVM (L w) j.val hL).aOp.toPOVM
  let B := MB (QuestionType.read w, 0)
  let f := fun a : ParsedAnswer (ι → F) A PauliAnswer =>
    (readFullPair a, reportedDual (L w) j.val .read a)
  have hc := coarse_joint_commutator_bound (registerState (ι → F) ξ) M R B hMB f
  have hl := introspect_read_full_estimate E X Z P L projectPauli D DP ξ hξ MA MB hfail w
  have hr := read_register_rigidity_bob E X Z P L projectPauli D DP ξ hξ MA MB hfail
    w hL j hMA hfine
  have hleft : coarseJointLeftError (registerState (ι → F) ξ) M B f ≤
      2 * (TypeGraph.edges E X Z ℓ).card * ε := by
    simpa only [coarseJointLeftError, M, B, f, POVM.sum_mats_map_prod] using hl
  have hright : coarseJointRightError (registerState (ι → F) ξ) R B f ≤
      (32 * ((ℓ - j.val : ℕ) : ℝ) ^ 2 + 4) * (TypeGraph.edges E X Z ℓ).card * ε + 4 * δ := by
    simpa only [coarseJointRightError, R, B, f, POVM.sum_mats_map_prod', IsPVM.toPOVM_mats] using hr
  change (∑ a, ∑ z, stateSqNorm (registerState (ι → F) ξ)
    ((M.mats a).val * (R.mats z).val - (R.mats z).val * (M.mats a).val)) ≤ _
  linarith only [hc, hleft, hright]

end MIPRE.Introspection.TypedEstimates

end

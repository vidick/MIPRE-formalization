/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.ReadRigidity
public import MIPRE.Foundations.Introspection.HidingInduction

@[expose] public section

/-! # The actual Read joint measurement supplies the dual commutator

The two marginals are Introspect's full question/answer and one fixed
prefix/dual readout. Their consistency follows from the actual reading test
and hiding rigidity, respectively. Commutation is derived at this coarse
alphabet; no fine commutator is subsequently coarse-grained.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the extracted register state is
the register model `Ξ.reg (ι → F)` of a normalized auxiliary model `Ξ`, the measurements are POVMs
in its algebras, and the honest dual readout enters Alice's algebra as `smulKron 1 _`.
-/

noncomputable section

namespace MIPRE.Introspection.TypedEstimates

open Finset Matrix Classical
set_option linter.unusedSectionVars false

variable {PauliType PauliAnswer F ι κ A : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype A] {ℓ : ℕ}

def introFullPair : ParsedAnswer (ι → F) A PauliAnswer → Option ((ι → F) × A)
  | .pair y a => some (y, a)
  | _ => none

def readFullPair : ParsedAnswer (ι → F) A PauliAnswer → Option ((ι → F) × A)
  | .read y _ a => some (y, a)
  | _ => none

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [StarProper 𝒜] [StarModule ℂ ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ] [StarProper ℬ]

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

theorem introspect_read_full_estimate (w : Bool) :
    (∑ z, (Ξ.reg (ι → F)).xSqNorm
      (((MA (QuestionType.introspect w, 0)).map introFullPair).op z)
      (((MB (QuestionType.read w, 0)).map readFullPair).op z)) ≤
      2 * (TypeGraph.edges E X Z ℓ).card * ε := by
  have hunit : ‖(Ξ.reg (ι → F)).ψ‖ = 1 := by rw [BipartiteModel.norm_reg_ψ, hΞ]
  apply aux_agreement_estimate E X Z P (questionCheck L X Z projectPauli D DP)
    (Ξ.reg (ι → F)) hunit MA MB hfail .introspect .read w w
    (TypeGraph.adj_introspect_read E X Z w)
  intro a b hab
  have hf := TypedPredicate.check_formats L X Z projectPauli D (fun p s => DP p s 0 0) hab
  cases a <;> cases b <;> simp [TypedPredicate.fits] at hf
  rename_i y a z zp b
  have he := TypedPredicate.check_reading L X Z projectPauli D (fun p s => DP p s 0 0) w hab
  exact congrArg some (Prod.ext he.1 he.2)

/-- The actual Read measurement supplies both tested marginals of the joint
measurement used for the X/dual half of product-form induction. -/
theorem introspect_dual_commutator [StarModule ℂ 𝒜] (w : Bool) (hL : (L w).SupportedOn univ)
    (j : Fin ℓ)
    (hMA : IsPVMIn (MA (QuestionType.hide w j, 0)).op)
    (hMB : IsPVMIn (MB (QuestionType.read w, 0)).op) {δ : ℝ}
    (hfine : ∑ i, (Ξ.reg (ι → F)).xSqNorm
      (((MA (QuestionType.hide w j, 0)).map (hidingCoarse (L w) j.val)).op i)
      (smulKron 1 (Honest.hideCoarseOp (L w) j.val hL i)) ≤ δ) :
    (∑ a, ∑ z, (Ξ.reg (ι → F)).stateSqNorm
      (((MA (QuestionType.introspect w, 0)).map introFullPair).op a *
          smulKron 1 (Honest.readDualOp (L w) j.val hL z) -
        smulKron 1 (Honest.readDualOp (L w) j.val hL z) *
          ((MA (QuestionType.introspect w, 0)).map introFullPair).op a)) ≤
      16 * ((32 * ((ℓ - j.val : ℕ) : ℝ) ^ 2 + 6) *
        (TypeGraph.edges E X Z ℓ).card * ε + 4 * δ) := by
  let M := (MA (QuestionType.introspect w, 0)).map introFullPair
  let R : POVMIn (Option ((ι → F) × (ι → F))) (Matrix (ι → F) (ι → F) 𝒜) :=
    (Honest.readDualOp_isPVM (L w) j.val hL).toIn.smulKron_one.toPOVMIn
  let B := MB (QuestionType.read w, 0)
  let f := fun a : ParsedAnswer (ι → F) A PauliAnswer =>
    (readFullPair a, reportedDual (L w) j.val .read a)
  have hc := coarse_joint_commutator_bound (Ξ.reg (ι → F)) M R B hMB f
  have hl := introspect_read_full_estimate E X Z P L projectPauli D DP Ξ hΞ MA MB hfail w
  have hr := read_register_rigidity_bob E X Z P L projectPauli D DP Ξ hΞ MA MB hfail
    w hL j hMA hfine
  have hleft : coarseJointLeftError (Ξ.reg (ι → F)) M B f ≤
      2 * (TypeGraph.edges E X Z ℓ).card * ε := by
    simpa only [coarseJointLeftError, M, B, f, POVMIn.sum_op_map_prod] using hl
  have hright : coarseJointRightError (Ξ.reg (ι → F)) R B f ≤
      (32 * ((ℓ - j.val : ℕ) : ℝ) ^ 2 + 4) * (TypeGraph.edges E X Z ℓ).card * ε + 4 * δ := by
    simpa only [coarseJointRightError, R, B, f, POVMIn.sum_op_map_prod',
      IsPVMIn.toPOVMIn_op] using hr
  change (∑ a, ∑ z, (Ξ.reg (ι → F)).stateSqNorm (M.op a * R.op z - R.op z * M.op a)) ≤ _
  linarith only [hc, hleft, hright]

end MIPRE.Introspection.TypedEstimates

end

end

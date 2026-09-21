/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.ReadChainEstimate
import MIPRE.Foundations.Introspection.ConditionalNormalizerStepAux

/-! # Read rigidity from the full hiding family

First discard the unused X tail across the two players, using projective
consistency. Then transport the resulting fixed dual readout along the actual
hiding-to-Read chain. No same-party coarse-distance contraction is used.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical
set_option linter.unusedSectionVars false

namespace Honest

variable {F ι H K : Type*}
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}

/-- The ideal joint prefix/dual measurement, with the unused X tail summed out. -/
def readDualOp (P : CL.CLFun F ι ℓ) (k : ℕ) (h : P.SupportedOn univ) :=
  fibSum (hideCoarseOp P k h) TypedEstimates.hidingForgetTail

theorem readDualOp_isPVM (P : CL.CLFun F ι ℓ) (k : ℕ) (h : P.SupportedOn univ) :
    IsPVM (readDualOp P k h) :=
  isPVM_fibSum (hideCoarseOp_isPVM P k h) TypedEstimates.hidingForgetTail

theorem readDualOp_registerState_mirror (P : CL.CLFun F ι ℓ) (k : ℕ)
    (h : P.SupportedOn univ) (ξ : H × K → ℂ) (i : Option ((ι → F) × (ι → F))) :
    aOp (aOp (readDualOp P k h i) : Matrix ((ι → F) × H) _ ℂ) *ᵥ registerState (ι → F) ξ =
      bOp (aOp (readDualOp P k h i) : Matrix ((ι → F) × K) _ ℂ) *ᵥ registerState (ι → F) ξ := by
  simpa only [fibSum_aOp, readDualOp] using
    fibSum_mirror (registerState (ι → F) ξ)
      (fun i => (aOp (hideCoarseOp P k h i) : Matrix ((ι → F) × H) _ ℂ))
      (fun i => (aOp (hideCoarseOp P k h i) : Matrix ((ι → F) × K) _ ℂ))
      (hideCoarseOp_registerState_mirror P k h ξ) TypedEstimates.hidingForgetTail i

end Honest

namespace TypedEstimates

variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype A]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}

theorem hidingForgetTail_mapped (P : CL.CLFun F ι ℓ) (j : Fin ℓ)
    (M : POVM (ParsedAnswer (ι → F) A PauliAnswer) H) (z : Option ((ι → F) × (ι → F))) :
    fibSum (fun i => ((M.map (hidingCoarse P j.val)).mats i).val) hidingForgetTail z =
      ((M.map (reportedDual P j.val (.hide j))).mats z).val := by
  rw [fibSum, ← POVM.map_mats, POVM.map_map]
  simp only [hidingForgetTail_coarse]

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

/-- Every Read dual marginal is rigid once the corresponding hiding level is
rigid. All intervening comparisons are supplied by the actual game. -/
theorem read_register_rigidity_alice (w : Bool) (hL : (L w).SupportedOn univ)
    (j : Fin ℓ)
    (hMA : IsPVM (fun a => ((MA (QuestionType.hide w j, 0)).mats a).val)) {δ : ℝ}
    (hfine : ∑ i, xSqNorm (registerState (ι → F) ξ)
      ((((MA (QuestionType.hide w j, 0)).map (hidingCoarse (L w) j.val)).mats i).val)
      (aOp (Honest.hideCoarseOp (L w) j.val hL i) : Matrix ((ι → F) × K) _ ℂ) ≤ δ) :
    (∑ z, xSqNorm (registerState (ι → F) ξ)
      ((((MA (QuestionType.read w, 0)).map (reportedDual (L w) j.val .read)).mats z).val)
      (aOp (Honest.readDualOp (L w) j.val hL z) : Matrix ((ι → F) × K) _ ℂ)) ≤
      16 * ((ℓ - j.val : ℕ) : ℝ) ^ 2 * (TypeGraph.edges E X Z ℓ).card * ε + 2 * δ := by
  have hseed : star (registerEPR (ι → F)) ⬝ᵥ registerEPR (ι → F) = 1 := by
    rw [registerEPR_eq_weyl]
    exact Weyl.epr_unit
  have hunit := expVec_unit hseed hξ
  have hc := sum_xSqNorm_fibSum_le (norm_evec_eq_one_of_unit hunit)
    (isPVM_povm_map (MA (QuestionType.hide w j, 0)) hMA (hidingCoarse (L w) j.val))
    (Honest.hideCoarseOp_isPVM (L w) j.val hL).aOp hidingForgetTail
  have hc' := hc.trans hfine
  simp only [hidingForgetTail_mapped, fibSum_aOp] at hc'
  change (∑ z, xSqNorm (registerState (ι → F) ξ)
    ((((MA (QuestionType.hide w j, 0)).map (reportedDual (L w) j.val (.hide j))).mats z).val)
    (aOp (Honest.readDualOp (L w) j.val hL z) : Matrix ((ι → F) × K) _ ℂ)) ≤ δ at hc'
  have hchain := hiding_read_dual_chain_estimate E X Z P L projectPauli D DP
    (registerState (ι → F) ξ) hunit MA MB hfail w hL j
  let R := (MA (QuestionType.read w, 0)).map (reportedDual (L w) j.val .read)
  let N := (MA (QuestionType.hide w j, 0)).map (reportedDual (L w) j.val (.hide j))
  have ht := sum_snorm_sq_triangle' (registerState (ι → F) ξ)
    (fun z => aOp (R.mats z).val) (fun z => aOp (N.mats z).val)
    (fun z => bOp (aOp (Honest.readDualOp (L w) j.val hL z) : Matrix ((ι → F) × K) _ ℂ))
  simp_rw [← xSqNorm_eq_snorm_sq] at ht
  have hchain' : (∑ z, snorm (registerState (ι → F) ξ)
      (aOp (R.mats z).val - aOp (N.mats z).val) ^ 2) ≤
      ((ℓ - j.val : ℕ) : ℝ) ^ 2 * (8 * (TypeGraph.edges E X Z ℓ).card * ε) := by
    change (∑ z, stateSqNorm (registerState (ι → F) ξ)
      ((N.mats z).val - (R.mats z).val)) ≤ _ at hchain
    simpa only [stateSqNorm, stateNorm, norm_stateVec_eq_snorm, aOp_sub,
      snorm_sub_comm] using hchain
  dsimp only [R, N] at ht hchain'
  linarith only [ht, hc', hchain']

/-- The actual Read consistency loop supplies rigidity on Bob's side too. -/
theorem read_register_rigidity_bob (w : Bool) (hL : (L w).SupportedOn univ)
    (j : Fin ℓ)
    (hMA : IsPVM (fun a => ((MA (QuestionType.hide w j, 0)).mats a).val)) {δ : ℝ}
    (hfine : ∑ i, xSqNorm (registerState (ι → F) ξ)
      ((((MA (QuestionType.hide w j, 0)).map (hidingCoarse (L w) j.val)).mats i).val)
      (aOp (Honest.hideCoarseOp (L w) j.val hL i) : Matrix ((ι → F) × K) _ ℂ) ≤ δ) :
    (∑ z, xSqNorm (registerState (ι → F) ξ)
      (aOp (Honest.readDualOp (L w) j.val hL z) : Matrix ((ι → F) × H) _ ℂ)
      ((((MB (QuestionType.read w, 0)).map (reportedDual (L w) j.val .read)).mats z).val)) ≤
      (32 * ((ℓ - j.val : ℕ) : ℝ) ^ 2 + 4) * (TypeGraph.edges E X Z ℓ).card * ε + 4 * δ := by
  have hseed : star (registerEPR (ι → F)) ⬝ᵥ registerEPR (ι → F) = 1 := by
    rw [registerEPR_eq_weyl]
    exact Weyl.epr_unit
  have hunit := expVec_unit hseed hξ
  have ha := read_register_rigidity_alice E X Z P L projectPauli D DP ξ hξ MA MB hfail
    w hL j hMA hfine
  let R := (MA (QuestionType.read w, 0)).map (reportedDual (L w) j.val .read)
  let N := (MB (QuestionType.read w, 0)).map (reportedDual (L w) j.val .read)
  have hloop := aux_agreement_estimate E X Z P (questionCheck L X Z projectPauli D DP)
    (registerState (ι → F) ξ) hunit MA MB hfail .read .read w w
    (TypeGraph.adj_self E X Z (QuestionType.read w))
    (reportedDual (L w) j.val .read) (reportedDual (L w) j.val .read)
    (fun a b hab => congrArg (reportedDual (L w) j.val .read)
      (TypedPredicate.check_consistency L X Z projectPauli D (fun p s => DP p s 0 0) hab))
  have he z : snorm (registerState (ι → F) ξ)
      (aOp (aOp (Honest.readDualOp (L w) j.val hL z) : Matrix ((ι → F) × H) _ ℂ) -
        aOp (R.mats z).val) ^ 2 =
      xSqNorm (registerState (ι → F) ξ) (R.mats z).val
        (aOp (Honest.readDualOp (L w) j.val hL z) : Matrix ((ι → F) × K) _ ℂ) := by
    rw [xSqNorm_eq_snorm_sq]
    simp only [snorm, Matrix.sub_mulVec,
      Honest.readDualOp_registerState_mirror (L w) j.val hL ξ, evec_sub]
    rw [norm_sub_rev]
  have ht := sum_snorm_sq_triangle' (registerState (ι → F) ξ)
    (fun z => aOp (aOp (Honest.readDualOp (L w) j.val hL z) : Matrix ((ι → F) × H) _ ℂ))
    (fun z => aOp (R.mats z).val) (fun z => bOp (N.mats z).val)
  simp only [he, ← xSqNorm_eq_snorm_sq] at ht
  dsimp only [R, N] at ht
  linarith only [ht, ha, hloop]

end TypedEstimates
end MIPRE.Introspection

end

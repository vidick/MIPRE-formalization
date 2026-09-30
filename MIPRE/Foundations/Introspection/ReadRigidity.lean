/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.ReadChainEstimate
public import MIPRE.Foundations.Introspection.ConditionalNormalizerStepAux

@[expose] public section

/-! # Read rigidity from the full hiding family

First discard the unused X tail across the two players, using projective
consistency. Then transport the resulting fixed dual readout along the actual
hiding-to-Read chain. No same-party coarse-distance contraction is used.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the EPR seed beside an
arbitrary auxiliary state is the register model `Ξ.reg (ι → F)` of a normalized model `Ξ`, the
strategy is a pair of POVM families of matrices over `ι → F` with entries in `Ξ`'s algebras, and
the honest dual readout `readDualOp`, a complex register matrix, acts as `smulKron 1 _` for either
player. Its exact mirror is the vector identity `π (πA _) ψ = π (πB _) ψ`, coarse-grained from the
mirror of the hiding family by `fibSum_mirror`; coarse-graining a POVM of the model is
`POVMIn.map`, and of an embedded register family `fibSumIn_smulKron_one`.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical
set_option linter.unusedSectionVars false

namespace Honest

variable {F ι : Type*}
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

/-- The ideal joint prefix/dual measurement, with the unused X tail summed out. -/
def readDualOp (P : CL.CLFun F ι ℓ) (k : ℕ) (h : P.SupportedOn univ) :=
  fibSum (hideCoarseOp P k h) TypedEstimates.hidingForgetTail

theorem readDualOp_isPVM (P : CL.CLFun F ι ℓ) (k : ℕ) (h : P.SupportedOn univ) :
    IsPVM (readDualOp P k h) :=
  isPVM_fibSum (hideCoarseOp_isPVM P k h) TypedEstimates.hidingForgetTail

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]

/-- The ideal dual readout is an exact mirror of itself on the register model of any bipartite
auxiliary model. -/
theorem readDualOp_registerState_mirror (P : CL.CLFun F ι ℓ) (k : ℕ)
    (h : P.SupportedOn univ) (Ξ : BipartiteModel 𝒞 𝒜 ℬ) (i : Option ((ι → F) × (ι → F))) :
    (Ξ.reg (ι → F)).π ((Ξ.reg (ι → F)).πA (smulKron 1 (readDualOp P k h i)))
        (Ξ.reg (ι → F)).ψ =
      (Ξ.reg (ι → F)).π ((Ξ.reg (ι → F)).πB (smulKron 1 (readDualOp P k h i)))
        (Ξ.reg (ι → F)).ψ := by
  simpa only [fibSumIn_smulKron_one, readDualOp, fibSum_eq_fibSumIn] using
    fibSum_mirror (Ξ.reg (ι → F)) (fun i => smulKron 1 (hideCoarseOp P k h i))
      (fun i => smulKron 1 (hideCoarseOp P k h i))
      (hideCoarseOp_registerState_mirror P k h Ξ) TypedEstimates.hidingForgetTail i

end Honest

namespace TypedEstimates

variable {PauliType PauliAnswer F ι κ A : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype A] {ℓ : ℕ}

/-- Forgetting the unused X tail of the coarse Hide measurement leaves its reported dual readout,
for a POVM in any ordered `⋆`-ring. -/
theorem hidingForgetTail_mapped (P : CL.CLFun F ι ℓ) (j : Fin ℓ)
    {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
    (M : POVMIn (ParsedAnswer (ι → F) A PauliAnswer) R) (z : Option ((ι → F) × (ι → F))) :
    fibSumIn (M.map (hidingCoarse P j.val)).op hidingForgetTail z =
      (M.map (reportedDual P j.val (.hide j))).op z := by
  rw [fibSumIn, ← POVMIn.map_op, POVMIn.map_map]
  simp only [hidingForgetTail_coarse]

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
  {ε : ℝ}
  (hfail : 1 - (Ξ.reg (ι → F)).povmValue (parsedGame E X Z P L projectPauli D DP) MA MB ≤ ε)

include hΞ hfail

/-- Every Read dual marginal is rigid once the corresponding hiding level is
rigid. All intervening comparisons are supplied by the actual game. -/
theorem read_register_rigidity_alice (w : Bool) (hL : (L w).SupportedOn univ)
    (j : Fin ℓ)
    (hMA : IsPVMIn (MA (QuestionType.hide w j, 0)).op) {δ : ℝ}
    (hfine : ∑ i, (Ξ.reg (ι → F)).xSqNorm
      (((MA (QuestionType.hide w j, 0)).map (hidingCoarse (L w) j.val)).op i)
      (smulKron 1 (Honest.hideCoarseOp (L w) j.val hL i)) ≤ δ) :
    (∑ z, (Ξ.reg (ι → F)).xSqNorm
      (((MA (QuestionType.read w, 0)).map (reportedDual (L w) j.val .read)).op z)
      (smulKron 1 (Honest.readDualOp (L w) j.val hL z))) ≤
      16 * ((ℓ - j.val : ℕ) : ℝ) ^ 2 * (TypeGraph.edges E X Z ℓ).card * ε + 2 * δ := by
  have hunit : ‖(Ξ.reg (ι → F)).ψ‖ = 1 := by rw [BipartiteModel.norm_reg_ψ, hΞ]
  have hc := (Ξ.reg (ι → F)).sum_xSqNorm_fibSum_le hunit
    (POVMIn.isPVMIn_map hMA (hidingCoarse (L w) j.val))
    (Honest.hideCoarseOp_isPVM (L w) j.val hL).toIn.smulKron_one hidingForgetTail
  have hc' := hc.trans hfine
  simp only [hidingForgetTail_mapped, fibSumIn_smulKron_one, ← fibSum_eq_fibSumIn] at hc'
  change (∑ z, (Ξ.reg (ι → F)).xSqNorm
    (((MA (QuestionType.hide w j, 0)).map (reportedDual (L w) j.val (.hide j))).op z)
    (smulKron 1 (Honest.readDualOp (L w) j.val hL z))) ≤ δ at hc'
  have hchain := hiding_read_dual_chain_estimate E X Z P L projectPauli D DP
    (Ξ.reg (ι → F)) hunit MA MB hfail w hL j
  let R := (MA (QuestionType.read w, 0)).map (reportedDual (L w) j.val .read)
  let N := (MA (QuestionType.hide w j, 0)).map (reportedDual (L w) j.val (.hide j))
  have ht := (Ξ.reg (ι → F)).sum_snorm_sq_triangle univ
    (fun z => (Ξ.reg (ι → F)).πA (R.op z)) (fun z => (Ξ.reg (ι → F)).πA (N.op z))
    (fun z => (Ξ.reg (ι → F)).πB (smulKron 1 (Honest.readDualOp (L w) j.val hL z)))
  have hchain' : (∑ z, (Ξ.reg (ι → F)).snorm
      ((Ξ.reg (ι → F)).πA (R.op z) - (Ξ.reg (ι → F)).πA (N.op z)) ^ 2) ≤
      ((ℓ - j.val : ℕ) : ℝ) ^ 2 * (8 * (TypeGraph.edges E X Z ℓ).card * ε) := by
    refine (Finset.sum_congr rfl fun z _ => ?_).trans_le hchain
    rw [BipartiteModel.stateSqNorm_sub_comm, BipartiteModel.stateSqNorm,
      BipartiteModel.stateNorm, map_sub]
  simp only [BipartiteModel.xSqNorm, BipartiteModel.xNorm] at hc' ⊢
  dsimp only [R, N] at ht hchain'
  linarith only [ht, hc', hchain']

/-- The actual Read consistency loop supplies rigidity on Bob's side too. -/
theorem read_register_rigidity_bob (w : Bool) (hL : (L w).SupportedOn univ)
    (j : Fin ℓ)
    (hMA : IsPVMIn (MA (QuestionType.hide w j, 0)).op) {δ : ℝ}
    (hfine : ∑ i, (Ξ.reg (ι → F)).xSqNorm
      (((MA (QuestionType.hide w j, 0)).map (hidingCoarse (L w) j.val)).op i)
      (smulKron 1 (Honest.hideCoarseOp (L w) j.val hL i)) ≤ δ) :
    (∑ z, (Ξ.reg (ι → F)).xSqNorm (smulKron 1 (Honest.readDualOp (L w) j.val hL z))
      (((MB (QuestionType.read w, 0)).map (reportedDual (L w) j.val .read)).op z)) ≤
      (32 * ((ℓ - j.val : ℕ) : ℝ) ^ 2 + 4) * (TypeGraph.edges E X Z ℓ).card * ε + 4 * δ := by
  have hunit : ‖(Ξ.reg (ι → F)).ψ‖ = 1 := by rw [BipartiteModel.norm_reg_ψ, hΞ]
  have ha := read_register_rigidity_alice E X Z P L projectPauli D DP Ξ hΞ MA MB hfail
    w hL j hMA hfine
  let R := (MA (QuestionType.read w, 0)).map (reportedDual (L w) j.val .read)
  let N := (MB (QuestionType.read w, 0)).map (reportedDual (L w) j.val .read)
  have hloop := aux_agreement_estimate E X Z P (questionCheck L X Z projectPauli D DP)
    (Ξ.reg (ι → F)) hunit MA MB hfail .read .read w w
    (TypeGraph.adj_self E X Z (QuestionType.read w))
    (reportedDual (L w) j.val .read) (reportedDual (L w) j.val .read)
    (fun a b hab => congrArg (reportedDual (L w) j.val .read)
      (TypedPredicate.check_consistency L X Z projectPauli D (fun p s => DP p s 0 0) hab))
  have he z : (Ξ.reg (ι → F)).snorm
      ((Ξ.reg (ι → F)).πA (smulKron 1 (Honest.readDualOp (L w) j.val hL z)) -
        (Ξ.reg (ι → F)).πA (R.op z)) ^ 2 =
      (Ξ.reg (ι → F)).xSqNorm (R.op z) (smulKron 1 (Honest.readDualOp (L w) j.val hL z)) := by
    rw [BipartiteModel.xSqNorm, BipartiteModel.xNorm, StateModel.snorm_sub_comm]
    simp only [StateModel.snorm, Op.snorm, map_sub, _root_.sub_apply,
      Honest.readDualOp_registerState_mirror (L w) j.val hL Ξ z]
  have ht := (Ξ.reg (ι → F)).sum_snorm_sq_triangle univ
    (fun z => (Ξ.reg (ι → F)).πA (smulKron 1 (Honest.readDualOp (L w) j.val hL z)))
    (fun z => (Ξ.reg (ι → F)).πA (R.op z)) (fun z => (Ξ.reg (ι → F)).πB (N.op z))
  simp only [he] at ht
  simp only [BipartiteModel.xSqNorm, BipartiteModel.xNorm] at ht ha hloop ⊢
  dsimp only [R, N] at ht
  linarith only [ht, ha, hloop]

end TypedEstimates
end MIPRE.Introspection

end

end

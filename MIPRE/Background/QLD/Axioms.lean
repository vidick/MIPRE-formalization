/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.Anticomm
import MIPRE.Background.QLD.Consistency
import MIPRE.Background.QLD.Expanded
import MIPRE.Background.QLD.Combined
import MIPRE.Foundations.GuardSorryFree

/-!
# Axiom audit for the Pauli basis test's orthonormalization step

`MIPRE/Background/QLD/` is this project's own mathematics, like the seeded-CL adapter of
`MIPRE/Background/LIDT/Adapter/`; it sits under `MIPRE/Background/` because it reaches into the
vendored orthonormalization development, and its guards are cheapest here, where the imports are
already paid for. `scripts/lean-coverage.py` reads every guard file and checks that the names
guarded are exactly the names the blueprint marks with a proof-level `\leanok`, so which file a
name sits in does not change what is claimed.

Blueprint `cor:ortho-from-consistency`. Printing the axioms in full is worth it here: it says
that the corollary rests on the vendored de la Salle theorem and the three standard axioms, and
in particular that the compactness step the paper's proof ends with --- which this repository
does not formalize, and which the corollary's comments explain away --- contributes nothing.
-/

/--
info: 'MIPRE.QLD.exists_projective_of_consistent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MIPRE.QLD.exists_projective_of_consistent

/-! ## The Magic Square's anticommutation input

Blueprint `lem:ms-direct-anticomm`. Both halves and the averaged form; `anti` is the
anticommutator the statement is about. -/

/--
info: 'MIPRE.QLD.MS.anti' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MIPRE.QLD.MS.anti

/--
info: 'MIPRE.QLD.MS.ms_direct_anticomm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MIPRE.QLD.MS.ms_direct_anticomm

/--
info: 'MIPRE.QLD.MS.ms_direct_anticomm'' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MIPRE.QLD.MS.ms_direct_anticomm'

/--
info: 'MIPRE.QLD.MS.ms_direct_anticomm_avg' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MIPRE.QLD.MS.ms_direct_anticomm_avg

/-! ## What winning the Pauli basis test implies

Blueprint `lem:qld-win`. The seven items, and the supporting vocabulary the proof of each one
runs through. `#guard_sorry_free` rather than `#print axioms` here: the list mixes definitions
with theorems, and their axiom lists differ. -/

#guard_sorry_free MIPRE.QLD.subtest_le,
  MIPRE.QLD.agree_subtest_le,
  MIPRE.QLD.item_consistency,
  MIPRE.QLD.item_lowDeg_aline,
  MIPRE.QLD.item_lowDeg_dline,
  MIPRE.QLD.item_pauli_consistency,
  MIPRE.QLD.item_commutation,
  MIPRE.QLD.item_commutation_consistency,
  MIPRE.QLD.item_ms_consistency_X,
  MIPRE.QLD.item_ms_consistency_Z,
  MIPRE.QLD.msPOVM,
  MIPRE.QLD.msEps,
  MIPRE.QLD.condFail_ms_le,
  MIPRE.QLD.one_sub_povmValue_ms_le,
  MIPRE.QLD.sum_msEps_le,
  MIPRE.QLD.item_magicSquare

-- blueprint `lem:qld-obs-consistency`
#guard_sorry_free MIPRE.QLD.pts_obs_consistency

/-! ## Signed commutation, the anticommuting case

Blueprint `lem:qld-obs-commutation-acomm`. The two point observables and the two variable
observables they are tied to, the sub-probability weight the items carry, item 7 in observable
form, the identification of item 6's anticommutator, and the lemma. -/

/-! ## The expansion stage's commutation

Blueprint `lem:qld-expanded-commutation`. The sign the strategy carries and the sign the ancilla
carries are the same sign, and they cancel identically. -/

#guard_sorry_free MIPRE.QLD.Anc,
  MIPRE.QLD.weylOf,
  MIPRE.QLD.ancVec,
  MIPRE.QLD.gam_eq_trDot,
  MIPRE.QLD.weylOf_isUnitary,
  MIPRE.QLD.weylOf_prod_isUnitary,
  MIPRE.QLD.hatObs,
  MIPRE.QLD.hatVec,
  MIPRE.QLD.norm_evec_epr,
  MIPRE.QLD.hatVec_unit,
  MIPRE.QLD.hatObs_comm_eq,
  MIPRE.QLD.norm_hatVec_hatObs_comm,
  MIPRE.QLD.hatObs_commutation,
  MIPRE.QLD.synPOVM,
  MIPRE.QLD.synPOVM_mats,
  MIPRE.QLD.weylOf_transpose,
  MIPRE.QLD.sum_bornProb_epr_synPOVM,
  MIPRE.QLD.ptValPOVM,
  MIPRE.QLD.hatPOVM,
  MIPRE.QLD.sum_xSqNorm_hatPOVM_le,
  MIPRE.QLD.hatPOVM_consistency,
  MIPRE.QLD.expanded_points

/-! ## The expansion stage: the hatted line measurements

Blueprint `lem:qld-expanded-lines`. The convolution of the strategy's line measurement with the
ancilla measurement that reports the restriction of the encoding to the line; its projectivity, its
self-consistency, and its consistency with the hatted point measurements. -/

#guard_sorry_free MIPRE.QLD.lineCoeffs,
  MIPRE.QLD.eval_lineCoeffs,
  MIPRE.QLD.dotF_indVec,
  MIPRE.QLD.padLine,
  MIPRE.QLD.linePoly_eval_eq_range,
  MIPRE.QLD.eval_padLine,
  MIPRE.QLD.rdLine,
  MIPRE.QLD.synLinePOVM,
  MIPRE.QLD.synLinePOVM_map_eval,
  MIPRE.QLD.lineAnsPOVM,
  MIPRE.QLD.hatLinePOVM,
  MIPRE.QLD.isPVM_hatLinePOVM,
  MIPRE.QLD.hatLinePOVM_map_eval,
  MIPRE.QLD.sum_xSqNorm_hatLinePOVM_le,
  MIPRE.QLD.hatLinePOVM_consistency,
  MIPRE.QLD.Content.omega_pt,
  MIPRE.QLD.sum_xSqNorm_hatLine_point_le,
  MIPRE.QLD.rep_add_lineParam_smul,
  MIPRE.QLD.abaseOf,
  MIPRE.QLD.ddirOf,
  MIPRE.QLD.dbaseOf,
  MIPRE.QLD.d_le_mul,
  MIPRE.QLD.m_le_mul,
  MIPRE.QLD.hsub_aline,
  MIPRE.QLD.hsub_dline,
  MIPRE.QLD.hatLinePOVM_point_consistency,
  MIPRE.QLD.expanded_lines_aline,
  MIPRE.QLD.expanded_lines_dline

/-! ## Signed commutation: both halves

Blueprint `lem:qld-obs-commutation`, `lem:qld-obs-commutation-comm` and
`lem:qld-obs-commutation-acomm`. The commuting half runs the chain through the `Pair` measurement,
projectivizes it, and applies the commutation analysis; the anticommuting half is the Magic
Square's anticommutator carried across the tensor factors. -/

#guard_sorry_free MIPRE.QLD.pairPOVM,
  MIPRE.QLD.pairPOVMB,
  MIPRE.QLD.ptPOVM,
  MIPRE.QLD.ptPOVMB,
  MIPRE.QLD.ptObsB,
  MIPRE.QLD.ptObs_eq_obs2,
  MIPRE.QLD.ptObsB_mul_self_le_one,
  MIPRE.QLD.sum_pairPOVM_X,
  MIPRE.QLD.sum_pairPOVM_Z,
  MIPRE.QLD.adj_pairB_point,
  MIPRE.QLD.link_pairB_point,
  MIPRE.QLD.link_pair_pair,
  MIPRE.QLD.chain_pair_point,
  MIPRE.QLD.chainQty,
  MIPRE.QLD.incQty,
  MIPRE.QLD.chainQty_nonneg,
  MIPRE.QLD.incQty_nonneg,
  MIPRE.QLD.commWeight,
  MIPRE.QLD.commWeight_nonneg,
  MIPRE.QLD.sum_commWeight_mul,
  MIPRE.QLD.sum_commWeight_le_one,
  MIPRE.QLD.xStateDist_ptObs_ptObsB,
  MIPRE.QLD.pairInconsistency_nonneg,
  MIPRE.QLD.incQty_le_condFail,
  MIPRE.QLD.sum_incQty_le,
  MIPRE.QLD.sq_norm_ptObs_comm_le_of_content,
  MIPRE.QLD.sum_chainQty_le,
  MIPRE.QLD.comm_signed_commutation,
  MIPRE.QLD.signed_commutation

#guard_sorry_free MIPRE.QLD.ptObs,
  MIPRE.QLD.varObs,
  MIPRE.QLD.ptObs_mul_self_le_one,
  MIPRE.QLD.varObs_mul_self_le_one,
  MIPRE.QLD.acommWeight,
  MIPRE.QLD.acommWeight_nonneg,
  MIPRE.QLD.sum_acommWeight_mul,
  MIPRE.QLD.xStateDist_ptObs_varObs_X,
  MIPRE.QLD.xStateDist_ptObs_varObs_Z,
  MIPRE.QLD.question_var,
  MIPRE.QLD.mats_msPOVM_var,
  MIPRE.QLD.bobs_msPOVM,
  MIPRE.QLD.anti_eq_varObs,
  MIPRE.QLD.sq_norm_ptObs_anticomm_le,
  MIPRE.QLD.acomm_signed_commutation

/-! ## The combining stage: the joint `XZ` point measurement

Blueprint `lem:qld-combined-points`. The hatted point measurement re-indexed by the point, its
observable family and the transform between them, Parseval for the commutator, the content split
that makes the probe average free, the two players' commutation inputs, and the lemma. -/

#guard_sorry_free MIPRE.QLD.pairTest_symm,
  MIPRE.QLD.accepts_symm,
  MIPRE.QLD.qldGame_mu_symm,
  MIPRE.QLD.povmValue_qldGame_swapVec,
  MIPRE.QLD.hatVec_swapVec,
  MIPRE.QLD.hatPtPOVM,
  MIPRE.QLD.hatPOVM_eq,
  MIPRE.QLD.hatMats,
  MIPRE.QLD.hatObsAt,
  MIPRE.QLD.hatObsAt_eq,
  MIPRE.QLD.trObs_ptVal,
  MIPRE.QLD.trObs_synPOVM,
  MIPRE.QLD.hatObsAt_self,
  MIPRE.QLD.hatComm,
  MIPRE.QLD.hatComm_eq_fourierOf,
  MIPRE.QLD.sum_stateSqNorm_hatComm,
  MIPRE.QLD.isPVM_hatMats,
  MIPRE.QLD.sum_content_split,
  MIPRE.QLD.sum_content_avg_probe,
  MIPRE.QLD.sum_content_hatComm_le,
  MIPRE.QLD.sum_content_hatComm_le_B,
  MIPRE.QLD.sum_content_hatMats_consistency,
  MIPRE.QLD.deltaQ,
  MIPRE.QLD.combined_points

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.Anticomm
import MIPRE.Background.QLD.Consistency
import MIPRE.Background.QLD.Expanded
import MIPRE.Background.QLD.Combined
import MIPRE.Background.QLD.Lines
import MIPRE.Background.QLD.Padded
import MIPRE.Background.QLD.PaddedLines
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

/-! ## The padded point measurement

Blueprint `lem:qld-padded-points`. The combined measurement coarse-grained along
`(a, b) |-> alpha a + beta b`, Bob's two ordered products and their completeness, the Parseval
identity for the coarse-graining, and the lemma. -/

#guard_sorry_free MIPRE.QLD.hatOrdZX,
  MIPRE.QLD.hatOrdXZ,
  MIPRE.QLD.sum_hatOrdZX,
  MIPRE.QLD.sum_hatOrdXZ,
  MIPRE.QLD.sum_avg_xSqNorm_fibre_eq,
  MIPRE.QLD.padded_points

/-! ## Pairs of lines

Blueprint `lem:qld-pairs-of-lines`. The bridge from coefficient vectors to Mathlib's polynomials
and the collision count it gives; the content shift, which is what turns the content distribution
into the product the pasting lemma's collision term needs, and the same device applied to the raw
direction, which is what makes a degenerate diagonal line rare; the line presentations and their
invariances; the marginal step at the QLD point measurements; and the lemma, both for an arbitrary
pair of presentations and with every input discharged from the game. -/

#guard_sorry_free MIPRE.QLD.toPoly,
  MIPRE.QLD.natDegree_toPoly_le,
  MIPRE.QLD.eval_toPoly,
  MIPRE.QLD.coeff_toPoly,
  MIPRE.QLD.toPoly_injective,
  MIPRE.QLD.card_agree_linePoly_le,
  MIPRE.QLD.lineParam_add_smul,
  MIPRE.QLD.rep_add_smul,
  MIPRE.QLD.Content.shiftPt,
  MIPRE.QLD.Content.shiftAlong,
  MIPRE.QLD.Content.shiftV,
  MIPRE.QLD.bijective_shift,
  MIPRE.QLD.sum_shift_gen,
  MIPRE.QLD.bijective_shift_gen,
  MIPRE.QLD.sum_content_shift_gen,
  MIPRE.QLD.sum_content_shiftAlong,
  MIPRE.QLD.dirOf_shiftPt,
  MIPRE.QLD.ddirOf_shiftPt,
  MIPRE.QLD.abaseOf_shiftAlong,
  MIPRE.QLD.dbaseOf_shiftAlong,
  MIPRE.QLD.question_aline_shiftAlong,
  MIPRE.QLD.question_dline_shiftAlong,
  MIPRE.QLD.hatLinePOVM_congr,
  MIPRE.QLD.LinePres,
  MIPRE.QLD.LinePres.param,
  MIPRE.QLD.LinePres.param_shiftAlong,
  MIPRE.QLD.LinePres.lineMats,
  MIPRE.QLD.LinePres.lineEvalMats,
  MIPRE.QLD.LinePres.isPVM_lineMats,
  MIPRE.QLD.LinePres.isPVM_lineEvalMats,
  MIPRE.QLD.LinePres.lineEvalMats_eq_fibSum,
  MIPRE.QLD.LinePres.lineMats_shiftAlong,
  MIPRE.QLD.LinePres.lineEvalMats_shiftPt_other,
  MIPRE.QLD.aPres,
  MIPRE.QLD.dPres,
  MIPRE.QLD.aPres_dir_ne_zero,
  MIPRE.QLD.collProb,
  MIPRE.QLD.card_collide_le,
  MIPRE.QLD.sum_content_degenerate_le,
  MIPRE.QLD.sum_content_collProb_aPres,
  MIPRE.QLD.sum_content_collProb_dPres,
  MIPRE.QLD.valOf,
  MIPRE.QLD.pairEquiv,
  MIPRE.QLD.extHat,
  MIPRE.QLD.sum_content_normSq_point_line_le,
  MIPRE.QLD.sum_xSqNorm_marg_point_le,
  MIPRE.QLD.sum_xSqNorm_marg_line_le_aux,
  MIPRE.QLD.sum_content_marg_line_le,
  MIPRE.QLD.pasteLine,
  MIPRE.QLD.fibSum_aOp,
  MIPRE.QLD.pasteJ_eq_pasteLine,
  MIPRE.QLD.pairs_of_lines_gen,
  MIPRE.QLD.pairs_of_lines,
  MIPRE.QLD.kappaPairs,
  MIPRE.QLD.deltaPairsD,
  MIPRE.QLD.deltaPairs,
  MIPRE.QLD.pairs_of_lines_of_items,
  MIPRE.QLD.aPres_items,
  MIPRE.QLD.dPres_items,
  MIPRE.QLD.qld_pairs_of_lines

/-! ## The sublines of a padded line

Blueprint `lem:qld-sublines`. The seed's block and offset; the blocks of the padded space and the
four-way case distinction on a coordinate position; the sampling procedure and the containment it is
built to satisfy; and the law, as four identities of averages, one per case of the construction. -/

#guard_sorry_free MIPRE.QLD.mul_card_div,
  MIPRE.QLD.seedEquiv,
  MIPRE.QLD.seedEquiv_fst,
  MIPRE.QLD.seedIn,
  MIPRE.QLD.chi_seedIn,
  MIPRE.QLD.seedIn_self,
  MIPRE.QLD.sum_seedIn,
  MIPRE.QLD.xIdx,
  MIPRE.QLD.zIdx,
  MIPRE.QLD.aIdx,
  MIPRE.QLD.bIdx,
  MIPRE.QLD.xIdx_val,
  MIPRE.QLD.zIdx_val,
  MIPRE.QLD.aIdx_val,
  MIPRE.QLD.bIdx_val,
  MIPRE.QLD.xIdx_injective,
  MIPRE.QLD.zIdx_injective,
  MIPRE.QLD.xIdx_ne_zIdx,
  MIPRE.QLD.xIdx_ne_aIdx,
  MIPRE.QLD.xIdx_ne_bIdx,
  MIPRE.QLD.zIdx_ne_aIdx,
  MIPRE.QLD.zIdx_ne_bIdx,
  MIPRE.QLD.aIdx_ne_bIdx,
  MIPRE.QLD.xBlk,
  MIPRE.QLD.zBlk,
  MIPRE.QLD.alph,
  MIPRE.QLD.bet,
  MIPRE.QLD.xBlk_apply,
  MIPRE.QLD.zBlk_apply,
  MIPRE.QLD.xBlk_zero,
  MIPRE.QLD.zBlk_zero,
  MIPRE.QLD.xBlk_add,
  MIPRE.QLD.zBlk_add,
  MIPRE.QLD.xBlk_smul,
  MIPRE.QLD.zBlk_smul,
  MIPRE.QLD.alph_add,
  MIPRE.QLD.bet_add,
  MIPRE.QLD.alph_smul,
  MIPRE.QLD.bet_smul,
  MIPRE.QLD.xBlk_add_smul,
  MIPRE.QLD.zBlk_add_smul,
  MIPRE.QLD.PadCase,
  MIPRE.QLD.padCase,
  MIPRE.QLD.padCase_eq_xc,
  MIPRE.QLD.padCase_eq_zc,
  MIPRE.QLD.padCase_xIdx,
  MIPRE.QLD.padCase_zIdx,
  MIPRE.QLD.padCase_aIdx,
  MIPRE.QLD.padCase_bIdx,
  MIPRE.QLD.le_of_padCase_zc,
  MIPRE.QLD.le_of_padCase_ab,
  MIPRE.QLD.le_of_padCase_dum,
  MIPRE.QLD.xBlk_single_xIdx,
  MIPRE.QLD.xBlk_single_of_le,
  MIPRE.QLD.zBlk_single_zIdx,
  MIPRE.QLD.zBlk_single_of_lt,
  MIPRE.QLD.zBlk_single_of_ge,
  MIPRE.QLD.xBlk_zeroBelow_of_le,
  MIPRE.QLD.xBlk_zeroBelow_xIdx,
  MIPRE.QLD.zBlk_zeroBelow_of_le,
  MIPRE.QLD.zBlk_zeroBelow_zIdx,
  MIPRE.QLD.zBlk_zeroBelow_of_ge,
  MIPRE.QLD.LPData,
  MIPRE.QLD.zeroBelow_zero,
  MIPRE.QLD.LPData.toSample,
  MIPRE.QLD.LPData.question,
  MIPRE.QLD.LPData.dir,
  MIPRE.QLD.LPData.dir_point,
  MIPRE.QLD.LPData.dir_aline,
  MIPRE.QLD.LPData.dir_dline,
  MIPRE.QLD.LPData.base_aline,
  MIPRE.QLD.LPData.base_dline,
  MIPRE.QLD.subXof,
  MIPRE.QLD.subX,
  MIPRE.QLD.subZof,
  MIPRE.QLD.subZ,
  MIPRE.QLD.subXof_xc,
  MIPRE.QLD.subXof_zc,
  MIPRE.QLD.subXof_ab,
  MIPRE.QLD.subXof_dum,
  MIPRE.QLD.subZof_dline_xc,
  MIPRE.QLD.subZof_point_xc,
  MIPRE.QLD.subZof_aline_xc,
  MIPRE.QLD.subZof_zc,
  MIPRE.QLD.subZof_ab,
  MIPRE.QLD.subZof_dum,
  MIPRE.QLD.subX_pt,
  MIPRE.QLD.subZ_pt,
  MIPRE.QLD.xBlk_dir_sub,
  MIPRE.QLD.zBlk_dir_sub,
  MIPRE.QLD.on_line_of_eq_or_zero,
  MIPRE.QLD.xBlk_on_subX,
  MIPRE.QLD.zBlk_on_subZ,
  MIPRE.QLD.xBlk_on_subX_aline,
  MIPRE.QLD.xBlk_on_subX_dline,
  MIPRE.QLD.zBlk_on_subZ_aline,
  MIPRE.QLD.zBlk_on_subZ_dline,
  MIPRE.QLD.subX_question_aline,
  MIPRE.QLD.subZ_question_aline,
  MIPRE.QLD.PadSum,
  MIPRE.QLD.padEquiv,
  MIPRE.QLD.padEquiv_inl_inl,
  MIPRE.QLD.padEquiv_inl_inr,
  MIPRE.QLD.padEquiv_symm_xIdx,
  MIPRE.QLD.padEquiv_symm_zIdx,
  MIPRE.QLD.sum_point_pad,
  MIPRE.QLD.sum_point_pad_x,
  MIPRE.QLD.sum_point_pad_z,
  MIPRE.QLD.sumRestr,
  MIPRE.QLD.sumAll,
  MIPRE.QLD.sumAll_eq_sum_sumRestr,
  MIPRE.QLD.sumSub,
  MIPRE.QLD.sumSub_free,
  MIPRE.QLD.sumSub_zc,
  MIPRE.QLD.sumSub_xc,
  MIPRE.QLD.sumSub_xc_dline,
  MIPRE.QLD.avgAll,
  MIPRE.QLD.avgRestr,
  MIPRE.QLD.avgSub,
  MIPRE.QLD.sumAll_const_mul,
  MIPRE.QLD.sumRestr_const_mul,
  MIPRE.QLD.cast_card_div,
  MIPRE.QLD.avgSub_free,
  MIPRE.QLD.avgSub_zc,
  MIPRE.QLD.avgSub_xc,
  MIPRE.QLD.avgSub_xc_dline

/-! ## The padded line measurement

Blueprint `lem:qld-padded-lines`. The content/product transfer and the product form of the
pairs-of-lines lemma; the combining map, its two degree bounds and the measurement it defines; the
restricted laws and the domination of the padded law by the product law; and the consistency bound in
both register versions. -/

#guard_sorry_free MIPRE.QLD.Content.lpX,
  MIPRE.QLD.Content.lpZ,
  MIPRE.QLD.ofLPX,
  MIPRE.QLD.ofLPZ,
  MIPRE.QLD.contentSplitX,
  MIPRE.QLD.pairSplitX,
  MIPRE.QLD.contentSplitZ,
  MIPRE.QLD.pairSplitZ,
  MIPRE.QLD.contentSplitPts,
  MIPRE.QLD.pairSplitPts,
  MIPRE.QLD.avg_content_eq_pair_X,
  MIPRE.QLD.avg_content_eq_pair_Z,
  MIPRE.QLD.avg_content_eq_pair_pts,
  MIPRE.QLD.avg_content_eq_pair_X',
  MIPRE.QLD.avg_content_eq_pair_Z',
  MIPRE.QLD.pairShift,
  MIPRE.QLD.pairDirX,
  MIPRE.QLD.ofLPX_pairShift,
  MIPRE.QLD.ofLPZ_pairShift,
  MIPRE.QLD.pairShift_zero,
  MIPRE.QLD.pairShift_add,
  MIPRE.QLD.pairDirX_shift,
  MIPRE.QLD.sum_pair_shift,
  MIPRE.QLD.pairCX,
  MIPRE.QLD.pairCZ,
  MIPRE.QLD.pairDirX_eq,
  MIPRE.QLD.pairCX_pairShift,
  MIPRE.QLD.pairCZ_pairShift,
  MIPRE.QLD.pairs_of_lines_prod,
  MIPRE.QLD.affEval,
  MIPRE.QLD.affEval_of_snd_eq_zero,
  MIPRE.QLD.affPoly,
  MIPRE.QLD.eval_affPoly,
  MIPRE.QLD.natDegree_affPoly_le,
  MIPRE.QLD.affPoly_of_snd_eq_zero,
  MIPRE.QLD.natDegree_affPoly_eq_zero,
  MIPRE.QLD.ofPoly,
  MIPRE.QLD.eval_ofPoly,
  MIPRE.QLD.DegLE,
  MIPRE.QLD.DegLE.mono,
  MIPRE.QLD.degLE_ofPoly,
  MIPRE.QLD.natDegree_toPoly_le_of_degLE,
  MIPRE.QLD.combinePoly,
  MIPRE.QLD.natDegree_comp_affPoly_le,
  MIPRE.QLD.natDegree_combinePoly_le,
  MIPRE.QLD.combine,
  MIPRE.QLD.eval_combine,
  MIPRE.QLD.degLE_combine_of_blocks_const,
  MIPRE.QLD.degLE_combine_of_ab_const,
  MIPRE.QLD.lineParam_dir_zero,
  MIPRE.QLD.lineParam_self,
  MIPRE.QLD.subAff,
  MIPRE.QLD.subAff_snd_of_eq_zero,
  MIPRE.QLD.on_line_affEval,
  MIPRE.QLD.lineParam_affEval,
  MIPRE.QLD.alph_single_of_ne,
  MIPRE.QLD.bet_single_of_ne,
  MIPRE.QLD.LPData.dir_congr,
  MIPRE.QLD.padShift,
  MIPRE.QLD.padShift_pt,
  MIPRE.QLD.padShift_s,
  MIPRE.QLD.padShift_raw,
  MIPRE.QLD.subX_padShift,
  MIPRE.QLD.subZ_padShift,
  MIPRE.QLD.subX_padShift_dir,
  MIPRE.QLD.subZ_padShift_dir,
  MIPRE.QLD.rep_xBlk_padShift,
  MIPRE.QLD.rep_zBlk_padShift,
  MIPRE.QLD.aAffOf,
  MIPRE.QLD.bAffOf,
  MIPRE.QLD.xAffOf,
  MIPRE.QLD.zAffOf,
  MIPRE.QLD.affEval_aAffOf,
  MIPRE.QLD.affEval_bAffOf,
  MIPRE.QLD.aPres_base_eq,
  MIPRE.QLD.dPres_base_eq,
  MIPRE.QLD.aPres_dir_ofLPX,
  MIPRE.QLD.aPres_dir_ofLPZ,
  MIPRE.QLD.dPres_dir_ofLPX,
  MIPRE.QLD.dPres_dir_ofLPZ,
  MIPRE.QLD.param_subX_padShift,
  MIPRE.QLD.param_subZ_padShift,
  MIPRE.QLD.padCombine,
  MIPRE.QLD.eval_padCombine,
  MIPRE.QLD.degLE_padCombine_aline,
  MIPRE.QLD.sum_pasteLine,
  MIPRE.QLD.posSemidef_pasteLine,
  MIPRE.QLD.SubRand,
  MIPRE.QLD.subPair,
  MIPRE.QLD.padLineMats,
  MIPRE.QLD.sum_padLineMats,
  MIPRE.QLD.posSemidef_padLineMats,
  MIPRE.QLD.sum_filter_fiber,
  MIPRE.QLD.sum_filter_padLineMats,
  MIPRE.QLD.sumAll_nonneg,
  MIPRE.QLD.sumAll_mono,
  MIPRE.QLD.sumRestr_nonneg,
  MIPRE.QLD.avgAll_nonneg,
  MIPRE.QLD.avgAll_mono,
  MIPRE.QLD.avgRestr_nonneg,
  MIPRE.QLD.avgAll_const_mul,
  MIPRE.QLD.sum_avgRestr,
  MIPRE.QLD.avgRestr_le_mul_avgAll,
  MIPRE.QLD.avgRestr_prod_le_mul_avgAll,
  MIPRE.QLD.sum_uniform_pts,
  MIPRE.QLD.avg_content_eq_pts,
  MIPRE.QLD.combined_points_pts,
  MIPRE.QLD.FactorsX,
  MIPRE.QLD.FactorsZ,
  MIPRE.QLD.factorsX_aPres,
  MIPRE.QLD.factorsX_dPres,
  MIPRE.QLD.factorsZ_aPres,
  MIPRE.QLD.factorsZ_dPres,
  MIPRE.QLD.lineMats_ofLPX,
  MIPRE.QLD.param_ofLPX,
  MIPRE.QLD.lineEvalMats_ofLPX,
  MIPRE.QLD.collProb_ofLPX,
  MIPRE.QLD.lineMats_ofLPZ,
  MIPRE.QLD.param_ofLPZ,
  MIPRE.QLD.lineEvalMats_ofLPZ,
  MIPRE.QLD.avg_pair_eq_content_X,
  MIPRE.QLD.avg_pair_eq_content_Z,
  MIPRE.QLD.avg_pair_eq_content_X_self,
  MIPRE.QLD.avg_pair_eq_content_X_collProb,
  MIPRE.QLD.pairs_of_lines_prod_of_items,
  MIPRE.QLD.lpEquiv,
  MIPRE.QLD.sumAll_eq_sum,
  MIPRE.QLD.card_lpData,
  MIPRE.QLD.avgAll_eq_uniform,
  MIPRE.QLD.avgAll_prod_eq_uniform,
  MIPRE.QLD.avgAll_one,
  MIPRE.QLD.avgAll_prod_one,
  MIPRE.QLD.avgAll_prod_nonneg,
  MIPRE.QLD.avgAll_avgRestr_le,
  MIPRE.QLD.avgRestr_avgAll_le,
  MIPRE.QLD.avgSub_le_mul_avgAll,
  MIPRE.QLD.shiftAB,
  MIPRE.QLD.xBlk_shiftAB,
  MIPRE.QLD.zBlk_shiftAB,
  MIPRE.QLD.alph_shiftAB,
  MIPRE.QLD.bet_shiftAB,
  MIPRE.QLD.shiftAB_shiftAB,
  MIPRE.QLD.shiftAB_zero,
  MIPRE.QLD.bijective_shiftAB,
  MIPRE.QLD.subX_shiftAB,
  MIPRE.QLD.subZ_shiftAB,
  MIPRE.QLD.sumSubAt,
  MIPRE.QLD.sumSub_eq_sum_sumSubAt,
  MIPRE.QLD.sumSubAt_shiftAB,
  MIPRE.QLD.sumSubAB,
  MIPRE.QLD.avgSubAB,
  MIPRE.QLD.sumSubAB_eq,
  MIPRE.QLD.avgSubAB_le_of_forall,
  MIPRE.QLD.avgAll_sub,
  MIPRE.QLD.sumSub_mono,
  MIPRE.QLD.avgSub_mono,
  MIPRE.QLD.sumSub_one,
  MIPRE.QLD.avgSub_one,
  MIPRE.QLD.sumSubAt_sub,
  MIPRE.QLD.sumSubAB_sub,
  MIPRE.QLD.avgSubAB_sub,
  MIPRE.QLD.avgSubAB_one,
  MIPRE.QLD.sum_bornProb_le_fibre,
  MIPRE.QLD.sum_bornProb_diag_le_one,
  MIPRE.QLD.pasteEval,
  MIPRE.QLD.pasteFib,
  MIPRE.QLD.pasteFib_eq,
  MIPRE.QLD.posSemidef_pasteFib,
  MIPRE.QLD.sum_pasteFib,
  MIPRE.QLD.ptComb,
  MIPRE.QLD.lineComb,
  MIPRE.QLD.lineComb_eq_sum_pasteFib,
  MIPRE.QLD.padded_lines_consistency,
  MIPRE.QLD.extVec2_swapVec,
  MIPRE.QLD.xSqNorm_swapVec,
  MIPRE.QLD.extHat_swapVec,
  MIPRE.QLD.padded_lines_consistency_swap

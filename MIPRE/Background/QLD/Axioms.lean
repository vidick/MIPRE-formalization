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
import MIPRE.Background.QLD.Legalize
import MIPRE.Background.QLD.PaddedValue
import MIPRE.Background.QLD.PaddedLIDT
import MIPRE.Background.QLD.Helper
import MIPRE.Background.QLD.MTilde
import MIPRE.Background.QLD.CLTransport
import MIPRE.Background.Introspection.HonestPauliLowDegree
import MIPRE.Background.Introspection.HonestPauliEdges
import MIPRE.Background.Introspection.HonestPauliGame
import MIPRE.Background.Introspection.CompleteGame
import MIPRE.Background.Introspection.BinaryGame
import MIPRE.Background.Introspection.BinaryPadding
import MIPRE.Background.Introspection.PauliRestriction
import MIPRE.Background.QLD.LineRepresentative
import MIPRE.Background.QLD.CLExplicitSeed
import MIPRE.Background.QLD.SeededLinePrograms
import MIPRE.Foundations.GuardSorryFree
import MIPRE.Background.QLD.PauliRowPrograms
import MIPRE.Background.QLD.PauliFactorPrograms
import MIPRE.Background.QLD.SamplerQueryProgram
import MIPRE.Background.QLD.CLExplicitTransport
import MIPRE.Background.QLD.SwapItemTwo

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

/-! ## The axis-parallel degree bound

Blueprint `lem:qld-axis-degree`: the degree computation, the legalization of a strategy that makes
the paper's format convention available at no cost, and the exact support of the expanded and
padded axis-line measurements on degree at most `d`. -/

#guard_sorry_free MIPRE.LowDegree.natDegree_lineRestrict_single_le,
  MIPRE.QLD.DegLE.add,
  MIPRE.QLD.degLE_zero,
  MIPRE.QLD.degLE_padLine,
  MIPRE.QLD.degLE_rdLine,
  MIPRE.QLD.degLE_lineCoeffs_aline,
  MIPRE.QLD.degLE_hatLine_outcome,
  MIPRE.QLD.Question.defaultAns,
  MIPRE.QLD.fmtOk_defaultAns,
  MIPRE.QLD.legalize,
  MIPRE.QLD.legalize_of_fmtOk,
  MIPRE.QLD.legalize_of_not_fmtOk,
  MIPRE.QLD.fmtOk_legalize,
  MIPRE.QLD.rdVal_legalize_point,
  MIPRE.QLD.rdPauli_legalize_pauli,
  MIPRE.QLD.rdBit_legalize_pairB,
  MIPRE.QLD.rdBit_legalize_var,
  MIPRE.QLD.rdBitPair_legalize_pair,
  MIPRE.QLD.rdProbe_legalize_point,
  MIPRE.QLD.LegalSupport,
  MIPRE.QLD.legalizeStrat,
  MIPRE.QLD.isPVM_legalizeStrat,
  MIPRE.QLD.legalizeStrat_mats_eq_zero,
  MIPRE.QLD.legalSupport_legalizeStrat,
  MIPRE.QLD.legalizeStrat_map,
  MIPRE.QLD.ptPOVM_legalizeStrat,
  MIPRE.QLD.ptObs_legalizeStrat,
  MIPRE.QLD.hatPtPOVM_legalizeStrat,
  MIPRE.QLD.hatMats_legalizeStrat,
  MIPRE.QLD.povmValue_le_legalizeStrat,
  MIPRE.QLD.one_sub_povmValue_legalizeStrat_le,
  MIPRE.QLD.lineAnsPOVM_aline_eq_zero_of_not_degLE,
  MIPRE.QLD.hatLinePOVM_aline_eq_zero_of_not_degLE,
  MIPRE.QLD.lineMats_aPres_eq_zero_of_not_degLE,
  MIPRE.QLD.padLineMats_aline_eq_zero_of_not_degLE

/-! ## The padded strategy and its value

Blueprint `lem:qld-global-setup`: mixtures and uniform averages of POVMs, the support-aware
conditional-failure bounds, the seeded test's value sample by sample, and the padded strategy on
the seeded test at `(q, 4m, d, 1)` with the two invariances that let the decider's reading be the
quantity `lem:qld-padded-lines` controls. -/

#guard_sorry_free MIPRE.POVM.aOp,
  MIPRE.POVM.aOp_mats,
  MIPRE.POVM.map_aOp,
  MIPRE.POVM.dirac,
  MIPRE.POVM.mix,
  MIPRE.POVM.mix_mats,
  MIPRE.bornProb_smul_left,
  MIPRE.bornProb_smul_right,
  MIPRE.bornProb_mix_left,
  MIPRE.bornProb_mix_right,
  MIPRE.POVM.ofPosSemidef,
  MIPRE.POVM.ofPosSemidef_mats,
  MIPRE.unifOn,
  MIPRE.unifOn_nonneg,
  MIPRE.sum_unifOn,
  MIPRE.POVM.avgOn,
  MIPRE.bornProb_avgOn_left,
  MIPRE.bornProb_avgOn_right,
  MIPRE.POVM.avgOn_mats,
  MIPRE.POVM.map_mix,
  MIPRE.POVM.map_dirac,
  MIPRE.POVM.map_avgOn,
  MIPRE.POVM.map_id,
  MIPRE.POVM.map_mats_eq_zero_of_forall_ne,
  MIPRE.POVM.map_congr_of_support,
  MIPRE.bornProb_zero_left,
  MIPRE.bornProb_zero_right,
  MIPRE.condFail_le_one_sub_sum_bornProb_map,
  MIPRE.condFail_le_one_sub_sum_bornProb_diag,
  MIPRE.sum_bornProb_map',
  MIPRE.POVM.map_const_mats,
  MIPRE.bornProb_one_one,
  MIPRE.LIDT.CL.sampleEquiv,
  MIPRE.LIDT.CL.card_ty,
  MIPRE.LIDT.CL.card_sample,
  MIPRE.LIDT.CL.sum_sample_eq,
  MIPRE.LIDT.CL.rep_add_lineParam_smul,
  MIPRE.LIDT.CL.lineParam_rep_add_smul,
  MIPRE.LIDT.CL.sum_indicator_apply_eq,
  MIPRE.LIDT.CL.sum_indicator_apply_eq_zero,
  MIPRE.LIDT.CL.sum_indicator_zeroBelow_eq_zero_le,
  MIPRE.LIDT.CL.one_sub_povmValue_clGame,
  MIPRE.QLD.padPtPair,
  MIPRE.QLD.padPtPair_mats,
  MIPRE.QLD.padComb,
  MIPRE.QLD.padPt,
  MIPRE.QLD.padPt_mats,
  MIPRE.QLD.padLinePOVM,
  MIPRE.QLD.padLinePOVM_mats,
  MIPRE.QLD.presOf,
  MIPRE.QLD.factorsX_presOf,
  MIPRE.QLD.factorsZ_presOf,
  MIPRE.QLD.presOf_base_eq,
  MIPRE.QLD.presOf_dir_ofLPX,
  MIPRE.QLD.presOf_dir_ofLPZ,
  MIPRE.QLD.lineMeas,
  MIPRE.QLD.lineMeas_mats,
  MIPRE.QLD.rawFiber,
  MIPRE.QLD.mem_rawFiber,
  MIPRE.QLD.lineDir,
  MIPRE.QLD.LPData.dir_eq_lineDir,
  MIPRE.QLD.rawSet,
  MIPRE.QLD.rawSet_nonempty,
  MIPRE.QLD.lineDir_of_mem_rawSet,
  MIPRE.QLD.lineQ,
  MIPRE.QLD.lineQ_point,
  MIPRE.QLD.lineQ_aline,
  MIPRE.QLD.lineQ_dline,
  MIPRE.QLD.lineTau,
  MIPRE.QLD.padShift_lineData,
  MIPRE.QLD.alineAns,
  MIPRE.QLD.dlineAns,
  MIPRE.QLD.lineAns,
  MIPRE.QLD.rdEval,
  MIPRE.QLD.padStrat,
  MIPRE.QLD.padStrat_point,
  MIPRE.QLD.padStrat_lineQ,
  MIPRE.QLD.exists_of_padStrat_point_mats_ne_zero,
  MIPRE.QLD.exists_of_padStrat_lineQ_mats_ne_zero,
  MIPRE.QLD.eval_padLine_of_degLE,
  MIPRE.QLD.lineMeas_aline_mats_eq_zero_of_not_degLE,
  MIPRE.QLD.padStrat_lineQ_map_rdEval,
  MIPRE.QLD.padStrat_point_map_toValue,
  MIPRE.QLD.lineMats_pairCX_padShift,
  MIPRE.QLD.lineMats_pairCZ_padShift,
  MIPRE.QLD.pasteLine_subPair_padShift,
  MIPRE.QLD.sum_filter_padLineMats_eq_lineComb,
  MIPRE.QLD.lineMeas_map_eval_mats

/-! Blueprint `lem:qld-global-success`: the agreement triangle, the conditional failure of the
padded strategy at each of the nine ordered type pairs, and the value bound. -/

#guard_sorry_free MIPRE.agreeSum,
  MIPRE.weightA,
  MIPRE.weightB,
  MIPRE.xDev,
  MIPRE.weightA_le_one,
  MIPRE.weightB_le_one,
  MIPRE.weightA_nonneg,
  MIPRE.weightB_nonneg,
  MIPRE.xDev_eq,
  MIPRE.bornProb_le_norm_mul_norm,
  MIPRE.agreeSum_le_sqrt_mul_sqrt,
  MIPRE.weightA_ge,
  MIPRE.weightB_ge,
  MIPRE.xDev_le,
  MIPRE.xDev_triangle,
  MIPRE.agreeSum_triangle,
  MIPRE.QLD.accepts_lineQ_point,
  MIPRE.QLD.accepts_point_lineQ,
  MIPRE.QLD.accepts_point_self,
  MIPRE.QLD.accepts_lineQ_lineQ_self,
  MIPRE.QLD.condFail_lineQ_point_le,
  MIPRE.QLD.condFail_point_lineQ_le,
  MIPRE.QLD.condFail_point_point_le,
  MIPRE.QLD.condFail_lineQ_lineQ_le,
  MIPRE.QLD.condFail_aline_dline_le,
  MIPRE.QLD.condFail_dline_aline_le,
  MIPRE.QLD.one_sub_sum_bornProb_le_avg_eval,
  MIPRE.QLD.Amb,
  MIPRE.QLD.ptFam,
  MIPRE.QLD.lineFam,
  MIPRE.QLD.lineEvalFam,
  MIPRE.QLD.sum_inv_card_fiber_sum,
  MIPRE.QLD.sum_rawSet_fiber,
  MIPRE.QLD.lineTermL,
  MIPRE.QLD.lineTermR,
  MIPRE.QLD.padGL,
  MIPRE.QLD.padGR,
  MIPRE.QLD.sum_bornProb_lineEvalFam_ptFam,
  MIPRE.QLD.sum_bornProb_ptFam_lineEvalFam,
  MIPRE.QLD.card_amb,
  MIPRE.QLD.card_subRand,
  MIPRE.QLD.sum_padGL_eq,
  MIPRE.QLD.sum_padGR_eq,
  MIPRE.QLD.avgSubAB_padGL,
  MIPRE.QLD.avgSubAB_padGR,
  MIPRE.QLD.inv_card_amb_eq,
  MIPRE.QLD.agreeSum_lineEvalFam_ptFam,
  MIPRE.QLD.agreeSum_ptFam_lineEvalFam,
  MIPRE.QLD.bornProb_extHat_ptComb_right,
  MIPRE.QLD.bornProb_extHat_ptComb_left,
  MIPRE.QLD.presOf_items,
  MIPRE.QLD.presOf_items_swap,
  MIPRE.QLD.presOf_coll,
  MIPRE.QLD.one_sub_avgSubAB_padGL_le,
  MIPRE.QLD.one_sub_avgSubAB_padGR_le,
  MIPRE.QLD.one_sub_inv_card_mul_sum_le,
  MIPRE.QLD.one_sub_agreeSum_lineEval_pt_le,
  MIPRE.QLD.one_sub_agreeSum_pt_lineEval_le,
  MIPRE.QLD.avg_amb_blocks,
  MIPRE.QLD.one_sub_agreeSum_pt_pt_le,
  MIPRE.QLD.sum_shift_param,
  MIPRE.QLD.evDef,
  MIPRE.QLD.evDef_nonneg,
  MIPRE.QLD.evDef_le_one,
  MIPRE.QLD.evDef_lineTau,
  MIPRE.QLD.sum_avg_evDef_le,
  MIPRE.QLD.sum_deg_le,
  MIPRE.QLD.sum_amb_eq,
  MIPRE.QLD.uniform_amb_nonneg,
  MIPRE.QLD.sum_uniform_amb,
  MIPRE.QLD.one_sub_agreeSum_uniform_eq,
  MIPRE.QLD.one_sub_agreeSum_lineEval_lineEval_le,
  MIPRE.QLD.padW,
  MIPRE.QLD.padW_point_point_le,
  MIPRE.QLD.padW_line_point_le,
  MIPRE.QLD.padW_point_line_le,
  MIPRE.QLD.padW_aline_dline_le,
  MIPRE.QLD.padW_dline_aline_le,
  MIPRE.QLD.padW_line_line_le,
  MIPRE.QLD.Sample.question_fst_eq_lineQ,
  MIPRE.QLD.Sample.question_snd_eq_lineQ,
  MIPRE.QLD.sum_ty,
  MIPRE.QLD.one_sub_povmValue_padStrat_eq,
  MIPRE.QLD.padStrat_value

/-! `lem:qld-global-pvm` (`MIPRE/Background/QLD/PaddedLIDT.lean`, with the reduced-state lemma of
`MIPRE/Background/QLD/Simul.lean` it uses). -/
#guard_sorry_free MIPRE.POVM.compress_aOp,
  MIPRE.QLD.bornProb_extVec2_aOp_aOp,
  MIPRE.QLD.ansZero,
  MIPRE.QLD.PadReg,
  MIPRE.QLD.padState,
  MIPRE.QLD.padState_unit,
  MIPRE.QLD.bornProb_padState_aOp_aOp,
  MIPRE.QLD.padPt_aOp_mats,
  MIPRE.QLD.inconsistency_padState_aOp_right,
  MIPRE.QLD.inconsistency_padState_aOp_left,
  MIPRE.QLD.deltaGS,
  MIPRE.QLD.deltaLD,
  MIPRE.QLD.deltaGS_nonneg,
  MIPRE.QLD.exists_global_pvm,
  MIPRE.QLD.exists_global_pvm_hat,
  MIPRE.QLD.GlobalPair,
  MIPRE.QLD.exists_globalPair

/-! `lem:qld-global-dummy` (`MIPRE/Background/QLD/Dummy.lean`, and its specialization in
`MIPRE/Background/QLD/PaddedLIDT.lean`). -/
#guard_sorry_free MIPRE.LowDegree.agreeOn,
  MIPRE.LowDegree.mem_agreeOn,
  MIPRE.LowDegree.prob_agreeOn_le_individualDegree,
  MIPRE.LIDT.expFinsupp,
  MIPRE.LIDT.expFinsupp_apply,
  MIPRE.LIDT.expFinsupp_injective,
  MIPRE.LIDT.LowIndDegPoly.toMv,
  MIPRE.LIDT.LowIndDegPoly.eval_toMv,
  MIPRE.LIDT.LowIndDegPoly.coeff_toMv,
  MIPRE.LIDT.LowIndDegPoly.degreeOf_toMv_le,
  MIPRE.LIDT.degreeOf_rename_le,
  MIPRE.bornProb_add_right,
  MIPRE.bornProb_mono_right,
  MIPRE.POVM.add_le_one,
  MIPRE.inconsistency_swapVec,
  MIPRE.sum_uniform_eq_one,
  MIPRE.sum_ite_eq_zero_sub,
  MIPRE.ProjectiveMeasurement.posSemidef_M,
  MIPRE.QLD.inconsistency_evalPOVM_eq,
  MIPRE.QLD.sum_bornProb_M_one,
  MIPRE.QLD.IsDummy,
  MIPRE.QLD.not_isDummy_xIdx,
  MIPRE.QLD.not_isDummy_zIdx,
  MIPRE.QLD.not_isDummy_aIdx,
  MIPRE.QLD.not_isDummy_bIdx,
  MIPRE.QLD.not_isDummy_of_eq_one,
  MIPRE.QLD.mix,
  MIPRE.QLD.mix_apply_of_not,
  MIPRE.QLD.mix_apply_of,
  MIPRE.QLD.xBlk_mix,
  MIPRE.QLD.zBlk_mix,
  MIPRE.QLD.alph_mix,
  MIPRE.QLD.bet_mix,
  MIPRE.QLD.mix_mix,
  MIPRE.QLD.mixSwap,
  MIPRE.QLD.mixSwap_apply_fst,
  MIPRE.QLD.padPt_mix,
  MIPRE.QLD.WIndep,
  MIPRE.QLD.wIndep_of_eq_one,
  MIPRE.QLD.eval_mix_of_wIndep,
  MIPRE.QLD.dumSub,
  MIPRE.QLD.dumSub_injective,
  MIPRE.QLD.comp_dumSub,
  MIPRE.QLD.rename_toMv_ne,
  MIPRE.QLD.mixAgree,
  MIPRE.QLD.mixAgree_eq_univ_of_wIndep,
  MIPRE.QLD.card_mixAgree_le,
  MIPRE.QLD.sum_mass_mixAgree_ge,
  MIPRE.QLD.sum_bad_mass_le,
  MIPRE.QLD.sum_bad_mass_le_of_le,
  MIPRE.QLD.GlobalPair.sum_bad_mass_A_le,
  MIPRE.QLD.GlobalPair.sum_bad_mass_B_le

/-! `lem:qld-global-products` (`MIPRE/Background/QLD/Products.lean`, and its specialization to the
padded state in `MIPRE/Background/QLD/PaddedLIDT.lean`). -/
#guard_sorry_free MIPRE.mul_self_le_self_of_le_one,
  MIPRE.one_sub_proj_conjTranspose_mul_self_le_one,
  MIPRE.snorm_sq_add_le,
  MIPRE.bornProb_mono_left,
  MIPRE.snorm_sq_aOp_mul_bOp,
  MIPRE.bornProb_one_eq_normSq_stateVecB,
  MIPRE.sum_snorm_sq_aOp_mul_bOp_le,
  MIPRE.stateSqNorm_extVec2_aOp,
  MIPRE.sum_avg_normSq_stateVecB_fibre_eq,
  MIPRE.QLD.ordZX,
  MIPRE.QLD.ordXZ,
  MIPRE.QLD.comm,
  MIPRE.QLD.sum_ordZX,
  MIPRE.QLD.sum_ordXZ,
  MIPRE.QLD.sand_sub_ordZX,
  MIPRE.QLD.sand_sub_ordXZ,
  MIPRE.QLD.norm_stateVecB_sand_sub_ordZX_le,
  MIPRE.QLD.norm_stateVecB_sand_sub_ordXZ_le,
  MIPRE.QLD.sum_avg_fibre_sand_sub_ord_le,
  MIPRE.QLD.setAB,
  MIPRE.QLD.xBlk_setAB,
  MIPRE.QLD.zBlk_setAB,
  MIPRE.QLD.alph_setAB,
  MIPRE.QLD.bet_setAB,
  MIPRE.QLD.setAB_setAB,
  MIPRE.QLD.abSwap,
  MIPRE.QLD.sum_pad_ab,
  MIPRE.QLD.sum_uniform_pad4,
  MIPRE.QLD.sum_content_blocks,
  MIPRE.QLD.sandComb,
  MIPRE.QLD.ordComb,
  MIPRE.QLD.ptComb_posSemidef,
  MIPRE.QLD.ptComb_le_one,
  MIPRE.QLD.ptComb_conjTranspose,
  MIPRE.QLD.sandComb_posSemidef,
  MIPRE.QLD.sandComb_le_one,
  MIPRE.QLD.sandComb_conjTranspose,
  MIPRE.QLD.sandComb_sub_ordComb,
  MIPRE.QLD.sum_snorm_sq_ordComb_le,
  MIPRE.QLD.sum_snorm_sq_ordZX_le,
  MIPRE.QLD.sum_snorm_sq_ordXZ_le,
  MIPRE.QLD.liftOp,
  MIPRE.QLD.isPVM_liftOp,
  MIPRE.QLD.sandComb_liftOp,
  MIPRE.QLD.comm_liftOp,
  MIPRE.QLD.normSq_stateVecB_padState_aOp_aOp,
  MIPRE.QLD.stateSqNorm_padState_aOp_aOp,
  MIPRE.QLD.swapVec_padState_unit,
  MIPRE.QLD.sum_comm_liftOp_B_le,
  MIPRE.QLD.sum_comm_liftOp_A_le,
  MIPRE.QLD.GlobalPair.cons_sandComb_A,
  MIPRE.QLD.GlobalPair.cons_sandComb_B,
  MIPRE.QLD.GlobalPair.products_ZX_A,
  MIPRE.QLD.GlobalPair.products_XZ_A,
  MIPRE.QLD.GlobalPair.products_ZX_B,
  MIPRE.QLD.GlobalPair.products_XZ_B

/-! `lem:qld-global-linear` (`MIPRE/Background/QLD/Linear.lean`, and its specialization to the
padded state in `MIPRE/Background/QLD/PaddedLIDT.lean`). -/
#guard_sorry_free MIPRE.LIDT.patch, MIPRE.LIDT.maskOn, MIPRE.LIDT.maskOff,
  MIPRE.LIDT.patch_maskOn_maskOff, MIPRE.LIDT.maskOn_patch, MIPRE.LIDT.maskOff_patch,
  MIPRE.LIDT.maskOn_eq_self, MIPRE.LIDT.maskOff_eq_self, MIPRE.LIDT.maskOn_apply_of_not,
  MIPRE.LIDT.maskOff_apply_of, MIPRE.LIDT.LowIndDegPoly.coef, MIPRE.LIDT.prod_pow_patch,
  MIPRE.LIDT.LowIndDegPoly.eval_eq_sum_coef, MIPRE.LIDT.LowIndDegPoly.eval_coef_of_eq_off,
  MIPRE.LIDT.LowIndDegPoly.coef_maskOff, MIPRE.LIDT.card_eval_eq_zero_le, MIPRE.posSemidef_of_proj,
  MIPRE.uniform_nonneg, MIPRE.QLD.abSet, MIPRE.QLD.mem_abSet, MIPRE.QLD.xIdx_notMem_abSet,
  MIPRE.QLD.zIdx_notMem_abSet, MIPRE.QLD.patAB, MIPRE.QLD.patAB_aIdx, MIPRE.QLD.patAB_bIdx,
  MIPRE.QLD.patAB_of_notMem, MIPRE.QLD.patAB_injective, MIPRE.QLD.pAB,
  MIPRE.QLD.eval_coef_abSet_setAB, MIPRE.QLD.eval_pAB, MIPRE.QLD.vec_two_eq, MIPRE.QLD.fin2Equiv,
  MIPRE.QLD.e10, MIPRE.QLD.e01, MIPRE.QLD.e10_ne_e01, MIPRE.QLD.linAB, MIPRE.QLD.eval_linAB,
  MIPRE.QLD.sum_agree_two_le, MIPRE.QLD.IsLinAB, MIPRE.QLD.patAB_eq_maskOn,
  MIPRE.QLD.exists_bad_coef, MIPRE.QLD.pAB_ne_linAB, MIPRE.QLD.sum_uniform_eval_eq_zero_le,
  MIPRE.QLD.bOp_mul_aOp_comm, MIPRE.QLD.sum_snorm_sq_ordXZ_eq, MIPRE.QLD.fibMap,
  MIPRE.QLD.fibMap_injective, MIPRE.QLD.fiber_eq_image, MIPRE.QLD.snorm_sq_ordComb_ordXZ_of_ne,
  MIPRE.QLD.ordComb_ordXZ_bet_zero, MIPRE.QLD.snorm_sq_ordComb_ordXZ_le,
  MIPRE.QLD.card_filter_snd_eq_zero, MIPRE.QLD.sum_filter_snorm_sq_ordComb_eq, MIPRE.QLD.sum_setAB,
  MIPRE.QLD.sum_uniform_setAB, MIPRE.QLD.sum_ab_snorm_sq_ordComb_le_of_good,
  MIPRE.QLD.sum_uniform_snorm_sq_ordComb_le_of_not_isLinAB, MIPRE.QLD.sum_bad_linear_mass_le,
  MIPRE.QLD.GlobalPair.sum_bad_linear_mass_A_le, MIPRE.QLD.GlobalPair.sum_bad_linear_mass_B_le

/-! ## Actual Pauli CL sampler content and honest measurements -/

#guard_sorry_free MIPRE.QLD.PauliCL.presentation_exactlyOn,
  MIPRE.QLD.PauliCL.questionOfVector_presentation,
  MIPRE.QLD.PauliCL.presentation_pauli_eval,
  MIPRE.QLD.PauliCL.qldGame_mu_presentation,
  MIPRE.QLD.PauliCL.binaryPresentation_exactlyOn,
  MIPRE.QLD.PauliCL.binaryPresentation_pauli_eval,
  MIPRE.QLD.PauliCL.qldGame_mu_binaryPresentation,
  MIPRE.QLD.PauliCL.questionOfVector_canonical,
  MIPRE.QLD.PauliCL.encode_decode_eval,
  MIPRE.QLD.PauliCL.pullbackStrategy_value,
  MIPRE.QLD.PauliCL.pullbackStrategy_pauli_A,
  MIPRE.QLD.PauliCL.pullbackStrategy_pauli_B

#guard_sorry_free MIPRE.QLD.Honest.probe_observable,
  MIPRE.QLD.Honest.probe_phase,
  MIPRE.QLD.Honest.answerOp_isPVM,
  MIPRE.QLD.Honest.answerOp_format_zero,
  MIPRE.QLD.Honest.answerOp_pauli,
  MIPRE.QLD.Honest.pvm_fibre_commute,
  MIPRE.QLD.Honest.pvm_fibre_reject,
  MIPRE.QLD.Honest.answerOp_aline_point_commute,
  MIPRE.QLD.Honest.answerOp_dline_point_commute,
  MIPRE.QLD.Honest.answerOp_pauli_point_commute,
  MIPRE.QLD.Honest.answerOp_aline_point_reject,
  MIPRE.QLD.Honest.answerOp_dline_point_reject,
  MIPRE.QLD.Honest.answerOp_pauli_point_reject,
  MIPRE.QLD.Honest.answerOp_point_pairB_commute,
  MIPRE.QLD.Honest.answerOp_point_pairB_reject,
  MIPRE.QLD.Honest.answerOp_point_var_commute,
  MIPRE.QLD.Honest.answerOp_point_var_reject,
  MIPRE.QLD.Honest.answerOp_con_var_commute,
  MIPRE.QLD.Honest.answerOp_con_var_reject,
  MIPRE.QLD.Honest.answerOp_pairB_pair_commute,
  MIPRE.QLD.Honest.answerOp_pairB_pair_reject

#guard_sorry_free MIPRE.QLD.Honest.qldGame_positive_content,
  MIPRE.QLD.Honest.answerOp_commute,
  MIPRE.QLD.Honest.answerOp_reject,
  MIPRE.QLD.Honest.strategy_isPCC,
  MIPRE.QLD.Honest.strategy_value,
  MIPRE.QLD.Honest.exists_perfectPCC

#print axioms MIPRE.QLD.Honest.exists_perfectPCC
#print axioms MIPRE.QLD.PauliCL.pullbackStrategy_value

#guard_sorry_free MIPRE.QLD.PauliCL.coordNumbering_point_X,
  MIPRE.QLD.PauliCL.coordNumbering_point_Z,
  MIPRE.QLD.PauliCL.coordNumbering_seed,
  MIPRE.QLD.PauliCL.coordNumbering_direction,
  MIPRE.QLD.PauliCL.coordNumbering_scalar_X,
  MIPRE.QLD.PauliCL.coordNumbering_scalar_Z,
  MIPRE.QLD.PauliCL.binaryCoordEquiv_val,
  MIPRE.QLD.PauliCL.binaryVectorEquiv_apply,
  MIPRE.QLD.PauliCL.representative_eq_canonLin,
  MIPRE.QLD.PauliCL.lineRepresentativeProg_canonLin

#guard_sorry_free MIPRE.Introspection.Complete.pauliOp_X,
  MIPRE.Introspection.Complete.pauliOp_Z,
  MIPRE.Introspection.Complete.sampleOp_commute,
  MIPRE.Introspection.Complete.sampleOp_reject,
  MIPRE.Introspection.Complete.strategy_isPCC,
  MIPRE.Introspection.Complete.strategy_value,
  MIPRE.Introspection.Complete.exists_perfectPCC,
  MIPRE.Introspection.BinaryComplete.pauliOp_X,
  MIPRE.Introspection.BinaryComplete.pauliOp_Z,
  MIPRE.Introspection.BinaryComplete.strategy_isPCC,
  MIPRE.Introspection.BinaryComplete.strategy_value,
  MIPRE.Introspection.BinaryComplete.exists_perfectPCC

#print axioms MIPRE.Introspection.BinaryComplete.exists_perfectPCC

#guard_sorry_free MIPRE.Introspection.PauliRestriction.strategy_state,
  MIPRE.Introspection.PauliRestriction.strategy_failure_le,
  MIPRE.Introspection.PauliRestriction.strategy_pauliAns_A,
  MIPRE.Introspection.PauliRestriction.strategy_pauliAns_B

#print axioms MIPRE.Introspection.PauliRestriction.strategy_failure_le

#guard_sorry_free MIPRE.QLD.PauliCL.ExplicitSeed.presentation_exactlyOn,
  MIPRE.QLD.PauliCL.ExplicitSeed.binaryPresentation_exactlyOn,
  MIPRE.QLD.PauliCL.ExplicitSeed.decode_presentation,
  MIPRE.QLD.PauliCL.ExplicitSeed.chi_seedPermutation,
  MIPRE.QLD.PauliCL.ExplicitSeed.qldGame_mu_selector_binary

#guard_sorry_free MIPRE.QLD.PauliCL.axisRepresentativeProg_legacy,
  MIPRE.QLD.PauliCL.diagonalRepresentativeProg_legacy

#guard_sorry_free MIPRE.Introspection.BinaryComplete.paddingEmbedding_number,
  MIPRE.Introspection.BinaryComplete.card_seed,
  MIPRE.Introspection.BinaryComplete.exists_padded_perfectPCC,
  MIPRE.Introspection.BinaryComplete.exists_depthPadded_perfectPCC

#guard_sorry_free MIPRE.QLD.PauliCL.linearBits_correct,
  MIPRE.QLD.PauliCL.marginalBits_correct,
  MIPRE.QLD.PauliCL.factorBits_correct,
  MIPRE.QLD.PauliCL.SamplerProgram.query_dimension,
  MIPRE.QLD.PauliCL.SamplerProgram.query_marginal,
  MIPRE.QLD.PauliCL.SamplerProgram.query_linear,
  MIPRE.QLD.PauliCL.SamplerProgram.query_factor,
  MIPRE.QLD.PauliCL.SamplerProgram.query_runs,
  MIPRE.QLD.PauliCL.ExplicitSeed.binaryOutputPermutation_presentation,
  MIPRE.QLD.PauliCL.ExplicitSeed.binaryQuestion_outputPermutation
/-! `lem:qld-global-separate` (`MIPRE/Background/QLD/Separate.lean`, and its specialization to the
padded state in `MIPRE/Background/QLD/PaddedLIDT.lean`). -/
#guard_sorry_free MIPRE.LIDT.LowIndDegPoly.eval_zero, MIPRE.LIDT.LowIndDegPoly.eval_sub,
  MIPRE.LIDT.LowIndDegPoly.const, MIPRE.LIDT.LowIndDegPoly.eval_const,
  MIPRE.LIDT.LowIndDegPoly.coef_eq_zero_of_not, MIPRE.LIDT.LowIndDegPoly.restrictOff,
  MIPRE.LIDT.LowIndDegPoly.restrictOff_apply_of, MIPRE.LIDT.LowIndDegPoly.eval_restrictOff,
  MIPRE.LIDT.LowIndDegPoly.DepOutside, MIPRE.LIDT.LowIndDegPoly.exists_coef_ne_zero_of_depOutside,
  MIPRE.QLD.mixOn, MIPRE.QLD.mixOn_mixOn, MIPRE.QLD.mixOnSwap, MIPRE.QLD.sum_mixOn,
  MIPRE.QLD.sum_uniform_mixOn, MIPRE.QLD.eval_mixOn, MIPRE.QLD.zSet, MIPRE.QLD.xSet,
  MIPRE.QLD.zIdx_mem_zSet, MIPRE.QLD.xIdx_mem_xSet, MIPRE.QLD.zBlk_mixOn_zSet,
  MIPRE.QLD.xBlk_mixOn_xSet, MIPRE.QLD.oneD, MIPRE.QLD.gA, MIPRE.QLD.gB, MIPRE.QLD.patch_abSet_aIdx,
  MIPRE.QLD.patch_abSet_bIdx, MIPRE.QLD.coef_patAB_eq_zero_of_isLinAB,
  MIPRE.QLD.pAB_eq_linAB_of_isLinAB, MIPRE.QLD.eval_setAB_of_isLinAB, MIPRE.QLD.IsGood,
  MIPRE.QLD.isGood_of, MIPRE.QLD.not_isGood_cases, MIPRE.QLD.card_filter_linear_le,
  MIPRE.QLD.ptComb_ordZX_eq, MIPRE.QLD.snorm_sq_ordXZ_le_bornProb,
  MIPRE.QLD.sum_ab_snorm_sq_ordComb_le_of_lin, MIPRE.QLD.sum_uniform_bornProb_readOn_le,
  MIPRE.QLD.sum_uniform_snorm_sq_ordComb_XZ_le_of_depB,
  MIPRE.QLD.sum_uniform_snorm_sq_ordComb_ZX_le_of_depA, MIPRE.QLD.sum_bad_mass_le_of_avg,
  MIPRE.QLD.sum_not_isGood_mass_le, MIPRE.QLD.GlobalPair.sum_not_isGood_mass_A_le,
  MIPRE.QLD.GlobalPair.sum_not_isGood_mass_B_le

/-! `lem:qld-global-complete` (`MIPRE/Background/QLD/Complete.lean`). -/
#guard_sorry_free MIPRE.LIDT.expandIdx, MIPRE.LIDT.expandIdx_apply_idx,
  MIPRE.LIDT.expandIdx_apply_of_not, MIPRE.LIDT.prod_pow_expandIdx,
  MIPRE.LIDT.LowIndDegPoly.blockPoly, MIPRE.LIDT.LowIndDegPoly.eval_blockPoly,
  MIPRE.QLD.isLinAB_of_isGood, MIPRE.QLD.notMem_xSet_iff, MIPRE.QLD.notMem_zSet_iff,
  MIPRE.QLD.not_depOutside_gA_of_isGood, MIPRE.QLD.not_depOutside_gB_of_isGood, MIPRE.QLD.gX,
  MIPRE.QLD.gZ, MIPRE.QLD.eval_gX, MIPRE.QLD.eval_gZ, MIPRE.QLD.pairOf, MIPRE.QLD.pairOf_of_isGood,
  MIPRE.QLD.pairMeas, MIPRE.QLD.pairMeas_mats, MIPRE.QLD.isPVM_pairMeas,
  MIPRE.QLD.evalMarg_pairMeas, MIPRE.QLD.inconsistency_map_eq

/-! `lem:qld-global-sandwich` (`MIPRE/Background/QLD/Complete.lean`). -/
#guard_sorry_free MIPRE.QLD.sum_uniform_zBlk, MIPRE.QLD.sum_uniform_xBlk,
  MIPRE.QLD.sq_sub_two_mul_le_sq, MIPRE.QLD.one_sub_two_sqrt_le_sum_snorm_sq, MIPRE.QLD.marg_Z_ge,
  MIPRE.QLD.marg_X_ge, MIPRE.QLD.inconsistency_evalMarg_Z_le, MIPRE.QLD.inconsistency_evalMarg_X_le

/-! `lem:qld-global-robustness` (`MIPRE/Background/QLD/Complete.lean` for the register
transport, `MIPRE/Background/QLD/PaddedLIDT.lean` for the errors). -/
#guard_sorry_free MIPRE.isPVM_reindex, MIPRE.isPVM_reindex_povm, MIPRE.reindex_aOp_aOp,
  MIPRE.POVM.aOp_aOp_reindex, MIPRE.ProjectiveMeasurement.isPVM_M, MIPRE.QLD.deltaProd,
  MIPRE.QLD.deltaSep, MIPRE.QLD.deltaS, MIPRE.QLD.GlobalPair.one_sub_two_eta_ge,
  MIPRE.QLD.GlobalPair.sum_not_isGood_mass_A_le', MIPRE.QLD.GlobalPair.sum_not_isGood_mass_B_le',
  MIPRE.QLD.liftPt, MIPRE.QLD.liftPt_mats, MIPRE.QLD.GlobalPair.inconsistency_evalMarg_A_le,
  MIPRE.QLD.GlobalPair.inconsistency_evalMarg_B_le

/-! `lem:qld-simultaneous` (`MIPRE/Background/QLD/Simul.lean` for the structure,
`MIPRE/Background/QLD/PaddedLIDT.lean` for the instance). -/
#guard_sorry_free MIPRE.QLD.PolyPair, MIPRE.QLD.PolyPair.proj, MIPRE.QLD.evalMarg,
  MIPRE.QLD.evalMarg_mats, MIPRE.QLD.isPVM_evalMarg, MIPRE.QLD.SimulPair, MIPRE.QLD.SimulPair.mono,
  MIPRE.QLD.SimulPair.bornProb_aOp_aOp, MIPRE.QLD.GlobalPair.toSimulPair, MIPRE.QLD.exists_simulPair

/-! `lem:qld-helper` (`MIPRE/Background/QLD/Helper.lean`, with the state-norm transfers in
`MIPRE/Background/QLD/Simul.lean`). -/
#guard_sorry_free MIPRE.stateSqNorm_eq_bornProb_one, MIPRE.normSq_stateVecB_eq_one_bornProb,
  MIPRE.QLD.SimulPair.stateSqNorm_aOp, MIPRE.QLD.SimulPair.normSq_stateVecB_aOp,
  MIPRE.QLD.SimulPair.xSqNorm_aOp, MIPRE.aOp_mul_one_sub_eq, MIPRE.snorm_aOp_mul_one_sub_le,
  MIPRE.snorm_sq_aOp_mul_one_sub_le, MIPRE.QLD.sum_bornProb_diag_eq, MIPRE.QLD.sum_content_pt,
  MIPRE.QLD.sum_uniform_xSqNorm_hatMats_le, MIPRE.QLD.SimulPair.hatMats_conjTranspose,
  MIPRE.QLD.SimulPair.sum_bornProb_evalMarg_ge, MIPRE.QLD.SimulPair.sum_xSqNorm_evalMarg_le,
  MIPRE.QLD.SimulPair.sum_xSqNorm_hat_le, MIPRE.QLD.SimulPair.sum_snorm_sq_evalMarg_one_sub_le

/-! `lem:qld-exact-paulis`. The exact half is
`MIPRE/Background/QLD/{ExactPauli,SwapUnitary}.lean`, the approximate half
`MIPRE/Background/QLD/{NonMultilinear,PauliBasis,Multilinear}.lean`, and the reading of the
latter as a closeness of two measurements `MIPRE/Background/QLD/MTilde.lean`. -/
#guard_sorry_free MIPRE.QLD.sCoarse, MIPRE.QLD.isPVM_sCoarse, MIPRE.QLD.sum_sCoarse_kron,
  MIPRE.QLD.mTilde, MIPRE.QLD.mTilde_eq_sum, MIPRE.QLD.cdPhase, MIPRE.QLD.wTilde,
  MIPRE.QLD.wTilde_eq, MIPRE.QLD.wTilde_conjTranspose, MIPRE.QLD.wTilde_mul_self,
  MIPRE.QLD.wTilde_mul_wTilde, MIPRE.QLD.dotF_smul_right, MIPRE.QLD.trDot_smul_smul,
  MIPRE.QLD.trDot_smul_right, MIPRE.QLD.sum_kron, MIPRE.QLD.kron_sum,
  MIPRE.QLD.prob_agree_ldEnc_le_of_not_multilinear, MIPRE.QLD.nonMultilinear_mass_le,
  MIPRE.QLD.sum_sub_le_of_eq_on, MIPRE.QLD.sum_normSq_point_sub_pauli_le, MIPRE.conv,
  MIPRE.conjTranspose_conv_mul_conv, MIPRE.sum_conv, MIPRE.sum_normSq_stateVecB_conv_eq,
  MIPRE.QLD.hatPtPOVM_mats_eq_conv, MIPRE.QLD.hatPauliPOVM_mats_eq_conv,
  MIPRE.QLD.sum_normSq_hat_point_sub_pauli_le, MIPRE.QLD.rdPauliVec, MIPRE.QLD.rdPauli_eq_dotF,
  MIPRE.QLD.dotF_add_left, MIPRE.QLD.weylPOVM, MIPRE.QLD.weylPOVM_mats, MIPRE.QLD.synOfPOVM_eq_map,
  MIPRE.QLD.hatPauli, MIPRE.QLD.hatPauli_map, MIPRE.POVM.map_kron_map, MIPRE.QLD.abs_bornProb_le,
  MIPRE.QLD.abs_sum_bornProb_le, MIPRE.abs_sum_weighted_bornProb_le, MIPRE.sum_filter_bornProb_eq,
  MIPRE.sum_mass_off_le, MIPRE.QLD.IsML, MIPRE.QLD.not_degreeOf_le_one_of_not_isML,
  MIPRE.QLD.sum_uniform_agree_ldEnc_le, MIPRE.QLD.polyMarg, MIPRE.QLD.evalMarg_eq_map_polyMarg,
  MIPRE.QLD.isPVM_polyMarg, MIPRE.QLD.isPVM_hatPauli, MIPRE.QLD.SimulPair.sum_bornProb_hatPauli_ge,
  MIPRE.QLD.SimulPair.sum_bornProb_off_le, MIPRE.QLD.SimulPair.sum_bornProb_not_isML_le,
  MIPRE.QLD.cubeData, MIPRE.QLD.IsInterp, MIPRE.QLD.cubeData_eq_of_eq_ldEnc,
  MIPRE.QLD.isInterp_of_exists, MIPRE.QLD.ne_ldEnc_of_not_isInterp, MIPRE.QLD.dotF_cubeData_indVec,
  MIPRE.QLD.sum_uniform_agree_ldEnc_le_of_not_isInterp,
  MIPRE.QLD.SimulPair.sum_bornProb_not_isInterp_le, MIPRE.sum_bornProb_map_eq,
  MIPRE.abs_sum_weighted_sub_le, MIPRE.QLD.SimulPair.sum_bornProb_polyMarg_ge,
  MIPRE.QLD.SimulPair.sum_bornProb_cubeData_ge, MIPRE.regroupEquiv, MIPRE.regroupVec,
  MIPRE.qform_comp_equiv, MIPRE.reindex_regroupEquiv, MIPRE.bornProb_regroupVec,
  MIPRE.regroupVec_unit, MIPRE.QLD.mTilde_eq_sTensor, MIPRE.QLD.isPVM_mTilde,
  MIPRE.QLD.dotF_add_right, MIPRE.QLD.cdPhase_add, MIPRE.QLD.wTilde_mul_add,
  MIPRE.QLD.add_self_eq_zero', MIPRE.QLD.add_eq_iff_eq_add, MIPRE.QLD.ptAtPOVM,
  MIPRE.QLD.hatPtPOVM_eq_kron, MIPRE.QLD.sum_kron_syn_eq_hatMats, MIPRE.QLD.sCoarse_eq_polyMarg,
  MIPRE.QLD.SimulPair.mVec, MIPRE.QLD.SimulPair.mVec_unit, MIPRE.QLD.SimulPair.mTildeAt,
  MIPRE.QLD.SimulPair.isPVM_mTildeAt, MIPRE.QLD.SimulPair.mTildeAt_eq,
  MIPRE.QLD.SimulPair.bornProb_mTildeAt, MIPRE.QLD.SimulPair.sum_bornProb_mTildeAt,
  MIPRE.QLD.SimulPair.sum_bornProb_mTilde_ge, MIPRE.QLD.SimulPair.inconsistency_mTilde_le,
  MIPRE.QLD.SimulPair.wTildeAt, MIPRE.QLD.SimulPair.wTildeAt_conjTranspose,
  MIPRE.QLD.SimulPair.wTildeAt_mul_self, MIPRE.QLD.SimulPair.wTildeAt_mul_add,
  MIPRE.QLD.SimulPair.wTildeAt_mul_wTildeAt

/-! `lem:qld-swap`: the swap isometry, both items relative to one auxiliary state. The exact
pieces are `MIPRE/Background/QLD/SwapUnitary.lean`, item 1
`MIPRE/Background/QLD/{SwapState,SwapItemOne}.lean`, the endgame's steps
`MIPRE/Background/QLD/{SwapMeasure,SwapEndgame}.lean`, and item 2's threading and the joint
statement `MIPRE/Background/QLD/SwapItemTwo.lean`. -/
#guard_sorry_free MIPRE.QLD.sTensor, MIPRE.QLD.sTensor_mul, MIPRE.QLD.sTensor_one,
  MIPRE.QLD.sTensor_conjTranspose, MIPRE.QLD.wTilde_eq_sTensor, MIPRE.QLD.uOf, MIPRE.QLD.swapU,
  MIPRE.QLD.uOf_conjTranspose, MIPRE.QLD.uOf_mul_conjTranspose, MIPRE.QLD.uOf_conjTranspose_mul,
  MIPRE.QLD.swapU_mul_conjTranspose, MIPRE.QLD.swapU_conjTranspose_mul, MIPRE.QLD.uOf_conj_wX,
  MIPRE.QLD.uOf_conj_wZ, MIPRE.QLD.swapU_conj_of_sign, MIPRE.QLD.swapU_conj_wTilde_X,
  MIPRE.QLD.swapU_conj_wTilde_Z, MIPRE.QLD.eprProj, MIPRE.QLD.eprProj_apply, MIPRE.QLD.twirl,
  MIPRE.QLD.wX_mul_wZ_apply, MIPRE.QLD.twirl_mul_twirl_eq_sum, MIPRE.QLD.twirl_mul_twirl,
  MIPRE.QLD.norm_sub_sq_le_of_re_inner_ge, MIPRE.QLD.re_inner_ge_of_two_close,
  MIPRE.QLD.norm_sub_normalize_sq_le, MIPRE.QLD.snorm_sum_le, MIPRE.QLD.kron_self_isometry,
  MIPRE.QLD.twirl_conjTranspose, MIPRE.QLD.snorm_twirl_le, MIPRE.QLD.twirl_mul_self,
  MIPRE.QLD.conj_epr, MIPRE.QLD.star_epr, MIPRE.QLD.eprProj_conjTranspose, MIPRE.QLD.epr_dotProduct,
  MIPRE.QLD.eprProj_mul_self, MIPRE.QLD.auxVec, MIPRE.QLD.bOp_eprProj_mulVec,
  MIPRE.QLD.exists_auxVec_close, MIPRE.QLD.conj_proj_of_sign, MIPRE.QLD.conj_syn_of_sign,
  MIPRE.QLD.swapU_conj_mTilde, MIPRE.QLD.swapU_conj_mTilde_X, MIPRE.QLD.swapU_conj_mTilde_Z,
  MIPRE.QLD.sum_snorm_sq_sub_eq_two_sub, MIPRE.QLD.sum_uniform_agree_bornProb_le,
  MIPRE.QLD.SimulPair.swapA, MIPRE.QLD.SimulPair.swapU_conj_mTildeAt,
  MIPRE.QLD.inconsistency_triangle, MIPRE.QLD.inconsistency_regroupVec, MIPRE.QLD.pauliAtPOVM,
  MIPRE.QLD.SimulPair.inconsistency_mTilde_pauli_le, MIPRE.QLD.abs_qform_sub_qform_le,
  MIPRE.QLD.SimulPair.bornProb_padded, MIPRE.QLD.SimulPair.inconsistency_padded,
  MIPRE.QLD.SimulPair.inconsistency_mTilde_pauli_le', MIPRE.QLD.inconsistency_eq_half_xPovmDist,
  MIPRE.QLD.inconsistency_pt_pt_le, MIPRE.QLD.inconsistency_pt_pauli_le,
  MIPRE.QLD.SimulPair.inconsistency_mTilde_pauli_le_of_win, MIPRE.QLD.bOp_mulVec_auxVec,
  MIPRE.QLD.mulVec_auxVec_congr, MIPRE.QLD.mulVec_auxVec_proj, MIPRE.QLD.mulVec_auxVec_syn,
  MIPRE.QLD.sum_snorm_sq_sub_le_of_agree, MIPRE.QLD.sum_uniform_bornProb_fibre_le,
  MIPRE.QLD.endEquiv, MIPRE.QLD.endVec, MIPRE.QLD.endVec_unit, MIPRE.QLD.reindex_endEquiv,
  MIPRE.QLD.qform_endVec, MIPRE.QLD.qform_bOp_twirl, MIPRE.QLD.outerPairEquiv, MIPRE.QLD.outerVec,
  MIPRE.QLD.outerVec_unit, MIPRE.QLD.reindex_outerPairEquiv, MIPRE.QLD.qform_outerVec,
  MIPRE.QLD.SimulPair.swapA_conj_wTildeAt, MIPRE.QLD.SimulPair.swapA_conj_wTildeAt_one,
  MIPRE.QLD.conj_inv_of_unitary, MIPRE.QLD.MirrorSimul.aliceSwap,
  MIPRE.QLD.MirrorSimul.aliceSwap_conjTranspose_mul,
  MIPRE.QLD.MirrorSimul.aliceSwap_conj_aliceWTilde, MIPRE.QLD.MirrorSimul.bobSwap_conj_bobWTilde,
  MIPRE.QLD.MirrorSimul.physSwap, MIPRE.QLD.MirrorSimul.physSwap_conjTranspose_mul,
  MIPRE.QLD.MirrorSimul.endState, MIPRE.QLD.MirrorSimul.endState_unit,
  MIPRE.QLD.MirrorSimul.qform_endState_weyl, MIPRE.QLD.deltaSelfCons,
  MIPRE.QLD.deltaSelfCons_nonneg, MIPRE.QLD.MirrorSimul.aliceWTilde_conjTranspose,
  MIPRE.QLD.MirrorSimul.aliceWTilde_mul_self, MIPRE.QLD.MirrorSimul.bobWTilde_conjTranspose,
  MIPRE.QLD.MirrorSimul.bobWTilde_mul_self, MIPRE.QLD.MirrorSimul.bornProb_wTilde_ge,
  MIPRE.QLD.MirrorSimul.qform_endState_twirl_ge, MIPRE.QLD.MirrorSimul.exists_aux_close,
  MIPRE.QLD.toMv_coeffTable, MIPRE.QLD.ancPoly, MIPRE.QLD.ancPoly_toMv, MIPRE.QLD.ancPoly_eval,
  MIPRE.QLD.ancPoly_toMv_ne, MIPRE.QLD.isPVM_conj_unitary, MIPRE.QLD.bnd_one_of_proj,
  MIPRE.QLD.mulVec_swapVec_aOp, MIPRE.QLD.mulVec_swapVec_bOp, MIPRE.QLD.qform_conj_eq,
  MIPRE.QLD.unit_of_norm_evec_eq_one, MIPRE.QLD.outerUnVec, MIPRE.QLD.outerVec_outerUnVec,
  MIPRE.QLD.norm_evec_outerUnVec, MIPRE.QLD.norm_evec_sub_outerUnVec, MIPRE.QLD.mulVec_outerUnVec,
  MIPRE.QLD.mulVec_outerUnVec_auxVec, MIPRE.QLD.deltaLegs, MIPRE.QLD.deltaItemTwo,
  MIPRE.QLD.etaItemOne, MIPRE.QLD.MirrorSimul.alicePauli, MIPRE.QLD.MirrorSimul.bobPauli,
  MIPRE.QLD.MirrorSimul.aliceConjPauli, MIPRE.QLD.MirrorSimul.bobConjPauli,
  MIPRE.QLD.MirrorSimul.aliceTau, MIPRE.QLD.MirrorSimul.bobTau,
  MIPRE.QLD.MirrorSimul.aliceSwap_mul_conjTranspose,
  MIPRE.QLD.MirrorSimul.physSwap_mul_conjTranspose, MIPRE.QLD.MirrorSimul.isPVM_alicePauli,
  MIPRE.QLD.MirrorSimul.isPVM_aliceConjPauli, MIPRE.QLD.MirrorSimul.isPVM_aliceTau,
  MIPRE.QLD.MirrorSimul.isPVM_bobTau, MIPRE.QLD.MirrorSimul.sum_aliceConjPauli_fibre,
  MIPRE.QLD.MirrorSimul.sum_bobTau_fibre, MIPRE.QLD.MirrorSimul.bornProb_physVec_pauli_bobMTilde,
  MIPRE.QLD.MirrorSimul.sum_bornProb_physVec_ge,
  MIPRE.QLD.MirrorSimul.sum_bornProb_conj_ge_of_close, MIPRE.QLD.MirrorSimul.sum_bornProb_fibre_ge,
  MIPRE.QLD.MirrorSimul.sum_snorm_sq_aliceConjPauli_le, MIPRE.QLD.MirrorSimul.physAux,
  MIPRE.QLD.MirrorSimul.norm_evec_physAux, MIPRE.QLD.MirrorSimul.norm_evec_physSwap_sub_physAux,
  MIPRE.QLD.MirrorSimul.aliceTau_mulVec_physAux, MIPRE.QLD.MirrorSimul.sum_snorm_sq_alice_le,
  MIPRE.QLD.MirrorSimul.mirror_physSwap_mulVec, MIPRE.QLD.MirrorSimul.sum_snorm_sq_bob_le,
  MIPRE.QLD.MirrorSimul.swap_isometry

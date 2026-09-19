/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.Anticomm
import MIPRE.Background.QLD.Consistency
import MIPRE.Background.QLD.Commutation
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

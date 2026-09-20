/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.GuardSorryFree
import MIPRE.Foundations.CL.Basic
import MIPRE.Foundations.LowDegree.SchwartzZippel
import MIPRE.Foundations.LowDegree.Anticomm
import MIPRE.Foundations.LowDegree.Shoup
import MIPRE.Foundations.LowDegree.SelfDual
import MIPRE.Foundations.CL.Canonical
import MIPRE.Foundations.CL.Closure
import MIPRE.Foundations.CL.Downsize
import MIPRE.Foundations.CL.Repeat
import MIPRE.Foundations.ClassMIPStar
import MIPRE.Foundations.Compression
import MIPRE.Foundations.Cost.Kleene
import MIPRE.Foundations.Cost.Semidecide
import MIPRE.Foundations.Cost.Toolkit
import MIPRE.Foundations.Cost.Universal
import MIPRE.Foundations.Games
import MIPRE.Foundations.StateDistance
import MIPRE.Foundations.PerfectStrategy
import MIPRE.Foundations.OracularComplete
import MIPRE.Foundations.OracularSound
import MIPRE.Foundations.LowDegree.SelfDualize
import MIPRE.Foundations.LowDegree.NormalBasis
import MIPRE.Foundations.SAT.AdmissibleField
import MIPRE.Foundations.Halting.Corollaries
import MIPRE.Foundations.Pipeline.Compress
import MIPRE.Foundations.Halting.LambdaBound
import MIPRE.Foundations.Halting.Semidecider
import MIPRE.Foundations.ValueApprox
import MIPRE.Foundations.ValueApprox.Cayley
import MIPRE.Foundations.ValueApprox.Dense
import MIPRE.Foundations.ValueApprox.Gaussian
import MIPRE.Foundations.ValueApprox.Norms
import MIPRE.Foundations.ValueApprox.Projective
import MIPRE.Foundations.ValueApprox.RE
import MIPRE.Foundations.ValueApprox.RawComplete
import MIPRE.Foundations.ValueApprox.RawPrimrec
import MIPRE.Foundations.ValueApprox.RawSemantics
import MIPRE.Foundations.ValueApprox.RawStrategy
import MIPRE.Foundations.ValueApprox.Strategy
import MIPRE.TM.CookLevin.DecoupledProg
import MIPRE.LCS.MagicSquare.Strategy
import MIPRE.LCS.Strategy.Equivalence
import MIPRE.LCS.Strategy.ObservableToProjector
import MIPRE.TM.Code.Encoding.MachineCode
import MIPRE.Foundations.WeylBinary
import MIPRE.Foundations.Commutation
import MIPRE.Foundations.Linearity
import MIPRE.Background.GowersHatami.Basic

/-!
# The blueprint's proof-level `\leanok` claims, guarded

`\leanok` is two marks. Inside a statement environment it claims the *statement* is
formalized; inside `\begin{proof}` it claims the *proof* is. The second is the project's
central claim -- CLAUDE.md's three artifacts, and rule 3 of `planning/formalization-plan.md`,
rest on `MIPRE/` being the one thing that is true because this repository says so -- and until
now it was maintained by hand. The evidence behind all 27 marks was one audit,
`planning/lean-coverage.md`, run against 80 modules and 1502 declarations; the tree is 122 and
2467, so two thirds of the named surface postdates it, and it is already wrong in one
direction, listing `MIPRE.syncValue_le_quantumValue` as carrying `sorryAx` when it is proved.

`#guard_sorry_free` (`MIPRE/Foundations/GuardSorryFree.lean`) fails the build if any name it
is given depends on `sorryAx`, and
`scripts/lean-coverage.py` checks that the set of names guarded here and in the vendored guard
files is exactly the set the blueprint marks with a proof-level `\leanok`. A mark without a
guard is an unchecked assertion about this project's own mathematics; a guard without a mark is
a leftover that will one day be read as one. Both are now build failures.

The three vendored trees have carried such a guard from the start
(`MIPRE/Background/{LIDT,Repetition,Orthonormalization}/Axioms.lean`), for the reason
`CONTRIBUTING.md` gives about the `sorry` exception: it is what keeps the exception from being
a loophole. The mathematics this project imports was machine-guarded; the mathematics it
writes itself was not. Names defined in the vendored trees stay guarded there, where the
imports are already paid for -- except `MIPRE.gowers_hatami`, whose module imports only
`Foundations.Distances` and Mathlib and which had no guard of its own.

Adding a declaration here is not how to claim it: mark the blueprint proof, and the check will
tell you the guard is missing.
-/

-- blueprint `lem:bounded-violation-re`
#guard_sorry_free MIPRE.Cost.primrec_natLeB,
  MIPRE.REPred.of_computable_exists,
  MIPRE.Verifier.BoundViolation,
  MIPRE.Verifier.ComputablyPresented,
  MIPRE.Verifier.boundBudget,
  MIPRE.Verifier.boundViolationB,
  MIPRE.Verifier.boundViolationB_iff,
  MIPRE.Verifier.not_isBounded_iff_exists,
  MIPRE.Verifier.rePred_not_isBounded

-- blueprint `lem:qld-averaging`
#guard_sorry_free MIPRE.stateSqNorm_avg_le

-- blueprint `lem:qld-povm-to-obs`
#guard_sorry_free MIPRE.obsOf,
  MIPRE.stateDist_obsOf_le

-- blueprint `lem:cl-closure`
#guard_sorry_free MIPRE.CL.CLFun.concat,
  MIPRE.CL.CLFun.directSum,
  MIPRE.CL.IsCLFun.concat,
  MIPRE.CL.IsCLFun.directSum,
  MIPRE.CL.IsCLFun.directSum',
  MIPRE.CL.IsCLFun.succ

-- blueprint `lem:cl-downsize`
#guard_sorry_free MIPRE.CL.CLFun.ExactlyOn.downsize,
  MIPRE.CL.CLFun.downsize,
  MIPRE.CL.CLFun.eval_downsize,
  MIPRE.CL.CLFun.eval_truncate_downsize,
  MIPRE.CL.CLFun.factorOfPrefix_downsize,
  MIPRE.CL.CLFun.mapOfPrefix_downsize,
  MIPRE.CL.CLFun.reindex,
  MIPRE.CL.IsCLFun.downsize,
  MIPRE.CL.IsCLFun.reindex,
  MIPRE.CL.clDist_downsize,
  MIPRE.CL.downsizeEquiv

-- blueprint `lem:cl-structure`
#guard_sorry_free MIPRE.CL.CLFun.ExactlyOn,
  MIPRE.CL.CLFun.ExactlyOn.biUnion_factorAt,
  MIPRE.CL.CLFun.SupportedOn.disjoint_factorAt,
  MIPRE.CL.CLFun.SupportedOn.eval_truncate_eq_sum,
  MIPRE.CL.CLFun.SupportedOn.factorAt_subset,
  MIPRE.CL.CLFun.SupportedOn.factorOfPrefix_eval,
  MIPRE.CL.CLFun.SupportedOn.mapOfPrefix_eval,
  MIPRE.CL.CLFun.factorAt,
  MIPRE.CL.CLFun.factorOfPrefix,
  MIPRE.CL.CLFun.mapAt,
  MIPRE.CL.CLFun.mapOfPrefix,
  MIPRE.CL.CLFun.truncate

-- blueprint `lem:code-canonical`
#guard_sorry_free Turing.decodeCodeExact_encodeCode,
  Turing.decodeCodeExact_sound,
  Turing.encodeCode_injective

-- blueprint `lem:compressible-criterion`
#guard_sorry_free MIPRE.Cost.compressibility_criterion,
  MIPRE.Cost.compressibility_criterion_levels

-- blueprint `lem:correct-tableau`
#guard_sorry_free MIPRE.TM.CookLevin.tableau_sat_iff

-- blueprint `lem:cost-budget-decidable`
#guard_sorry_free MIPRE.Cost.Machine.costStep,
  MIPRE.Cost.Machine.costStep_iterate,
  MIPRE.Cost.Machine.evalForCostD,
  MIPRE.Cost.Machine.evalForCostD_eq_some,
  MIPRE.Cost.Machine.haltsWithinB,
  MIPRE.Cost.Machine.haltsWithin_iff_evalForCostD,
  MIPRE.Cost.Machine.haltsWithin_of_evalForCostD,
  MIPRE.Cost.Machine.primrec_haltsWithinB,
  MIPRE.Cost.Machine.stepCostD,
  MIPRE.Cost.Machine.stepCostD_toData,
  MIPRE.Cost.decidableHaltsWithin

-- blueprint `lem:halting-form`
#guard_sorry_free MIPRE.Cost.compressibility_criterion_halting,
  MIPRE.Cost.recursive_compression_halting

-- blueprint `lem:cl-famsum`
#guard_sorry_free MIPRE.CL.CLFun.famSum,
  MIPRE.CL.IsCLFun.famSum,
  MIPRE.CL.CLFun.exactlyOn_famSum,
  MIPRE.CL.CLFun.eval_famSum,
  MIPRE.CL.CLFun.eval_truncate_famSum,
  MIPRE.CL.CLFun.factorOfPrefix_famSum,
  MIPRE.CL.CLFun.mapOfPrefix_famSum,
  MIPRE.CL.clDist_famSum

-- blueprint `thm:compression` (proof: the composition of the three stages)
#guard_sorry_free MIPRE.GapCompression,
  MIPRE.GapCompression.ofPipeline

-- blueprint `lem:compress-sampler-indep`
#guard_sorry_free MIPRE.GapCompression,
  MIPRE.Pipeline.sampler,
  MIPRE.Pipeline.samplerProg_eq,
  MIPRE.Pipeline.output_sampler

-- blueprint `lem:compress-margin`
#guard_sorry_free MIPRE.Pipeline.eps1,
  MIPRE.Pipeline.intro_margin,
  MIPRE.Pipeline.exists_mu,
  MIPRE.Pipeline.eps2,
  MIPRE.Pipeline.ar_margin

-- blueprint `lem:compress-tau`
#guard_sorry_free MIPRE.Pipeline.exists_eps2_lower,
  MIPRE.Pipeline.exists_tau

-- blueprint `cor:main-quantum`
#guard_sorry_free MIPRE.Halting.halting_reduction_both_of,
  MIPRE.Halting.halting_reduction_quantum_of

-- blueprint `cor:value-uncomputable`
#guard_sorry_free MIPRE.Halting.gameValue_uncomputable_of,
  MIPRE.Halting.quantumValue_uncomputable_of

-- blueprint `thm:halting-undecidable`
#guard_sorry_free MIPRE.Halting.exists_code_halts_of_isRE,
  MIPRE.halting_re,
  MIPRE.halting_undecidable

-- blueprint `thm:mipstar-eq-re`
#guard_sorry_free MIPRE.Halting.mipstar_eq_re_of,
  MIPRE.Halting.re_subset_mipstar_of,
  MIPRE.Halting.exists_code_halts_of_isRE

-- blueprint `lem:halt-construction`
#guard_sorry_free MIPRE.Cost.Prog.freezeBuildProg,
  MIPRE.Cost.Prog.readProg,
  MIPRE.Cost.Prog.readProg_runs,
  MIPRE.Cost.Prog.wrapBuildProg,
  MIPRE.Halting.comprStr,
  MIPRE.Halting.comprStr_accepts,
  MIPRE.Halting.haltProg,
  MIPRE.Halting.haltProg_accepts_iff,
  MIPRE.Halting.haltProg_runs,
  MIPRE.Halting.haltProg_runs_inv,
  MIPRE.Halting.prepProg,
  MIPRE.Halting.prepProg_runs

-- blueprint `lem:halting-semidecider`
#guard_sorry_free MIPRE.Halting.exists_sem_of_tab,
  MIPRE.REPred.or,
  MIPRE.Verifier.LongAcceptance,
  MIPRE.Verifier.longAcceptanceB,
  MIPRE.Verifier.longAcceptanceB_iff,
  MIPRE.Verifier.not_rejectsLong_iff_exists,
  MIPRE.Verifier.rePred_not_rejectsLong

-- blueprint `lem:kleene`
#guard_sorry_free MIPRE.Cost.efficient_fixed_point

-- blueprint `lem:lambda`
#guard_sorry_free MIPRE.Cost.PolyBounded.absorb,
  MIPRE.Cost.PolyBounded.absorb_log,
  MIPRE.Cost.Prog.wrapCoreCost,
  MIPRE.Cost.Prog.wrapCore_cost',
  MIPRE.Halting.ansBound_le_lamOf,
  MIPRE.Halting.comprPoly,
  MIPRE.Halting.exists_compressorSpec,
  MIPRE.Halting.isBounded_comprStr,
  MIPRE.Halting.lamOf,
  MIPRE.Halting.lamOf_ge

-- blueprint `lem:dhalt-values`
#guard_sorry_free MIPRE.Halting.CompressorSpec.toObligations,
  MIPRE.Halting.comprStr_accepts,
  MIPRE.Halting.haltProg_accepts_iff

-- blueprint `thm:halting`
#guard_sorry_free MIPRE.Halting.exists_obligations,
  MIPRE.Halting.halting_reduces_to_gameValue_of,
  MIPRE.Halting.halting_reduction,
  MIPRE.Halting.halting_reduction_of

-- blueprint `lem:lambda-bound`
#guard_sorry_free MIPRE.Halting.four_mul_succ_lt_two_pow,
  MIPRE.Halting.lambda_bound,
  MIPRE.Halting.log_lt_div,
  MIPRE.Halting.sq_le_two_pow_of_four_le

-- blueprint `lem:mermin-peres`
#guard_sorry_free MIPRE.LCS.MagicSquare.grid,
  MIPRE.LCS.MagicSquare.grid_sameEquation_comm,
  MIPRE.LCS.MagicSquare.isObservable_grid,
  MIPRE.LCS.MagicSquare.merminPeresStrategy

-- blueprint `lem:mipstar-sub-re`
#guard_sorry_free MIPRE.MIPStar.exists_semidecider,
  MIPRE.MIPStar.isRE

-- blueprint `lem:norm-two-psd`
#guard_sorry_free MIPRE.ValueApprox.posSemidef_realSmul_one_add_and_sub_iff

-- blueprint `lem:observable-projector`
#guard_sorry_free MIPRE.LCS.commute_observableToProjector,
  MIPRE.LCS.isMeasurementSystem_observableToProjector,
  MIPRE.LCS.observableToProjector

-- blueprint `lem:observable-strategy`
#guard_sorry_free MIPRE.LCS.ObservableStrategy.aliceMeasurement_commute_bobMeasurement,
  MIPRE.LCS.ObservableStrategy.isMeasurementSystem_aliceMeasurement,
  MIPRE.LCS.ObservableStrategy.toProjectorStrategy

-- blueprint `lem:perturbation-split`
#guard_sorry_free MIPRE.ValueApprox.dotProduct_kronecker_perturb,
  MIPRE.ValueApprox.dotProduct_mulVec_perturb,
  MIPRE.ValueApprox.kronecker_sub_kronecker

-- blueprint `lem:rational-pvm-dense`
#guard_sorry_free MIPRE.ValueApprox.GaussianRat,
  MIPRE.ValueApprox.IsPVM,
  MIPRE.ValueApprox.IsPVM.exists_entriesIn_norm_sub_le,
  MIPRE.ValueApprox.IsPVM.exists_unitary_pattern,
  MIPRE.ValueApprox.cayley,
  MIPRE.ValueApprox.cayley_mem_unitaryGroup,
  MIPRE.ValueApprox.exists_isSkewHermitian_cayley_eq,
  MIPRE.ValueApprox.exists_norm_eq_one_isUnit_one_add_smul,
  MIPRE.ValueApprox.exists_unitary_entriesIn_norm_smul_sub_le,
  MIPRE.ValueApprox.norm_cayley_sub_cayley_le

-- blueprint `lem:rational-strategies-suffice`
#guard_sorry_free MIPRE.ValueApprox.ExactStrategy,
  MIPRE.ValueApprox.ExactStrategy.EntriesIn,
  MIPRE.ValueApprox.ExactStrategy.IsValid,
  MIPRE.ValueApprox.ExactStrategy.toStrategy,
  MIPRE.ValueApprox.ExactStrategy.value,
  MIPRE.ValueApprox.ExactStrategy.value_le_quantumValue,
  MIPRE.ValueApprox.abs_bornValue_sub_le,
  MIPRE.ValueApprox.exists_exactStrategy_value_gt,
  MIPRE.ValueApprox.lt_quantumValue_iff

-- blueprint `lem:recursive-compression`
#guard_sorry_free MIPRE.Cost.recursive_compression

-- blueprint `lem:semidecide-encoded`
#guard_sorry_free MIPRE.Cost.Data.primrec_decode_prod_nat,
  MIPRE.Cost.exists_semidecider_of_decode,
  MIPRE.Cost.exists_semidecider_prod_nat

-- blueprint `lem:smn`
#guard_sorry_free MIPRE.Cost.hardcode_size,
  MIPRE.Cost.hardcode_time,
  MIPRE.Cost.hardcode_time_rev,
  MIPRE.Cost.smn_polyTime

-- blueprint `lem:sync-le-valco`
#guard_sorry_free MIPRE.syncValue_le_commValue

-- blueprint `lem:sync-le-valstar`
#guard_sorry_free MIPRE.syncValue_le_quantumValue

-- blueprint `lem:universal-tm`
#guard_sorry_free MIPRE.Cost.exists_clocked_universal,
  MIPRE.Cost.exists_efficient_universal

-- blueprint `lem:value-lower-approx`
#guard_sorry_free MIPRE.Cost.exists_semidecider,
  MIPRE.ValueApprox.Check,
  MIPRE.ValueApprox.REPred.of_primrecRel_exists,
  MIPRE.ValueApprox.RawStrategy,
  MIPRE.ValueApprox.RawStrategy.interp,
  MIPRE.ValueApprox.check_iff_interp,
  MIPRE.ValueApprox.exists_check_iff,
  MIPRE.ValueApprox.primrecPred_check,
  MIPRE.ValueApprox.rePred_lt_quantumValue,
  MIPRE.exists_semidecider_lt_quantumValue,
  MIPRE.rePred_lt_quantumValue_comp

-- blueprint `thm:gowers-hatami`. Under `MIPRE/Background/` but with no vendored guard
-- of its own, its module importing only `Foundations.Distances` and Mathlib.
#guard_sorry_free MIPRE.gowers_hatami

-- blueprint `thm:parallel-repetition`: the statement's structure and its soundness bound,
-- guarded here with the Foundations; the instance `MIPRE.repetition` is guarded in
-- `MIPRE/Background/Repetition/Axioms.lean`, beside the vendored theorem it consumes.
#guard_sorry_free MIPRE.Repetition,
  MIPRE.Repetition.soundBound

-- blueprint `thm:succinct-sat`: the statement's structure and the instance that inhabits it.
#guard_sorry_free MIPRE.SAT.SuccinctCookLevin,
  MIPRE.SAT.succinctCookLevin

-- blueprint `lem:decoupled-5sat`, likewise.
#guard_sorry_free MIPRE.SAT.DecoupledDescriber,
  MIPRE.SAT.decoupledDescriber

-- blueprint `lem:schwartz-zippel`: the three shapes the low-degree machinery consumes,
-- all of them Mathlib's lemma specialized.
#guard_sorry_free MIPRE.LowDegree.agree,
  MIPRE.LowDegree.prob_agree_le_totalDegree,
  MIPRE.LowDegree.prob_agree_le_individualDegree,
  MIPRE.LowDegree.card_agree_le_of_natDegree

-- blueprint `lem:downsize-field`: items 1 and 2 of the paper's `lem:downsize_field`.
#guard_sorry_free MIPRE.LowDegree.coord_eq_trace,
  MIPRE.LowDegree.trace_mul_eq_dot

-- blueprint `lem:perfect-rejects-nothing`: the value-one characterization every completeness
-- argument in the pipeline needs.
#guard_sorry_free MIPRE.sum_re_tracial,
  MIPRE.re_nonneg_tracial,
  MIPRE.re_eq_zero_of_tracialValue_eq_one,
  MIPRE.SyncStrategy.value_eq_tracialValue,
  MIPRE.SyncStrategy.re_eq_zero_of_value_eq_one

-- blueprint `lem:cl-canonical`: the two complements of a subspace, and the canonical linear
-- map the low-degree test's line representatives are computed by.
#guard_sorry_free MIPRE.CL.finrank_perp,
  MIPRE.CL.perp_perp,
  MIPRE.CL.isCompl_canonCompl,
  MIPRE.CL.card_pivots,
  MIPRE.CL.ker_canonLin,
  MIPRE.CL.range_canonLin,
  MIPRE.CL.ker_lperp

-- blueprint `lem:hs-closeness` and `lem:close-measurements-close-values`: the two estimates
-- the soundness of oracularization rests on. The square root is spent in the second and
-- nowhere else.
#guard_sorry_free MIPRE.sum_hsNormSq_sub_le,
  MIPRE.sum_ntr_mul_ge

-- blueprint `lem:oracular-completeness` and `lem:oracular-soundness`: the two clauses of
-- `thm:oracularization` at the level of games.
#guard_sorry_free MIPRE.SeededGame.oracleStrategy,
  MIPRE.SeededGame.isPCC_oracleStrategy,
  MIPRE.SeededGame.oracleStrategy_value_eq_one,
  MIPRE.SeededGame.soundStrategy,
  MIPRE.SeededGame.soundStrategy_value_ge

-- blueprint `lem:group-algebra-selfdualization`: the self-dualization step of
-- `lem:self-dual-basis`, in the group algebra.
#guard_sorry_free MIPRE.LowDegree.exists_mul_involute_eq,
  MIPRE.LowDegree.mul_self_bijective,
  MIPRE.LowDegree.exists_mul_involute_eq_of_charTwo

-- blueprint `lem:self-dual-basis-exists`: in characteristic two and odd degree a self-dual
-- normal basis exists. Existence, not construction: `lem:self-dual-basis` still asserts an
-- algorithm, and that half is open.
#guard_sorry_free MIPRE.LowDegree.gramPair,
  MIPRE.LowDegree.gramPair_ofAlg,
  MIPRE.LowDegree.isUnit_gram,
  MIPRE.LowDegree.exists_gramPair_eq_one,
  MIPRE.LowDegree.exists_isSelfDualBasis_isNormalBasis,
  MIPRE.LowDegree.exists_selfDualNormalBasis_two

-- blueprint `fact:omega-anticomm-prob`: the probability that a Pauli-test question tuple is
-- anticommuting, and that it is commuting. The definitions are guarded with the theorems
-- because the statement is about them: `acTuples` and `cTuples` are the two events, and
-- `card_acTuples_add_card_cTuples` is what says they partition the sample space, so that
-- neither bound could hold for a mis-defined event.
#guard_sorry_free MIPRE.LowDegree.indVec,
  MIPRE.LowDegree.indPair,
  MIPRE.LowDegree.indPair_eq_eval,
  MIPRE.LowDegree.acGamma,
  MIPRE.LowDegree.acTuples,
  MIPRE.LowDegree.cTuples,
  MIPRE.LowDegree.card_acTuples_add_card_cTuples,
  MIPRE.LowDegree.prob_anticommuting_ge,
  MIPRE.LowDegree.prob_commuting_ge

-- blueprint `lem:admissible-field-exists`: the field interface `thm:pcp-decider` takes as a
-- parameter is inhabited.
#guard_sorry_free MIPRE.SAT.binFieldGalois,
  MIPRE.SAT.nonempty_binField

-- blueprint `lem:pauli-binary`: the coordinate relabelling of a self-dual basis carries the
-- Weyl system over `F_q` to the Weyl system over `F_2`, and the target really is qubits.
#guard_sorry_free MIPRE.Weyl.binEquiv,
  MIPRE.Weyl.binEquiv_apply,
  MIPRE.Weyl.binEquiv_add,
  MIPRE.Weyl.binEquiv_injective,
  MIPRE.Weyl.binEquiv_eq_iff,
  MIPRE.Weyl.trDot_binEquiv,
  MIPRE.Weyl.wX_binEquiv,
  MIPRE.Weyl.wZ_binEquiv,
  MIPRE.Weyl.card_binEquiv,
  MIPRE.Weyl.proj_binEquiv,
  MIPRE.Weyl.proj_wZ_binEquiv,
  MIPRE.Weyl.proj_wX_binEquiv,
  MIPRE.Weyl.eprScale_binEquiv,
  MIPRE.Weyl.epr_binEquiv,
  MIPRE.Weyl.pauli_binary,
  MIPRE.Weyl.exists_binEquiv_pauli_binary,
  MIPRE.Weyl.trDot_two,
  MIPRE.Weyl.sgn_trDot_two,
  MIPRE.Weyl.wZ_two_diag,
  MIPRE.Weyl.wX_two_apply

-- blueprint `lem:commutation-analysis`: consistency with a joint projective measurement on the
-- other side gives approximate commutation on this one, and the two facts that run it.
#guard_sorry_free MIPRE.qform_nonneg_of_nonneg,
  MIPRE.qform_le_of_le,
  MIPRE.sum_snorm_sq_mul_le,
  MIPRE.sum_snorm_sq_triangle',
  MIPRE.sum_snorm_sq_triangle3,
  MIPRE.sum_weighted_snorm_sq_triangle3,
  MIPRE.POVM.sum_mats_map_prod,
  MIPRE.POVM.sum_mats_map_prod',
  MIPRE.sum_xSqNorm_le_of_two_step,
  MIPRE.aOp_mono,
  MIPRE.bOp_mono,
  MIPRE.bOp_sum,
  MIPRE.sum_aOp_conjTranspose_mul_self_le_one,
  MIPRE.sum_bOp_conjTranspose_mul_self_le_one,
  MIPRE.sum_bOp_conjTranspose_mul_self_of_isPVM,
  MIPRE.IsPVM.marg_mul_marg,
  MIPRE.IsPVM.marg_mul_marg',
  MIPRE.IsPVM.sum_marg_left,
  MIPRE.IsPVM.sum_marg_right,
  MIPRE.IsPVM.marg_left,
  MIPRE.IsPVM.marg_right,
  MIPRE.sum_prod_snorm_sq_mul_le_fst,
  MIPRE.sum_prod_snorm_sq_mul_le_snd,
  MIPRE.commutation_analysis_abstract,
  MIPRE.commutation_analysis,
  MIPRE.commutation_analysis_aOp,
  MIPRE.obs2_commutator_eq

-- blueprint `lem:naimark-dilation`: a question-indexed family of POVMs is the compression, by one
-- question-independent isometry, of a family of projective measurements.
#guard_sorry_free MIPRE.ancillaProj,
  MIPRE.ancillaProj_conjTranspose,
  MIPRE.ancillaProj_mul_self,
  MIPRE.sum_ancillaProj,
  MIPRE.exists_isometry_of_povm,
  MIPRE.ancillaEmbed,
  MIPRE.ancillaEmbed_isometry,
  MIPRE.exists_unitary_extending,
  MIPRE.exists_projective_dilation,
  MIPRE.dotProduct_mulVec_submatrix,
  MIPRE.dotProduct_comp_equiv,
  MIPRE.dotProduct_mulVec_conj

-- blueprint `thm:linearity`: the Fourier transform of the family, Parseval making its squares a
-- POVM, the dilation, and the exactly linear family with its transported error.
#guard_sorry_free MIPRE.fourierOf,
  MIPRE.fourierOf_conjTranspose,
  MIPRE.fourierOf_posSemidef,
  MIPRE.sum_sgn_smul_fourierOf_sq,
  MIPRE.sum_fourierOf_sq,
  MIPRE.exists_exactly_linear,
  MIPRE.extVecA,
  MIPRE.ancillaEmbed_kron_isometry,
  MIPRE.norm_evec_extVecA,
  MIPRE.kron_one_mul_ancillaEmbed,
  MIPRE.ancillaEmbed_conjTranspose_mul_kron_one,
  MIPRE.compress_mul_kron_one,
  MIPRE.compress_kron_one_mul,
  MIPRE.qform_extVecA,
  MIPRE.stateSqNorm_sub_of_isometry,
  MIPRE.conjTranspose_mul_self_of_involution,
  MIPRE.exists_exactly_linear_close

/-!
## The one axiom

`#guard_sorry_free` catches `sorryAx` and nothing else, so an `axiom` would otherwise enter
the dependency graph unnoticed. There is exactly one, and it is the one the blueprint says
this project assumes beyond Mathlib: `MIPRE.LowDegree.exists_shoup_irreducible`, Shoup's
deterministic irreducible-polynomial construction at `p = 2`, the single admitted node
(`1.1.6.1.1`) under `lem:self-dual-basis`. `MIPRE/Foundations/LowDegree/Shoup.lean` carries
its contract, including the five things it deliberately does not claim.

The pin itself lives beside the axiom, in `Shoup.lean`: a `#guard_msgs in #print axioms`
on the one declaration that uses it, which fails the build if another axiom appears, if the
dependency disappears (the axiom having been proved, which is worth noticing), or if the name
changes. It is not written here because `#print axioms` in *this* file is how the guard files
claim a blueprint proof is formalized, and pinning an axiom is not such a claim --- Shoup's
theorem is assumed, not proved. `scripts/lean-coverage.py` closes the loop from the other
side: it fails if any `axiom` declared outside the vendored trees is not named in this file.
-/



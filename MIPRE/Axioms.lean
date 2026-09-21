/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.GuardSorryFree
import MIPRE.Foundations.Blocks
import MIPRE.Foundations.CL.Basic
import MIPRE.Foundations.LowDegree.SchwartzZippel
import MIPRE.Foundations.LowDegree.ZeroBasis
import MIPRE.Foundations.LowDegree.BinarySquareRoot
import MIPRE.Foundations.LowDegree.BinaryInverse
import MIPRE.Foundations.LowDegree.BinaryMatrixInverse
import MIPRE.Foundations.LowDegree.BinaryKernel
import MIPRE.Foundations.SAT.FieldTrace
import MIPRE.Foundations.SAT.FrobeniusMatrix
import MIPRE.Foundations.SAT.TraceGram
import MIPRE.Foundations.SAT.BasisTransport
import MIPRE.Foundations.SAT.EffectiveSelfDual
import MIPRE.Foundations.SAT.EffectiveNormalBasis
import MIPRE.Foundations.Introspection.Commutation
import MIPRE.Foundations.Introspection.Twirl
import MIPRE.Foundations.Introspection.Measurements
import MIPRE.Foundations.Introspection.BlockPOVM
import MIPRE.Foundations.Introspection.TwirlDistance
import MIPRE.Foundations.Introspection.VaryingPauliMixing
import MIPRE.Foundations.Introspection.Conditioning
import MIPRE.Foundations.Introspection.ConditionalConsistency
import MIPRE.Foundations.CL.Graph
import MIPRE.Foundations.CL.DetypingQueries
import MIPRE.Foundations.CL.DetypingSoundness
import MIPRE.Foundations.SAT.Arithmetization
import MIPRE.Foundations.SAT.FiniteCircuitArithmetization
import MIPRE.Foundations.SAT.CircuitFieldCorrect
import MIPRE.TM.CookLevin.PcpCircuit
import MIPRE.TM.CookLevin.PcpViewSize
import MIPRE.TM.CookLevin.ClassicalPcp
import MIPRE.Foundations.SAT.Padding
import MIPRE.Foundations.SAT.PcpAlgebra
import MIPRE.Foundations.SAT.PcpBlocks
import MIPRE.Foundations.SAT.QuotientField
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
import MIPRE.TM.CookLevin.PaddingParams
import MIPRE.TM.CookLevin.PcpParameters
import MIPRE.LCS.MagicSquare.Strategy
import MIPRE.LCS.Strategy.Equivalence
import MIPRE.LCS.Strategy.ObservableToProjector
import MIPRE.TM.Code.Encoding.MachineCode
import MIPRE.Foundations.WeylBinary
import MIPRE.Foundations.Commutation
import MIPRE.Foundations.Linearity
import MIPRE.Foundations.Sandwich
import MIPRE.Foundations.Pasting
import MIPRE.Foundations.Expanded
import MIPRE.Foundations.WeylEPR
import MIPRE.Foundations.Swap
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

-- blueprint `lem:pcp-zero-basis`: preserve the individual-degree bounds needed by the PCP.
#guard_sorry_free MIPRE.SAT.ArrayProg.eqBits,
  MIPRE.SAT.ArrayProg.eqNat,
  MIPRE.SAT.ArrayProg.getD,
  MIPRE.SAT.Fml.renameBy,
  MIPRE.SAT.Fml.eval_rename,
  MIPRE.SAT.ceilPowerProg,
  MIPRE.SAT.le_ceilPower,
  MIPRE.SAT.ceilPower_le_twice,
  MIPRE.Cost.PolyTimeFun.bitsValue,
  MIPRE.Cost.PolyTimeFun.predN,
  MIPRE.Cost.PolyTimeFun.addUnary,
  MIPRE.Cost.PolyTimeFun.subUnary

#guard_sorry_free MIPRE.SAT.cubeIndexEquiv,
  MIPRE.SAT.clauseInput5_injective,
  MIPRE.SAT.PcpParams.clauseInput5_pointClause,
  MIPRE.SAT.PcpParams.pointClause_pointFromClause,
  MIPRE.SAT.PcpParams.degreeOf_circuitArith,
  MIPRE.SAT.PcpParams.eval_circuitArith_bool,
  MIPRE.SAT.PcpParams.eval_iff_exists_circuitArith,
  MIPRE.SAT.PcpParams.exists_proof_of_formula5_sat,
  MIPRE.SAT.PcpParams.formula5_sat_of_majority,
  MIPRE.SAT.PcpParams.completeness_of_describes,
  MIPRE.SAT.PcpParams.soundness_of_describes,
  MIPRE.TM.CookLevin.Pad.esize_bitBlocks_le,
  MIPRE.TM.CookLevin.Pad.esize_view_le,
  MIPRE.TM.CookLevin.Pad.pcpInput_size_polynomial,
  MIPRE.TM.CookLevin.Pad.pcpProgram_time_le

#guard_sorry_free MIPRE.SAT.PolyTimeFun.casesGate,
  MIPRE.SAT.Circuit.lastInputValueProg,
  MIPRE.SAT.Circuit.lastInputValue_range,
  MIPRE.SAT.Circuit.gateBitsProg,
  MIPRE.SAT.Circuit.evalBits_gateBits,
  MIPRE.SAT.Circuit.circuitBitsProg,
  MIPRE.SAT.Circuit.circuitBitsProg_apply,
  MIPRE.SAT.Circuit.length_circuitBits,
  MIPRE.SAT.Circuit.evalBits_circuitBits,
  MIPRE.SAT.Circuit.evalBits_circuitBits_finite,
  MIPRE.SAT.shoupBinField_charP,
  MIPRE.SAT.shoupBinField_toBits_ofBits

#guard_sorry_free MIPRE.LowDegree.eval_killCompl,
  MIPRE.LowDegree.degreeOf_killCompl_le,
  MIPRE.SAT.Circuit.inputRef_injective,
  MIPRE.SAT.Circuit.routedConsistent_iff,
  MIPRE.SAT.Circuit.eval_iff_routedConsistent,
  MIPRE.SAT.Circuit.degreeOf_routedArith_le,
  MIPRE.SAT.Circuit.eval_routedArith_iff,
  MIPRE.SAT.Circuit.eval_routedArith_bool,
  MIPRE.SAT.Circuit.degreeOf_finiteArith_le,
  MIPRE.SAT.Circuit.eval_finiteArith_bool,
  MIPRE.SAT.Circuit.eval_iff_exists_finiteArith

#guard_sorry_free MIPRE.TM.CookLevin.Pad.formula5_circuit,
  MIPRE.TM.CookLevin.Pad.describe,
  MIPRE.TM.CookLevin.Pad.describe_wellFormed,
  MIPRE.TM.CookLevin.Pad.describe_describes,
  MIPRE.TM.CookLevin.Pad.innerDim_isPow,
  MIPRE.TM.CookLevin.Pad.innerDim_le,
  MIPRE.TM.CookLevin.Pad.two_mul_le_innerDim,
  MIPRE.SAT.Circuit.padGatesProg,
  MIPRE.SAT.Circuit.wellFormed_padGates,
  MIPRE.SAT.Circuit.eval_padGates,
  MIPRE.TM.CookLevin.Pad.describeExact,
  MIPRE.TM.CookLevin.Pad.describeExact_wellFormed,
  MIPRE.TM.CookLevin.Pad.describeExact_describes,
  MIPRE.TM.CookLevin.Pad.describeExact_gateCount,
  MIPRE.TM.CookLevin.Pad.describeExact_variables,
  MIPRE.TM.CookLevin.Pad.outerDim_isPow,
  MIPRE.TM.CookLevin.Pad.outerDim_polynomial,
  MIPRE.TM.CookLevin.Pad.innerDim_add_bound_le_gateCount,
  MIPRE.TM.CookLevin.Pad.paddingParams,
  MIPRE.TM.CookLevin.Pad.paddingParams_apply

#guard_sorry_free MIPRE.TM.CookLevin.Pad.pcpParamsProg,
  MIPRE.TM.CookLevin.Pad.pcpParamsProg_apply,
  MIPRE.TM.CookLevin.Pad.pcpParams_odd,
  MIPRE.TM.CookLevin.Pad.pcpParams_field_large,
  MIPRE.TM.CookLevin.Pad.pcpParams_inner_dvd,
  MIPRE.TM.CookLevin.Pad.pcpParams_outer_dvd

#guard_sorry_free MIPRE.LowDegree.exists_cubeZero_division,
  MIPRE.LowDegree.exists_zero_basis

-- Formula arithmetization and the two classical PCP polynomial tests.
#guard_sorry_free MIPRE.SAT.Cnf5.sat_pad_iff,
  MIPRE.SAT.Circuit.DescribesDecider.of_pad

#guard_sorry_free MIPRE.SAT.Fml.eval_arith,
  MIPRE.SAT.Fml.degreeOf_arith_le

#guard_sorry_free MIPRE.SAT.PcpAlgebra.completeness,
  MIPRE.SAT.PcpAlgebra.degreeOf_constraint_le,
  MIPRE.SAT.PcpAlgebra.degreeOf_zeroCombination_le,
  MIPRE.SAT.PcpAlgebra.identities_of_majority,
  MIPRE.SAT.PcpAlgebra.clause_satisfied_of_identities,
  MIPRE.SAT.PcpAlgebra.clause_decoded_of_identities,
  MIPRE.LowDegree.eq_of_majority_agree,
  MIPRE.LowDegree.eq_of_majority_subset

#guard_sorry_free MIPRE.SAT.PcpAlgebra.degreeOf_liftAnswer_le,
  MIPRE.SAT.PcpAlgebra.literal_product_degree_le,
  MIPRE.SAT.PcpAlgebra.honest_constraint_degree_le,
  MIPRE.SAT.PcpAlgebra.typedAccepts_ev_iff,
  MIPRE.SAT.PcpAlgebra.exists_proof_of_satisfying_assignment,
  MIPRE.SAT.PcpAlgebra.decoded_clause_of_majority

-- blueprint `lem:group-algebra-selfdualization`: the self-dualization step of
-- `lem:self-dual-basis`, in the group algebra.
#guard_sorry_free MIPRE.LowDegree.exists_mul_involute_eq,
  MIPRE.LowDegree.mul_self_bijective,
  MIPRE.LowDegree.exists_mul_involute_eq_of_charTwo,
  MIPRE.LowDegree.binarySquareRoot,
  MIPRE.LowDegree.coeff_binarySquareRoot,
  MIPRE.LowDegree.binarySquareRoot_mul_self,
  MIPRE.LowDegree.binarySquareRoot_mul_involute

-- The coefficient permutation is an actual polynomial-time program.
#guard_sorry_free MIPRE.LowDegree.rootBitsProg,
  MIPRE.LowDegree.rootBitsProg_time_le,
  MIPRE.LowDegree.groupOfBits_rootBits,
  MIPRE.LowDegree.rootBitsProg_square

-- Effective polynomial-basis arithmetic, modulo only the existing Shoup axiom.
#guard_sorry_free MIPRE.LowDegree.BinaryPolynomial.normalize_monic,
  MIPRE.LowDegree.BinaryPolynomial.evalBits_xor,
  MIPRE.LowDegree.BinaryPolynomial.evalBits_mulReduce,
  MIPRE.LowDegree.BinaryPolynomial.xorBitsProg,
  MIPRE.LowDegree.BinaryPolynomial.mulReduceProg,
  MIPRE.LowDegree.BinaryPolynomial.shoupLowerCoeffs_length,
  MIPRE.LowDegree.BinaryPolynomial.shoupLowerCoeffs_poly,
  MIPRE.SAT.quotientBinField,
  MIPRE.SAT.quotientBinField_toBits_ofBits,
  MIPRE.SAT.quotientBinField_ofBits,
  MIPRE.SAT.quotientBinField_add,
  MIPRE.SAT.quotientBinField_mul,
  MIPRE.SAT.shoupBinField,
  MIPRE.SAT.shoupAdmissibleField,
  MIPRE.SAT.shoupMulProg_time_le,
  MIPRE.SAT.shoupMulProg_correct

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

-- The complete classical PCP and its executable field tests.
#guard_sorry_free MIPRE.SAT.BinField,
  MIPRE.SAT.PcpParams,
  MIPRE.SAT.PcpProof,
  MIPRE.SAT.PcpProof.ev,
  MIPRE.SAT.ViewFormat,
  MIPRE.SAT.PcpDecider,
  MIPRE.SAT.validProg_true_iff,
  MIPRE.SAT.viewFormatProg_true_iff,
  MIPRE.SAT.shoupRoot_equation,
  MIPRE.SAT.shoupRoot_eval_toBits,
  MIPRE.SAT.shoupRoot_eval_eq_iff,
  MIPRE.SAT.PcpFieldTests.checksProg_true_iff,
  MIPRE.SAT.PcpViewTests.checks_typed_iff,
  MIPRE.TM.CookLevin.Pad.verifyPcp_reject_invalid,
  MIPRE.TM.CookLevin.Pad.verifyPcp_time_le,
  MIPRE.TM.CookLevin.Pad.verifyPcp_rawView_iff,
  MIPRE.TM.CookLevin.Pad.classicalPcp_completeness,
  MIPRE.TM.CookLevin.Pad.classicalPcp_soundness,
  MIPRE.TM.CookLevin.Pad.classicalPcpDecider

-- Effective inversion, Frobenius iteration, and trace.
#guard_sorry_free MIPRE.LowDegree.BinaryPolynomial.powerBitsProg,
  MIPRE.LowDegree.BinaryPolynomial.evalBits_powerBits,
  MIPRE.LowDegree.BinaryPolynomial.evalBits_inverseBits,
  MIPRE.SAT.shoupInvProg_correct,
  MIPRE.SAT.shoupInvProg_time_le,
  MIPRE.LowDegree.BinaryPolynomial.frobeniusTraceProg,
  MIPRE.LowDegree.BinaryPolynomial.evalBits_frobeniusTrace,
  MIPRE.LowDegree.BinaryPolynomial.evalBits_frobeniusTrace_trace,
  MIPRE.SAT.shoupBinField_finrank,
  MIPRE.SAT.shoupFrobeniusTraceProg_frobenius,
  MIPRE.SAT.shoupFrobeniusTraceProg_period,
  MIPRE.SAT.shoupTraceProg_correct,
  MIPRE.SAT.shoupTraceProg_time_le

-- Effective binary linear algebra and matrix inversion.
#guard_sorry_free MIPRE.LowDegree.BinaryLinear.dotBits_vectorBits,
  MIPRE.LowDegree.BinaryLinear.applyBits_matrixBits,
  MIPRE.LowDegree.BinaryLinear.xorBits_vectorBits,
  MIPRE.LowDegree.BinaryLinear.transposeBits_matrixBits,
  MIPRE.LowDegree.BinaryLinear.mulBits_matrixBits,
  MIPRE.LowDegree.BinaryLinear.dotBitsProg,
  MIPRE.LowDegree.BinaryLinear.applyBitsProg,
  MIPRE.LowDegree.BinaryLinear.transposeBitsProg,
  MIPRE.LowDegree.BinaryLinear.mulBitsProg,
  MIPRE.LowDegree.BinaryLinear.reduceRowsProg,
  MIPRE.LowDegree.BinaryLinear.reduceRows_rowBits,
  MIPRE.LowDegree.BinaryLinear.represents_typedReduce,
  MIPRE.LowDegree.BinaryLinear.basisRowsProg,
  MIPRE.LowDegree.BinaryLinear.basisRowsProg_correct,
  MIPRE.LowDegree.BinaryLinear.typedBasis_linearIndependent,
  MIPRE.LowDegree.BinaryLinear.typedBasis_span,
  MIPRE.LowDegree.BinaryLinear.typedBasis_length_le,
  MIPRE.LowDegree.BinaryLinear.basisSolveProg_correct,
  MIPRE.LowDegree.BinaryLinear.matrixSolveProg_correct,
  MIPRE.LowDegree.BinaryLinear.matrixSolveProg_encoding,
  MIPRE.LowDegree.BinaryLinear.inverseMatrixProg,
  MIPRE.LowDegree.BinaryLinear.inverseMatrixProg_encoding,
  MIPRE.LowDegree.BinaryLinear.inverseMatrixProg_correct,
  MIPRE.LowDegree.BinaryLinear.mul_inverseMatrix,
  MIPRE.LowDegree.BinaryLinear.inverseMatrix_mul

-- Effective generators of binary matrix kernels.
#guard_sorry_free MIPRE.LowDegree.BinaryLinear.kernelMap_range,
  MIPRE.LowDegree.BinaryLinear.kernel_generators_span,
  MIPRE.LowDegree.BinaryLinear.kernelGeneratorsProg,
  MIPRE.LowDegree.BinaryLinear.kernelGeneratorsProg_encoding,
  MIPRE.LowDegree.BinaryLinear.kernelGeneratorsProg_correct

-- Effective field matrices and multiplication-table transport.
#guard_sorry_free MIPRE.LowDegree.BinaryLinear.vectorBits_vectorValue,
  MIPRE.SAT.shoupCoordinateEquiv_encoding,
  MIPRE.SAT.shoupPowerBasis_encoding,
  MIPRE.SAT.shoupMulProg_encoding,
  MIPRE.SAT.fieldMapMatrixProg_correct,
  MIPRE.SAT.shoupFrobeniusMatrixProg,
  MIPRE.SAT.shoupFrobeniusMatrixProg_correct,
  MIPRE.SAT.shoupFrobeniusMatrix_minpoly,
  MIPRE.SAT.shoupFrobeniusMatrix_period,
  MIPRE.SAT.shoupFrobeniusMatrix_squarefree,
  MIPRE.SAT.shoupFrobeniusMatrixProg_time_le,
  MIPRE.SAT.shoupTraceBitProg_correct,
  MIPRE.SAT.shoupTraceGramProg,
  MIPRE.SAT.shoupTraceGramProg_correct,
  MIPRE.SAT.shoupTraceGram_surjective,
  MIPRE.SAT.shoupInverseGramProg,
  MIPRE.SAT.shoupInverseGramProg_correct,
  MIPRE.SAT.shoupInBasisProg,
  MIPRE.SAT.shoupInBasisProg_correct,
  MIPRE.SAT.shoupMultiplicationTableProg,
  MIPRE.SAT.shoupMultiplicationTableProg_correct,
  MIPRE.SAT.shoupMultiplicationTableProg_time_le

-- Effective self-dualization of a supplied normal basis.
#guard_sorry_free MIPRE.Cost.recordIteratesProg,
  MIPRE.Cost.recordIteratesProg_apply,
  MIPRE.LowDegree.BinaryLinear.groupMatrixHom,
  MIPRE.LowDegree.BinaryLinear.inverseMatrix_groupMatrix,
  MIPRE.LowDegree.BinaryLinear.inverseRootMatrix_square,
  MIPRE.LowDegree.BinaryLinear.inverseRootMatrix_gram,
  MIPRE.LowDegree.BinaryLinear.circulantBitsProg_correct,
  MIPRE.LowDegree.BinaryLinear.rootBitsProg_vectorBits,
  MIPRE.LowDegree.BinaryLinear.inverseRootMatrixProg,
  MIPRE.LowDegree.BinaryLinear.inverseRootMatrixProg_correct,
  MIPRE.SAT.shoupTraceGram_normal_circulant,
  MIPRE.SAT.shoupNormalGram_selfDualize,
  MIPRE.SAT.shoupChangedVectors_normal,
  MIPRE.SAT.shoupSelfDualBasis_selfDual,
  MIPRE.SAT.shoupSelfDualBasis_normal,
  MIPRE.SAT.shoupSelfDualizeProg,
  MIPRE.SAT.shoupSelfDualizeProg_correct,
  MIPRE.SAT.shoupSelfDualizeProg_time_le

-- Effective normal element and complete self-dual normal basis algorithm.
#guard_sorry_free MIPRE.LowDegree.PrimitiveBinaryComponent.exists_mul_eq,
  MIPRE.LowDegree.splitAllComponents_primitive,
  MIPRE.LowDegree.ComponentFamily.length_le_finrank,
  MIPRE.LowDegree.BinaryLinear.groupFixedGeneratorsProg_correct,
  MIPRE.LowDegree.BinaryLinear.groupComponents_primitive,
  MIPRE.LowDegree.BinaryLinear.groupComponents_length_le,
  MIPRE.LowDegree.BinaryLinear.groupComponentsProg,
  MIPRE.LowDegree.BinaryLinear.groupComponentsProg_correct,
  MIPRE.SAT.shoupFrobeniusAction_injective,
  MIPRE.SAT.shoupProjectedVector_ne_zero,
  MIPRE.SAT.shoupNormalElement_projection,
  MIPRE.SAT.shoupNormalOrbitMap_injective,
  MIPRE.SAT.shoupNormalBasis_normal,
  MIPRE.SAT.shoupOrbitProg_correct,
  MIPRE.SAT.shoupActionProg_correct,
  MIPRE.SAT.shoupNormalElementProg_correct,
  MIPRE.SAT.shoupNormalBasisProg,
  MIPRE.SAT.shoupNormalBasisProg_correct
#guard_sorry_free MIPRE.SAT.shoupSelfDualNormalBasis_selfDual,
  MIPRE.SAT.shoupSelfDualNormalBasis_normal,
  MIPRE.SAT.shoupSelfDualNormalBasisProg,
  MIPRE.SAT.shoupSelfDualNormalBasisProg_correct,
  MIPRE.SAT.shoupSelfDualNormalDataProg,
  MIPRE.SAT.shoupSelfDualNormalDataProg_correct,
  MIPRE.SAT.shoupSelfDualNormalDataProg_time_le,
  MIPRE.SAT.effective_selfDualNormalBasis

-- Introspection's linear-map Fourier formulas, commutation, twirl, and positive index.
#guard_sorry_free MIPRE.Introspection.subspaceTrace_eq_zero_iff,
  MIPRE.Introspection.sum_subspace_sign,
  MIPRE.Introspection.linear_measurement_fourier,
  MIPRE.Introspection.linear_measurement_fourier_inverse,
  MIPRE.Introspection.linear_measurements_commute,
  MIPRE.Introspection.twirlX_wZ,
  MIPRE.Introspection.twirlZ_wX,
  MIPRE.Introspection.delta_zero_index,
  MIPRE.Introspection.two_le_exp_index_iff

#guard_sorry_free MIPRE.Introspection.weyl_projectors_isPVM,
  MIPRE.Introspection.linear_measurement_isPVM,
  MIPRE.Introspection.joint_measurement_isPVM,
  MIPRE.Introspection.sampling_hiding_isPVM

#guard_sorry_free MIPRE.Introspection.linear_twirl_blocks,
  MIPRE.Introspection.averagedBlock_posSemidef,
  MIPRE.Introspection.sum_averagedBlock_eq_one,
  MIPRE.Introspection.blockPOVM,
  MIPRE.Introspection.linear_twirl_povm

#guard_sorry_free MIPRE.Introspection.stateSqNorm_mul_of_isometry,
  MIPRE.Introspection.unitaryTwirl_dist_le,
  MIPRE.Introspection.unitaryTwirl_outcome_dist_le

-- blueprint `lem:qld-combined-points`, the generic half: the Fourier dictionary between an
-- `F_q`-valued measurement and its binary observables, the sandwich of two projective
-- measurements, the five-link chain that makes it self-consistent, the two-sided extension, and
-- the dilated joint measurement.
#guard_sorry_free MIPRE.fourierVec,
  MIPRE.sum_norm_fourierVec_sq,
  MIPRE.trObs,
  MIPRE.trFourier,
  MIPRE.trFourier_trObs,
  MIPRE.trObs_map,
  MIPRE.pairVec,
  MIPRE.sum_prod_eq_sum_pairVec,
  MIPRE.fourierOf_pair_mul,
  MIPRE.sum_stateSqNorm_fourierOf,
  MIPRE.obs2_map,
  MIPRE.swapVec_expVec,
  MIPRE.Weyl.swapVec_epr,
  MIPRE.bornProb_swapVec,
  MIPRE.povmValue_swapVec_of_symm,
  MIPRE.sum_weighted_mul_le_sqrt,
  MIPRE.sum_weighted_sqrt_le,
  MIPRE.abs_qform_conjTranspose_mul_le,
  MIPRE.proj_le_one,
  MIPRE.snorm_le_one_of_proj,
  MIPRE.bornProb_eq_qform,
  MIPRE.abs_qform_aOp_mul_bOp_le,
  MIPRE.stateNorm_mul_le,
  MIPRE.norm_stateVecB_mul_le,
  MIPRE.xSqNorm_eq_expand,
  MIPRE.one_sub_sum_bornProb_eq,
  MIPRE.sand,
  MIPRE.sum_sand,
  MIPRE.sandPOVM,
  MIPRE.sum_stateSqNorm_ord,
  MIPRE.abs_link1_le,
  MIPRE.abs_link2_le,
  MIPRE.abs_link3_le,
  MIPRE.link4_eq,
  MIPRE.link5_eq,
  MIPRE.one_sub_sum_bornProb_sand_le,
  MIPRE.extVec2,
  MIPRE.extVec2_unit,
  MIPRE.bornProb_extVec2,
  MIPRE.sum_xSqNorm_dilated_eq,
  MIPRE.sum_xSqNorm_dilated_aOp_le,
  MIPRE.exists_projective_joint

-- blueprint `lem:qld-padded-points`, the generic half: Parseval over one and two copies of the
-- field, the coarse-graining by a linear form whose zero probe drops out, and the two ways a
-- coarse-graining is paid for -- free for projective families, Parseval otherwise.
#guard_sorry_free MIPRE.sum_norm_fourierVecRaw_sq,
  MIPRE.trVecRaw,
  MIPRE.sum_norm_trVecRaw_sq,
  MIPRE.sum_norm_char_two_sq,
  MIPRE.sum_avg_norm_fibre_sq,
  MIPRE.sum_xSqNorm_map_le,
  MIPRE.sum_mulVec',
  MIPRE.xSqNorm_eq_norm_evec_sq,
  MIPRE.sum_fibre_dev

-- blueprint `lem:cool-closeness-fact`: attaching a family's own element and summing along the
-- fibres of an outcome map costs nothing, simultaneously over all the fibres; and the marginal
-- step that consumes it.
#guard_sorry_free MIPRE.snorm_sq_mul_le_of_contraction,
  MIPRE.snorm_sq_sum_proj_mul,
  MIPRE.sum_snorm_sq_cool,
  MIPRE.sum_fibre_fst,
  MIPRE.sum_snorm_sq_cool_prod,
  MIPRE.IsPVM.aOp,
  MIPRE.IsPVM.bOp,
  MIPRE.sum_xSqNorm_marg_le,
  MIPRE.sum_snorm_sq_mul_proj_le,
  MIPRE.sum_xSqNorm_marg_le',
  MIPRE.IsPVM.comp_equiv,
  MIPRE.normSq_stateVecB_sub_le,
  MIPRE.sum_weighted_const_mul,
  MIPRE.xSqNorm_extVec2_aOp

-- blueprint `lem:pasting-updated`, the `k = 2` case: Alice's joint projective measurement against
-- the sandwich of Bob's two families, coarse-grained by evaluation. The collision term is a
-- hypothesis of the analytic core and a lemma of its own for a product question distribution.
#guard_sorry_free MIPRE.fibSum,
  MIPRE.isPVM_fibSum,
  MIPRE.sum_fiber,
  MIPRE.abs_sum_sum_le_sqrt,
  MIPRE.sum_comm4,
  MIPRE.sum_prod_eq,
  MIPRE.sum_prod_uniform,
  MIPRE.sum_prod_uniform_one,
  MIPRE.sum_weighted_add,
  MIPRE.sum_weighted_div,
  MIPRE.qform_conjTranspose,
  MIPRE.sum_sq_le_one_of_sum_eq_one,
  MIPRE.sum_snorm_sq_orth_le_one,
  MIPRE.sum_snorm_sq_povm_le_one,
  MIPRE.sum_snorm_sq_prod_le_one,
  MIPRE.sum_bornProb_le_fibSum,
  MIPRE.sum_xSqNorm_fibSum_le,
  MIPRE.sum_snorm_sq_comm_eq,
  MIPRE.pasteJ,
  MIPRE.sandOp_posSemidef,
  MIPRE.sum_sandOp,
  MIPRE.sum_snorm_sq_sandOp_le_one,
  MIPRE.sandOpG_posSemidef,
  MIPRE.sum_sandOpG,
  MIPRE.pasteJ_posSemidef,
  MIPRE.sum_pasteJ,
  MIPRE.abs_sigma_sub_cloud_le,
  MIPRE.abs_sand_sub_ord_le,
  MIPRE.sum_bornProb_ord_ge,
  MIPRE.sum_snorm_sq_comm_coarse_le,
  MIPRE.collisionTerm,
  MIPRE.collisionTerm_nonneg,
  MIPRE.strife_sub_cloud_eq,
  MIPRE.sum_snorm_sq_comm_fine_le,
  MIPRE.one_sub_sum_bornProb_pasteJ_le',
  MIPRE.one_sub_sum_bornProb_pasteJ_le,
  MIPRE.sum_xSqNorm_pasteJ_le,
  MIPRE.sum_collisionTerm_le

/-! ## Introspection mixing, conditioning, and graph rejection sampling -/

#guard_sorry_free MIPRE.Introspection.sum_norm_linearFourier_sq,
  MIPRE.Introspection.linear_measurement_parseval,
  MIPRE.Introspection.linear_measurement_commutator_parseval,
  MIPRE.Introspection.linear_measurement_commutator_parseval_avg,
  MIPRE.Introspection.commutator_product_bound,
  MIPRE.Introspection.two_sided_commutation,
  MIPRE.Introspection.two_sided_commutation_avg,
  MIPRE.Introspection.unitaryTwirl_comp,
  MIPRE.Introspection.composed_twirl_dist_le,
  MIPRE.Introspection.submeasurement_completion_mass,
  MIPRE.Introspection.submeasurement_completion_dist,
  MIPRE.Introspection.submeasurement_completion_dist_avg,
  MIPRE.Introspection.snorm_right_projector_le,
  MIPRE.Introspection.retained_fibre_dist,
  MIPRE.Introspection.controlledPOVM,
  MIPRE.Introspection.retained_block_le_completion,
  MIPRE.Introspection.block_retention_precompletion,
  MIPRE.Introspection.block_retention_dist_avg,
  MIPRE.Introspection.mirror_expVec,
  MIPRE.Introspection.eprWithAux_norm,
  MIPRE.Introspection.eprWithAux_wX_mirror,
  MIPRE.Introspection.eprWithAux_readout_mirror,
  MIPRE.Introspection.pauli_twirl_dist_le,
  MIPRE.Introspection.fine_commutator_parseval,
  MIPRE.Introspection.kernel_commutator_parseval,
  MIPRE.Introspection.pauli_twirl_readout_dist_le,
  MIPRE.Introspection.exists_pauli_mixing,
  MIPRE.Introspection.exists_pauli_mixing_avg,
  MIPRE.Introspection.exists_pauli_mixing_varying,
  MIPRE.Introspection.mixing_error_sqrt_bound,
  MIPRE.Introspection.exists_pauli_mixing_sqrt,
  MIPRE.Introspection.stateSqNorm_expVec_kron,
  MIPRE.Introspection.conditional_sqNorm,
  MIPRE.Introspection.conditional_commutator,
  MIPRE.Introspection.conditional_sqNorm_sum,
  MIPRE.Introspection.conditional_commutator_sum,
  MIPRE.Introspection.submeasurement_agreement_dist,
  MIPRE.Introspection.conditional_consistency,
  MIPRE.CL.Graph.presentation,
  MIPRE.CL.Graph.presentation_exactlyOn,
  MIPRE.CL.Graph.presentation_eval,
  MIPRE.CL.Graph.localValid_output_iff,
  MIPRE.CL.Graph.localValid_both_iff,
  MIPRE.CL.Graph.card_validSeeds,
  MIPRE.CL.Graph.mem_validSeeds_iff,
  MIPRE.CL.Graph.invalid_seed_locally_detected,
  MIPRE.CL.Graph.opposite_output_zero_of_invalid,
  MIPRE.CL.Graph.card_seeds,
  MIPRE.CL.Graph.validProbability_eq,
  MIPRE.CL.Graph.inv_pow_le_validProbability,
  MIPRE.CL.Graph.conditional_average

/-!
## Detyped presentations, query routing, and finite-game soundness

The finite-game result uses the same answer alphabets. It does not discharge
the ambient wrapper, answer-cutoff, or runtime obligations.
-/

#guard_sorry_free MIPRE.CL.Detyping.presentation,
  MIPRE.CL.Detyping.presentation_exactlyOn,
  MIPRE.CL.Detyping.presentation_eval,
  MIPRE.CL.Detyping.card_coord,
  MIPRE.CL.Detyping.select_eq_some_iff,
  MIPRE.CL.Detyping.select_output,
  MIPRE.CL.Detyping.select_eq_none_iff,
  MIPRE.CL.Detyping.graph_output_of_select,
  MIPRE.CL.Detyping.presentation_eval_valid,
  MIPRE.CL.Detyping.presentation_eval_invalid,
  MIPRE.CL.Detyping.sum_valid_questions,
  MIPRE.CL.Detyping.conditional_average,
  MIPRE.CL.CLFun.embed,
  MIPRE.CL.CLFun.ExactlyOn.embed,
  MIPRE.CL.CLFun.eval_embed,
  MIPRE.CL.CLFun.eval_truncate_embed,
  MIPRE.CL.CLFun.factorOfPrefix_embed,
  MIPRE.CL.CLFun.mapOfPrefix_embed,
  MIPRE.CL.CLFun.zeroOn_exactlyOn,
  MIPRE.CL.CLFun.eval_truncate_zeroOn,
  MIPRE.CL.CLFun.mapOfPrefix_zeroOn,
  MIPRE.CL.CLFun.factorOfPrefix_zeroOn,
  MIPRE.CL.Detyping.marginal_graph,
  MIPRE.CL.Detyping.marginal_content,
  MIPRE.CL.Detyping.factor_first,
  MIPRE.CL.Detyping.factor_second,
  MIPRE.CL.Detyping.factor_content,
  MIPRE.CL.Detyping.linear_first,
  MIPRE.CL.Detyping.linear_second,
  MIPRE.CL.Detyping.linear_content,
  MIPRE.SampledGame.game,
  MIPRE.SampledGame.sum_dist_mul,
  MIPRE.SampledGame.one_sub_value,
  MIPRE.CL.Detyping.typedGame,
  MIPRE.CL.Detyping.game,
  MIPRE.CL.Detyping.game_mu_eq_clDist,
  MIPRE.CL.Detyping.view_disjoint,
  MIPRE.CL.Detyping.restrict,
  MIPRE.CL.Detyping.restrict_state,
  MIPRE.CL.Detyping.restrict_failAt,
  MIPRE.CL.Detyping.valid_average_le,
  MIPRE.CL.Detyping.restrict_failure_eq,
  MIPRE.CL.Detyping.restrict_failure_le,
  MIPRE.CL.Detyping.restrict_value_ge

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

/-! ## Blocks of an index type

Blueprint `lem:qld-sublines`, the measure-preserving half of a block decomposition: an assignment to
a sum index type is a pair of assignments to the summands, uniform and independent, together with the
bookkeeping -- rewriting under nested sums, reordering them, and pulling a constant out -- that a
block decomposition then needs. -/

#guard_sorry_free MIPRE.avg_comp_equiv_fst,
  MIPRE.sumArrow,
  MIPRE.sum_arrow_pair,
  MIPRE.sum_arrow_inl,
  MIPRE.sum_congr1,
  MIPRE.sum_congr2,
  MIPRE.sum_congr3,
  MIPRE.sum_congr4,
  MIPRE.sum_nsmul1,
  MIPRE.sum_nsmul2,
  MIPRE.sum_nsmul3,
  MIPRE.sum_nsmul4,
  MIPRE.sum_comm_four_in,
  MIPRE.sum_comm_four_mid,
  MIPRE.sum_comm_six,
  MIPRE.sum_comm_six_swap,
  MIPRE.sum_prod_fst

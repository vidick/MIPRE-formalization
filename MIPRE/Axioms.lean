/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.GuardSorryFree
import MIPRE.Foundations.Introspection.BasisProg
import MIPRE.Foundations.Introspection.AuxiliaryReadProgram
import MIPRE.Foundations.Introspection.AuxiliarySamplingCorrect
import MIPRE.Foundations.Introspection.AuxiliaryCanonicalProgram
import MIPRE.Background.Introspection.DecisionKernelComplete
import MIPRE.Background.Introspection.CanonicalDecodedStrategy
import MIPRE.Background.Introspection.NumberedSoundness
import MIPRE.Background.Introspection.Compiler
import MIPRE.Background.Pipeline
import MIPRE.Foundations.Blocks
import MIPRE.Foundations.CL.Basic
import MIPRE.Foundations.LowDegree.SchwartzZippel
import MIPRE.Foundations.LowDegree.ZeroBasis
import MIPRE.Foundations.LowDegree.BinarySquareRoot
import MIPRE.Foundations.LowDegree.BinaryInverse
import MIPRE.Foundations.LowDegree.BinaryNormalize
import MIPRE.Foundations.LowDegree.BinaryDivision
import MIPRE.Foundations.LowDegree.BinaryQuotient
import MIPRE.Foundations.LowDegree.BinaryExactDivision
import MIPRE.Foundations.LowDegree.BinaryQuotientReduced
import MIPRE.Foundations.LowDegree.BinaryFactorization
import MIPRE.Foundations.LowDegree.BinaryArtinSchreierLoop
import MIPRE.Foundations.LowDegree.BinaryOrbitDescent
import MIPRE.Foundations.LowDegree.BinaryNonresidueCorrectness
import MIPRE.Foundations.LowDegree.BinaryOddPrimeConstructor
import MIPRE.Foundations.LowDegree.BinaryComposedSum
import MIPRE.Foundations.LowDegree.BinaryDegreeDecomposition
import MIPRE.Foundations.LowDegree.Shoup
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
import MIPRE.Foundations.CL.DetypingComplete
import MIPRE.Foundations.CL.DetypingAnswers
import MIPRE.Foundations.CL.DetypingProgGraph
import MIPRE.Foundations.CL.DetypingProgTyped
import MIPRE.Foundations.CL.DetypingProgSampler
import MIPRE.Foundations.CL.DetypingProgCost
import MIPRE.Foundations.Introspection.TypedPresentation
import MIPRE.Foundations.Introspection.TypedPredicate
import MIPRE.Foundations.Introspection.AmbientMixing
import MIPRE.Foundations.Introspection.ErrorBounds
import MIPRE.Foundations.Introspection.HidingTests
import MIPRE.Foundations.Introspection.FinalExtraction
import MIPRE.Foundations.Introspection.Runtime
import MIPRE.Foundations.CL.DetypingDeciderGame
import MIPRE.Foundations.CL.DetypingDeciderTransport
import MIPRE.Foundations.CL.DetypingClock
import MIPRE.Foundations.Introspection.TypedEstimates
import MIPRE.Foundations.Introspection.SamplerCost
import MIPRE.Foundations.Introspection.ClockCost
import MIPRE.Foundations.Introspection.ClockSimulation
import MIPRE.Foundations.Introspection.ClockCompiler
import MIPRE.Foundations.Introspection.ClockSimulationCost
import MIPRE.Foundations.Introspection.ParserGuard
import MIPRE.Foundations.Introspection.HonestCoreGame
import MIPRE.Foundations.Introspection.HonestSampling
import MIPRE.Foundations.Introspection.HonestFirstHide
import MIPRE.Foundations.Introspection.HonestReading
import MIPRE.Foundations.Introspection.HonestParsed
import MIPRE.Foundations.Introspection.HonestParsedHiding
import MIPRE.Foundations.Introspection.HonestHidingCommute
import MIPRE.Foundations.Introspection.HonestHidingAcceptance
import MIPRE.Foundations.Introspection.HidingInductionDilation
import MIPRE.Foundations.Introspection.HidingInduction
import MIPRE.Foundations.Introspection.HidingRigidity
import MIPRE.Foundations.Introspection.TypedExtraction
import MIPRE.Foundations.Introspection.HidingNormalizer
import MIPRE.Foundations.Introspection.ConditionalNormalizerMirror
import MIPRE.Foundations.Introspection.ConditionalNormalizerIdeal
import MIPRE.Foundations.Introspection.HonestCompleteGame
import MIPRE.Foundations.Introspection.HonestPauliEdges
import MIPRE.Foundations.Introspection.TypedPrefixChainEstimate
import MIPRE.Foundations.Introspection.HidingNormalizerPrefix
import MIPRE.Foundations.Introspection.SourceCompilerBinary
import MIPRE.Foundations.Introspection.SourceCompilerCost
import MIPRE.Foundations.Introspection.ConditionalNormalizerStepGame
import MIPRE.Foundations.Introspection.ConditionalNormalizerStepSeed
import MIPRE.Foundations.Introspection.ReadRigidityGame
import MIPRE.Foundations.Introspection.ProductStageReadTests
import MIPRE.Foundations.Introspection.ProductStageZTests
import MIPRE.Foundations.Introspection.AdaptivePrefixAdvance
import MIPRE.Foundations.Introspection.AdaptivePrefixCommutator
import MIPRE.Foundations.Introspection.AdaptiveDualLocal
import MIPRE.Foundations.Introspection.AdaptivePrefixStrategy
import MIPRE.Foundations.Introspection.StrategyReplacementDilation
import MIPRE.Foundations.Introspection.AdaptiveXTest
import MIPRE.Foundations.Introspection.AdaptiveZTest
import MIPRE.Foundations.Introspection.AdaptivePrefixMarginal
import MIPRE.Foundations.Introspection.AdaptiveGameStage
import MIPRE.Foundations.Introspection.AdaptiveNextStrategy
import MIPRE.Foundations.Introspection.IntrospectCanonicalization
import MIPRE.Foundations.Introspection.StrategyReplacementErrors
import MIPRE.Foundations.Introspection.AdaptiveInductionIteration
import MIPRE.Foundations.Introspection.AdaptiveTerminalInvariant
import MIPRE.Foundations.Introspection.PrimitiveSoundness
import MIPRE.Foundations.Introspection.ExtractedStateSoundness
import MIPRE.Foundations.Introspection.HonestMagicSquareGame
import MIPRE.Foundations.Introspection.IsometricCompletionError
import MIPRE.Foundations.Introspection.ValidPauliSoundness
import MIPRE.Foundations.Introspection.LineRepresentativeProg
import MIPRE.Foundations.Introspection.PauliRestriction
import MIPRE.Foundations.Introspection.SeededLineProg
import MIPRE.Foundations.Introspection.SourcePaddingValue
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
import MIPRE.Foundations.OracularTensor
import MIPRE.Foundations.OracularTyped
import MIPRE.Foundations.OracularSampler
import MIPRE.Foundations.OracularDecider
import MIPRE.Foundations.OracularDeciderCost
import MIPRE.Foundations.Pipeline.Oracularization
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
import MIPRE.LCS.NonlocalGame
import MIPRE.LCS.Strategy.Equivalence
import MIPRE.LCS.Strategy.ObservableToProjector
import MIPRE.TM.Code.Encoding.MachineCode
import MIPRE.Foundations.WeylBinary
import MIPRE.Foundations.Commutation
import MIPRE.Foundations.Linearity
import MIPRE.Foundations.Sandwich
import MIPRE.Foundations.Pasting
import MIPRE.Foundations.LowDegreeSandwich
import MIPRE.Background.LIDT.Extraction
import MIPRE.Background.LIDT.Padding
import MIPRE.Background.LIDT.Simultaneous
import MIPRE.Background.AnswerReduction.ArSampler
import MIPRE.Background.AnswerReduction.ArDecider
import MIPRE.Background.AnswerReduction.Construction
import MIPRE.Background.AnswerReduction.Complete
import MIPRE.Background.AnswerReduction.SoundFinal
import MIPRE.Background.AnswerReduction.Instance
import MIPRE.MainTheorem
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

-- blueprint `thm:lcs-perfect`
#guard_sorry_free MIPRE.LCS.exists_tensorStrategy_value_eq_one_of_localLoss_annihilates_epr

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

-- blueprint `lem:oracular-soundness-tensor`: soundness of oracularization for arbitrary
-- tensor-product strategies, the form `Verifier.valStar` needs, with the synchronous constant.
#guard_sorry_free MIPRE.SeededGame.tensorSound,
  MIPRE.SeededGame.tensorSound_value_ge,
  MIPRE.SeededGame.quantumValue_ge_of_oracular,
  MIPRE.sum_snorm_sq_ge_of_close,
  MIPRE.sum_snorm_sq_chain,
  MIPRE.SeededGame.sum_snorm_sq_joint_le,
  MIPRE.SeededGame.succAt_oracle_le,
  MIPRE.SeededGame.succAt_tensorSound_ge,
  MIPRE.SeededGame.sum_failAt_four_le

-- blueprint `lem:oracular-typed-transfers`: the typed oracularized game of a normal form
-- verifier, in the vocabulary of the detyping compiler, and its two value transfers.
#guard_sorry_free MIPRE.CL.CLFun.eval_ident,
  MIPRE.CL.CLFun.exactlyOn_ident,
  MIPRE.exactlyOn_roleFamily,
  MIPRE.SeededGame.typedGame_mu,
  MIPRE.SeededGame.quantumValue_typedGame_le,
  MIPRE.SyncStrategy.pushTo,
  MIPRE.SyncStrategy.value_le_pushTo,
  MIPRE.SyncStrategy.isPCC_pushTo,
  MIPRE.Verifier.valStar_ge_of_typed,
  MIPRE.Verifier.exists_typed_perfectPCC,
  MIPRE.pairDec_pairEnc,
  MIPRE.parseAns_encAns,
  MIPRE.oaccepts_of_oraclePred,
  MIPRE.oraclePred_encAns,
  MIPRE.Verifier.valStar_ge_of_oraclePred,
  MIPRE.Verifier.exists_oraclePred_perfectPCC

-- blueprint `lem:oracle-typed-sampler`: the typed oracularized sampler, its query clauses, its
-- running time and its program as a polynomial-time function of the input sampler's.
#guard_sorry_free MIPRE.oracleSampler,
  MIPRE.oracleSampler_cl,
  MIPRE.oracleSampler_dim,
  MIPRE.OracleSampler.core,
  MIPRE.OracleSampler.route_dimension,
  MIPRE.OracleSampler.route_alice,
  MIPRE.OracleSampler.route_bob,
  MIPRE.OracleSampler.route_oracle,
  MIPRE.OracleSampler.core_runs_within,
  MIPRE.OracleSampler.oracleSampler_timeBound,
  MIPRE.OracleSampler.samplerProgFun,
  MIPRE.OracleSampler.samplerProgFun_apply

-- blueprint `lem:oracle-typed-decider`: the typed oracularized decider, total, its acceptance law
-- `oraclePred` through the clock, and the two value transfers of the compiled typed game.
#guard_sorry_free MIPRE.OracleDecider.oracleDecider,
  MIPRE.OracleDecider.oracleDecider_total,
  MIPRE.OracleDecider.oracleDecider_accepts_iff,
  MIPRE.OracleDecider.gameProg_accepts_iff,
  MIPRE.OracleDecider.core_accepts_iff,
  MIPRE.OracleDecider.accepts_sound,
  MIPRE.OracleDecider.accepts_complete,
  MIPRE.OracleDecider.deciderProgFun,
  MIPRE.OracleDecider.deciderProgFun_apply,
  MIPRE.OracleDecider.typedPredicate_sound,
  MIPRE.OracleDecider.typedPredicate_complete,
  MIPRE.OracleDecider.valStar_ge_of_typedPredicate,
  MIPRE.OracleDecider.exists_typedPredicate_perfectPCC

-- blueprint `lem:oracle-decider-time`: the running times of the typed oracularized decider — the
-- core's, which discharges the budget hypothesis, and the decider's own.
#guard_sorry_free MIPRE.OracleDecider.gameProg_runs_within,
  MIPRE.OracleDecider.core_runs_within,
  MIPRE.OracleDecider.core_timeBound,
  MIPRE.OracleDecider.core_accepting_le,
  MIPRE.OracleDecider.budget_sufficient,
  MIPRE.OracleDecider.exists_typedPredicate_perfectPCC_within,
  MIPRE.OracleDecider.oracleDecider_runs_within,
  MIPRE.OracleDecider.oracleDecider_timeBound

-- blueprint `thm:oracularization`: the specification inhabited, and the value transfers of the
-- typed oracularized verifier and of the detyped one, with `ℓ + 3` levels.
#guard_sorry_free MIPRE.Oracularization.construction,
  MIPRE.Oracularization.typed_soundness,
  MIPRE.Oracularization.typed_completeness,
  MIPRE.Oracularization.detyped,
  MIPRE.Oracularization.detyped_completeness,
  MIPRE.Oracularization.detyped_soundness

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
  MIPRE.TM.CookLevin.Pad.pcpParams_outer_dvd,
  MIPRE.TM.CookLevin.Pad.pcpParams_field_eventually_large,
  MIPRE.TM.CookLevin.Pad.fieldDegree_le

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

-- Generic normalization, independent of the Shoup construction.
#guard_sorry_free MIPRE.LowDegree.BinaryPolynomial.normalizeBitsProg_apply,
  MIPRE.LowDegree.BinaryPolynomial.length_normalizeBits_le,
  MIPRE.LowDegree.BinaryPolynomial.evalBits_normalizeBits,
  MIPRE.LowDegree.BinaryPolynomial.normalizeBits_getLast

/-- info: 'MIPRE.LowDegree.BinaryPolynomial.normalizeBitsProg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MIPRE.LowDegree.BinaryPolynomial.normalizeBitsProg

/-- info: 'MIPRE.LowDegree.BinaryPolynomial.polyOfBits_normalizeBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MIPRE.LowDegree.BinaryPolynomial.polyOfBits_normalizeBits

-- Monic division and quotient coordinates precede irreducibility.
#guard_sorry_free MIPRE.LowDegree.BinaryPolynomial.divModBitsProg_apply,
  MIPRE.LowDegree.BinaryPolynomial.divModBits_width,
  MIPRE.LowDegree.BinaryPolynomial.degree_divModBits_remainder_lt,
  MIPRE.LowDegree.BinaryQuotient.length_toBits,
  MIPRE.LowDegree.BinaryQuotient.ofBits_toBits,
  MIPRE.LowDegree.BinaryQuotient.toBits_ofBits,
  MIPRE.LowDegree.BinaryQuotient.evalBits_eq_iff,
  MIPRE.LowDegree.BinaryQuotient.ofBits_xor,
  MIPRE.LowDegree.BinaryQuotient.ofBits_mulReduce

/-- info: 'MIPRE.LowDegree.BinaryPolynomial.divModBitsProg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MIPRE.LowDegree.BinaryPolynomial.divModBitsProg

/-- info: 'MIPRE.LowDegree.BinaryPolynomial.polyOfBits_divModBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MIPRE.LowDegree.BinaryPolynomial.polyOfBits_divModBits

-- Canonical Euclidean algorithms and the complete quotient fixed space.
#guard_sorry_free MIPRE.LowDegree.BinaryPolynomial.normalizeBits_eq_nil_iff,
  MIPRE.LowDegree.BinaryPolynomial.length_normalizeBits,
  MIPRE.LowDegree.BinaryPolynomial.divModBits_eq_div_modByMonic,
  MIPRE.LowDegree.BinaryPolynomial.gcdBitsProg,
  MIPRE.LowDegree.BinaryPolynomial.polyOfBits_gcdBits,
  MIPRE.LowDegree.BinaryPolynomial.gcdBits_width,
  MIPRE.LowDegree.BinaryPolynomial.quotientBitsProg,
  MIPRE.LowDegree.BinaryPolynomial.polyOfBits_quotientBits,
  MIPRE.LowDegree.BinaryPolynomial.polyOfBits_quotientBits_mul,
  MIPRE.LowDegree.BinaryPolynomial.quotientBits_width,
  MIPRE.LowDegree.BinaryQuotient.frobeniusMatrixProg,
  MIPRE.LowDegree.BinaryQuotient.frobeniusMatrixProg_correct,
  MIPRE.LowDegree.BinaryQuotient.fixedGeneratorsProg,
  MIPRE.LowDegree.BinaryQuotient.fixedGeneratorsProg_correct,
  MIPRE.LowDegree.BinaryQuotient.fixedGenerator_idempotent,
  MIPRE.LowDegree.BinaryQuotient.fixedGenerator_spans,
  MIPRE.LowDegree.BinaryQuotient.square_bijective

-- Supplied-modulus squarefree factorization has no irreducible-construction dependency.
#guard_sorry_free MIPRE.LowDegree.BinaryQuotient.factorBitsProg,
  MIPRE.LowDegree.BinaryQuotient.factorBitsProg_factors,
  MIPRE.LowDegree.BinaryQuotient.factorBitsProg_prod

-- Effective Frobenius orbit products and certified constructors for every prime power.
#guard_sorry_free MIPRE.LowDegree.BinaryQuotient.orbitPolynomialBitsProg,
  MIPRE.LowDegree.BinaryQuotient.map_orbitPolynomialBits,
  MIPRE.LowDegree.BinaryQuotient.orbitPolynomialBits_monic_natDegree,
  MIPRE.LowDegree.BinaryQuotient.orbitPolynomialBits_eq_minpoly,
  MIPRE.LowDegree.BinaryQuotient.orbitPolynomialBits_irreducible,
  MIPRE.LowDegree.BinaryPolynomial.nonresidueLiftBitsProg,
  MIPRE.LowDegree.BinaryPolynomial.nonresidueLiftBitsProg_correct,
  MIPRE.LowDegree.BinaryPolynomial.nonresidueLiftBits_order,
  MIPRE.LowDegree.BinaryPolynomial.nonresidueLiftBits_degree_coprime,
  MIPRE.LowDegree.BinaryArtinSchreier.powerTwoBitsProg,
  MIPRE.LowDegree.BinaryArtinSchreier.powerTwoBits_correct,
  MIPRE.LowDegree.BinaryArtinSchreier.powerTwoBits_length,
  MIPRE.LowDegree.BinaryQuotient.traceBitsProg,
  MIPRE.LowDegree.BinaryQuotient.evalBits_traceBits,
  MIPRE.LowDegree.BinaryPrimePowerTrace.flat_trace_natDegree,
  MIPRE.LowDegree.BinaryPolynomial.oddPrimePowerBitsProg,
  MIPRE.LowDegree.BinaryPolynomial.oddPrimePowerBits_correct,
  MIPRE.LowDegree.BinaryPolynomial.oddPrimePowerBits_length,
  MIPRE.LowDegree.BinaryPolynomial.oddPrimePowerBits_width_le

-- Coprime-degree assembly and its proof-only decomposition have no Shoup dependency.
#guard_sorry_free MIPRE.LowDegree.BinaryQuotient.composedSumBitsProg,
  MIPRE.LowDegree.BinaryQuotient.composedSumBits_correct,
  MIPRE.LowDegree.BinaryDegreeFactors.degreeFactors_prod,
  MIPRE.LowDegree.BinaryDegreeFactors.degreeFactors_pairwise,
  MIPRE.LowDegree.BinaryDegreeFactors.degreeFactors_dvd,
  MIPRE.LowDegree.BinaryDegreeFactors.degreeFactors_pos,
  MIPRE.LowDegree.BinaryDegreeFactors.degreeFactors_le,
  MIPRE.LowDegree.BinaryDegreeFactors.prefix_prod_dvd

/-- info: 'MIPRE.LowDegree.BinaryQuotient.orbitPolynomialBitsProg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MIPRE.LowDegree.BinaryQuotient.orbitPolynomialBitsProg

/-- info: 'MIPRE.LowDegree.BinaryPolynomial.nonresidueLiftBitsProg_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MIPRE.LowDegree.BinaryPolynomial.nonresidueLiftBitsProg_correct

/-- info: 'MIPRE.LowDegree.BinaryArtinSchreier.powerTwoBitsProg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MIPRE.LowDegree.BinaryArtinSchreier.powerTwoBitsProg

/-- info: 'MIPRE.LowDegree.BinaryArtinSchreier.powerTwoBits_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MIPRE.LowDegree.BinaryArtinSchreier.powerTwoBits_correct

/-- info: 'MIPRE.LowDegree.BinaryPolynomial.oddPrimePowerBitsProg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MIPRE.LowDegree.BinaryPolynomial.oddPrimePowerBitsProg

/-- info: 'MIPRE.LowDegree.BinaryPolynomial.oddPrimePowerBits_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MIPRE.LowDegree.BinaryPolynomial.oddPrimePowerBits_correct

/-- info: 'MIPRE.LowDegree.BinaryQuotient.composedSumBitsProg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MIPRE.LowDegree.BinaryQuotient.composedSumBitsProg

/-- info: 'MIPRE.LowDegree.BinaryQuotient.composedSumBits_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MIPRE.LowDegree.BinaryQuotient.composedSumBits_correct

-- The executable unary decomposition agrees with the proof-only factorization list.
#guard_sorry_free MIPRE.LowDegree.DegreeArithmetic.modUnaryProg,
  MIPRE.LowDegree.DegreeArithmetic.dvdUnaryProg,
  MIPRE.LowDegree.DegreeArithmetic.mulUnaryProg,
  MIPRE.LowDegree.DegreeArithmetic.primeUnaryProg,
  MIPRE.LowDegree.DegreeArithmetic.primeUnary_eq,
  MIPRE.LowDegree.DegreeArithmetic.primePowerUnaryProg,
  MIPRE.LowDegree.DegreeArithmetic.primePowerUnary_correct,
  MIPRE.LowDegree.DegreeArithmetic.primePowerPairsProg,
  MIPRE.LowDegree.DegreeArithmetic.primePowerPairs_eq,
  MIPRE.LowDegree.DegreeArithmetic.primePowerPairs_prod,
  MIPRE.LowDegree.DegreeArithmetic.primePowerPairs_pairwise

/-- info: 'MIPRE.LowDegree.DegreeArithmetic.primePowerPairsProg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MIPRE.LowDegree.DegreeArithmetic.primePowerPairsProg

-- Effective polynomial-basis arithmetic using the proved uniform constructor.
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
#guard_sorry_free MIPRE.CL.FixedSampler.sampler,
  MIPRE.CL.FixedSampler.sampler_timeBound,
  MIPRE.CL.Graph.sampler,
  MIPRE.CL.Graph.sampler_dim,
  MIPRE.CL.Graph.sampler_timeBound,
  MIPRE.CL.TypedSampler.specialize,
  MIPRE.CL.TypedSampler.specialize_timeBoundAt,
  MIPRE.CL.Detyping.decodeView_view,
  MIPRE.CL.Detyping.decodeQuestion_output,
  MIPRE.CL.Detyping.complete,
  MIPRE.CL.Detyping.complete_state,
  MIPRE.CL.Detyping.complete_player_independent,
  MIPRE.CL.Detyping.complete_isPCC,
  MIPRE.CL.Detyping.complete_value,
  MIPRE.CL.Detyping.exists_perfectPCC,
  MIPRE.CL.Detyping.sampler,
  MIPRE.CL.Detyping.sampler_dim,
  MIPRE.CL.Detyping.samplerProg_closed,
  MIPRE.CL.Detyping.samplerProg_halts,
  MIPRE.CL.Detyping.samplerProg_dimension,
  MIPRE.CL.Detyping.samplerProg_marginal,
  MIPRE.CL.Detyping.samplerProg_linear,
  MIPRE.CL.Detyping.samplerProg_factor,
  MIPRE.CL.Detyping.sampler_haltsWithin,
  MIPRE.CL.Detyping.sampler_timeBoundAt_uniform_degree,
  MIPRE.CL.Detyping.sampler_timeBound,
  MIPRE.CL.Detyping.restrictAnswers_state,
  MIPRE.CL.Detyping.restrictAnswers_failAt_le,
  MIPRE.CL.Detyping.restrictAnswers_failure_le,
  MIPRE.CL.Detyping.restrictAnswers_value_ge,
  MIPRE.Introspection.QuestionType.card,
  MIPRE.Introspection.QuestionType.esize_aux_le,
  MIPRE.Introspection.TypeGraph.symmetric,
  MIPRE.Introspection.TypeGraph.adj_pauli,
  MIPRE.Introspection.TypeGraph.adj_different_roles_iff,
  MIPRE.Introspection.TypeGraph.adj_pauli_aux_iff,
  MIPRE.Introspection.TypeGraph.adj_hide_hide_iff,
  MIPRE.Introspection.TypeGraph.edges_nonempty,
  MIPRE.Introspection.TypeGraph.detyping_factor_of_pauli_card,
  MIPRE.Introspection.TypedPresentation.family_exactlyOn,
  MIPRE.Introspection.TypedPresentation.marginal_aux,
  MIPRE.Introspection.TypedPresentation.linear_aux,
  MIPRE.Introspection.TypedPresentation.factor_aux,
  MIPRE.Introspection.TypedPresentation.joint_aux_zero,
  MIPRE.Introspection.TypedPresentation.mu_cross_introspect,
  MIPRE.Introspection.TypedPresentation.failAt_cross_introspect_le,
  MIPRE.Introspection.CLChecks.sampling_prefix,
  MIPRE.Introspection.CLChecks.hidingPauli_coarse,
  MIPRE.Introspection.CLChecks.hidingNext_coarse,
  MIPRE.Introspection.TypedPredicate.check,
  MIPRE.Introspection.TypedPredicate.check_formats,
  MIPRE.Introspection.TypedPredicate.check_consistency,
  MIPRE.Introspection.TypedPredicate.check_sampling,
  MIPRE.Introspection.TypedPredicate.check_sampling_prefix,
  MIPRE.Introspection.TypedPredicate.check_reading,
  MIPRE.Introspection.TypedPredicate.check_game,
  MIPRE.Introspection.TypedPredicate.check_game_reversed,
  MIPRE.Introspection.registerPOVM,
  MIPRE.Introspection.registerOp_isPVM,
  MIPRE.Introspection.stateSqNorm_registerOp,
  MIPRE.Introspection.registerEPR_norm,
  MIPRE.Introspection.registerState_split,
  MIPRE.Introspection.stateSqNorm_registerExtend,
  MIPRE.Introspection.exists_register_mixing_sqrt,
  MIPRE.Introspection.coordinateSplit,
  MIPRE.Introspection.coordinateLinear_restrict,
  MIPRE.Introspection.coordinateInsert_linear,
  MIPRE.Introspection.exists_ambient_pauli_mixing,
  MIPRE.Introspection.readout_isPVM,
  MIPRE.Introspection.bornProb_registerEPR_readout,
  MIPRE.Introspection.readout_eq_synOf,
  MIPRE.Introspection.sampled_dist_eq_clDist,
  MIPRE.Introspection.conditionalReadout_isPVM,
  MIPRE.Introspection.bornProb_conditionalReadout,
  MIPRE.Introspection.readoutAcceptance_eq_value,
  MIPRE.Introspection.quantumValue_ge_of_readoutAcceptance,
  MIPRE.Introspection.exists_strategy_of_readoutAcceptance,
  MIPRE.Introspection.verifier_readoutAcceptance_eq_value,
  MIPRE.Introspection.errorProfile_power,
  MIPRE.Introspection.exists_errorProfile_power,
  MIPRE.Introspection.iteratedRoot_eq_rpow,
  MIPRE.Introspection.errorProfile_iteratedRoot,
  MIPRE.Introspection.errorProfile_power_of_le,
  MIPRE.Introspection.errorProfile_scale_input,
  MIPRE.Introspection.errorProfile_scaled_power,
  MIPRE.Introspection.state_transfer_loss_le_three_sqrt,
  MIPRE.CL.CLFun.SupportedOn.proj_eval_cons,
  MIPRE.CL.CLFun.SupportedOn.outputPrefix_eval,
  MIPRE.CL.CLFun.ExactlyOn.outputPrefix_self,
  MIPRE.CL.CLFun.ExactlyOn.outputPrefix_univ,
  MIPRE.Introspection.agreement_subtest_average,
  MIPRE.Introspection.sampling_pauli_estimate,
  MIPRE.Introspection.sampling_prefix_estimate,
  MIPRE.Introspection.mapped_operator_zero_of_not_range,
  MIPRE.Introspection.off_range_weight_le,
  MIPRE.Introspection.same_side_via_common_other,
  MIPRE.Introspection.hiding_same_side_estimate,
  MIPRE.Introspection.operator_chain_telescope,
  MIPRE.Introspection.stateSqNorm_hiding_chain,
  MIPRE.Introspection.hiding_chain_average,
  MIPRE.Introspection.hiding_chain_uniform,
  MIPRE.Introspection.legal_query_size_le,
  MIPRE.Introspection.legal_query_cost_le,
  MIPRE.Introspection.original_decider_haltsWithin,
  MIPRE.Introspection.polynomial_ansBound,
  MIPRE.Introspection.original_simulation_haltsWithin,
  MIPRE.AnswerReduction.sampler_cost_le_power

#guard_sorry_free MIPRE.Introspection.CLChecks.prefixRegister_subset,
  MIPRE.Introspection.CLChecks.proj_prefixRegister,
  MIPRE.Introspection.CLChecks.prefixRegister_full,
  MIPRE.Introspection.TypedPredicate.check_directed,
  MIPRE.Introspection.TypedPredicate.check_directed_reversed,
  MIPRE.Introspection.TypedPredicate.check_hiding_read,
  MIPRE.Introspection.TypedPredicate.check_hiding_read_reversed,
  MIPRE.Introspection.TypedPredicate.check_hiding_next,
  MIPRE.Introspection.TypedPredicate.check_hiding_next_reversed,
  MIPRE.Introspection.TypedPredicate.check_hiding_pauli,
  MIPRE.Introspection.TypedPredicate.check_hiding_pauli_reversed,
  MIPRE.Introspection.TypedEstimates.questionCheck,
  MIPRE.Introspection.TypedEstimates.parsedGame,
  MIPRE.Introspection.TypedEstimates.aux_agreement_estimate,
  MIPRE.Introspection.TypedEstimates.sampling_prefix_estimate,
  MIPRE.Introspection.TypedEstimates.hiding_read_estimate,
  MIPRE.Introspection.TypedEstimates.hiding_read_same_side_estimate,
  MIPRE.Introspection.typedSampler,
  MIPRE.Introspection.typedSampler_dim,
  MIPRE.Introspection.typedSampler_cl,
  MIPRE.Introspection.typedSampler_prog_independent,
  MIPRE.Introspection.detypedSampler,
  MIPRE.Introspection.detypedSampler_dim,
  MIPRE.Introspection.detypedSampler_cl,
  MIPRE.Introspection.typedSampler_haltsWithin,
  MIPRE.Introspection.typedSampler_timeBoundAt,
  MIPRE.Introspection.detypedSampler_timeBound,
  MIPRE.CL.Detyping.DeciderProgram.prog_closed,
  MIPRE.CL.Detyping.DeciderProgram.prog_halts,
  MIPRE.CL.Detyping.DeciderProgram.decider,
  MIPRE.CL.Detyping.DeciderProgram.raw_accepts_iff,
  MIPRE.CL.Detyping.DeciderProgram.accepts_iff,
  MIPRE.CL.Detyping.DeciderProgram.verifier,
  MIPRE.CL.Detyping.DeciderProgram.verifier_rejectsLong,
  MIPRE.CL.Detyping.DeciderProgram.bounded_acceptance,
  MIPRE.CL.Detyping.DeciderProgram.bounded_acceptance_edge,
  MIPRE.CL.Detyping.DeciderProgram.verifier_game_D

#guard_sorry_free MIPRE.CL.Detyping.DeciderProgram.numbered_clDist,
  MIPRE.CL.Detyping.DeciderProgram.verifier_game_mu,
  MIPRE.CL.Detyping.DeciderProgram.toFinite_state,
  MIPRE.CL.Detyping.DeciderProgram.toFinite_value,
  MIPRE.CL.Detyping.DeciderProgram.restrictAmbient_state,
  MIPRE.CL.Detyping.DeciderProgram.restrictAmbient_failure_le,
  MIPRE.CL.Detyping.DeciderProgram.restrictAmbient_value_ge,
  MIPRE.CL.Detyping.DeciderProgram.fromFiniteSync_isPCC,
  MIPRE.CL.Detyping.DeciderProgram.exists_ambientPerfectPCC,
  MIPRE.CL.Detyping.DeciderProgram.verifier_hasPerfectPCC,
  MIPRE.CL.Detyping.ClockProgram.constant,
  MIPRE.CL.Detyping.ClockProgram.ofPolyTimeFun,
  MIPRE.CL.Detyping.ClockProgram.clockedResult_eq_iff,
  MIPRE.CL.Detyping.ClockProgram.wrapProg_halts,
  MIPRE.CL.Detyping.ClockProgram.wrapProg_accepts_iff,
  MIPRE.CL.Detyping.ClockProgram.wrap,
  MIPRE.CL.Detyping.ClockProgram.wrap_total,
  MIPRE.CL.Detyping.ClockProgram.wrap_accepts_iff_of_bounded,
  MIPRE.CL.Detyping.ClockProgram.decider,
  MIPRE.CL.Detyping.ClockProgram.decider_total,
  MIPRE.CL.Detyping.ClockProgram.decider_accepts_iff,
  MIPRE.CL.Detyping.ClockProgram.wrapProg_haltsWithin

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

-- blueprint `lem:ar-sandwich-support`, the paper's `lem:ld-sandwich`: the `k`-fold sandwich of
-- projective measurements, from evaluated coordinate agreement to evaluated tuple agreement, with
-- the explicit constant `2 sqrt 2 k`.
#guard_sorry_free MIPRE.one_sub_sum_bornProb_ldSandwich_le,
  MIPRE.sandK,
  MIPRE.sandK_zero,
  MIPRE.sandK_succ,
  MIPRE.sandK_snoc,
  MIPRE.sandK_nonneg,
  MIPRE.sum_sandK,
  MIPRE.sqrt_sum_xSqNorm_sandK_le,
  MIPRE.sqrt_sum_xSqNorm_sandStep_le,
  MIPRE.sum_snorm_sq_sandStep_le,
  MIPRE.snorm_sandStep_le,
  MIPRE.sandStep_identity,
  MIPRE.snorm_add3_le,
  MIPRE.sqrt_sum_weighted_sq_add_le,
  MIPRE.sqrt_sum_weighted_sq_le_add3,
  MIPRE.sum_mul_sum_eq_sum_prod,
  MIPRE.sqrt_wsum_le_add3,
  MIPRE.IsPVM.le_one,
  MIPRE.IsPVM.aOp_contraction,
  MIPRE.IsPVM.bOp_contraction,
  MIPRE.sum_bOp_conjTranspose_mul_self_le_one_of_nonneg,
  MIPRE.fibSum_comp_equiv,
  MIPRE.fibSum_marg_left,
  MIPRE.fibSum_snd,
  MIPRE.fibSum_fibSum,
  MIPRE.sum_sum_bornProb_eq_one,
  MIPRE.one_sub_sum_bornProb_le_sqrt,
  MIPRE.sum_bornProb_le_fibSum_of_nonneg,
  MIPRE.one_sub_sum_bornProb_le_eval

-- blueprint `lem:lidt-ldc-extraction`: from the single-codeword conclusions for the combined
-- point measurements to the simultaneous conclusions, by extracting the exactly `x`-linear
-- outcomes.
#guard_sorry_free MIPRE.LIDT.Simul.pevY,
  MIPRE.LIDT.Simul.eval_pevY,
  MIPRE.LIDT.Simul.eval_sub,
  MIPRE.LIDT.Simul.unitExp,
  MIPRE.LIDT.Simul.unitExp_injective,
  MIPRE.LIDT.Simul.prod_pow_unitExp,
  MIPRE.LIDT.Simul.linPoly,
  MIPRE.LIDT.Simul.eval_linPoly,
  MIPRE.LIDT.Simul.linPoly_unitExp,
  MIPRE.LIDT.Simul.linPoly_of_forall_ne,
  MIPRE.LIDT.Simul.linPoly_injective,
  MIPRE.LIDT.Simul.IsXLin,
  MIPRE.LIDT.Simul.xCoef,
  MIPRE.LIDT.Simul.pevY_eq_linPoly,
  MIPRE.LIDT.Simul.exists_badCoef,
  MIPRE.LIDT.Simul.pevY_apply,
  MIPRE.LIDT.Simul.padB,
  MIPRE.LIDT.Simul.padB_castLE,
  MIPRE.LIDT.Simul.extract,
  MIPRE.LIDT.Simul.extEval,
  MIPRE.LIDT.Simul.badQ,
  MIPRE.LIDT.Simul.badQ_ne_zero,
  MIPRE.LIDT.Simul.pevY_badQ,
  MIPRE.LIDT.Simul.card_agree_le,
  MIPRE.LIDT.Simul.agreeX,
  MIPRE.LIDT.Simul.agreeX_le_one,
  MIPRE.LIDT.Simul.badInd,
  MIPRE.LIDT.Simul.agreeX_le,
  MIPRE.LIDT.Simul.sum_uniform_badInd_le,
  MIPRE.LIDT.Simul.sum_uniform_one,
  MIPRE.LIDT.Simul.sum_agreeX_le,
  MIPRE.LIDT.Simul.inconsistency_eq_one_sub,
  MIPRE.LIDT.Simul.sum_bornProb_map_right,
  MIPRE.LIDT.Simul.sum_bornProb_map_left,
  MIPRE.LIDT.Simul.xOf,
  MIPRE.LIDT.Simul.yOf,
  MIPRE.LIDT.Simul.sum_uniform_pad,
  MIPRE.LIDT.Simul.sum_uniform_agree,
  MIPRE.LIDT.Simul.inconsistency_extract_right_le,
  MIPRE.LIDT.Simul.inconsistency_extract_left_le,
  MIPRE.LIDT.Simul.inconsistency_map_le,
  MIPRE.LIDT.Simul.isPVM_pm,
  MIPRE.LIDT.Simul.extractPM,
  MIPRE.LIDT.Simul.extractPM_toPOVM,
  MIPRE.LIDT.Simul.evalTuplePOVM,
  MIPRE.LIDT.Simul.evalTuplePOVM_extractPM,
  MIPRE.LIDT.Simul.combPOVM,
  MIPRE.LIDT.Simul.extracted_conclusions

/-! ## The padded adapter and the simultaneous seeded CL theorem (answer reduction, AR-2) -/

#guard_sorry_free MIPRE.LIDT.Simul.valAt,
  MIPRE.LIDT.Simul.IsCross,
  MIPRE.LIDT.Simul.SampleRel,
  MIPRE.LIDT.Simul.sample_mem_line,
  MIPRE.LIDT.Simul.accepts_sample_imp,
  MIPRE.LIDT.Simul.accepts_sample_of,
  MIPRE.LIDT.Simul.eq_rep_add_lineParam,
  MIPRE.LIDT.Simul.shiftOf,
  MIPRE.LIDT.Simul.eq_rep_add_shiftOf,
  MIPRE.LIDT.Simul.lineParam_rep_add,
  MIPRE.LIDT.Simul.rep_add_smul',
  MIPRE.LIDT.Simul.yOf_add,
  MIPRE.LIDT.Simul.yOf_smul,
  MIPRE.LIDT.Simul.xOf_add,
  MIPRE.LIDT.Simul.xOf_smul,
  MIPRE.LIDT.Simul.yOf_zero,
  MIPRE.LIDT.Simul.jIdx,
  MIPRE.LIDT.Simul.jIdx_of_le,
  MIPRE.LIDT.Simul.yOf_single_of_le,
  MIPRE.LIDT.Simul.yOf_single_of_lt,
  MIPRE.LIDT.Simul.xOf_single_of_le,
  MIPRE.LIDT.Simul.yOf_zeroBelow,
  MIPRE.LIDT.Simul.yOf_rep_single_of_le,
  MIPRE.LIDT.Simul.yOf_rep_single_of_lt,
  MIPRE.LIDT.Simul.exists_yOf_rep,
  MIPRE.LIDT.Simul.jOf,
  MIPRE.LIDT.Simul.tyMap,
  MIPRE.LIDT.Simul.qmap,
  MIPRE.LIDT.Simul.wyOf,
  MIPRE.LIDT.Simul.sampleMap,
  MIPRE.LIDT.Simul.qmap_question,
  MIPRE.LIDT.Simul.xr,
  MIPRE.LIDT.Simul.xr_add,
  MIPRE.LIDT.Simul.xr_smul,
  MIPRE.LIDT.Simul.xr_zero,
  MIPRE.LIDT.Simul.linEval,
  MIPRE.LIDT.Simul.eval_linPoly_padB,
  MIPRE.LIDT.Simul.affPoly,
  MIPRE.LIDT.Simul.eval_affPoly,
  MIPRE.LIDT.Simul.natDegree_affPoly_le,
  MIPRE.LIDT.Simul.natDegree_affPoly_le_of_zero,
  MIPRE.LIDT.Simul.valsOf,
  MIPRE.LIDT.Simul.polysOf,
  MIPRE.LIDT.Simul.lineAns,
  MIPRE.LIDT.Simul.rmap,
  MIPRE.LIDT.Simul.fmtOk_rmap,
  MIPRE.LIDT.Simul.base_add_lineParam,
  MIPRE.LIDT.Simul.eval_lineAns_eq,
  MIPRE.LIDT.Simul.valAt_line_aux,
  MIPRE.LIDT.Simul.natDegree_polysOf_values,
  MIPRE.LIDT.Simul.valAt_rmap,
  MIPRE.LIDT.Simul.sample_question_mem,
  MIPRE.LIDT.Simul.valAt_eq_of_sampleRel,
  MIPRE.LIDT.Simul.eq_point_of_not_cross,
  MIPRE.LIDT.Simul.not_isCross_point_left,
  MIPRE.LIDT.Simul.not_isCross_point_right,
  MIPRE.LIDT.Simul.accepts_rmap,
  MIPRE.LIDT.Simul.clGame_D_rmap,
  MIPRE.LIDT.Simul.sampleEquiv,
  MIPRE.LIDT.Simul.card_ty,
  MIPRE.LIDT.Simul.card_sample,
  MIPRE.LIDT.Simul.eq_of_xOf_yOf,
  MIPRE.LIDT.Simul.card_jOf_fiber_le,
  MIPRE.LIDT.Simul.card_sampleMap_fiber_le,
  MIPRE.LIDT.Simul.clGame_mu_fibre,
  MIPRE.LIDT.Simul.sum_mu_qmap_le,
  MIPRE.LIDT.Simul.tuplePOVMA,
  MIPRE.LIDT.Simul.tuplePOVMB,
  MIPRE.LIDT.Simul.toPOVM_mergeAt,
  MIPRE.LIDT.Simul.padded,
  MIPRE.LIDT.Simul.exists_padded_value,
  MIPRE.LIDT.Simul.pointPOVMA_padded,
  MIPRE.LIDT.Simul.pointPOVMB_padded,
  MIPRE.LIDT.Simul.padM,
  MIPRE.LIDT.Simul.le_padM,
  MIPRE.LIDT.Simul.padM_le,
  MIPRE.LIDT.Simul.padM_le_mul,
  MIPRE.LIDT.Simul.padM_dvd,
  MIPRE.LIDT.Simul.simA,
  MIPRE.LIDT.Simul.deltaSim,
  MIPRE.LIDT.Simul.forty_le_simA,
  MIPRE.LIDT.Simul.clA_add_one_le_simA,
  MIPRE.LIDT.Simul.rpow_le_rpow_simA,
  MIPRE.LIDT.Simul.deltaCL_padded_le,
  MIPRE.LIDT.Simul.one_le_deltaSim,
  MIPRE.LIDT.Simul.constPM,
  MIPRE.LIDT.Simul.inconsistency_le_one,
  MIPRE.LIDT.Simul.clSoundness_padded,
  MIPRE.LIDT.Simul.clSoundness

-- blueprint `lem:ar-typed-sampler`: the typed answer-reduced sampler, its PCP half answered
-- directly, with the parameter routine and the copies' stage programs.
#guard_sorry_free MIPRE.CL.DirectSampler,
  MIPRE.CL.TypedSampler.prodDirect,
  MIPRE.CL.CLFun.toBits_eval_truncate_prodCL,
  MIPRE.CL.CLFun.toBits_mapOfPrefix_prodCL,
  MIPRE.CL.CLFun.indicatorBits_factorOfPrefix_prodCL,
  MIPRE.LIDT.CL.Regs.eval_pres,
  MIPRE.LIDT.CL.Regs.mapOfPrefix_two,
  MIPRE.AnswerReduction.Pcp.comps_marginal,
  MIPRE.AnswerReduction.StageProg.copyProg,
  MIPRE.AnswerReduction.StageProg.copyProg_apply,
  MIPRE.AnswerReduction.StageProg.copyAnswer_marginal,
  MIPRE.AnswerReduction.StageProg.copyAnswer_linear,
  MIPRE.AnswerReduction.StageProg.copyAnswer_factor,
  MIPRE.AnswerReduction.powSel,
  MIPRE.AnswerReduction.PcpFamily,
  MIPRE.AnswerReduction.PcpFamily.directSampler,
  MIPRE.AnswerReduction.family,
  MIPRE.AnswerReduction.parProg,
  MIPRE.AnswerReduction.parProg_runs,
  MIPRE.AnswerReduction.typedSampler,
  MIPRE.AnswerReduction.typedSampler_cl,
  MIPRE.AnswerReduction.typedSampler_prog

-- blueprint `lem:ar-typed-decider`: the typed answer-reduced decider, total, with the typed
-- predicate as its acceptance law.
#guard_sorry_free MIPRE.AnswerReduction.ldB_aline,
  MIPRE.AnswerReduction.ldB_dline,
  MIPRE.AnswerReduction.sideB_eq,
  MIPRE.AnswerReduction.verdictB_eq,
  MIPRE.AnswerReduction.verdictP_apply,
  MIPRE.AnswerReduction.parseBP_apply,
  MIPRE.AnswerReduction.typedDecider,
  MIPRE.AnswerReduction.core_runs,
  MIPRE.AnswerReduction.accepts_iff,
  MIPRE.AnswerReduction.total,
  MIPRE.AnswerReduction.size_margQuery_le,
  MIPRE.AnswerReduction.typedDecider_time

-- blueprint `lem:ar-typed-sampler`, its running time: the parameter routine's, the product's,
-- and the typed sampler's.
#guard_sorry_free MIPRE.AnswerReduction.ParamsBound,
  MIPRE.AnswerReduction.parProg_time,
  MIPRE.CL.ProductSampler.route_call_size,
  MIPRE.CL.ProductSampler.prog_time,
  MIPRE.AnswerReduction.typedSampler_time

-- blueprint `lem:ar-construction`: the answer-reduced verifier, its programs, and its complexity
-- clause.
#guard_sorry_free MIPRE.AnswerReduction.cutVal,
  MIPRE.AnswerReduction.arCut,
  MIPRE.AnswerReduction.arVerifier,
  MIPRE.AnswerReduction.arSamplerProg,
  MIPRE.AnswerReduction.arSamplerProg_eq,
  MIPRE.AnswerReduction.arCompute,
  MIPRE.AnswerReduction.arCompute_eq,
  MIPRE.AnswerReduction.arVerifier_within,
  MIPRE.CL.Detyping.sampler_time,
  MIPRE.CL.Detyping.DeciderProgram.route_call_typed,
  MIPRE.CL.Detyping.DeciderProgram.prog_time,
  MIPRE.Pipeline.PDom,
  MIPRE.Pipeline.PRuns

-- blueprint `lem:ar-sampler-independence`: the output sampler depends only on the input sampler.
#guard_sorry_free MIPRE.AnswerReduction.arVerifier_sampler,
  MIPRE.AnswerReduction.arSamplerProg_eq

-- blueprint `lem:ar-completeness`: completeness of answer reduction, through the oracularized
-- honest strategy read through a question map, honest low-degree answers, and detyping.
#guard_sorry_free MIPRE.AnswerReduction.arVerifier_completeness,
  MIPRE.AnswerReduction.arVerifier_hasPerfectPCC,
  MIPRE.AnswerReduction.ShoupField,
  MIPRE.AnswerReduction.exists_typedGame_perfectPCC,
  MIPRE.AnswerReduction.hdata,
  MIPRE.AnswerReduction.accepts_honestAns,
  MIPRE.AnswerReduction.side_honest,
  MIPRE.AnswerReduction.honestAns,
  MIPRE.AnswerReduction.consistent_of_oaccepts,
  MIPRE.AnswerReduction.exists_proofGood,
  MIPRE.AnswerReduction.acceptsWithin_of_accepts,
  MIPRE.AnswerReduction.valid_of,
  MIPRE.AnswerReduction.length_enc_honestAns_le,
  MIPRE.SyncStrategy.pushQ,
  MIPRE.SyncStrategy.isPCC_pushQ,
  MIPRE.SyncStrategy.value_pushQ_eq_one,
  MIPRE.LIDT.CL.honest,
  MIPRE.LIDT.CL.accepts_honest,
  MIPRE.LIDT.CL.Regs.sampleOf_eval_question

-- blueprint `lem:ar-soundness-setup`: detyping soundness for answer reduction.
#guard_sorry_free MIPRE.AnswerReduction.typedStrategy,
  MIPRE.AnswerReduction.typedStrategy_value_ge

-- blueprint `lem:ar-decoding`: the decoded strategy for the typed oracularized game, the PCP's
-- soundness through the decoder, and `val*` of the input from a typed strategy.
#guard_sorry_free MIPRE.AnswerReduction.MAo,
  MIPRE.AnswerReduction.MBo,
  MIPRE.AnswerReduction.decAns,
  MIPRE.AnswerReduction.pcpOf,
  MIPRE.AnswerReduction.pcpSound,
  MIPRE.AnswerReduction.one_sub_povmValue_decoded_le,
  MIPRE.AnswerReduction.valStar_ge_decoded,
  MIPRE.AnswerReduction.valStar_ge_of_typedGame

-- blueprint `lem:ar-error-assembly`: soundness of answer reduction, under `FieldLarge`.
#guard_sorry_free MIPRE.AnswerReduction.arVerifier_soundness,
  MIPRE.AnswerReduction.FieldLarge,
  MIPRE.AnswerReduction.errE,
  MIPRE.AnswerReduction.errE_le,
  MIPRE.AnswerReduction.sqrt_le_delta,
  MIPRE.AnswerReduction.exists_threshold_clB,
  MIPRE.AnswerReduction.z_le

-- blueprint `lem:ar-global-tests`, `lem:ar-input-tests`, `lem:ar-common-polynomials`,
-- `lem:ar-simultaneous-proof`: the tests, the extraction per seed, and the relations of `J`.
#guard_sorry_free MIPRE.AnswerReduction.sum_edges_le,
  MIPRE.AnswerReduction.sum_copyFail_le,
  MIPRE.AnswerReduction.sum_copyFail6_le,
  MIPRE.AnswerReduction.sum_dis_edge_le,
  MIPRE.AnswerReduction.sum_dis_MA1_MB6_le,
  MIPRE.AnswerReduction.sum_dis_MA6_MB1_le,
  MIPRE.AnswerReduction.exists_ext1,
  MIPRE.AnswerReduction.ext1_spec,
  MIPRE.AnswerReduction.sum_deltaSim1_le,
  MIPRE.LIDT.Simul.sum_deltaSim_le,
  MIPRE.AnswerReduction.exists_ext6,
  MIPRE.AnswerReduction.ext6_spec,
  MIPRE.AnswerReduction.sum_deltaSim6_le,
  MIPRE.AnswerReduction.sum_dis_JAe_GBe_le,
  MIPRE.AnswerReduction.sum_dis_GAe_JBe_le

-- blueprint `lem:pcp-format` and `lem:pcp-complexity`: the PCP's proof format and its bounds.
#guard_sorry_free MIPRE.SAT.PcpProof,
  MIPRE.SAT.PcpProof.ev,
  MIPRE.SAT.PcpProof.rawView,
  MIPRE.SAT.ViewFormat,
  MIPRE.SAT.viewFormat_rawView,
  MIPRE.TM.CookLevin.Pad.verifyPcp_time_le,
  MIPRE.TM.CookLevin.Pad.pcpInput_size_polynomial,
  MIPRE.TM.CookLevin.Pad.outerDim_polynomial,
  MIPRE.AnswerReduction.exists_paramsBound_classical

-- blueprint `lem:answer-reduction-supply` and `thm:answer-reduction`: the answer-reduction
-- contract, inhabited over the classical PCP decider.
#guard_sorry_free MIPRE.AnswerReduction.answerReduction,
  MIPRE.AnswerReduction.shoupField_classical,
  MIPRE.AnswerReduction.exists_paramsBound_classical,
  MIPRE.AnswerReduction.fieldLarge_classical

-- blueprint `thm:compression-target`: gap-preserving compression, inhabited.
#guard_sorry_free MIPRE.gapCompression

-- blueprint `thm:main`, `cor:main-quantum`, `cor:value-uncomputable`, `thm:mipstar-eq-re`: the
-- main theorem and its consequences, with no hypothesis.
#guard_sorry_free HaltingGameValue.halting_reduces_to_gameValue,
  HaltingGameValue.HaltingReducesToGameValue,
  MIPRE.Halting.halting_reduces_to_gameValue_of,
  MIPRE.Halting.halting_reduction_quantum,
  MIPRE.Halting.gameValue_uncomputable,
  MIPRE.Halting.quantumValue_uncomputable,
  MIPRE.Halting.mipstar_eq_re,
  MIPRE.Halting.re_subset_mipstar

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
## The proved Shoup construction and its consumers

`#guard_sorry_free` excludes `sorryAx`; exact guards additionally exclude any
replacement unproved assumption. The former imported construction is now the
proved theorem `MIPRE.LowDegree.exists_shoup_irreducible`, witnessed directly by
the specified ambient program. The public constructor and both effective
consumers below depend only on Lean's standard axioms. The companion ledger's
historical admission remains unchanged; these guards describe the Lean proof.
-/

#guard_sorry_free MIPRE.LowDegree.BinaryPolynomial.irreducibleBitsProg,
  MIPRE.LowDegree.BinaryPolynomial.irreducibleBits_correct,
  MIPRE.LowDegree.BinaryPolynomial.irreducibleBits_length,
  MIPRE.LowDegree.BinaryPolynomial.irreducibleBitsProg_time_le,
  MIPRE.LowDegree.exists_shoup_irreducible,
  MIPRE.LowDegree.shoupIrreducible,
  MIPRE.LowDegree.shoupIrreducible_monic,
  MIPRE.LowDegree.shoupIrreducible_irreducible,
  MIPRE.LowDegree.shoupIrreducible_natDegree

/-- info: 'MIPRE.LowDegree.BinaryPolynomial.irreducibleBitsProg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MIPRE.LowDegree.BinaryPolynomial.irreducibleBitsProg

/-- info: 'MIPRE.LowDegree.BinaryPolynomial.irreducibleBits_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MIPRE.LowDegree.BinaryPolynomial.irreducibleBits_correct

/-- info: 'MIPRE.LowDegree.BinaryPolynomial.irreducibleBitsProg_time_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MIPRE.LowDegree.BinaryPolynomial.irreducibleBitsProg_time_le

/-- info: 'MIPRE.LowDegree.exists_shoup_irreducible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MIPRE.LowDegree.exists_shoup_irreducible

/-- info: 'MIPRE.LowDegree.shoupIrreducible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MIPRE.LowDegree.shoupIrreducible

/-- info: 'MIPRE.TM.CookLevin.Pad.classicalPcpDecider' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MIPRE.TM.CookLevin.Pad.classicalPcpDecider

/-- info: 'MIPRE.SAT.effective_selfDualNormalBasis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MIPRE.SAT.effective_selfDualNormalBasis


/-! ## Introspection construction, induction stages, and final extraction -/

#guard_sorry_free MIPRE.Introspection.ClockArithmetic.uniformProg_closed,
  MIPRE.Introspection.ClockArithmetic.uniformProg_runs,
  MIPRE.Introspection.growingClock_budget,
  MIPRE.Introspection.growingClock_runs,
  MIPRE.Introspection.growingClock_size,
  MIPRE.Introspection.growingClockCompiler_apply,
  MIPRE.Introspection.growingClockCompiler_runs,
  MIPRE.Introspection.growingClock_polynomial_time,
  MIPRE.Introspection.growingClock_ansBound_time,
  MIPRE.Introspection.ClockSimulation.prog_closed,
  MIPRE.Introspection.ClockSimulation.prog_halts,
  MIPRE.Introspection.ClockSimulation.decider_accepts_iff,
  MIPRE.Introspection.ClockSimulation.original_decider_preserved,
  MIPRE.Introspection.ClockSimulation.compiler_apply,
  MIPRE.Introspection.ClockSimulation.compiler_binary_bounds,
  MIPRE.Introspection.ClockSimulation.decider_haltsWithin,
  MIPRE.Introspection.ClockSimulation.original_decider_ansBound_time

#guard_sorry_free MIPRE.Introspection.Honest.coreOp_isPVM,
  MIPRE.Introspection.Honest.coreOp_commute,
  MIPRE.Introspection.Honest.coreStrategy_dimension,
  MIPRE.Introspection.Honest.exists_corePerfectPCC,
  MIPRE.Introspection.Honest.pauliZ_sample_commute,
  MIPRE.Introspection.Honest.sample_typed_reject_zero,
  MIPRE.Introspection.Honest.firstHideOp_isPVM,
  MIPRE.Introspection.Honest.pauli_firstHide_commute,
  MIPRE.Introspection.Honest.firstHide_typed_reject_zero

#guard_sorry_free MIPRE.Introspection.coarse_joint_commutator_bound,
  MIPRE.Introspection.productStage_mixing_premises,
  MIPRE.Introspection.exists_product_stage_of_coarse_tests

#guard_sorry_free MIPRE.Introspection.Honest.readRegister_isPVM,
  MIPRE.Introspection.Honest.hideRegister_isPVM,
  MIPRE.Introspection.Honest.readOp_marginal,
  MIPRE.Introspection.Honest.fullReadOp_isPVM,
  MIPRE.Introspection.Honest.fullReadOp_marginal,
  MIPRE.Introspection.Honest.introspect_read_commute,
  MIPRE.Introspection.Honest.read_typed_reject_zero

#guard_sorry_free MIPRE.Introspection.Honest.hideRegister_marginal,
  MIPRE.Introspection.Honest.hideOp_marginal,
  MIPRE.Introspection.Honest.pauliX_coordinateSplit,
  MIPRE.Introspection.Honest.stopHide_split,
  MIPRE.Introspection.Honest.readRegister_entry_supported,
  MIPRE.Introspection.Honest.hideRegister_entry_supported,
  MIPRE.Introspection.Honest.hidingNext_stop_join,
  MIPRE.Introspection.Honest.hidingNext_join,
  MIPRE.Introspection.Honest.hidingRead_join,
  MIPRE.Introspection.Honest.hideOp_commute_next,
  MIPRE.Introspection.Honest.hideOp_commute_read,
  MIPRE.Introspection.Honest.hideOp_reject_next_zero,
  MIPRE.Introspection.Honest.hideOp_reject_read_zero

#guard_sorry_free MIPRE.Introspection.Honest.parsedCoreOp_isPVM,
  MIPRE.Introspection.Honest.parsedReadOp_isPVM,
  MIPRE.Introspection.Honest.parsedHideOp_isPVM,
  MIPRE.Introspection.Honest.parsedCore_read_commute,
  MIPRE.Introspection.Honest.parsedRead_core_commute,
  MIPRE.Introspection.Honest.parsedCore_read_reject_zero,
  MIPRE.Introspection.Honest.parsedRead_core_reject_zero,
  MIPRE.Introspection.Honest.parsedHide_next_commute,
  MIPRE.Introspection.Honest.parsedHide_next_commute_reversed,
  MIPRE.Introspection.Honest.parsedHide_read_commute,
  MIPRE.Introspection.Honest.parsedRead_hide_commute,
  MIPRE.Introspection.Honest.parsedHide_next_reject_zero,
  MIPRE.Introspection.Honest.parsedHide_next_reject_zero_reversed,
  MIPRE.Introspection.Honest.parsedHide_read_reject_zero,
  MIPRE.Introspection.Honest.parsedRead_hide_reject_zero

#guard_sorry_free MIPRE.Introspection.bornProb_extVecA,
  MIPRE.Introspection.stateSqNorm_extVecA_aOp,
  MIPRE.Introspection.dilated_pvm_distance,
  MIPRE.Introspection.conditionalDilationOp_isPVM,
  MIPRE.Introspection.conditionalDilationOp_compress,
  MIPRE.Introspection.conditionalDilationOp_born,
  MIPRE.Introspection.extVecA_registerState,
  MIPRE.Introspection.exists_conditional_projective_dilation,
  MIPRE.Introspection.exists_varying_conditional_projective_dilation

#guard_sorry_free MIPRE.Introspection.conditional_coarse_consistency,
  MIPRE.Introspection.CLChecks.prefixRegister_outputPrefix_succ,
  MIPRE.Introspection.CLChecks.dualReadout_outputPrefix,
  MIPRE.Introspection.TypedEstimates.hiding_next_accepts_conditional,
  MIPRE.Introspection.TypedEstimates.hiding_next_conditional_estimate

#guard_sorry_free MIPRE.Introspection.pvm_event_stability,
  MIPRE.Introspection.joint_distance_left,
  MIPRE.Introspection.testAcceptance_stability_left,
  MIPRE.Introspection.testAcceptance_stability_right,
  MIPRE.Introspection.testAcceptance_stability,
  MIPRE.Introspection.qform_state_stability,
  MIPRE.Introspection.povmValue_state_stability,
  MIPRE.Introspection.povmValue_failure_transfer

#guard_sorry_free MIPRE.Introspection.TypedExtraction.cross_check,
  MIPRE.Introspection.TypedExtraction.condWin_cross_eq,
  MIPRE.Introspection.TypedExtraction.cross_failure_le,
  MIPRE.Introspection.TypedExtraction.pairReadout_isPVM,
  MIPRE.Introspection.TypedExtraction.condWin_cross_readout,
  MIPRE.Introspection.TypedExtraction.exists_strategy_of_terminal_form,
  MIPRE.Introspection.TypedExtraction.exists_strategy_of_approx_terminal_form,
  MIPRE.Introspection.TypedExtraction.exists_strategy_of_state_and_terminal_approx

/-! ## Executable introspection answer parsing and guarded source calls -/
#guard_sorry_free MIPRE.Introspection.AnswerParser.field_append_injective,
  MIPRE.Introspection.AnswerParser.pairCheck_iff,
  MIPRE.Introspection.AnswerParser.tripleCheck_iff,
  MIPRE.Introspection.AnswerParser.pairCheck_pairBits,
  MIPRE.Introspection.AnswerParser.tripleCheck_tripleBits,
  MIPRE.Introspection.AnswerParser.pairBits_lt_outer,
  MIPRE.Introspection.AnswerParser.readBits_lt_outer,
  MIPRE.Introspection.AnswerParser.hideBits_lt_outer,
  MIPRE.Introspection.AnswerParser.pairCheck_original_cutoff,
  MIPRE.Introspection.AnswerParser.readCheck_original_cutoff,
  MIPRE.Introspection.AnswerParser.guardedProg_closed,
  MIPRE.Introspection.AnswerParser.guardedProg_reject,
  MIPRE.Introspection.AnswerParser.guardedProg_halts,
  MIPRE.Introspection.AnswerParser.guardedProg_haltsWithin,
  MIPRE.Introspection.AnswerParser.callReady_fields,
  MIPRE.Introspection.AnswerParser.guardedProg_accepts_iff

/-! ## Introspection continuation: guarded normalizers and complete auxiliary game -/

#guard_sorry_free MIPRE.Introspection.CLChecks.prefixRegister_mono,
  MIPRE.Introspection.CLChecks.outputPrefix_outputPrefix,
  MIPRE.Introspection.CLChecks.prefixRegister_congr,
  MIPRE.Introspection.CLChecks.dualReadout_congr,
  MIPRE.Introspection.CLChecks.dualReadout_proj_compl_prefix,
  MIPRE.Introspection.CLChecks.tail_proj_tail,
  MIPRE.Introspection.TypedEstimates.hidingNextGuarded_factor,
  MIPRE.Introspection.TypedEstimates.hiding_next_accepts_guarded,
  MIPRE.Introspection.TypedEstimates.hiding_next_guarded_estimate,
  MIPRE.Introspection.TypedEstimates.hiding_next_normalizer_estimate

#guard_sorry_free MIPRE.Introspection.conditionalIdeal_isPVM,
  MIPRE.Introspection.conditional_coarse_overlap,
  MIPRE.Introspection.conditional_coarse_ideal_distance,
  MIPRE.Introspection.conditional_normalizer_change,
  MIPRE.Introspection.conditional_coarse_ideal_replacement,
  MIPRE.Introspection.conditional_coarse_ideal_of_test,
  MIPRE.Introspection.conditionalIdeal_mirror,
  MIPRE.Introspection.conditional_coarse_ideal_replacement_mirror

#guard_sorry_free MIPRE.Introspection.TypedEstimates.check_hiding_next_prefix,
  MIPRE.Introspection.TypedEstimates.check_hiding_read_prefix,
  MIPRE.Introspection.TypedEstimates.prefixChainType_adj,
  MIPRE.Introspection.TypedEstimates.prefixChainType_check,
  MIPRE.Introspection.TypedEstimates.prefix_chain_step_estimate,
  MIPRE.Introspection.TypedEstimates.hiding_introspect_prefix_estimate

#guard_sorry_free MIPRE.Introspection.TypedEstimates.prefix_chain_step_estimate_bob,
  MIPRE.Introspection.TypedEstimates.hiding_introspect_prefix_estimate_bob,
  MIPRE.Introspection.TypedEstimates.hidingNormalizer_eq_reportedPrefix,
  MIPRE.Introspection.TypedEstimates.hidingNormalizer_estimate

#guard_sorry_free MIPRE.Introspection.conditionalIdeal_eq_coarse_of_reject,
  MIPRE.Introspection.Honest.hidingPrefixOp_isPVM,
  MIPRE.Introspection.Honest.hidingPrefixOp_commute_hideOp,
  MIPRE.Introspection.Honest.hideOp_prefix_fixed,
  MIPRE.Introspection.Honest.hidingPrefixOp_mul_next,
  MIPRE.Introspection.Honest.hideCoarseOp_isPVM,
  MIPRE.Introspection.Honest.hideCoarseOp_conditionalIdeal_eq_next,
  MIPRE.Introspection.Honest.hideCoarseOp_conditionalIdeal_step

#guard_sorry_free MIPRE.Introspection.mirror_retained_distance_le,
  MIPRE.Introspection.conditional_coarse_ideal_replacement_retained,
  MIPRE.Introspection.Honest.hideCoarseOp_transpose,
  MIPRE.Introspection.Honest.hideCoarseOp_epr_mirror,
  MIPRE.Introspection.Honest.hideNextRetain_mapped,
  MIPRE.Introspection.Honest.hideCoarseOp_step_of_normalizer,
  MIPRE.Introspection.Honest.hideCoarseOp_registerState_mirror,
  MIPRE.Introspection.Honest.hidingPrefixOp_registerState_mirror,
  MIPRE.Introspection.Honest.hideCoarseOp_aux_step_of_normalizer,
  MIPRE.Introspection.TypedEstimates.hiding_next_seed_rigidity,
  MIPRE.Introspection.TypedEstimates.hiding_next_register_rigidity

#guard_sorry_free MIPRE.Introspection.Honest.hideOp_zero_eq_firstHideOp,
  MIPRE.Introspection.Honest.pauliX_hideOp_zero_commute,
  MIPRE.Introspection.Honest.pauliX_hideOp_zero_reject,
  MIPRE.Introspection.Honest.parsedPauliXOp_isPVM,
  MIPRE.Introspection.Honest.parsedPauliZOp_isPVM,
  MIPRE.Introspection.Honest.parsedPauliX_hide_commute,
  MIPRE.Introspection.Honest.parsedPauliZ_sample_commute,
  MIPRE.Introspection.Honest.parsedPauliX_hide_reject_zero,
  MIPRE.Introspection.Honest.parsedPauliZ_sample_reject_zero,
  MIPRE.Introspection.Honest.parsedHide_pauliX_reject_zero,
  MIPRE.Introspection.Honest.parsedSample_pauliZ_reject_zero,
  MIPRE.Introspection.Honest.auxOp_isPVM,
  MIPRE.Introspection.Honest.auxOp_commute,
  MIPRE.Introspection.Honest.auxOp_reject_zero,
  MIPRE.Introspection.Honest.auxStrategy_dimension,
  MIPRE.Introspection.Honest.auxStrategy_isPCC,
  MIPRE.Introspection.Honest.auxStrategy_value,
  MIPRE.Introspection.Honest.exists_auxPerfectPCC

#guard_sorry_free MIPRE.Introspection.DynamicParser.boundedOffset_length_le,
  MIPRE.Introspection.DynamicParser.pairCheck_iff,
  MIPRE.Introspection.DynamicParser.tripleCheck_iff,
  MIPRE.Introspection.DynamicParser.pairCheck_original_cutoff,
  MIPRE.Introspection.DynamicParser.readCheck_original_cutoff,
  MIPRE.Introspection.SourceCompiler.boundsProg_closed,
  MIPRE.Introspection.SourceCompiler.boundsProg_runs,
  MIPRE.Introspection.SourceCompiler.boundsProg_runs_cost,
  MIPRE.Introspection.SourceCompiler.sourceCheck_iff,
  MIPRE.Introspection.SourceCompiler.guardCheck_iff,
  MIPRE.Introspection.SourceCompiler.GuardReady_cutoffs,
  MIPRE.Introspection.SourceCompiler.GuardReady_question_lengths,
  MIPRE.Introspection.SourceCompiler.GuardReady_padding,
  MIPRE.Introspection.SourceCompiler.projectedProg_reject,
  MIPRE.Introspection.SourceCompiler.projectedProg_accepts_iff,
  MIPRE.Introspection.SourceCompiler.crossProg_closed,
  MIPRE.Introspection.SourceCompiler.crossProg_halts,
  MIPRE.Introspection.SourceCompiler.bounded_dimensionResult,
  MIPRE.Introspection.SourceCompiler.crossProg_original_iff,
  MIPRE.Introspection.SourceCompiler.crossCompiler_apply,
  MIPRE.Introspection.SourceCompiler.crossCompiler_binary_bounds,
  MIPRE.Introspection.SourceCompiler.crossProg_haltsWithin

#guard_sorry_free MIPRE.Introspection.TypedPresentation.mu_constant_edge,
  MIPRE.Introspection.TypedPresentation.mu_pauli_aux,
  MIPRE.Introspection.TypedPresentation.mu_aux_pauli,
  MIPRE.Introspection.TypedEstimates.pauli_aux_agreement_estimate,
  MIPRE.Introspection.TypedEstimates.aux_pauli_agreement_estimate,
  MIPRE.Introspection.Honest.pauliXReadout_firstHide,
  MIPRE.Introspection.Honest.pauliXReadout_registerState_mirror,
  MIPRE.Introspection.TypedEstimates.hiding_first_agreement_estimate,
  MIPRE.Introspection.TypedEstimates.hiding_first_register_rigidity,
  MIPRE.Introspection.TypedEstimates.idealZ_prefix_fibSum,
  MIPRE.Introspection.TypedEstimates.introspect_prefix_register_rigidity_bob

#guard_sorry_free MIPRE.Introspection.sum_xSqNorm_mirror_transfer,
  MIPRE.Introspection.TypedEstimates.hiding_register_orientation,
  MIPRE.Introspection.TypedEstimates.hiding_register_recurrence,
  MIPRE.Introspection.TypedEstimates.hiding_register_iteration,
  MIPRE.Introspection.TypedEstimates.hiding_register_iteration_uniform,
  MIPRE.Introspection.TypedEstimates.hiding_register_rigidity_of_pauli

#guard_sorry_free MIPRE.Introspection.CLChecks.factorOfPrefix_outputPrefix,
  MIPRE.Introspection.CLChecks.factorOfPrefix_subset_prefixRegister,
  MIPRE.Introspection.TypedEstimates.check_hiding_next_dual,
  MIPRE.Introspection.TypedEstimates.check_hiding_read_dual,
  MIPRE.Introspection.TypedEstimates.hiding_read_dual_chain_estimate,
  MIPRE.Introspection.Honest.readDualOp_isPVM,
  MIPRE.Introspection.Honest.readDualOp_registerState_mirror,
  MIPRE.Introspection.TypedEstimates.read_register_rigidity_alice,
  MIPRE.Introspection.TypedEstimates.read_register_rigidity_bob,
  MIPRE.Introspection.TypedEstimates.read_register_rigidity_of_pauli

#guard_sorry_free MIPRE.Introspection.TypedEstimates.introspect_read_full_estimate,
  MIPRE.Introspection.TypedEstimates.introspect_dual_commutator,
  MIPRE.Introspection.TypedEstimates.introspect_coarseZ_commutator_bob,
  MIPRE.Introspection.TypedEstimates.introspect_coarseZ_commutator_alice

#guard_sorry_free MIPRE.Introspection.CLChecks.residual_supported,
  MIPRE.Introspection.CLChecks.residual_exactlyOn,
  MIPRE.Introspection.CLChecks.stageFactor_subset_residual,
  MIPRE.Introspection.CLChecks.residualRegister_step,
  MIPRE.Introspection.CLChecks.dualReadout_stageLinear,
  MIPRE.Introspection.prefixWeight_eq_card,
  MIPRE.Introspection.prefixWeight_pos_iff,
  MIPRE.Introspection.sum_prefixWeight_supported,
  MIPRE.Introspection.hidingPrefixOp_registerState_weight,
  MIPRE.Introspection.prefixResidual_distance_sum,
  MIPRE.Introspection.prefixResidual_commutator_sum

#guard_sorry_free MIPRE.Introspection.Honest.hidingPrefixOp_factor,
  MIPRE.Introspection.Honest.readDualOp_eq_registerDual,
  MIPRE.Introspection.Honest.dualRegister_cons_succ,
  MIPRE.Introspection.Honest.synX_split_second,
  MIPRE.Introspection.Honest.readDualOp_prefix_factor,
  MIPRE.Introspection.readDualOp_stage_factor,
  MIPRE.Introspection.adaptiveZ_readout_factor

#guard_sorry_free MIPRE.Introspection.prefixResidual_isPVM,
  MIPRE.Introspection.prefixResidual_reassembled_isPVM,
  MIPRE.Introspection.prefixResidual_reassembled_distance,
  MIPRE.Introspection.prefixResidual_reassembled_commutator_sum,
  MIPRE.Introspection.adaptiveZ_reassembled_commutator_sum,
  MIPRE.Introspection.prefixResidualOp_extend

#guard_sorry_free MIPRE.Introspection.stageRemaining_step,
  MIPRE.Introspection.prefixStageMarginalError_eq,
  MIPRE.Introspection.prefixStageCommutatorError_eq,
  MIPRE.Introspection.exists_adaptive_prefix_mixing,
  MIPRE.Introspection.transportedConditionalDilation_compress,
  MIPRE.Introspection.exists_adaptive_prefix_dilation,
  MIPRE.Introspection.adaptiveReplacement_distance

#guard_sorry_free MIPRE.Introspection.testAcceptance_stability_map_left,
  MIPRE.Introspection.replaceExtended_other,
  MIPRE.Introspection.replaceExtended_value,
  MIPRE.Introspection.registeredReplacementStrategy_value_loss,
  MIPRE.Introspection.exists_conditional_replacement_strategy,
  MIPRE.Introspection.exists_adaptive_replacement_strategy

#guard_sorry_free MIPRE.Introspection.advancePrefix_old_prefix,
  MIPRE.Introspection.advancePrefix_remaining,
  MIPRE.Introspection.advancePrefix_injective,
  MIPRE.Introspection.advancePrefix_eval,
  MIPRE.Introspection.adaptiveLinear_readout_factor,
  MIPRE.Introspection.advancePrefix_projector_assembly

#guard_sorry_free MIPRE.Introspection.adaptiveDualLabel_injective,
  MIPRE.Introspection.adaptiveX_reassembled_commutator_le,
  MIPRE.Introspection.TypedEstimates.introspect_adaptiveX_commutator,
  MIPRE.Introspection.option_readout_commutator_sum,
  MIPRE.Introspection.TypedEstimates.introspect_adaptiveZ_commutator

#guard_sorry_free MIPRE.Introspection.advancePrefix_fibSum_sqNorm,
  MIPRE.Introspection.prefixStageMarginalError_reassembled

#guard_sorry_free MIPRE.Introspection.graphRefinementPOVM_isPVM,
  MIPRE.Introspection.graphRefinementPOVM_recover,
  MIPRE.Introspection.stageAnswerRefinement_commutator,
  MIPRE.Introspection.stageAnswerDecode_prefix,
  MIPRE.Introspection.stageAnswerDecode_next,
  MIPRE.Introspection.stageAnswerRefinementPOVM_decode_recover,
  MIPRE.Introspection.canonicalizeIntro_isPVM,
  MIPRE.Introspection.TypedEstimates.canonicalizeIntro_value

#guard_sorry_free MIPRE.Introspection.adaptiveReplacementJointOp_next_factor,
  MIPRE.Introspection.nextPrefixResidual_isPVM,
  MIPRE.Introspection.adaptiveReplacementJointOp_next_reassembly,
  MIPRE.Introspection.nextPrefixDecodedPOVM_isPVM,
  MIPRE.Introspection.registeredReplacement_next_mats,
  MIPRE.Introspection.exists_adaptive_next_strategy

#guard_sorry_free MIPRE.Introspection.TypedEstimates.introspect_prefix_register_rigidity_alice,
  MIPRE.Introspection.stageAnswerRefinement_coarse_marginal,
  MIPRE.Introspection.stageAnswerRefinement_marginal_le_reported,
  MIPRE.Introspection.TypedEstimates.introspect_adaptive_marginal,
  MIPRE.Introspection.TypedEstimates.introspect_refined_stage_bounds,
  MIPRE.Introspection.TypedEstimates.exists_game_adaptive_prefix_dilation,
  MIPRE.Introspection.adaptiveStepLoss_le_root,
  MIPRE.Introspection.adaptiveFailureBudget_mono

#guard_sorry_free MIPRE.Introspection.stateSqNorm_registeredExtendOp,
  MIPRE.Introspection.xSqNorm_registeredExtendOp,
  MIPRE.Introspection.bornProb_registeredExtendOp,
  MIPRE.Introspection.registeredReplacement_samePartyError_other,
  MIPRE.Introspection.registeredReplacement_crossError_other,
  MIPRE.Introspection.TypedEstimates.pauliAliceError_registeredReplacement,
  MIPRE.Introspection.TypedEstimates.pauliBobError_registeredExtension,
  MIPRE.Introspection.TypedEstimates.hidingAliceError_registeredReplacement,
  MIPRE.Introspection.TypedEstimates.hidingBobError_registeredExtension,
  MIPRE.Introspection.TypedEstimates.readAliceError_registeredReplacement,
  MIPRE.Introspection.TypedEstimates.readBobError_registeredExtension

#print axioms MIPRE.Introspection.exists_adaptive_next_strategy
#print axioms MIPRE.Introspection.TypedEstimates.exists_game_adaptive_prefix_dilation
#print axioms MIPRE.Introspection.TypedEstimates.canonicalizeIntro_value

#guard_sorry_free MIPRE.Introspection.exists_initial_residual,
  MIPRE.Introspection.initialIntroPrefixInvariant,
  MIPRE.Introspection.nextPrefixDecodedPOVM_some_support,
  MIPRE.Introspection.registeredReplacement_nextOption_mats,
  MIPRE.Introspection.canonicalizeIntro_adaptive_selected,
  MIPRE.Introspection.registeredReplacement_canonicalizeIntro,
  MIPRE.Introspection.introSuccessorFamily_isPVM,
  MIPRE.Introspection.introSuccessorInvariant,
  MIPRE.Introspection.TypedEstimates.exists_intro_successor

#guard_sorry_free MIPRE.Introspection.adaptiveStageBudget_mono_depth,
  MIPRE.Introspection.adaptiveFailureBudget_nonneg,
  MIPRE.Introspection.adaptiveSmallThreshold_pos,
  MIPRE.Introspection.adaptiveFailureBudget_le_threshold,
  MIPRE.Introspection.adaptiveStageBudget_le_one_of_threshold

#guard_sorry_free MIPRE.Introspection.introIterationState_unit,
  MIPRE.Introspection.TypedEstimates.introBobZError_introIterationState,
  MIPRE.Introspection.TypedEstimates.exists_intro_iteration

#print axioms MIPRE.Introspection.TypedEstimates.exists_intro_successor
#print axioms MIPRE.Introspection.TypedEstimates.exists_intro_iteration

#guard_sorry_free MIPRE.Introspection.terminalAuxPOVM_isPVM,
  MIPRE.Introspection.IntroPrefixInvariant.terminal_some,
  MIPRE.Introspection.IntroPrefixInvariant.terminal_none

#guard_sorry_free MIPRE.Introspection.swapVec_registerState,
  MIPRE.Introspection.TypedPresentation.mu_swap,
  MIPRE.Introspection.TypedEstimates.parsedGame_value_swap,
  MIPRE.Introspection.introBobIterationState_unit,
  MIPRE.Introspection.TypedEstimates.introAliceZError_of_iteration_other,
  MIPRE.Introspection.TypedEstimates.hidingBobError_introIterationState,
  MIPRE.Introspection.TypedEstimates.exists_intro_bob_iteration

#guard_sorry_free MIPRE.Introspection.adaptiveFailureBudget_add,
  MIPRE.Introspection.introTwoSidedState_unit,
  MIPRE.Introspection.TypedEstimates.exists_intro_two_sided_iteration

#guard_sorry_free MIPRE.Introspection.completeOptionPOVM_isPVM,
  MIPRE.Introspection.option_valid_acceptance_le_complete,
  MIPRE.Introspection.readoutAcceptance_le_completedValue,
  MIPRE.Introspection.IntroPrefixInvariant.terminal_parsed_pair,
  MIPRE.Introspection.TypedExtraction.exists_strategy_of_terminal_invariants

#guard_sorry_free MIPRE.Introspection.iteratedRoot_scale_le,
  MIPRE.Introspection.adaptiveFailureBudget_le_power,
  MIPRE.Introspection.adaptiveSoundness_power_cases,
  MIPRE.Introspection.exists_adaptiveSoundness_errorProfile

#guard_sorry_free MIPRE.Introspection.TypedEstimates.introAliceZError_le_of_bob,
  MIPRE.Introspection.primitiveBudgetCoefficient_bounds,
  MIPRE.Introspection.primitiveSoundnessCoefficient_one_le,
  MIPRE.Introspection.primitiveSoundness_power_bounds,
  MIPRE.Introspection.exists_primitiveSoundness_errorProfile,
  MIPRE.Introspection.TypedEstimates.quantumValue_ge_of_primitive_pauli,
  MIPRE.Introspection.TypedEstimates.quantumValue_ge_of_primitive_profile

#print axioms MIPRE.Introspection.TypedEstimates.quantumValue_ge_of_primitive_pauli
#print axioms MIPRE.Introspection.TypedEstimates.quantumValue_ge_of_primitive_profile

#guard_sorry_free MIPRE.Introspection.sum_pvm_snorm_sq,
  MIPRE.Introspection.sum_pvm_difference_snorm_sq_le,
  MIPRE.Introspection.sum_stateSqNorm_state_transfer_le,
  MIPRE.Introspection.sum_bob_snorm_state_transfer_le,
  MIPRE.Introspection.extractedSoundnessCoefficient_one_le,
  MIPRE.Introspection.extractedSoundness_power_bound,
  MIPRE.Introspection.exists_extractedSoundness_errorProfile,
  MIPRE.Introspection.TypedEstimates.quantumValue_ge_of_extracted_state

#guard_sorry_free MIPRE.Introspection.HonestMagicSquare.grid_isObservable,
  MIPRE.Introspection.HonestMagicSquare.cells_commute,
  MIPRE.Introspection.HonestMagicSquare.row_product,
  MIPRE.Introspection.HonestMagicSquare.variableOp_isPVM,
  MIPRE.Introspection.HonestMagicSquare.constraintOp_isPVM,
  MIPRE.Introspection.HonestMagicSquare.variable_constraint_commute,
  MIPRE.Introspection.HonestMagicSquare.constraint_reject_zero,
  MIPRE.Introspection.HonestMagicSquare.variableOp_embeds_first,
  MIPRE.Introspection.HonestMagicSquare.variableOp_embeds_second,
  MIPRE.Introspection.HonestMagicSquare.grid_transpose,
  MIPRE.Introspection.HonestMagicSquare.constraintOp_transpose,
  MIPRE.Introspection.HonestMagicSquare.questionOp_isPVM,
  MIPRE.Introspection.HonestMagicSquare.questionOp_reject,
  MIPRE.Introspection.HonestMagicSquare.strategy_isPCC,
  MIPRE.Introspection.HonestMagicSquare.strategy_value,
  MIPRE.Introspection.HonestMagicSquare.exists_perfectPCC

#print axioms MIPRE.Introspection.TypedEstimates.quantumValue_ge_of_extracted_state
#print axioms MIPRE.Introspection.HonestMagicSquare.exists_perfectPCC

#guard_sorry_free MIPRE.Introspection.isometricPOVM_isPVM,
  MIPRE.Introspection.isometricEffect_intertwine,
  MIPRE.Introspection.isometricState_unit,
  MIPRE.Introspection.povmValue_isometricState,
  MIPRE.Introspection.isometricState_map_alice_deviation,
  MIPRE.Introspection.isometricState_map_bob_deviation,
  MIPRE.Introspection.projector_mass_le_state_distance,
  MIPRE.Introspection.isometricComplement_alice_mass,
  MIPRE.Introspection.isometricComplement_bob_mass,
  MIPRE.Introspection.isometricEffect_alice_error_le,
  MIPRE.Introspection.isometricEffect_bob_error_le

#guard_sorry_free MIPRE.Introspection.isometricPOVM_map_mats_eq,
  MIPRE.Introspection.TypedEstimates.quantumValue_ge_of_isometric_images,
  MIPRE.Introspection.submeasurement_extension_mass,
  MIPRE.Introspection.submeasurement_extension_dist,
  MIPRE.Introspection.valid_outcome_error_le,
  MIPRE.Introspection.isometric_valid_outcome_alice_error_le,
  MIPRE.Introspection.isometric_valid_outcome_bob_error_le,
  MIPRE.Introspection.validSoundnessCoefficient_one_le,
  MIPRE.Introspection.exists_validSoundness_errorProfile,
  MIPRE.Introspection.TypedEstimates.quantumValue_ge_of_valid_isometric_images

#print axioms MIPRE.Introspection.TypedEstimates.quantumValue_ge_of_valid_isometric_images

#guard_sorry_free MIPRE.Introspection.LineProgram.lineRepresentativeProg_correct,
  MIPRE.Introspection.LineProgram.lineRepresentativeProg_runs,
  MIPRE.Introspection.LineProgram.lineRepresentativeProg_time_le

#guard_sorry_free MIPRE.Introspection.completePauliPOVM_isPVM,
  MIPRE.Introspection.completePauliPOVM_mats_of_ne,
  MIPRE.Introspection.TypedEstimates.check_pauli_completed,
  MIPRE.Introspection.TypedEstimates.completed_pauli_condFail_le,
  MIPRE.Introspection.TypedEstimates.typed_edge_mean_failure_le

#guard_sorry_free MIPRE.Introspection.SeedProgram.selector_eq_bits,
  MIPRE.Introspection.SeedProgram.card_selector_fiber,
  MIPRE.Introspection.SeedProgram.selectorProg_correct,
  MIPRE.Introspection.SeedProgram.selectorProg_runs,
  MIPRE.Introspection.SeededLineProgram.axisRepresentativeProg_correct,
  MIPRE.Introspection.SeededLineProgram.selectedDirectionProg_correct,
  MIPRE.Introspection.SeededLineProgram.diagonalRepresentativeProg_correct,
  MIPRE.Introspection.SeededLineProgram.axisRepresentativeProg_runs,
  MIPRE.Introspection.SeededLineProgram.diagonalRepresentativeProg_runs

#guard_sorry_free MIPRE.Introspection.SourcePadding.family_supported,
  MIPRE.Introspection.SourcePadding.depthFamily_exactlyOn,
  MIPRE.Introspection.SourcePadding.depthFamily_eval,
  MIPRE.Introspection.SourcePadding.strategy_isPCC,
  MIPRE.Introspection.SourcePadding.strategy_value,
  MIPRE.Introspection.SourcePadding.average_pull,
  MIPRE.Introspection.SourcePadding.restrictStrategy_state,
  MIPRE.Introspection.SourcePadding.restrictStrategy_value,
  MIPRE.Introspection.SourcePadding.quantumValue_le,
  MIPRE.Introspection.SourcePadding.quantumValue_depthFamily_le

#guard_sorry_free MIPRE.Introspection.BasisProgram.toSelfDualProg_correct,
  MIPRE.Introspection.BasisProgram.fromSelfDualProg_correct,
  MIPRE.Introspection.AuxiliaryProgram.readingCheck_typed,
  MIPRE.Introspection.AuxiliaryProgram.rawCheck_haltsWithin,
  MIPRE.Introspection.AuxiliaryProgram.samplingProg_depthFamily,
  MIPRE.Introspection.AuxiliaryCanonical.canonicalProg_correct

/-! ## Canonical introspection compiler, finite kernel and QLD transport -/

#guard_sorry_free MIPRE.Introspection.PauliSampler.sampler,
  MIPRE.Introspection.PauliSampler.fullCompiler_apply,
  MIPRE.Introspection.PauliSampler.finalCompiler_apply,
  MIPRE.Introspection.PauliSampler.finalSampler_dim_zero,
  MIPRE.Introspection.PauliSampler.finalSampler_uniform_bound

#guard_sorry_free MIPRE.QLD.PauliBinaryProgram.program_ofBits_iff,
  MIPRE.QLD.PauliBinaryProgram.program_canonical,
  MIPRE.QLD.PauliAnswerProgram.answerBits_decodeBits,
  MIPRE.Introspection.DecisionKernel.Answer.pauliDecode_format,
  MIPRE.Introspection.DecisionKernel.Answer.rawProject_pauliDecode

#guard_sorry_free MIPRE.Introspection.AuxiliaryDual.rowSpaceCheck_correct,
  MIPRE.Introspection.AuxiliaryDecision.guarded_complete,
  MIPRE.Introspection.AuxiliaryDecision.check_raw_sound,
  MIPRE.Introspection.DecisionKernel.program_sound_numbered,
  MIPRE.Introspection.DecisionKernel.program_complete_numbered

#guard_sorry_free MIPRE.Introspection.ExplicitGame.game_mu,
  MIPRE.Introspection.ExplicitGame.game_D,
  MIPRE.Introspection.ExplicitGame.toLegacy_value,
  MIPRE.Introspection.ExplicitGame.pccToExplicit_isPCC,
  MIPRE.Introspection.AuxiliaryQuotient.value_le_decodedStrategy,
  MIPRE.Introspection.NumberedComplete.exists_perfectPCC_with_format,
  MIPRE.Introspection.NumberedSoundness.quantumValue_ge_of_qld,
  MIPRE.Introspection.NumberedSoundness.canonical_quantumValue_ge

#guard_sorry_free MIPRE.Introspection.DecisionCompiler.resources_with_cutoff,
  MIPRE.Introspection.DecisionCompiler.raw_accepts_iff,
  MIPRE.Introspection.DecisionCompiler.output_hasPerfectPCC_of_raw,
  MIPRE.Introspection.DecisionCompiler.exists_raw_failure_le,
  MIPRE.Introspection.CanonicalDecoded.value_le,
  MIPRE.Introspection.CanonicalDecoded.supported_A,
  MIPRE.Introspection.CanonicalDecoded.supported_B

#guard_sorry_free MIPRE.Introspection.exists_seven,
  MIPRE.Introspection.seven,
  MIPRE.Introspection.CanonicalComplete.output_hasPerfectPCC,
  MIPRE.Introspection.CompiledSoundness.output_soundness

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

/-! `cor:compression-from-answer-reduction`: the pipeline with its supplied stages
(`MIPRE/Background/Pipeline.lean`). -/
#guard_sorry_free MIPRE.GapCompression.ofAnswerReduction,
  MIPRE.Halting.halting_reduces_to_gameValue_of_answerReduction,
  MIPRE.Halting.halting_reduction_quantum_of_answerReduction,
  MIPRE.Halting.gameValue_uncomputable_of_answerReduction,
  MIPRE.Halting.quantumValue_uncomputable_of_answerReduction,
  MIPRE.Halting.re_subset_mipstar_of_answerReduction,
  MIPRE.Halting.mipstar_eq_re_of_answerReduction

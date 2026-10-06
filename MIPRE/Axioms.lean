/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.GuardSorryFree
public import MIPRE.Foundations.Introspection.BasisProg
public import MIPRE.Foundations.Introspection.AuxiliaryReadProgram
public import MIPRE.Foundations.Introspection.AuxiliarySamplingCorrect
public import MIPRE.Foundations.Introspection.AuxiliaryCanonicalProgram
public import MIPRE.Background.Introspection.DecisionKernelComplete
public import MIPRE.Background.Introspection.CanonicalDecodedStrategy
public import MIPRE.Background.Introspection.NumberedSoundness
public import MIPRE.Background.Introspection.Compiler
public import MIPRE.Background.Pipeline
public import MIPRE.Foundations.Blocks
public import MIPRE.Foundations.CL.Basic
public import MIPRE.Foundations.LowDegree.SchwartzZippel
public import MIPRE.Foundations.LowDegree.ZeroBasis
public import MIPRE.Foundations.LowDegree.BinarySquareRoot
public import MIPRE.Foundations.LowDegree.BinaryInverse
public import MIPRE.Foundations.LowDegree.BinaryNormalize
public import MIPRE.Foundations.LowDegree.BinaryDivision
public import MIPRE.Foundations.LowDegree.BinaryQuotient
public import MIPRE.Foundations.LowDegree.BinaryExactDivision
public import MIPRE.Foundations.LowDegree.BinaryQuotientReduced
public import MIPRE.Foundations.LowDegree.BinaryFactorization
public import MIPRE.Foundations.LowDegree.BinaryArtinSchreierLoop
public import MIPRE.Foundations.LowDegree.BinaryOrbitDescent
public import MIPRE.Foundations.LowDegree.BinaryNonresidueCorrectness
public import MIPRE.Foundations.LowDegree.BinaryOddPrimeConstructor
public import MIPRE.Foundations.LowDegree.BinaryComposedSum
public import MIPRE.Foundations.LowDegree.BinaryDegreeDecomposition
public import MIPRE.Foundations.LowDegree.Shoup
public import MIPRE.Foundations.LowDegree.BinaryMatrixInverse
public import MIPRE.Foundations.LowDegree.BinaryKernel
public import MIPRE.Foundations.SAT.FieldTrace
public import MIPRE.Foundations.SAT.FrobeniusMatrix
public import MIPRE.Foundations.SAT.TraceGram
public import MIPRE.Foundations.SAT.BasisTransport
public import MIPRE.Foundations.SAT.EffectiveSelfDual
public import MIPRE.Foundations.SAT.EffectiveNormalBasis
public import MIPRE.Foundations.Introspection.Commutation
public import MIPRE.Foundations.Introspection.Twirl
public import MIPRE.Foundations.Introspection.Measurements
public import MIPRE.Foundations.Introspection.BlockPOVM
public import MIPRE.Foundations.Introspection.TwirlDistance
public import MIPRE.Foundations.Introspection.VaryingPauliMixing
public import MIPRE.Foundations.Introspection.Conditioning
public import MIPRE.Foundations.Introspection.ConditionalConsistency
public import MIPRE.Foundations.CL.Graph
public import MIPRE.Foundations.CL.DetypingQueries
public import MIPRE.Foundations.CL.DetypingSoundness
public import MIPRE.Foundations.CL.DetypingComplete
public import MIPRE.Foundations.CL.DetypingAnswers
public import MIPRE.Foundations.CL.DetypingProgGraph
public import MIPRE.Foundations.CL.DetypingProgTyped
public import MIPRE.Foundations.CL.DetypingProgSampler
public import MIPRE.Foundations.CL.DetypingProgCost
public import MIPRE.Foundations.Introspection.TypedPresentation
public import MIPRE.Foundations.Introspection.TypedPredicate
public import MIPRE.Foundations.Introspection.AmbientMixing
public import MIPRE.Foundations.Introspection.ErrorBounds
public import MIPRE.Foundations.Introspection.HidingTests
public import MIPRE.Foundations.Introspection.FinalExtraction
public import MIPRE.Foundations.Introspection.Runtime
public import MIPRE.Foundations.CL.DetypingDeciderGame
public import MIPRE.Foundations.CL.DetypingDeciderTransport
public import MIPRE.Foundations.CL.DetypingClock
public import MIPRE.Foundations.Introspection.TypedEstimates
public import MIPRE.Foundations.Introspection.SamplerCost
public import MIPRE.Foundations.Introspection.ClockCost
public import MIPRE.Foundations.Introspection.ClockSimulation
public import MIPRE.Foundations.Introspection.ClockCompiler
public import MIPRE.Foundations.Introspection.ClockSimulationCost
public import MIPRE.Foundations.Introspection.ParserGuard
public import MIPRE.Foundations.Introspection.HonestCoreGame
public import MIPRE.Foundations.Introspection.HonestSampling
public import MIPRE.Foundations.Introspection.HonestFirstHide
public import MIPRE.Foundations.Introspection.HonestReading
public import MIPRE.Foundations.Introspection.HonestParsed
public import MIPRE.Foundations.Introspection.HonestParsedHiding
public import MIPRE.Foundations.Introspection.HonestHidingCommute
public import MIPRE.Foundations.Introspection.HonestHidingAcceptance
public import MIPRE.Foundations.Introspection.HidingInductionDilation
public import MIPRE.Foundations.Introspection.HidingInduction
public import MIPRE.Foundations.Introspection.HidingRigidity
public import MIPRE.Foundations.Introspection.TypedExtraction
public import MIPRE.Foundations.Introspection.HidingNormalizer
public import MIPRE.Foundations.Introspection.ConditionalNormalizerMirror
public import MIPRE.Foundations.Introspection.ConditionalNormalizerIdeal
public import MIPRE.Foundations.Introspection.HonestCompleteGame
public import MIPRE.Foundations.Introspection.HonestPauliEdges
public import MIPRE.Foundations.Introspection.TypedPrefixChainEstimate
public import MIPRE.Foundations.Introspection.HidingNormalizerPrefix
public import MIPRE.Foundations.Introspection.SourceCompilerBinary
public import MIPRE.Foundations.Introspection.SourceCompilerCost
public import MIPRE.Foundations.Introspection.ConditionalNormalizerStepGame
public import MIPRE.Foundations.Introspection.ConditionalNormalizerStepSeed
public import MIPRE.Foundations.Introspection.ReadRigidityGame
public import MIPRE.Foundations.Introspection.ProductStageReadTests
public import MIPRE.Foundations.Introspection.ProductStageZTests
public import MIPRE.Foundations.Introspection.AdaptivePrefixAdvance
public import MIPRE.Foundations.Introspection.AdaptivePrefixCommutator
public import MIPRE.Foundations.Introspection.AdaptiveDualLocal
public import MIPRE.Foundations.Introspection.AdaptivePrefixStrategy
public import MIPRE.Foundations.Introspection.StrategyReplacementDilation
public import MIPRE.Foundations.Introspection.AdaptiveXTest
public import MIPRE.Foundations.Introspection.AdaptiveZTest
public import MIPRE.Foundations.Introspection.AdaptivePrefixMarginal
public import MIPRE.Foundations.Introspection.AdaptiveGameStage
public import MIPRE.Foundations.Introspection.AdaptiveNextStrategy
public import MIPRE.Foundations.Introspection.IntrospectCanonicalization
public import MIPRE.Foundations.Introspection.StrategyReplacementErrors
public import MIPRE.Foundations.Introspection.AdaptiveInductionIteration
public import MIPRE.Foundations.Introspection.AdaptiveTerminalInvariant
public import MIPRE.Foundations.Introspection.PrimitiveSoundness
public import MIPRE.Foundations.Introspection.ExtractedStateSoundness
public import MIPRE.Foundations.Introspection.HonestMagicSquareGame
public import MIPRE.Foundations.Introspection.IsometricCompletionError
public import MIPRE.Foundations.Introspection.ValidPauliSoundness
public import MIPRE.Foundations.Introspection.LineRepresentativeProg
public import MIPRE.Foundations.Introspection.PauliRestriction
public import MIPRE.Foundations.Introspection.SeededLineProg
public import MIPRE.Foundations.Introspection.SourcePaddingValue
public import MIPRE.Foundations.SAT.Arithmetization
public import MIPRE.Foundations.SAT.FiniteCircuitArithmetization
public import MIPRE.Foundations.SAT.CircuitFieldCorrect
public import MIPRE.TM.CookLevin.PcpCircuit
public import MIPRE.TM.CookLevin.PcpViewSize
public import MIPRE.TM.CookLevin.ClassicalPcp
public import MIPRE.Foundations.SAT.Padding
public import MIPRE.Foundations.SAT.PcpAlgebra
public import MIPRE.Foundations.SAT.PcpBlocks
public import MIPRE.Foundations.SAT.QuotientField
public import MIPRE.Foundations.LowDegree.Anticomm
public import MIPRE.Foundations.LowDegree.Shoup
public import MIPRE.Foundations.LowDegree.SelfDual
public import MIPRE.Foundations.CL.Canonical
public import MIPRE.Foundations.CL.Closure
public import MIPRE.Foundations.CL.Downsize
public import MIPRE.Foundations.CL.Repeat
public import MIPRE.Foundations.ClassMIPStarComputable
public import MIPRE.Foundations.ClassMIPStarTab
public import MIPRE.Foundations.Compression
public import MIPRE.Foundations.Cost.Kleene
public import MIPRE.Foundations.Cost.Semidecide
public import MIPRE.Foundations.Cost.Toolkit
public import MIPRE.Foundations.Cost.Universal
public import MIPRE.Foundations.Games
public import MIPRE.Foundations.StateDistance
public import MIPRE.Foundations.PerfectStrategy
public import MIPRE.Foundations.OracularComplete
public import MIPRE.Foundations.OracularSound
public import MIPRE.Foundations.OracularTensor
public import MIPRE.Foundations.OracularTyped
public import MIPRE.Foundations.OracularSampler
public import MIPRE.Foundations.OracularDecider
public import MIPRE.Foundations.OracularDeciderCost
public import MIPRE.Foundations.Pipeline.Oracularization
public import MIPRE.Foundations.LowDegree.SelfDualize
public import MIPRE.Foundations.LowDegree.NormalBasis
public import MIPRE.Foundations.SAT.AdmissibleField
public import MIPRE.Foundations.Halting.Corollaries
public import MIPRE.Foundations.Pipeline.Compress
public import MIPRE.Foundations.Halting.LambdaBound
public import MIPRE.Foundations.Halting.Semidecider
public import MIPRE.Foundations.Halting.Paper.Main
public import MIPRE.Foundations.Halting.Paper.ClassMain
public import MIPRE.Foundations.ValueApprox
public import MIPRE.Foundations.ValueApprox.Cayley
public import MIPRE.Foundations.ValueApprox.Dense
public import MIPRE.Foundations.ValueApprox.Gaussian
public import MIPRE.Foundations.ValueApprox.Norms
public import MIPRE.Foundations.ValueApprox.Projective
public import MIPRE.Foundations.ValueApprox.RE
public import MIPRE.Foundations.ValueApprox.RawComplete
public import MIPRE.Foundations.ValueApprox.RawPrimrec
public import MIPRE.Foundations.ValueApprox.RawSemantics
public import MIPRE.Foundations.ValueApprox.RawStrategy
public import MIPRE.Foundations.ValueApprox.Strategy
public import MIPRE.TM.CookLevin.DecoupledProg
public import MIPRE.TM.CookLevin.PaddingParams
public import MIPRE.TM.CookLevin.PcpParameters
public import MIPRE.LCS.MagicSquare.Strategy
public import MIPRE.LCS.NonlocalGame
public import MIPRE.LCS.Strategy.Equivalence
public import MIPRE.LCS.Strategy.ObservableToProjector
public import MIPRE.TM.Code.Encoding.MachineCode
public import MIPRE.Foundations.WeylBinary
public import MIPRE.Foundations.Commutation
public import MIPRE.Foundations.Linearity
public import MIPRE.Foundations.Sandwich
public import MIPRE.Foundations.Pasting
public import MIPRE.Foundations.LowDegreeSandwich
public import MIPRE.Background.LIDT.Extraction
public import MIPRE.Background.LIDT.Padding
public import MIPRE.Background.LIDT.Simultaneous
public import MIPRE.Background.AnswerReduction.ArSampler
public import MIPRE.Background.AnswerReduction.ArDecider
public import MIPRE.Background.AnswerReduction.Construction
public import MIPRE.Background.AnswerReduction.Complete
public import MIPRE.Background.AnswerReduction.SoundFinal
public import MIPRE.Background.AnswerReduction.Instance
public import MIPRE.MainTheorem
public import MIPRE.Foundations.Tsirelson.Conditional
public import MIPRE.Tsirelson
public import MIPRE.MIPCo
public import MIPRE.Background.Orthonormalization.FinitePairOrtho
public import MIPRE.Background.Orthonormalization.DyadicOrtho
public import MIPRE.Background.LIDT.Co.CommutativityPoints.BridgeTheorems.DropBridges
public import MIPRE.Background.LIDT.Co.CommutativityPoints.AnswerTheorems
public import MIPRE.Background.LIDT.Co.Doubling.Orthonormalization
public import MIPRE.Background.LIDT.Co.Doubling.Sdp
public import MIPRE.Background.LIDT.Co.Doubling.Strategy
public import MIPRE.Background.LIDT.Co.Preliminaries.SwitchSandwichMain.Completeness
public import MIPRE.Background.LIDT.Co.Preliminaries.SelfConsistency.DataProcessing
public import MIPRE.Background.LIDT.Co.Preliminaries.CompletionTransfer
public import MIPRE.Background.LIDT.Co.ExpansionHypercubeGraph.Theorems.Results
public import MIPRE.Background.LIDT.Co.Test.SchwartzZippelStep
public import MIPRE.Background.LIDT.Co.GlobalVariance.Theorems.MainTheorems
public import MIPRE.Background.LIDT.Co.Commutativity.Main.Results
public import MIPRE.Background.LIDT.Co.MakingMeasurementsProjective.Orthonormalization
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Results.SelfImprovementTop.Core
public import MIPRE.Background.LIDT.Co.Pasting.Bernoulli.Final
public import MIPRE.Foundations.Expanded
public import MIPRE.Foundations.WeylEPR
public import MIPRE.Foundations.Swap
public import MIPRE.Background.GowersHatami.Basic
public import MIPRE.Foundations.CommutingDilation
public import MIPRE.Tailored.Game
public import MIPRE.Tailored.MagicSquare
public import MIPRE.Tailored.OfTNFV
public import MIPRE.Background.Tailored.Repetition.Soundness
public import MIPRE.Background.Tailored.Repetition.Stage
public import MIPRE.Tailored.Halting.Main
public import MIPRE.Tailored.Class
public import MIPRE.Tailored.Intro.Closure
public import MIPRE.Tailored.Intro.Transport
public import MIPRE.Tailored.Intro.Input
public import MIPRE.Tailored.Intro.Binary
public import MIPRE.Tailored.Detyping
public import MIPRE.Tailored.Intro.Layout
public import MIPRE.Tailored.Intro.Source
public import MIPRE.Tailored.Intro.Presentation
public import MIPRE.Background.Tailored.Intro.Pauli
public import MIPRE.Tailored.CanonicalCost
public import MIPRE.Tailored.ClassVerifier
public import MIPRE.Tailored.Intro.SourceCons
public import MIPRE.Tailored.Intro.RegCons
public import MIPRE.Background.Tailored.Intro.PauliConsKernel
public import MIPRE.Tailored.OfTNFVT
public import MIPRE.Background.Tailored.Intro.Typed
public import MIPRE.Background.Tailored.Intro.Complete
public import MIPRE.Background.Tailored.Intro.Output
public import MIPRE.Tailored.Intro.KerGensProg

@[expose] public section

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

-- blueprint `cor:halting-consequences`: the chapter-7 consequences, from compression
#guard_sorry_free MIPRE.Halting.halting_reduction_quantum_of,
  MIPRE.Halting.gameValue_uncomputable_of,
  MIPRE.Halting.quantumValue_uncomputable_of,
  MIPRE.Halting.mipstarComputable_eq_re_of,
  MIPRE.Halting.re_subset_mipstarComputable_of

-- blueprint `thm:halting-undecidable`
#guard_sorry_free MIPRE.Halting.exists_code_halts_of_isRE,
  MIPRE.halting_re,
  MIPRE.halting_undecidable

-- blueprint `thm:mipstar-eq-re`
#guard_sorry_free MIPRE.Halting.exists_code_halts_of_isRE,
  MIPRE.Halting.re_subset_mipclass_of_reduction,
  MIPRE.Halting.mipclass_eq_re_of_reduction

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
  MIPRE.Halting.prepProg_runs,
  MIPRE.Halting.prep,
  MIPRE.Halting.body,
  MIPRE.Halting.F,
  MIPRE.Halting.dec,
  MIPRE.Halting.Vhalt,
  MIPRE.Halting.body_runs_iff,
  MIPRE.Halting.dec_runs_iff

-- blueprint `lem:halting-semidecider`
#guard_sorry_free MIPRE.Halting.exists_sem_of_tab,
  MIPRE.Halting.exists_sem_lower,
  MIPRE.Halting.exists_sem_upper,
  MIPRE.REPred.or,
  MIPRE.Verifier.LongAcceptance,
  MIPRE.Verifier.longAcceptanceB,
  MIPRE.Verifier.longAcceptanceB_iff,
  MIPRE.Verifier.not_rejectsLong_iff_exists,
  MIPRE.Verifier.rePred_not_rejectsLong

-- blueprint `lem:kleene`
#guard_sorry_free MIPRE.Cost.efficient_fixed_point, MIPRE.Cost.kleeneFix,
  MIPRE.Cost.kleeneFix_runs_of

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
  MIPRE.Halting.lamOf_ge,
  MIPRE.Halting.exists_lamBound,
  MIPRE.Halting.Lam0,
  MIPRE.Halting.Lam0_spec,
  MIPRE.Halting.esize_dec,
  MIPRE.Halting.dec_cost,
  MIPRE.Halting.exists_dec_cost_poly,
  MIPRE.Halting.decCostPoly,
  MIPRE.Halting.dec_cost_spec,
  MIPRE.Halting.Vhalt_decider_cost,
  MIPRE.Halting.wrapCoreCost_le_WZ,
  MIPRE.Halting.lamF,
  MIPRE.Halting.lamz

-- blueprint `lem:dhalt-values`
#guard_sorry_free MIPRE.Halting.CompressorSpec.toObligations,
  MIPRE.Halting.comprStr_accepts,
  MIPRE.Halting.haltProg_accepts_iff,
  MIPRE.Halting.accepts_iff,
  MIPRE.Halting.accepts_iff_W,
  MIPRE.Halting.A_of_branch1,
  MIPRE.Halting.B_of_branch2,
  MIPRE.Halting.rejectsLong_of_not_branch1,
  MIPRE.Halting.A_step,
  MIPRE.Halting.B_step

-- blueprint `thm:halting`
#guard_sorry_free MIPRE.Halting.exists_obligations,
  MIPRE.Halting.halting_reduction_lower,
  MIPRE.Halting.halting_reduction_lower_strings,
  MIPRE.Halting.halting_reduction_lower_of,
  MIPRE.Halting.halting_reduction_both_of,
  MIPRE.Halting.halting_reduces_to_gameValue_of,
  MIPRE.Halting.halting_reduction,
  MIPRE.Halting.halting_reduction_of,
  MIPRE.Halting.halting_paper,
  MIPRE.Halting.halting_paper_valStar,
  MIPRE.Halting.Vpaper,
  MIPRE.Halting.semL,
  MIPRE.Halting.hasPerfectPCC_of_halts,
  MIPRE.Halting.valStar_le_of_not_halts,
  MIPRE.Halting.classV,
  MIPRE.Halting.classV_efficient,
  MIPRE.Halting.classV_value,
  MIPRE.Halting.classV_values,
  MIPRE.Halting.sampProg,
  MIPRE.Halting.decProg,
  MIPRE.Halting.sampProg_runs,
  MIPRE.Halting.decProg_accepts,
  MIPRE.Halting.decProg_runs,
  MIPRE.GapCompression.samplerFamily

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
#guard_sorry_free MIPRE.MIPStarComputable.exists_semidecider,
  MIPRE.MIPStarComputable.isRE,
  MIPRE.MIPClass.isRE,
  MIPRE.MIPClass.exists_semidecider,
  MIPRE.ValueModel.tensor_lowerRE

/-! `lem:mipstar-poly-sub`: the paper's class is contained in the computable one
(`MIPRE/Foundations/ClassMIPStarTab.lean`). -/
#guard_sorry_free MIPRE.MIPStar.toComputable, MIPRE.MIPStar.isRE, MIPRE.PolyVerifier.tab,
  MIPRE.PolyVerifier.tab_computable, MIPRE.PolyVerifier.quantumValue_tab

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
-- tensor-product strategies, the form `Verifier.valStar` needs, with the synchronous constant —
-- the model-level `lem:oracular-soundness-model` in the tensor-product model.
#guard_sorry_free MIPRE.SeededGame.tensorSound,
  MIPRE.SeededGame.tensorSound_value_ge,
  MIPRE.SeededGame.quantumValue_ge_of_oracular

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
  MIPRE.Introspection.val_ge_of_readoutAcceptance,
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
  MIPRE.CL.Detyping.DeciderProgram.toFinite_value,
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
  MIPRE.Introspection.star_averagedBlock,
  MIPRE.Introspection.averagedBlock_nonneg,
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
-- soundness through the decoder, and the input's value from a typed strategy, in a model.
#guard_sorry_free MIPRE.AnswerReduction.MAo,
  MIPRE.AnswerReduction.MBo,
  MIPRE.AnswerReduction.decAns,
  MIPRE.AnswerReduction.pcpOf,
  MIPRE.AnswerReduction.pcpSound,
  MIPRE.AnswerReduction.one_sub_povmValue_decoded_le,
  MIPRE.AnswerReduction.val_ge_decoded,
  MIPRE.AnswerReduction.val_ge_of_typedGame

-- blueprint `lem:ar-error-assembly`: soundness of answer reduction, under `FieldLarge`, for a
-- projective strategy in a model and in `val*`, at explicit constants.
#guard_sorry_free MIPRE.AnswerReduction.arVerifier_soundness,
  MIPRE.AnswerReduction.FieldLarge,
  MIPRE.AnswerReduction.errE,
  MIPRE.AnswerReduction.errE_le,
  MIPRE.AnswerReduction.sqrt_le_delta,
  MIPRE.AnswerReduction.exists_threshold_clB,
  MIPRE.AnswerReduction.z_le,
  MIPRE.AnswerReduction.soundA,
  MIPRE.AnswerReduction.soundC,
  MIPRE.AnswerReduction.one_le_delta_of_trivial,
  MIPRE.AnswerReduction.val_ge_of_arStrategy,
  MIPRE.AnswerReduction.arVerifier_soundness_tensor

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
  MIPRE.Halting.mipstarComputable_eq_re,
  MIPRE.Halting.re_subset_mipstarComputable,
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
  MIPRE.Introspection.mirror_expand,
  MIPRE.Introspection.reg_wX_mirror,
  MIPRE.Introspection.reg_readout_mirror,
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

#guard_sorry_free MIPRE.Introspection.qform_πA_expandA,
  MIPRE.Introspection.stateSqNorm_expandA_diagonal,
  MIPRE.Introspection.dilated_pvm_distance,
  MIPRE.Introspection.conditionalDilationOp_isPVM,
  MIPRE.Introspection.conditionalDilationOp_compress,
  MIPRE.Introspection.conditionalDilationOp_born,
  MIPRE.Introspection.regExchange,
  MIPRE.Introspection.regExchange_W_ψ,
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
  MIPRE.Introspection.TypedEstimates.introBobZError,
  MIPRE.Introspection.TypedEstimates.introAliceZError,
  MIPRE.Introspection.TypedEstimates.exists_intro_successor

#guard_sorry_free MIPRE.Introspection.adaptiveStageBudget_mono_depth,
  MIPRE.Introspection.adaptiveFailureBudget_nonneg,
  MIPRE.Introspection.adaptiveSmallThreshold_pos,
  MIPRE.Introspection.adaptiveFailureBudget_le_threshold,
  MIPRE.Introspection.adaptiveStageBudget_le_one_of_threshold

#guard_sorry_free MIPRE.Introspection.TypedEstimates.exists_intro_iteration

#print axioms MIPRE.Introspection.TypedEstimates.exists_intro_successor
#print axioms MIPRE.Introspection.TypedEstimates.exists_intro_iteration

#guard_sorry_free MIPRE.Introspection.terminalAuxPOVM_isPVM,
  MIPRE.Introspection.IntroPrefixInvariant.terminal_some,
  MIPRE.Introspection.IntroPrefixInvariant.terminal_none

#guard_sorry_free MIPRE.Introspection.TypedPresentation.mu_swap,
  MIPRE.Introspection.TypedEstimates.parsedGame_transpose,
  MIPRE.Introspection.TypedEstimates.swap_reg_bornProb,
  MIPRE.Introspection.TypedEstimates.swap_reg_povmValue,
  MIPRE.Introspection.TypedEstimates.swap_reg_stateSqNorm,
  MIPRE.Introspection.TypedEstimates.swap_reg_swap_stateSqNorm,
  MIPRE.Introspection.TypedEstimates.swap_reg_xSqNorm,
  MIPRE.Introspection.TypedEstimates.parsedGame_value_swap,
  MIPRE.Introspection.TypedEstimates.introBobZError_swap,
  MIPRE.Introspection.TypedEstimates.introAliceZError_swap,
  MIPRE.Introspection.TypedEstimates.hidingAliceError_swap,
  MIPRE.Introspection.TypedEstimates.hidingBobError_swap,
  MIPRE.Introspection.TypedEstimates.exists_intro_bob_iteration

#guard_sorry_free MIPRE.Introspection.adaptiveFailureBudget_add,
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

#guard_sorry_free MIPRE.Introspection.transportA_map_op,
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
  MIPRE.Introspection.SourcePadding.restrictStrategy_value,
  MIPRE.Introspection.SourcePadding.exists_projStrat_value_ge,
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
  MIPRE.Introspection.DecisionCompiler.val_reference,
  MIPRE.Introspection.DecisionCompiler.output_val_cutoff,
  MIPRE.Introspection.DecisionCompiler.output_val_eq_reference,
  MIPRE.Introspection.CanonicalDecoded.value_le,
  MIPRE.Introspection.CanonicalDecoded.supported_A,
  MIPRE.Introspection.CanonicalDecoded.supported_B

#guard_sorry_free MIPRE.Introspection.exists_seven,
  MIPRE.Introspection.seven,
  MIPRE.Introspection.CanonicalComplete.output_hasPerfectPCC,
  MIPRE.Introspection.CompiledSoundness.output_soundness,
  MIPRE.Introspection.sevenConstant,
  MIPRE.Introspection.sevenConstant_spec,
  MIPRE.Introspection.one_le_sevenConstant,
  MIPRE.Introspection.sevenC,
  MIPRE.Introspection.sevenC_spec,
  MIPRE.Introspection.sevenOutput_soundness

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
  MIPRE.Halting.re_subset_mipstarComputable_of_answerReduction,
  MIPRE.Halting.mipstarComputable_eq_re_of_answerReduction

/-! `lem:correlation-sets-basic` and `lem:tsirelson-conditional`: the correlation sets and the
separation from an upper semidecider (`MIPRE/Foundations/Correlations.lean`,
`MIPRE/Foundations/Tsirelson/Conditional.lean`). -/
#guard_sorry_free MIPRE.CommutingOperatorStrategy.correlation_nonneg,
  MIPRE.CommutingOperatorStrategy.correlation_sum,
  MIPRE.commutingOperatorValue_nonneg,
  MIPRE.commutingOperatorValue_le_one,
  MIPRE.TensorProductStrategy.correlation_toCommuting,
  MIPRE.Cq_subset_Cqc,
  MIPRE.quantumValue_le_commutingOperatorValue,
  MIPRE.payoff_le_quantumValue_of_mem_Cqa,
  MIPRE.payoff_le_commutingOperatorValue_of_mem_Cqc,
  MIPRE.Cqa_subset_Cqc_of_isClosed,
  MIPRE.HaltingReductionQuantum,
  MIPRE.exists_quantumValue_lt_commutingOperatorValue,
  MIPRE.exists_mem_Cqc_not_mem_Cqa,
  MIPRE.exists_Cqa_ne_Cqc,
  MIPRE.tsirelson_of_upperRE_of_isClosed

/-! The Positivstellensatz route to `cor:tsirelson`: `lem:cone-archimedean`,
`lem:cone-state-gns`, `lem:cqc-compact`, `thm:nc-positivstellensatz`, `lem:sos-certificates`,
`lem:valco-upper-re` and `cor:tsirelson` (`MIPRE/Foundations/NCPoly/`,
`MIPRE/Foundations/GNS.lean`, `MIPRE/Foundations/Tsirelson/`, `MIPRE/Tsirelson.lean`). -/
#guard_sorry_free MIPRE.NCPoly.star_mul_mul_mem_qmod_of_mem,
  MIPRE.NCPoly.archimedean_of_gen,
  MIPRE.Tsirelson.cone_archimedean,
  MIPRE.NCPoly.re_inner_eval_nonneg,
  MIPRE.Tsirelson.strategy_nonneg,
  MIPRE.Tsirelson.value_le_of_mem,
  MIPRE.Tsirelson.isConeState_stateOf,
  MIPRE.GNS.GenData.strategy,
  MIPRE.GNS.GenData.strategy_correlation,
  MIPRE.Tsirelson.stateStrategy,
  MIPRE.Tsirelson.stateStrategy_correlation,
  MIPRE.Tsirelson.stateStrategy_value,
  MIPRE.Tsirelson.mem_Cqc_iff,
  MIPRE.Tsirelson.stateSpace,
  MIPRE.Tsirelson.isCompact_stateSpace,
  MIPRE.Tsirelson.image_correlationOf_stateSpace,
  MIPRE.isCompact_Cqc,
  MIPRE.isClosed_Cqc,
  MIPRE.Cqa_subset_Cqc,
  MIPRE.exists_separating_functional_of_archimedean,
  MIPRE.Tsirelson.exists_isConeState_of_not_mem,
  MIPRE.Tsirelson.sub_gamePoly_mem_cone_of_lt,
  MIPRE.Tsirelson.commutingOperatorValue_lt_iff,
  MIPRE.Tsirelson.Dominant,
  MIPRE.Tsirelson.re_inner_eval_ge,
  MIPRE.Tsirelson.commutingOperatorValue_lt_of_certificate,
  MIPRE.Tsirelson.exists_certificate_of_lt,
  MIPRE.Tsirelson.exists_certificate_iff,
  MIPRE.commutingUpperRE,
  MIPRE.Tsirelson.Coded.CheckUpper,
  MIPRE.Tsirelson.Coded.primrecRel_checkUpper,
  MIPRE.Tsirelson.checkUpper_iff,
  MIPRE.tsirelson,
  MIPRE.tsirelson_of_haltingReduction,
  MIPRE.tsirelson_of_upperRE

/-! `thm:separation`: the explicit separation through the recursion theorem
(`MIPRE/Foundations/Tsirelson/Separation.lean`, `MIPRE/Tsirelson.lean`). -/
#guard_sorry_free
  MIPRE.separation,
  MIPRE.separation_of_upperRE,
  MIPRE.exists_quantumValue_le_half_commutingOperatorValue_eq_one,
  MIPRE.exists_mem_Cqc_payoff_eq_commutingOperatorValue

/-! The commuting-operator track (`planning/mipco-track.md`, Phase 0):
`lem:compressible-criterion-nested`, `lem:mipco-sub-core`, `thm:halting-co` and
`thm:mipco-eq-core`, the last two from a gap compression sound in `ValueModel.commuting`
(`MIPRE.GapCompression.Sound`), which `MIPRE.gapCompressionCo_sound` provides
(`thm:mipco-eq-core-unconditional`, below). The reduction and the classes are generic in a value model
(`MIPRE/Foundations/ValueModel.lean`, the `Halting/` modules and `Foundations/ClassMIPStarComputable.lean`);
the commuting-operator instances are `MIPRE/Foundations/ClassMIPCo.lean` and
`MIPRE/MIPCo.lean`. -/
#guard_sorry_free MIPRE.Cost.compressibility_criterion_nested

#guard_sorry_free MIPRE.MIPCo.isCoRE,
  MIPRE.MIPCo.exists_cosemidecider,
  MIPRE.MIPClass.isCoRE,
  MIPRE.MIPClass.exists_cosemidecider,
  MIPRE.ValueModel.commuting_upperRE

#guard_sorry_free MIPRE.Halting.halting_reduction_upper,
  MIPRE.Halting.halting_reduction_upper_strings,
  MIPRE.Halting.halting_reduction_upper_of,
  MIPRE.Halting.halting_reduction_commuting_of,
  MIPRE.Halting.classOne,
  MIPRE.Halting.classA_subset_classOne,
  MIPRE.Halting.val_tab_eq_one_of_mem_classOne

#guard_sorry_free MIPRE.Halting.mipco_eq_core_of,
  MIPRE.Halting.core_subset_mipco_of,
  MIPRE.Halting.core_subset_mipclass_of_reduction,
  MIPRE.Halting.mipclass_eq_core_of_reduction

/-! The commuting-operator track, Phase 1(a) (`planning/mipco-track.md` §5): the
commutation-preserving dilation, `lem:co-dilation`, and the attainment of `ω_co` on projective
strategies, `thm:co-value-projective` (`MIPRE/Foundations/OperatorMatrix.lean`,
`MIPRE/Foundations/HalmosDilation.lean`, `MIPRE/Foundations/CommutingDilation.lean`). -/
#guard_sorry_free MIPRE.OperatorMatrix.toCLMStarAlgHom,
  MIPRE.OperatorMatrix.amplify,
  MIPRE.OperatorMatrix.emb,
  MIPRE.OperatorMatrix.inner_emb_toCLM_emb,
  MIPRE.OperatorMatrix.toCLM_diagonal_emb,
  MIPRE.Halmos.extension,
  MIPRE.Halmos.conjTranspose_mul_extension,
  MIPRE.Halmos.extension_mul_conjTranspose,
  MIPRE.Halmos.naimark,
  MIPRE.Halmos.naimark_mul_conjTranspose_mul,
  MIPRE.Halmos.proj,
  MIPRE.Halmos.isStarProjection_proj,
  MIPRE.Halmos.sum_proj,
  MIPRE.Halmos.proj_naimark_inl_inl,
  MIPRE.Halmos.commute_diagonal_proj_naimark,
  MIPRE.CommutingOperatorStrategy.dilateLeft,
  MIPRE.CommutingOperatorStrategy.correlation_dilateLeft,
  MIPRE.CommutingOperatorStrategy.swap,
  MIPRE.CommutingOperatorStrategy.correlation_swap,
  MIPRE.CommutingOperatorStrategy.dilateRight,
  MIPRE.CommutingOperatorStrategy.correlation_dilateRight

#guard_sorry_free MIPRE.CommutingOperatorStrategy.exists_isProjective_correlation_eq,
  MIPRE.CommutingOperatorStrategy.exists_isProjective_value_eq,
  MIPRE.commutingOperatorValue_eq_iSup_isProjective,
  MIPRE.exists_isProjective_lt_value,
  MIPRE.TensorProductStrategy.isProjective_toCommuting

/-! The commuting-operator track, Phase 1(b) and (c) (`planning/mipco-track.md` §5): the
commuting-operator value as a supremum of model values, `lem:co-value-model`
(`MIPRE/Foundations/POVMValue.lean`); the ancilla extension of a bipartite model,
`lem:ancilla-extension` (`MIPRE/Foundations/AncillaModel.lean`); the soundness chain of
compression in a value model, `lem:compress-sound-in`, and its composition,
`thm:pipeline-sound-in` (`MIPRE/Foundations/Pipeline/Compress.lean`); and `MIP^co = coRE` from
the three stages' clauses, `cor:mipco-from-stages` (`MIPRE/MIPCo.lean`). -/
#guard_sorry_free MIPRE.CommutingOperatorStrategy.aliceMeas,
  MIPRE.CommutingOperatorStrategy.bobMeas,
  MIPRE.CommutingOperatorStrategy.aliceMeas_op,
  MIPRE.CommutingOperatorStrategy.bobMeas_op,
  MIPRE.CommutingOperatorStrategy.correlation_eq_bornProb,
  MIPRE.CommutingOperatorStrategy.value_eq_povmValue,
  MIPRE.commutingOperatorValue_eq_iSup_povmValue

#guard_sorry_free MIPRE.BipartiteModel.bornProb_expand_smulKron,
  MIPRE.BipartiteModel.stateSqNorm_expand_smulKron_one,
  MIPRE.BipartiteModel.swap_stateSqNorm_expand_smulKron_one,
  MIPRE.BipartiteModel.norm_expand_state,
  MIPRE.IsPVMIn.smulKron

#guard_sorry_free MIPRE.Pipeline.output_val_le,
  MIPRE.GapCompression.ofPipeline_sound,
  MIPRE.mipco_eq_core_of_stages,
  MIPRE.gapCompressionCo

/-! The commuting-operator track, Phase 2 (`planning/mipco-track.md` §5): strategies in a model
read in `ω_co`, `lem:model-strategy-co` (`MIPRE/Foundations/CommutingModel.lean`); the
repetition bound in `ω_co` and parallel repetition sound there, `lem:repetition-sound-bound-co`
and `thm:parallel-repetition-co` (`MIPRE/Background/Repetition/Soundness.lean`, `Verifier.lean`,
`VerifierCo.lean`, `MIPRE/Foundations/Pipeline/Repetition.lean`); oracularization in a bipartite model and in
`ω_co`, `lem:oracular-soundness-model` and `lem:oracular-soundness-co`
(`MIPRE/Foundations/OracularModel.lean`); post-processing and detyping in a model,
`lem:transports-model` (`MIPRE/Foundations/OracularModel.lean`,
`MIPRE/Foundations/CL/DetypingModel.lean`); and oracularization sound in both value models,
`thm:oracularization-in-model` (`MIPRE/Foundations/OracularValue.lean`,
`MIPRE/Foundations/Pipeline/Oracularization.lean`). -/
#guard_sorry_free MIPRE.BipartiteModel.toCommuting,
  MIPRE.BipartiteModel.correlation_toCommuting,
  MIPRE.BipartiteModel.value_toCommuting,
  MIPRE.BipartiteModel.povmValue_le_commutingOperatorValue,
  MIPRE.IsPVMIn.of_map,
  MIPRE.IsPVMIn.of_isStarProjection,
  MIPRE.CommutingOperatorStrategy.isPVMIn_aliceMeas,
  MIPRE.CommutingOperatorStrategy.isPVMIn_bobMeas,
  MIPRE.exists_isPVMIn_lt_povmValue

#guard_sorry_free MIPRE.Repetition.exp_le_soundBound,
  MIPRE.Repetition.repConstCo,
  MIPRE.Repetition.commutingOperatorValue_repeat_le_soundBound,
  MIPRE.Repetition.GameSoundIn,
  MIPRE.Repetition.GameSoundIn.mono,
  MIPRE.Repetition.gameSoundIn_tensor,
  MIPRE.Repetition.gameSoundIn_commuting

#guard_sorry_free MIPRE.val_repVerifier,
  MIPRE.val_repVerifier_le,
  MIPRE.Repetition.soundBound_anti,
  MIPRE.Repetition.withConst,
  MIPRE.Repetition.SoundIn.withConst,
  MIPRE.repetition_withConst_soundIn,
  MIPRE.Repetition.repConstBoth,
  MIPRE.repetitionCo,
  MIPRE.repetitionCo_soundIn_commuting

#guard_sorry_free MIPRE.SeededGame.povmValue_sound_ge,
  MIPRE.StateModel.sum_snorm_sq_ge_of_close,
  MIPRE.StateModel.sum_snorm_sq_eq_one_of_isPVMIn,
  MIPRE.BipartiteModel.sum_snorm_sq_chain,
  MIPRE.SeededGame.oracleView,
  MIPRE.SeededGame.isPVMIn_oracleJoint,
  MIPRE.SeededGame.sum_snorm_sq_joint_le,
  MIPRE.SeededGame.condWin_oracle_le,
  MIPRE.SeededGame.condWin_sound_ge,
  MIPRE.SeededGame.sum_condFail_four_le,
  MIPRE.SeededGame.commutingOperatorValue_ge_of_oracular

#guard_sorry_free MIPRE.BipartiteModel.povmValue_le_postprocess,
  MIPRE.quantumValue_le_postprocess,
  MIPRE.commutingOperatorValue_le_postprocess,
  MIPRE.SampledGame.one_sub_povmValue,
  MIPRE.CL.Detyping.restrict_condFail_eq,
  MIPRE.CL.Detyping.typed_failure_povm,
  MIPRE.CL.Detyping.failure_povm,
  MIPRE.CL.Detyping.restrict_failure_eq_povm,
  MIPRE.CL.Detyping.restrict_failure_le_povm,
  MIPRE.CL.Detyping.restrict_povmValue_ge,
  MIPRE.one_sub_mul_one_sub_iSup_le,
  MIPRE.CL.Detyping.quantumValue_typedGame_ge,
  MIPRE.CL.Detyping.commutingOperatorValue_typedGame_ge

#guard_sorry_free MIPRE.ValueModel.tensor_oracularSound,
  MIPRE.ValueModel.commuting_oracularSound,
  MIPRE.ValueModel.OracularSound.typedGame_ge_ambient,
  MIPRE.SeededGame.val_typedGame_le,
  MIPRE.Verifier.val_ge_of_typed,
  MIPRE.Oracularization.typed_soundness_val,
  MIPRE.Oracularization.detyped_soundness_val

/-! The commuting-operator track, Phase 3 (`planning/mipco-track.md` §5): projective strategies in
a bipartite model and their operations, `lem:model-proj-strategy`, and their reading in the two
models, `lem:model-proj-strategy-values` (`MIPRE/Foundations/ModelStrategy.lean`); the seeded CL
test sound in the tensor-product model, `lem:lidt-sound-in-tensor`
(`MIPRE/Background/LIDT/ModelSoundness.lean`); and answer reduction sound in `ω_co` given that
test's soundness in the commuting-operator model, `thm:ar-sound-co`
(`MIPRE/Background/AnswerReduction/SoundFinal.lean`, `Instance.lean`). The answer-reduction
chain itself is restated in a model under its existing guards. -/
#guard_sorry_free MIPRE.BipartiteModel.ProjStrat.failAt_nonneg,
  MIPRE.BipartiteModel.ProjStrat.failAt_le_one,
  MIPRE.BipartiteModel.ProjStrat.one_sub_value_eq_sum_failAt,
  MIPRE.BipartiteModel.ProjStrat.value_le_one,
  MIPRE.BipartiteModel.ProjStrat.value_nonneg,
  MIPRE.BipartiteModel.ProjStrat.failAt_adapt_le,
  MIPRE.BipartiteModel.ProjStrat.value_relabel,
  MIPRE.BipartiteModel.povmValue_congr_game,
  MIPRE.POVMIn.map_map,
  MIPRE.POVMIn.map_id,
  MIPRE.BipartiteModel.inconsistency_eq_sum_dis,
  MIPRE.BipartiteModel.inconsistency_uniform,
  MIPRE.BipartiteModel.sum_dis_le_of_inconsistency,
  MIPRE.BipartiteModel.inconsistency_uniform_unit,
  MIPRE.POVMIn.toPOVM_toIn,
  MIPRE.POVM.toIn_map

#guard_sorry_free MIPRE.TensorProductStrategy.toModel,
  MIPRE.TensorProductStrategy.value_toModel,
  MIPRE.TensorProductStrategy.failAt_toModel,
  MIPRE.star_dotProduct_self_eq_one,
  MIPRE.BipartiteModel.ProjStrat.toTensor,
  MIPRE.BipartiteModel.ProjStrat.value_toTensor,
  MIPRE.BipartiteModel.ProjStrat.value_le_commutingOperatorValue,
  MIPRE.exists_projStrat_lt_commutingOperatorValue,
  MIPRE.ValueModel.tensor_dominates,
  MIPRE.ValueModel.commuting_dominates,
  MIPRE.inconsistency_eq_tensor

#guard_sorry_free MIPRE.LIDT.Simul.soundIn_tensor,
  MIPRE.LIDT.Simul.tuplePOVMA_toTensor,
  MIPRE.LIDT.Simul.tuplePOVMB_toTensor,
  MIPRE.LIDT.Simul.evalTuplePOVM_toIn

#guard_sorry_free MIPRE.AnswerReduction.arVerifier_soundness_commuting,
  MIPRE.AnswerReduction.answerReduction_soundIn_commuting,
  MIPRE.AnswerReduction.arVerifier_soundness_of_approx,
  MIPRE.AnswerReduction.answerReduction_soundIn_of_approx, MIPRE.LIDT.Simul.approxSoundIn_commuting

/-! The commuting-operator track, Phase 4 (`planning/mipco-track.md` §5): local isometries of
bipartite models, `lem:local-isometry` (`MIPRE/Foundations/LocalIsometry.lean`); moving registers
along them, `lem:ancilla-isometries` (`MIPRE/Foundations/AncillaIsometry.lean`); the register
model, `lem:register-model` (`MIPRE/Foundations/Introspection/RegisterModel.lean`); the ancilla
extension of a tensor-product model, `lem:tensor-expand` (`MIPRE/Foundations/TensorExpand.lean`);
the one-sided ancilla extension, `lem:one-sided-extension`
(`MIPRE/Foundations/AncillaDilation.lean`); the projective dilation in a star-ordered ring,
`lem:kraus-dilation` (`MIPRE/Foundations/KrausDilation.lean`); domination of POVM strategies and
approximation by projective ones, `lem:povm-domination` (`MIPRE/Foundations/POVMDomination.lean`,
`MIPRE/Foundations/Introspection/SourcePaddingValue.lean`); reductions of POVM strategies,
`lem:povm-reduction` (`MIPRE/Foundations/POVMReduction.lean`, `MIPRE/Foundations/ModelOver.lean`);
the Pauli basis test sound in the tensor-product model, `lem:qld-sound-in-tensor`
(`MIPRE/Background/QLD/Soundness.lean` since Phase 5, as the tensor-product instance of `thm:qld`,
with the definitions in `MIPRE/Background/QLD/ModelSoundness.lean`); and introspection sound in
every value model where that test is, `thm:intro-sound-co`
(`MIPRE/Background/Introspection/Compiler.lean`). The introspection analysis itself is restated in
a model under its existing guards. -/
#guard_sorry_free MIPRE.BipartiteModel.LocalIsometry.intertwine,
  MIPRE.BipartiteModel.LocalIsometry.bornProb_withState,
  MIPRE.BipartiteModel.LocalIsometry.stateSqNorm_withState,
  MIPRE.BipartiteModel.LocalIsometry.bornProb_of_W_ψ,
  MIPRE.BipartiteModel.LocalIsometry.stateSqNorm_of_W_ψ,
  MIPRE.BipartiteModel.LocalIsometry.swap_stateSqNorm_of_W_ψ,
  MIPRE.BipartiteModel.LocalIsometry.xSqNorm_of_W_ψ,
  MIPRE.BipartiteModel.LocalIsometry.comp_W_ψ,
  MIPRE.BipartiteModel.LocalIsometry.isPVMIn_transportA,
  MIPRE.BipartiteModel.LocalIsometry.isPVMIn_transportB,
  MIPRE.BipartiteModel.LocalIsometry.intertwine_transportOpA,
  MIPRE.BipartiteModel.LocalIsometry.povmValue_transport,
  MIPRE.BipartiteModel.LocalIsometry.povmValue_pushforward

#guard_sorry_free MIPRE.BipartiteModel.inert,
  MIPRE.BipartiteModel.inert_W_ψ,
  MIPRE.BipartiteModel.relabel,
  MIPRE.BipartiteModel.relabel_W_ψ,
  MIPRE.BipartiteModel.assoc,
  MIPRE.BipartiteModel.assoc_W_ψ,
  MIPRE.BipartiteModel.swapExpand,
  MIPRE.BipartiteModel.swapExpand_W_ψ,
  MIPRE.BipartiteModel.expand_π_πA_apply,
  MIPRE.BipartiteModel.expand_π_πB_apply

#guard_sorry_free MIPRE.BipartiteModel.norm_reg_ψ,
  MIPRE.BipartiteModel.reg_mirror,
  MIPRE.BipartiteModel.reg_mirror_smulKron,
  MIPRE.BipartiteModel.regRelabel_W_ψ,
  MIPRE.BipartiteModel.regSplit_W_ψ,
  MIPRE.BipartiteModel.regExtend_W_ψ,
  MIPRE.BipartiteModel.regSwap_W_ψ,
  MIPRE.Introspection.registerEPR_equiv,
  MIPRE.Introspection.registerEPR_prod

#guard_sorry_free MIPRE.BipartiteModel.tensorExpand,
  MIPRE.BipartiteModel.tensorExpand_W_ψ,
  MIPRE.BipartiteModel.tensorUnexpand,
  MIPRE.BipartiteModel.tensorUnexpand_W_ψ,
  MIPRE.BipartiteModel.tensorUnexpand_ΦA,
  MIPRE.BipartiteModel.tensorUnexpand_ΦB,
  MIPRE.BipartiteModel.tensorIsometry,
  MIPRE.BipartiteModel.tensorIsometry_W,
  MIPRE.BipartiteModel.compSymmHom,
  MIPRE.BipartiteModel.compSymmHom_kronecker_one

#guard_sorry_free MIPRE.BipartiteModel.norm_expandA_ψ,
  MIPRE.BipartiteModel.qform_expandA,
  MIPRE.BipartiteModel.bornProb_expandA,
  MIPRE.BipartiteModel.stateSqNorm_expandA,
  MIPRE.BipartiteModel.inertA_W_ψ,
  MIPRE.BipartiteModel.LocalIsometry.expand_W_ψ,
  MIPRE.BipartiteModel.LocalIsometry.expandA_W_ψ,
  MIPRE.BipartiteModel.exchange_W_ψ

#guard_sorry_free MIPRE.exists_sum_star_mul_self,
  MIPRE.sum_star_mul_self_pad,
  MIPRE.Halmos.isPVMIn_proj,
  MIPRE.DilationAncilla,
  MIPRE.exists_pvm_dilation_ge,
  MIPRE.exists_pvm_dilation

#guard_sorry_free MIPRE.ValueModel.DominatesPOVM.dominates,
  MIPRE.ValueModel.tensor_dominatesPOVM,
  MIPRE.ValueModel.commuting_dominatesPOVM,
  MIPRE.ValueModel.tensor_projApprox,
  MIPRE.ValueModel.commuting_projApprox,
  MIPRE.povmValue_le_quantumValue

#guard_sorry_free MIPRE.BipartiteModel.POVMReduces.refl,
  MIPRE.BipartiteModel.POVMReduces.trans,
  MIPRE.BipartiteModel.POVMReduces.swap,
  MIPRE.BipartiteModel.LocalIsometry.povmReduces,
  MIPRE.BipartiteModel.povmReduces_expandA,
  MIPRE.BipartiteModel.povmReduces_expandB,
  MIPRE.BipartiteModel.povmValue_swap_game,
  MIPRE.ValueModel.DominatesPOVM.of_povmReduces,
  MIPRE.ModelOver.povmReduces_expandA,
  MIPRE.ModelOver.norm_expandA_ψ,
  MIPRE.POVMIn.compress_op

#guard_sorry_free MIPRE.QLD.soundIn_tensor, MIPRE.QLD.approxSoundIn_tensor,
  MIPRE.QLD.approxSoundIn_commuting, MIPRE.BipartiteModel.LocalIsometry.withStates

#guard_sorry_free MIPRE.Introspection.seven_soundIn, MIPRE.Introspection.seven_soundIn_commuting

/-! The Pauli extraction for the introspection game and the source bound from it, in a bipartite
model: `lem:intro-pauli-extraction` and `lem:intro-extracted-soundness`
(`MIPRE/Background/Introspection/RestrictedSoundness.lean`, `RestrictedProfileSoundness.lean`),
which replace the tensor-product statements of the removed `PauliExtraction.lean`. -/
#guard_sorry_free MIPRE.Introspection.RestrictedSoundness.restriction,
  MIPRE.Introspection.RestrictedSoundness.edgeCount,
  MIPRE.Introspection.RestrictedSoundness.edgeCount_one_le,
  MIPRE.Introspection.RestrictedSoundness.exists_extraction,
  MIPRE.Introspection.RestrictedSoundness.validAnswer,
  MIPRE.Introspection.RestrictedSoundness.project_validAnswer,
  MIPRE.Introspection.RestrictedSoundness.Extraction

#guard_sorry_free MIPRE.Introspection.RestrictedSoundness.quantumValue_ge_of_extraction,
  MIPRE.Introspection.RestrictedSoundness.profileCoefficient,
  MIPRE.Introspection.RestrictedSoundness.profileCoefficient_one_le

/-! The commuting-operator track, Phase 5 (`planning/mipco-track.md` §5): isomorphisms of bipartite
models and what they carry, `lem:model-iso`, and those between extensions, `lem:extension-isos`
(`MIPRE/Foundations/ModelIso.lean`); readings of an extension, `lem:model-reading`
(`MIPRE/Foundations/ModelReading.lean`); embeddings, `lem:model-embedding`
(`MIPRE/Foundations/ModelEmbedding.lean`); the seeded test moved between models,
`lem:lidt-model-transport` (`MIPRE/Background/LIDT/ModelTransport.lean`); the commutant of a matrix
amplification, `lem:ampl-commutant`, and the extension of a commuting-operator model,
`lem:co-extension` (`MIPRE/Foundations/AmplCommutant.lean`); the seeded test in those extensions,
`lem:lidt-sound-co-expand` (`MIPRE/Background/LIDT/CoExpand.lean`); scalar matrices on a register,
`lem:register-action` (`MIPRE/Foundations/EPRContraction.lean`); the state calculus and Parseval in
a model, `lem:model-state-calculus` and `lem:model-parseval`
(`MIPRE/Foundations/ModelCalculus.lean`); the Pauli basis test sound in the commuting-operator model
given the seeded test, `lem:qld-sound-co` (`MIPRE/Background/QLD/Soundness.lean`); and
`MIP^co = coRE` from the seeded test alone, `cor:mipco-from-lidt` (`MIPRE/MIPCo.lean`). The Pauli
basis analysis itself is restated in a model under the guards of
`MIPRE/Background/QLD/Axioms.lean`. -/

-- blueprint `lem:model-iso`
#guard_sorry_free MIPRE.BipartiteModel.Iso.refl_ΦA, MIPRE.BipartiteModel.Iso.refl_ΦB,
  MIPRE.BipartiteModel.Iso.symm_W, MIPRE.BipartiteModel.Iso.symm_ΦA,
  MIPRE.BipartiteModel.Iso.symm_ΦB, MIPRE.BipartiteModel.Iso.trans_W,
  MIPRE.BipartiteModel.Iso.trans_ΦA, MIPRE.BipartiteModel.Iso.trans_ΦB,
  MIPRE.BipartiteModel.Iso.swap_W, MIPRE.BipartiteModel.Iso.swap_ΦA,
  MIPRE.BipartiteModel.Iso.swap_ΦB, MIPRE.BipartiteModel.Iso.symm_symm,
  MIPRE.BipartiteModel.Iso.swap_swap, MIPRE.BipartiteModel.Iso.toLocalIsometry_W,
  MIPRE.BipartiteModel.Iso.toLocalIsometry_ΦA, MIPRE.BipartiteModel.Iso.toLocalIsometry_ΦB,
  MIPRE.BipartiteModel.Iso.toLocalIsometry_W_ψ, MIPRE.BipartiteModel.Iso.toLocalIsometry_ΦA_one,
  MIPRE.BipartiteModel.Iso.toLocalIsometry_ΦB_one, MIPRE.BipartiteModel.Iso.swap_toLocalIsometry,
  MIPRE.BipartiteModel.Iso.bornProb_eq, MIPRE.BipartiteModel.Iso.stateSqNorm_eq,
  MIPRE.BipartiteModel.Iso.swap_stateSqNorm_eq, MIPRE.BipartiteModel.Iso.xSqNorm_eq,
  MIPRE.BipartiteModel.Iso.norm_ψ_eq, MIPRE.BipartiteModel.Iso.pushA,
  MIPRE.BipartiteModel.Iso.pushA_op, MIPRE.BipartiteModel.Iso.isPVMIn_pushA,
  MIPRE.BipartiteModel.Iso.symm_pushA_pushA, MIPRE.BipartiteModel.Iso.pushA_symm_pushA,
  MIPRE.BipartiteModel.Iso.pushB, MIPRE.BipartiteModel.Iso.pushB_op,
  MIPRE.BipartiteModel.Iso.isPVMIn_pushB, MIPRE.BipartiteModel.Iso.symm_pushB_pushB,
  MIPRE.BipartiteModel.Iso.pushB_symm_pushB, MIPRE.BipartiteModel.Iso.povmValue_eq,
  MIPRE.BipartiteModel.Iso.povmValue_push, MIPRE.BipartiteModel.Iso.pushStrat,
  MIPRE.BipartiteModel.Iso.pushStrat_PA, MIPRE.BipartiteModel.Iso.pushStrat_PB,
  MIPRE.BipartiteModel.Iso.value_pushStrat, MIPRE.BipartiteModel.Iso.dominates,
  MIPRE.BipartiteModel.Iso.inconsistency_eq, MIPRE.BipartiteModel.Iso.inconsistency_push,
  MIPRE.BipartiteModel.ProjStrat.swap, MIPRE.BipartiteModel.ProjStrat.swap_PA,
  MIPRE.BipartiteModel.ProjStrat.swap_PB, MIPRE.BipartiteModel.ProjStrat.value_swap,
  MIPRE.BipartiteModel.inconsistency_swap

-- blueprint `lem:extension-isos`
#guard_sorry_free MIPRE.OperatorMatrix.amplSubsingleton,
  MIPRE.OperatorMatrix.amplSubsingleton_apply, MIPRE.norm_evec_comp_swap,
  MIPRE.matrixUnitStarAlgEquiv, MIPRE.matrixUnitStarAlgEquiv_apply, MIPRE.submatrixStarAlgEquiv,
  MIPRE.submatrixStarAlgEquiv_apply, MIPRE.submatrixStarAlgEquiv_symm_apply,
  MIPRE.mapMatrixStarAlgEquiv, MIPRE.mapMatrixStarAlgEquiv_apply,
  MIPRE.mapMatrixStarAlgEquiv_symm_apply, MIPRE.BipartiteModel.expandUnit,
  MIPRE.BipartiteModel.expandUnit_ΦA, MIPRE.BipartiteModel.expandUnit_ΦB,
  MIPRE.BipartiteModel.assocIso, MIPRE.BipartiteModel.assocIso_ΦA, MIPRE.BipartiteModel.assocIso_ΦB,
  MIPRE.BipartiteModel.relabelIso, MIPRE.BipartiteModel.relabelIso_ΦA,
  MIPRE.BipartiteModel.relabelIso_ΦB, MIPRE.BipartiteModel.swapExpandIso,
  MIPRE.BipartiteModel.swapExpandIso_ΦA, MIPRE.BipartiteModel.swapExpandIso_ΦB,
  MIPRE.BipartiteModel.Iso.expandCongrW, MIPRE.BipartiteModel.Iso.ampl_expandCongrW,
  MIPRE.BipartiteModel.Iso.expandCongr, MIPRE.BipartiteModel.Iso.expandCongr_ΦA,
  MIPRE.BipartiteModel.Iso.expandCongr_ΦB, MIPRE.BipartiteModel.tensorExpandIso,
  MIPRE.BipartiteModel.tensorExpandIso_ΦA, MIPRE.BipartiteModel.tensorExpandIso_ΦB,
  MIPRE.BipartiteModel.tensorReindexW, MIPRE.BipartiteModel.tensorReindexW_apply,
  MIPRE.BipartiteModel.tensorReindexIso, MIPRE.BipartiteModel.tensorReindexIso_ΦA,
  MIPRE.BipartiteModel.tensorReindexIso_ΦB

-- blueprint `lem:model-reading`
#guard_sorry_free MIPRE.reindexStarAlgHomR_apply, MIPRE.smulKron_eq_diagonal_mul,
  MIPRE.compHom_smulKron_smulKron, MIPRE.compHom_smulKron_one, MIPRE.moveEquiv_apply,
  MIPRE.moveEquiv_symm_apply, MIPRE.basisVec_apply, MIPRE.basisVec_swap, MIPRE.norm_basisVec,
  MIPRE.BipartiteModel.recut_toStateModel, MIPRE.BipartiteModel.recut_πA_apply,
  MIPRE.BipartiteModel.recut_πB_apply, MIPRE.BipartiteModel.expand_πA_apply,
  MIPRE.BipartiteModel.expand_πB_apply, MIPRE.BipartiteModel.expand_πA_mul_πB_apply,
  MIPRE.BipartiteModel.recut_move_πA, MIPRE.BipartiteModel.recut_move_πB,
  MIPRE.BipartiteModel.recutAmpl, MIPRE.BipartiteModel.recutAmpl_apply,
  MIPRE.BipartiteModel.recutIsom, MIPRE.BipartiteModel.recutAmpl_recutIsom_W,
  MIPRE.BipartiteModel.recutIsom_ΦA, MIPRE.BipartiteModel.recutIsom_ΦB,
  MIPRE.BipartiteModel.recutIsom_W_ψ, MIPRE.BipartiteModel.recutIso,
  MIPRE.BipartiteModel.recutIso_ΦA, MIPRE.BipartiteModel.recutIso_ΦB,
  MIPRE.BipartiteModel.recutIso_toLocalIsometry, MIPRE.BipartiteModel.bornProb_expand_basisVec

-- blueprint `lem:model-embedding`
#guard_sorry_free MIPRE.POVMIn.pushforward_comp, MIPRE.BipartiteModel.inconsistency_map_equiv,
  MIPRE.BipartiteModel.star_πA_mul_πB_mul_self, MIPRE.BipartiteModel.LocalIsometry.toWithState_W,
  MIPRE.BipartiteModel.LocalIsometry.toWithState_ΦA,
  MIPRE.BipartiteModel.LocalIsometry.toWithState_ΦB,
  MIPRE.BipartiteModel.LocalIsometry.intertwine_sum,
  MIPRE.BipartiteModel.LocalIsometry.snorm_sum_mul_of_W_ψ,
  MIPRE.BipartiteModel.LocalIsometry.qform_sum_mul_of_W_ψ,
  MIPRE.BipartiteModel.LocalIsometry.ofUnitary, MIPRE.BipartiteModel.LocalIsometry.ofUnitary_W,
  MIPRE.BipartiteModel.LocalIsometry.ofUnitary_ΦA, MIPRE.BipartiteModel.LocalIsometry.ofUnitary_ΦB,
  MIPRE.BipartiteModel.LocalIsometry.ofUnitary_ΦA_one,
  MIPRE.BipartiteModel.LocalIsometry.ofUnitary_ΦB_one, MIPRE.BipartiteModel.Embedding.id_W,
  MIPRE.BipartiteModel.Embedding.id_ΦA, MIPRE.BipartiteModel.Embedding.id_ΦB,
  MIPRE.BipartiteModel.Embedding.comp_toLocalIsometry, MIPRE.BipartiteModel.Embedding.comp_W,
  MIPRE.BipartiteModel.Embedding.comp_ΦA, MIPRE.BipartiteModel.Embedding.comp_ΦB,
  MIPRE.BipartiteModel.Embedding.swap_toLocalIsometry, MIPRE.BipartiteModel.Embedding.swap_W,
  MIPRE.BipartiteModel.Embedding.swap_ΦA, MIPRE.BipartiteModel.Embedding.swap_ΦB,
  MIPRE.BipartiteModel.Embedding.swap_swap, MIPRE.BipartiteModel.Embedding.bornProb,
  MIPRE.BipartiteModel.Embedding.stateSqNorm, MIPRE.BipartiteModel.Embedding.swap_stateSqNorm,
  MIPRE.BipartiteModel.Embedding.xSqNorm, MIPRE.BipartiteModel.Embedding.norm_ψ,
  MIPRE.BipartiteModel.Embedding.inconsistency_pushforward,
  MIPRE.BipartiteModel.Embedding.povmValue_pushforward,
  MIPRE.BipartiteModel.Iso.toEmbedding_toLocalIsometry, MIPRE.BipartiteModel.Iso.toEmbedding_W,
  MIPRE.BipartiteModel.Iso.toEmbedding_ΦA, MIPRE.BipartiteModel.Iso.toEmbedding_ΦB,
  MIPRE.BipartiteModel.inertEmb, MIPRE.BipartiteModel.inertEmb_toLocalIsometry,
  MIPRE.BipartiteModel.inertEmb_ΦA, MIPRE.BipartiteModel.inertEmb_ΦB, MIPRE.BipartiteModel.assocEmb,
  MIPRE.BipartiteModel.assocEmb_toLocalIsometry, MIPRE.BipartiteModel.assocEmb_ΦA,
  MIPRE.BipartiteModel.assocEmb_ΦB, MIPRE.BipartiteModel.relabelEmb,
  MIPRE.BipartiteModel.relabelEmb_toLocalIsometry, MIPRE.BipartiteModel.relabelEmb_ΦA,
  MIPRE.BipartiteModel.relabelEmb_ΦB, MIPRE.BipartiteModel.swapExpandEmb,
  MIPRE.BipartiteModel.swapExpandEmb_toLocalIsometry, MIPRE.BipartiteModel.swapExpandEmb_ΦA,
  MIPRE.BipartiteModel.swapExpandEmb_ΦB, MIPRE.BipartiteModel.recutEmb,
  MIPRE.BipartiteModel.recutEmb_toLocalIsometry, MIPRE.BipartiteModel.recutEmb_ΦA,
  MIPRE.BipartiteModel.recutEmb_ΦB

-- blueprint `lem:lidt-model-transport`
#guard_sorry_free MIPRE.LIDT.CL.Sample.swapTy, MIPRE.LIDT.CL.Sample.swapTyEquiv,
  MIPRE.LIDT.CL.subtests_swap, MIPRE.LIDT.CL.accepts_swap, MIPRE.LIDT.CL.clGame_μ_swap,
  MIPRE.LIDT.CL.clGame_D_swap, MIPRE.LIDT.Simul.tuplePOVMAIn_pushStrat,
  MIPRE.LIDT.Simul.tuplePOVMBIn_pushStrat, MIPRE.LIDT.Simul.evalTuplePOVMIn_symm_pushA,
  MIPRE.LIDT.Simul.evalTuplePOVMIn_symm_pushB, MIPRE.LIDT.Simul.SoundIn.of_iso,
  MIPRE.LIDT.Simul.SoundIn.iff_of_iso, MIPRE.LIDT.Simul.SoundIn.swap,
  MIPRE.LIDT.Simul.soundIn_tensor_fintype, MIPRE.LIDT.Simul.soundIn_expand_tensor,
  MIPRE.LIDT.Simul.soundIn_swap_expand, MIPRE.LIDT.Simul.soundIn_swap_expand_of_norm

-- blueprint `lem:ampl-commutant`
#guard_sorry_free MIPRE.OperatorMatrix.entries, MIPRE.OperatorMatrix.entries_apply,
  MIPRE.OperatorMatrix.sum_emb, MIPRE.OperatorMatrix.toCLM_entries,
  MIPRE.OperatorMatrix.entries_toCLM, MIPRE.OperatorMatrix.toCLM_injective,
  MIPRE.OperatorMatrix.commute_toCLM_iff, MIPRE.commute_diagonal_const_iff,
  MIPRE.liftLeft_diagonal_const, MIPRE.liftRight_diagonal_const, MIPRE.commute_liftLeft_liftRight,
  MIPRE.mul_liftRight_single_apply, MIPRE.liftRight_single_mul_apply,
  MIPRE.mul_liftLeft_single_apply, MIPRE.liftLeft_single_mul_apply, MIPRE.eq_liftLeft_of_commute,
  MIPRE.eq_liftRight_of_commute, MIPRE.uniformProj, MIPRE.isStarProjection_uniformProj,
  MIPRE.isStarProjection_single_one, MIPRE.single_eq_smul_mul_uniformProj_mul,
  MIPRE.commute_liftRight_single_of_commute, MIPRE.OperatorMatrix.commute_toCLM_liftLeft_liftRight,
  MIPRE.OperatorMatrix.exists_eq_toCLM_liftLeft, MIPRE.OperatorMatrix.exists_eq_toCLM_liftRight,
  MIPRE.OperatorMatrix.toCLM_liftLeft_injective, MIPRE.OperatorMatrix.toCLM_liftRight_injective,
  MIPRE.mem_centralizer_of_forall_commute, MIPRE.nonempty_of_norm_evec_eq_one, MIPRE.twoOutcome,
  MIPRE.isStarProjection_twoOutcome, MIPRE.sum_twoOutcome

-- blueprint `lem:co-extension`
#guard_sorry_free MIPRE.CommutingOperatorStrategy.expandRegProj,
  MIPRE.CommutingOperatorStrategy.isStarProjection_expandRegProj,
  MIPRE.CommutingOperatorStrategy.expandBobMat,
  MIPRE.CommutingOperatorStrategy.expandBobMat_inl_inl,
  MIPRE.CommutingOperatorStrategy.expandBobMat_inr_inr,
  MIPRE.CommutingOperatorStrategy.expandBobMat_inl_inr,
  MIPRE.CommutingOperatorStrategy.expandBobMat_inr_inl,
  MIPRE.CommutingOperatorStrategy.commute_expandBobMat_apply,
  MIPRE.CommutingOperatorStrategy.isPositive_toCLM_liftRight_expandBobMat,
  MIPRE.CommutingOperatorStrategy.sum_expandBobMat,
  MIPRE.CommutingOperatorStrategy.sum_toCLM_liftRight_expandBobMat,
  MIPRE.CommutingOperatorStrategy.expandStrategyAux, MIPRE.CommutingOperatorStrategy.expandStrategy,
  MIPRE.CommutingOperatorStrategy.expandAliceRep, MIPRE.CommutingOperatorStrategy.expandBobRep,
  MIPRE.CommutingOperatorStrategy.expandAliceRep_apply,
  MIPRE.CommutingOperatorStrategy.expandBobRep_apply,
  MIPRE.CommutingOperatorStrategy.expandAliceRep_eq,
  MIPRE.CommutingOperatorStrategy.expandBobRep_eq,
  MIPRE.CommutingOperatorStrategy.expandAliceRep_mem,
  MIPRE.CommutingOperatorStrategy.exists_expandAliceRep_eq,
  MIPRE.CommutingOperatorStrategy.expandAliceHom,
  MIPRE.CommutingOperatorStrategy.expandAliceHom_bijective,
  MIPRE.CommutingOperatorStrategy.expandAliceEquiv,
  MIPRE.CommutingOperatorStrategy.coe_expandAliceEquiv,
  MIPRE.CommutingOperatorStrategy.expandBobRep_mem,
  MIPRE.CommutingOperatorStrategy.exists_expandBobRep_eq,
  MIPRE.CommutingOperatorStrategy.expandBobHom,
  MIPRE.CommutingOperatorStrategy.expandBobHom_bijective,
  MIPRE.CommutingOperatorStrategy.expandBobEquiv,
  MIPRE.CommutingOperatorStrategy.coe_expandBobEquiv,
  MIPRE.CommutingOperatorStrategy.mem_expandStrategy_aliceAlg_iff,
  MIPRE.CommutingOperatorStrategy.mem_expandStrategy_bobAlg_iff,
  MIPRE.CommutingOperatorStrategy.expandIso, MIPRE.CommutingOperatorStrategy.expandIso_W,
  MIPRE.CommutingOperatorStrategy.expandIso_ΦA, MIPRE.CommutingOperatorStrategy.expandIso_ΦB

-- blueprint `lem:lidt-sound-co-expand`
#guard_sorry_free MIPRE.LIDT.Simul.SoundCo.expand

-- blueprint `lem:register-action`
#guard_sorry_free MIPRE.OperatorMatrix.regActHom, MIPRE.OperatorMatrix.regAct,
  MIPRE.OperatorMatrix.regActHom_apply, MIPRE.OperatorMatrix.regAct_eq_toCLM,
  MIPRE.OperatorMatrix.regAct_mul, MIPRE.OperatorMatrix.regAct_one,
  MIPRE.OperatorMatrix.regAct_conjTranspose, MIPRE.OperatorMatrix.regAct_add,
  MIPRE.OperatorMatrix.regAct_smul, MIPRE.OperatorMatrix.regAct_sum,
  MIPRE.OperatorMatrix.isStarProjection_regAct, MIPRE.OperatorMatrix.regAct_apply,
  MIPRE.OperatorMatrix.regAct_toLp_smul, MIPRE.OperatorMatrix.regAct_vecMulVec,
  MIPRE.OperatorMatrix.norm_toLp_smul, MIPRE.BipartiteModel.expand_π_πA_smulKron_one,
  MIPRE.BipartiteModel.expand_π_πB_smulKron_one, MIPRE.BipartiteModel.expand_π_smulKron_one_mul

-- blueprint `lem:model-state-calculus`
#guard_sorry_free MIPRE.Op.abs_qform_sub_qform_le, MIPRE.StateModel.snorm_sq_sum_orthogonal,
  MIPRE.StateModel.snorm_sq_sum_orthogonal', MIPRE.StateModel.sum_snorm_sq_chain_le,
  MIPRE.StateModel.snorm_sq_obs_sub_le, MIPRE.StateModel.abs_qform_sub_qform_le,
  MIPRE.StateModel.abs_qform_withState_sub_qform_le, MIPRE.BipartiteModel.sum_stateSqNorm_sub_le,
  MIPRE.BipartiteModel.sum_stateSqNorm_sub_le_four_of_le,
  MIPRE.BipartiteModel.sum_stateSqNorm_sub_le_four

-- blueprint `lem:model-parseval`
#guard_sorry_free MIPRE.sum_norm_charSum_sq, MIPRE.sum_sgn_trMul_eq_ite, MIPRE.sum_star_sgn_trMul,
  MIPRE.sum_star_sgn_trMul2, MIPRE.sum_norm_trSum_sq, MIPRE.sum_norm_trSum2_sq,
  MIPRE.sum_avg_norm_fibreSum_sq, MIPRE.StateModel.sum_avg_snorm_sq_fibre_eq,
  MIPRE.BipartiteModel.sum_avg_stateSqNorm_fibre_eq, MIPRE.BipartiteModel.sum_avg_xSqNorm_fibre_eq

-- blueprint `lem:qld-sound-co`
#guard_sorry_free MIPRE.QLD.soundCo_of_lidt

-- blueprint `cor:mipco-from-lidt`
#guard_sorry_free MIPRE.mipco_eq_core_of_lidt

/-! The commuting-operator track, Phase 6 (`planning/mipco-track.md` §5, C6a): finite pairs and
their ancilla extensions, `lem:finite-pair-expand` (`MIPRE/Foundations/FinitePairExpand.lean`);
`ω_co` approached in dyadic pairs since C6b, `lem:co-value-finite-pair`
(`MIPRE/Background/Repetition/{TracialApprox,DyadicApprox}.lean`); answer reduction and the Pauli
basis test from the seeded test in dyadic pairs, `thm:ar-sound-co-fin` and `lem:qld-approx-co-fin`;
and the conditional theorem, `cor:mipco-from-lidt-fin` (`MIPRE/MIPCo.lean`). -/

-- blueprint `lem:finite-pair-expand`
#guard_sorry_free MIPRE.BipartiteModel.IsFinitePair.expand, MIPRE.BipartiteModel.IsFinitePair.swap

-- blueprint `lem:co-value-finite-pair`
#guard_sorry_free MIPRE.Repetition.nonempty_of_lt_commutingOperatorValue,
  MIPRE.Repetition.exists_projStrat_expand_stdModel, MIPRE.Repetition.commutingFinitePairApprox

-- blueprint `thm:ar-sound-co-fin`
#guard_sorry_free MIPRE.AnswerReduction.answerReduction_soundIn_commuting_fin,
  MIPRE.LIDT.Simul.approxSoundIn_commuting_of_fin

-- blueprint `lem:qld-approx-co-fin`
#guard_sorry_free MIPRE.QLD.approxSoundIn_commuting_of_fin

-- blueprint `cor:mipco-from-lidt-fin`
#guard_sorry_free MIPRE.mipco_eq_core_of_lidtFin,
  MIPRE.gapCompressionCo_sound_of_lidtFin

/-! The commuting-operator track, C6b's II₁ orthonormalization tier (`planning/c6b-plan.md`, T1):
a centre-valued trace for a von Neumann algebra with a faithful tracial vector functional,
`lem:center-valued-trace` (`MIPRE/Background/Orthonormalization/{CenterTrace,CenterTraceClauses,
CenterComparison}.lean`); de la Salle's Theorem 1.2 without abelian projections,
`thm:orthonormalization-no-abelian` (`NoAbelian.lean`); and in a finite pair,
`cor:orthonormalization-finite-pair` (`FinitePairOrtho.lean`). -/

-- blueprint `lem:center-valued-trace`
#guard_sorry_free MIPRE.Orthonormalization.vecFunctional, MIPRE.Orthonormalization.IsCenterExpectation,
  MIPRE.Orthonormalization.eq_of_isCentralIn_of_pairing, MIPRE.Orthonormalization.exists_isCenterExpectation,
  MIPRE.Orthonormalization.mvNEquiv_of_map_eq, MIPRE.Orthonormalization.IsCenterExpectation.isCenterValuedTrace,
  MIPRE.Orthonormalization.exists_isCenterValuedTrace

-- blueprint `thm:orthonormalization-no-abelian`
#guard_sorry_free MIPRE.Orthonormalization.povm_orthogonalization_of_isCenterValuedTrace,
  MIPRE.Orthonormalization.povm_orthogonalization_vecTrace

-- blueprint `cor:orthonormalization-finite-pair`
#guard_sorry_free MIPRE.Orthonormalization.vnA, MIPRE.Orthonormalization.mem_vnA_iff,
  MIPRE.Orthonormalization.povm_orthogonalization_finitePair

/-! The commuting-operator track, the rest of C6b's II₁ tier (`planning/c6b-plan.md`, T2–T5):
unital dyadic matrix units and Pauli sites, `lem:dyadic-units-closure` and `lem:pauli-sites-units`
(`MIPRE/Foundations/MatUnits.lean`); no abelian projections under dyadic units and a vector trace,
`thm:no-abelian-dyadic`, and the closure of dyadic pairs, `lem:dyadic-pair-closure`
(`MIPRE/Foundations/DyadicPair.lean`); the twisted Pauli algebra, `lem:pauli-algebra`
(`MIPRE/Background/Repetition/PauliAlgebra.lean`); amplification by it, `lem:amplification-dyadic`
(`Amplify.lean`); and orthonormalization in a dyadic pair, `cor:orthonormalization-dyadic-pair`
(`MIPRE/Background/Orthonormalization/DyadicOrtho.lean`). The value lemma restated to dyadic pairs
keeps its guard in the C6a block above. -/

-- blueprint `lem:dyadic-units-closure`
#guard_sorry_free MIPRE.IsMatUnits.mul_cancel, MIPRE.IsMatUnits.map, MIPRE.IsMatUnits.op,
  MIPRE.IsMatUnits.diagonal, MIPRE.IsMatUnits.prod, MIPRE.HasDyadicUnits.map,
  MIPRE.HasDyadicUnits.op, MIPRE.HasDyadicUnits.matrix, MIPRE.HasDyadicUnits.prod

-- blueprint `lem:pauli-sites-units`
#guard_sorry_free MIPRE.PauliSites, MIPRE.PauliSites.proj, MIPRE.PauliSites.xpow,
  MIPRE.PauliSites.unit, MIPRE.PauliSites.isMatUnits_unit, MIPRE.PauliSites.commute_unit,
  MIPRE.PauliSites.units, MIPRE.PauliSites.units_mul, MIPRE.PauliSites.star_units,
  MIPRE.PauliSites.sum_units_diag, MIPRE.PauliSites.isMatUnits_units,
  MIPRE.PauliSites.hasDyadicUnits

-- blueprint `thm:no-abelian-dyadic`
#guard_sorry_free MIPRE.mul_star_le_mul_of_commute, MIPRE.VecTrace.tr, MIPRE.VecTrace.tr_one,
  MIPRE.VecTrace.tr_mul_comm, MIPRE.VecTrace.re_tr_nonneg, MIPRE.VecTrace.re_tr_mono,
  MIPRE.VecTrace.tr_star_mul_self, MIPRE.VecTrace.card_mul_re_tr_le_one,
  MIPRE.VecTrace.eq_zero_of_dyadicUnits, MIPRE.BipartiteModel.mul_mem_opsA,
  MIPRE.BipartiteModel.star_mem_opsA, MIPRE.BipartiteModel.IsFinitePair.eq_zero_of_abelianA,
  MIPRE.BipartiteModel.IsFinitePair.eq_zero_of_abelianB

-- blueprint `lem:dyadic-pair-closure`
#guard_sorry_free MIPRE.BipartiteModel.IsDyadicPair.swap, MIPRE.BipartiteModel.IsDyadicPair.expand,
  MIPRE.BipartiteModel.IsDyadicPair.eq_zero_of_abelianA,
  MIPRE.BipartiteModel.IsDyadicPair.eq_zero_of_abelianB

-- blueprint `lem:pauli-algebra`
#guard_sorry_free MIPRE.Repetition.Pauli.pauliA, MIPRE.Repetition.Pauli.pauliTrace,
  MIPRE.Repetition.Pauli.pauliStd, MIPRE.Repetition.Pauli.pauliSites,
  MIPRE.Repetition.Pauli.pauliStd_hasDyadicUnits

-- blueprint `lem:amplification-dyadic`
#guard_sorry_free MIPRE.Repetition.leftVNHom, MIPRE.Repetition.rightVNHom,
  MIPRE.Repetition.isDyadicPair_stdModel, MIPRE.Repetition.hasDyadicUnits_tensorStep,
  MIPRE.Repetition.isDyadicPair_stdModel_tensorStep, MIPRE.Repetition.inclLeft,
  MIPRE.Repetition.τ_inclLeft, MIPRE.Repetition.isPosElem_map, MIPRE.Repetition.amplify,
  MIPRE.Repetition.amplify_correlation, MIPRE.Repetition.isDyadicPair_stdModel_amplify,
  MIPRE.Repetition.exists_tracialStrategy_isDyadicPair

-- blueprint `cor:orthonormalization-dyadic-pair`
#guard_sorry_free MIPRE.Orthonormalization.povm_orthogonalization_dyadicPair,
  MIPRE.Orthonormalization.povm_orthogonalization_dyadicPairB

/-! The commuting-operator track, C6b's port (`planning/c6b-plan.md`, M0–M1): swap symmetry as
three theorems of the symmetric model, `lem:sym-model-swap`
(`MIPRE/Background/LIDT/Co/Basic/QuantumState.lean`), and the commutativity of points over it,
`lem:co-commutativity-points` (`MIPRE/Background/LIDT/Co/CommutativityPoints/BridgeTheorems/
DropBridges.lean` and `AnswerTheorems.lean`). The port is not a vendored tree, so its guards live
here. The model itself, `def:sym-model`, is a definition and carries no proof-level mark. -/

-- blueprint `lem:sym-model-swap`
#guard_sorry_free MIPRE.LIDT.Co.SymModel.ev_flip, MIPRE.LIDT.Co.SymModel.ev_L_eq_ev_R,
  MIPRE.LIDT.Co.SymModel.ev_L_mul_R_comm

-- blueprint `lem:co-commutativity-points`
#guard_sorry_free MIPRE.LIDT.Co.CommutativityPoints.commutativityPoints,
  MIPRE.LIDT.Co.CommutativityPoints.answerCommutativityPoints

/-! The doubling and the summed semidefinite form (C6b, M2 and M9 of `planning/c6b-plan.md`).
The order of a finite pair's algebras, `lem:finite-pair-order`
(`MIPRE/Foundations/FinitePairOrder.lean`); the doubled model of a finite pair as a finite pair,
its role average and its abelian projections, `lem:doubled-model-finite-pair`,
`lem:doubled-model-role-average` and `lem:doubled-model-no-abelian`
(`MIPRE/Foundations/Doubling.lean` and `MIPRE/Background/LIDT/Co/Doubling/`); the symmetric
strategy, `thm:doubled-symmetrization`, and orthonormalization in the doubled model,
`thm:doubled-orthonormalization`; the summed form in a commutant with a vector trace,
`thm:summed-sdp` (`MIPRE/Foundations/SummedSdp.lean` and
`MIPRE/Background/Orthonormalization/SdpMaximizer.lean`), and in the doubled model,
`cor:summed-sdp-doubled` (`Co/Doubling/Sdp.lean`). The doubled model itself, `def:doubled-model`,
is a definition and carries no proof-level mark. -/

-- blueprint `lem:finite-pair-order`
#guard_sorry_free MIPRE.BipartiteModel.IsFinitePair.equivA,
  MIPRE.BipartiteModel.IsFinitePair.equivB, MIPRE.BipartiteModel.IsFinitePair.nonneg_iff_A,
  MIPRE.BipartiteModel.IsFinitePair.nonneg_iff_B, MIPRE.BipartiteModel.IsFinitePair.le_iff_A,
  MIPRE.BipartiteModel.IsFinitePair.le_iff_B, MIPRE.POVMIn.mapHom, MIPRE.isPVMIn_map_equiv_iff

-- blueprint `lem:doubled-model-finite-pair`
#guard_sorry_free MIPRE.LIDT.Co.Doubling.isFinitePair, MIPRE.LIDT.Co.Doubling.tr_diag2_L,
  MIPRE.LIDT.Co.Doubling.L_nonneg_iff, MIPRE.LIDT.Co.Doubling.R_nonneg_iff,
  MIPRE.LIDT.Co.Doubling.equiv_nonneg_iff, MIPRE.LIDT.Co.Doubling.isDyadicPair,
  MIPRE.LIDT.Co.Doubling.model_L_injective, MIPRE.LIDT.Co.SymModel.L_cfc,
  MIPRE.LIDT.Co.Doubling.cfc_mem_opsA

-- blueprint `lem:doubled-model-role-average`
#guard_sorry_free MIPRE.LIDT.Co.Doubling.ev_L, MIPRE.LIDT.Co.Doubling.inner_L_mul_R,
  MIPRE.LIDT.Co.Doubling.bornProb_model_eq, MIPRE.LIDT.Co.Doubling.qBipartiteConsDefect_model,
  MIPRE.LIDT.Co.Doubling.dis_model, MIPRE.LIDT.Co.Doubling.inconsistency_model,
  MIPRE.LIDT.Co.Doubling.bipartiteConsError_model,
  MIPRE.LIDT.Co.Doubling.bipartiteConsError_components_le_two_mul,
  MIPRE.LIDT.Co.bipartiteConsError_eq_inconsistency

-- blueprint `lem:doubled-model-no-abelian`
#guard_sorry_free MIPRE.NoAbelianProj, MIPRE.noAbelianProj_diag2Set_iff,
  MIPRE.LIDT.Co.Doubling.noAbelianProj_iff,
  MIPRE.LIDT.Co.Doubling.noAbelianProj_opsA_of_isDyadicPair,
  MIPRE.LIDT.Co.Doubling.noAbelianProj_opsB_of_isDyadicPair

-- blueprint `thm:doubled-symmetrization`
#guard_sorry_free MIPRE.LIDT.Co.ProjStrat.lowIndividualDegreeFailureProbability,
  MIPRE.LIDT.Co.ProjStrat.PassesLowIndividualDegreeTest, MIPRE.LIDT.Co.Doubling.pairProjMeas,
  MIPRE.LIDT.Co.Doubling.symmStrat,
  MIPRE.LIDT.Co.Doubling.symmStrat_axisParallel_eq_roleAverage,
  MIPRE.LIDT.Co.Doubling.symmStrat_selfConsistency_eq_pointAgreement,
  MIPRE.LIDT.Co.Doubling.symmStrat_diagonal_eq_roleAverage,
  MIPRE.LIDT.Co.Doubling.symmStrat_isGood_three_mul

-- blueprint `thm:doubled-orthonormalization`
#guard_sorry_free MIPRE.LIDT.Co.SymModel.orthonormalization_of_isFinitePair,
  MIPRE.LIDT.Co.SymModel.orthonormalization_of_isFinitePair_sddRel,
  MIPRE.LIDT.Co.Doubling.orthonormalization_model,
  MIPRE.LIDT.Co.Doubling.orthonormalization_of_isDyadicPair,
  MIPRE.LIDT.Co.Doubling.orthonormalization_model_sddRel

-- blueprint `thm:summed-sdp`
#guard_sorry_free MIPRE.SummedSdp.IsSummedSdp, MIPRE.SummedSdp.IsSummedSdp.sum_mul_eq,
  MIPRE.SummedSdp.IsFaithfulTrace, MIPRE.SummedSdp.isSummedSdp_of_firstOrder,
  MIPRE.SummedSdp.isSummedSdp_of_isMaxOn, MIPRE.SummedSdp.isSummedSdp_of_le,
  MIPRE.Orthonormalization.exists_isMaxOn_obj, MIPRE.Orthonormalization.exists_isSummedSdp,
  MIPRE.Orthonormalization.exists_isSummedSdp_centralizer,
  MIPRE.Orthonormalization.exists_isSummedSdp_finitePairA,
  MIPRE.Orthonormalization.exists_isSummedSdp_finitePairB

-- blueprint `cor:summed-sdp-doubled`
#guard_sorry_free MIPRE.LIDT.Co.Doubling.isSummedSdp_prod_iff,
  MIPRE.LIDT.Co.Doubling.isSummedSdp_map_iff_of_nonneg_iff,
  MIPRE.LIDT.Co.Doubling.exists_isSummedSdp_loc, MIPRE.LIDT.Co.Doubling.isSummedSdp_L_iff,
  MIPRE.LIDT.Co.Doubling.isSummedSdp_R_iff, MIPRE.LIDT.Co.Doubling.exists_isSummedSdp_model,
  MIPRE.LIDT.Co.Doubling.isSummedSdp_equivA_iff, MIPRE.LIDT.Co.Doubling.isSummedSdp_equivB_iff,
  MIPRE.LIDT.Co.Doubling.exists_isSummedSdp_A, MIPRE.LIDT.Co.Doubling.exists_isSummedSdp_B,
  MIPRE.LIDT.Co.Doubling.isSummedSdp_equiv_iff, MIPRE.LIDT.Co.Doubling.exists_isSummedSdp_prod

/-! The rest of the preliminaries and the local-to-global variance inequality (C6b, M3 and M5 of
`planning/c6b-plan.md`): the switch sandwich and the self-consistency calculus over a symmetric
model, `lem:co-switch-sandwich-self-consistency`
(`MIPRE/Background/LIDT/Co/Preliminaries/SwitchSandwichMain/Completeness.lean`,
`BipartiteSelfConsistency/`, `SelfConsistency/` and `CompletionTransfer.lean`), and the
local-to-global inequality on any vector state by Gram positivity, `lem:co-local-to-global`
(`MIPRE/Background/LIDT/Co/ExpansionHypercubeGraph/`). -/

-- blueprint `lem:co-switch-sandwich-self-consistency`
#guard_sorry_free MIPRE.LIDT.Co.Preliminaries.switchSandwich,
  MIPRE.LIDT.Co.Preliminaries.twoNotionsOfSelfConsistency,
  MIPRE.LIDT.Co.Preliminaries.bipartiteSSC_implies_localSSC_liftLeft,
  MIPRE.LIDT.Co.Preliminaries.otherTwoNotionsOfSelfConsistency,
  MIPRE.LIDT.Co.Preliminaries.selfConsistencyImpliesDataProcessing,
  MIPRE.LIDT.Co.Preliminaries.completingToMeasurement

-- blueprint `lem:co-local-to-global`
#guard_sorry_free MIPRE.LIDT.Co.ExpansionHypercubeGraph.localVariance,
  MIPRE.LIDT.Co.ExpansionHypercubeGraph.globalVariance,
  MIPRE.LIDT.Co.ExpansionHypercubeGraph.re_combinedTraceForm_nonneg,
  MIPRE.LIDT.Co.ExpansionHypercubeGraph.traceForm_localToGlobal,
  MIPRE.LIDT.Co.ExpansionHypercubeGraph.localToGlobal,
  MIPRE.LIDT.Co.ExpansionHypercubeGraph.localToGlobalBipartite

/-! The Schwartz--Zippel step, the global variance of the points, the commutation of the slice
measurements and orthonormalization in a symmetric model (C6b, M4, M6, M7 and M8 of
`planning/c6b-plan.md`): `lem:co-schwartz-zippel-step`
(`MIPRE/Background/LIDT/Co/Test/SchwartzZippelStep.lean`), `lem:co-global-variance-of-points`
(`MIPRE/Background/LIDT/Co/GlobalVariance/`), `lem:co-commutation-g`
(`MIPRE/Background/LIDT/Co/Commutativity/`) and `lem:co-orthonormalization`
(`MIPRE/Background/LIDT/Co/MakingMeasurementsProjective/`), whose rounding calls the
orthonormalization tier in place of the vendored finite-dimensional route. -/

-- blueprint `lem:co-schwartz-zippel-step`
#guard_sorry_free MIPRE.LIDT.Co.Test.MainFormalStep5ExpansionBound,
  MIPRE.LIDT.Co.Test.mainFormalStep5_expansionBound,
  MIPRE.LIDT.Co.Test.mainFormalStep5_selfConsistency_ofExpansionBound,
  MIPRE.LIDT.Co.Test.mainFormalStep5_selfConsistency_ofExpansionBound_heterogeneous

-- blueprint `lem:co-global-variance-of-points`
#guard_sorry_free MIPRE.LIDT.Co.GlobalVariance.weightedPointConditionedOperatorAtPolynomial,
  MIPRE.LIDT.Co.GlobalVariance.GlobalVarianceOfPointsStatement,
  MIPRE.LIDT.Co.GlobalVariance.localVarianceTransportChainBound,
  MIPRE.LIDT.Co.GlobalVariance.globalVarianceOfPoints

-- blueprint `lem:co-commutation-g`
#guard_sorry_free MIPRE.LIDT.Co.Commutativity.commDataProcessedG_of_commutativityPoints,
  MIPRE.LIDT.Co.Commutativity.commDataProcessedG,
  MIPRE.LIDT.Co.Commutativity.comMain_of_commutativityPoints,
  MIPRE.LIDT.Co.Commutativity.comMain

-- blueprint `lem:co-orthonormalization`
#guard_sorry_free
  MIPRE.LIDT.Co.MakingMeasurementsProjective.leftPlacedProjectivizationRepair_of_sourceAlmostProjective_two_mul,
  MIPRE.LIDT.Co.MakingMeasurementsProjective.orthonormalizationMainLemma,
  MIPRE.LIDT.Co.MakingMeasurementsProjective.orthonormalization,
  MIPRE.LIDT.Co.MakingMeasurementsProjective.orthonormalizationMeasurement_of_consistency_from_projectivizationRepair_heterogeneous,
  MIPRE.LIDT.Co.MakingMeasurementsProjective.orthonormalizationMeasurement_right_of_consistency_from_projectivizationRepair_heterogeneous

/-! Self-improvement and pasting in a symmetric model (C6b, M10 and M11 of
`planning/c6b-plan.md`): `lem:co-self-improvement`
(`MIPRE/Background/LIDT/Co/SelfImprovement/`), whose semidefinite program is M9's summed form
through `SdpStatementWithSlackness.of_isSummedSdp` and whose rounding is M8's orthonormalization,
and `lem:co-ld-pasting` (`MIPRE/Background/LIDT/Co/Pasting/`). -/

-- blueprint `lem:co-self-improvement`
#guard_sorry_free MIPRE.LIDT.Co.SelfImprovement.SdpStatementWithSlackness.of_isSummedSdp,
  MIPRE.LIDT.Co.SelfImprovement.sdp_statement_with_slackness,
  MIPRE.LIDT.Co.SelfImprovement.selfImprovementHelper,
  MIPRE.LIDT.Co.SelfImprovement.selfImprovementHelperError_pos,
  MIPRE.LIDT.Co.SelfImprovement.SelfImprovementConclusion,
  MIPRE.LIDT.Co.SelfImprovement.selfImprovement,
  MIPRE.LIDT.Co.SelfImprovement.selfImprovement_of_axisParallel_selfConsistency

-- blueprint `lem:co-ld-pasting`
#guard_sorry_free MIPRE.LIDT.Co.Pasting.chernoffBernoulliMatrix,
  MIPRE.LIDT.Co.Pasting.LdPastingConclusion,
  MIPRE.LIDT.Co.Pasting.ldPastingNCompleteness,
  MIPRE.LIDT.Co.Pasting.ldPastingSubMeas,
  MIPRE.LIDT.Co.Pasting.ldPastingNontrivial,
  MIPRE.LIDT.Co.Pasting.ldPasting

/-! The end of the port (C6b, M12–M14 of `planning/c6b-plan.md`): the main induction over a
symmetric model, `lem:co-main-induction`
(`MIPRE/Background/LIDT/Co/MainInductionStep/Theorems/MainTheorems/Successor.lean`); the main
theorem in a dyadic pair,
`thm:co-main-formal` (`MIPRE/Background/LIDT/Co/Test/MainTheorem/MainFormal.lean`), through the
main induction in the doubled model and the unsymmetrization of Theorem E,
`lem:doubled-unsymmetrization` (`MIPRE/Background/LIDT/Co/Doubling/Unsymmetrization.lean`); the
canonical-line theorem in a dyadic pair, `lem:co-lidt-canonical-line`
(`MIPRE/Background/LIDT/Co/Bridge/`), and the model chain to `SoundIn`,
`lem:lidt-sound-in-of-model-lidt` (`MIPRE/Background/LIDT/Co/Chain/`); `SoundFin`,
`thm:lidt-sound-fin` (`MIPRE/Background/LIDT/Co/SoundFin.lean`); and, without hypothesis, the
commuting-operator soundness of compression, the halting reduction to `ω_co` and
`MIP^co = coRE`, `thm:mipco-eq-core-unconditional` (`MIPRE/MIPCo.lean`). -/

-- blueprint `lem:co-main-induction`
#guard_sorry_free MIPRE.LIDT.Co.MainInductionStep.mainInduction

-- blueprint `lem:doubled-unsymmetrization`
#guard_sorry_free MIPRE.LIDT.Co.Doubling.symmStrat_pointConsistency_unsymmetrize

-- blueprint `thm:co-main-formal`
#guard_sorry_free MIPRE.LIDT.Co.Test.mainFormal

-- blueprint `lem:co-lidt-canonical-line`
#guard_sorry_free MIPRE.LIDT.Co.Bridge.soundness,
  MIPRE.LIDT.Co.Bridge.soundLidtIn_of_isDyadicPair

-- blueprint `lem:lidt-sound-in-of-model-lidt`
#guard_sorry_free MIPRE.LIDT.Co.Chain.soundIn_of_soundLidtIn

-- blueprint `thm:lidt-sound-fin`
#guard_sorry_free MIPRE.LIDT.Simul.soundFin

-- blueprint `thm:mipco-eq-core-unconditional`
#guard_sorry_free MIPRE.mipco_eq_core,
  MIPRE.gapCompressionCo_sound,
  MIPRE.halting_reduction_commuting,
  MIPRE.core_subset_mipco

-- blueprint `lem:tailored-trivial-zpc`
#guard_sorry_free MIPRE.Tailored.PermStrategy.trivial,
  MIPRE.Tailored.PermStrategy.trivial_proj, MIPRE.Tailored.hasPerfectZPC_of_accepts_zero

-- blueprint `lem:signed-perm`
#guard_sorry_free MIPRE.Tailored.SignedPerm.toMatrix_mul,
  MIPRE.Tailored.SignedPerm.toMatrix_injective, MIPRE.Tailored.SignedPerm.toMatrix_inv,
  MIPRE.Tailored.SignedPerm.toMatrix_negOne, MIPRE.Tailored.SignedPerm.toMatrix_diag,
  MIPRE.Tailored.SignedPerm.toMatrix_prod, MIPRE.Tailored.SignedPerm.toMatrix_map,
  MIPRE.Tailored.SignedPerm.toMatrix_mem_unitaryGroup, MIPRE.Tailored.IsSignedPerm.isHermitian,
  MIPRE.Tailored.IsSignedPerm.isDiag_iff, MIPRE.Tailored.IsSignedPerm.kronecker,
  MIPRE.Tailored.IsSignedPerm.conjTranspose_eq_transpose

-- blueprint `lem:fourier-pvm`
#guard_sorry_free MIPRE.Tailored.isPVMIn_fourierFactor, MIPRE.Tailored.isPVMIn_fourierProj,
  MIPRE.Tailored.mul_fourierProj, MIPRE.Tailored.obsChar_mul_fourierProj,
  MIPRE.Tailored.pvmObs_fourierProj_bit, MIPRE.Tailored.pvmObs_fourierProj_dotBit,
  MIPRE.Tailored.isDiag_fourierProj

-- blueprint `lem:data-processing`
#guard_sorry_free MIPRE.Tailored.pvmObs_coarse_affine, MIPRE.Tailored.isDiag_coarse

-- blueprint `lem:perm-strategy-perfect`
#guard_sorry_free MIPRE.Tailored.PermStrategy.isPVMIn_proj,
  MIPRE.Tailored.PermStrategy.commute_proj, MIPRE.Tailored.PermStrategy.value_eq_one_of,
  MIPRE.Tailored.PermStrategy.dotBit_of_obsChar, MIPRE.Tailored.satisfies_ofFn_iff

-- blueprint `lem:zpc-pcc`
#guard_sorry_free MIPRE.Tailored.PermStrategy.toSync, MIPRE.Tailored.PermStrategy.isPCC_toSync,
  MIPRE.Tailored.PermStrategy.value_toSync, MIPRE.Tailored.PermStrategy.double,
  MIPRE.Tailored.PermStrategy.value_double, MIPRE.Tailored.TailoredGame.HasPerfectZPC.doubled,
  MIPRE.Tailored.TailoredGame.HasPerfectZPC.exists_pcc,
  MIPRE.Tailored.TailoredGame.HasPerfectZPC.syncValue_eq_one,
  MIPRE.Tailored.TailoredGame.HasPerfectZPC.valStar_eq_one

-- blueprint `lem:tailored-product-accepts`
#guard_sorry_free MIPRE.Tailored.TailoredGame.repeat_accepts_iff,
  MIPRE.Tailored.TailoredGame.satisfies_padCons_iff

-- blueprint `lem:tensor-power-zpc`
#guard_sorry_free MIPRE.Tailored.slot, MIPRE.Tailored.isSignedPerm_slot,
  MIPRE.Tailored.isDiag_slot, MIPRE.Tailored.commute_slot_slot,
  MIPRE.Tailored.prod_slot_finRange, MIPRE.Tailored.PermStrategy.repeat,
  MIPRE.Tailored.PermStrategy.proj_repeat,
  MIPRE.Tailored.PermStrategy.proj_mul_eq_zero_of_value_eq_one,
  MIPRE.Tailored.PermStrategy.value_repeat_eq_one, MIPRE.Tailored.PermStrategy.comap,
  MIPRE.Tailored.PermStrategy.value_comap_eq_one,
  MIPRE.Tailored.TailoredGame.HasPerfectZPC.repeat_doubled

-- blueprint `thm:tailored-rep-from-spec`
#guard_sorry_free MIPRE.Tailored.TailoredVerifier.RepSpec.accepts_iff,
  MIPRE.Tailored.TailoredVerifier.RepSpec.accepts_of_accepts,
  MIPRE.Tailored.TailoredVerifier.RepSpec.hasPerfectZPC,
  MIPRE.Tailored.TailoredVerifier.RepSpec.valStar_le_repeat,
  MIPRE.Tailored.TailoredVerifier.RepSpec.valStar_le, MIPRE.quantumValue_le_of_coarse,
  MIPRE.Tailored.PermStrategy.exists_accepts

-- blueprint `lem:tailored-rep-programs`
#guard_sorry_free MIPRE.Tailored.RepProg.repSpec, MIPRE.Tailored.RepProg.repLen_lenIs,
  MIPRE.Tailored.RepProg.good_of_repLen, MIPRE.Tailored.RepProg.repLp_lpIs_iff,
  MIPRE.Tailored.Calls.mapCall_runs, MIPRE.Tailored.Calls.mapCall_inv

-- blueprint `lem:tailored-rep-programs-time`
#guard_sorry_free MIPRE.Tailored.RepProg.repLen_timeBound, MIPRE.Tailored.RepProg.repLp_timeBound,
  MIPRE.Tailored.RepProg.repLen_lenBound

-- blueprint `thm:tailored-rep`
#guard_sorry_free MIPRE.Tailored.tailoredRepetition

-- blueprint `prop:magic-square-zpc`
#guard_sorry_free MIPRE.Tailored.MagicSquare.game, MIPRE.Tailored.MagicSquare.obs,
  MIPRE.Tailored.MagicSquare.strategy, MIPRE.Tailored.MagicSquare.value_strategy,
  MIPRE.Tailored.MagicSquare.hasPerfectZPC, MIPRE.Tailored.MagicSquare.valStar_eq_one

-- blueprint `lem:canonical-decider`
#guard_sorry_free MIPRE.Tailored.canonProg_accepts,
  MIPRE.Tailored.TailoredVerifier.tgame_accepts_iff

-- blueprint `lem:of-tnfv`
#guard_sorry_free MIPRE.Tailored.TailoredVerifier.ofTNFV_accepts_iff,
  MIPRE.Tailored.TailoredVerifier.ofTNFV_game_D, MIPRE.Tailored.TailoredVerifier.valStar_ofTNFV,
  MIPRE.Tailored.TailoredVerifier.hasPerfectPCC_ofTNFV

-- blueprint `lem:tailored-dhalt-values`
#guard_sorry_free MIPRE.Tailored.Halting.lp_runs_iff,
  MIPRE.Tailored.Halting.hasPerfectZPC_of_branch1,
  MIPRE.Tailored.Halting.valStar_eq_zero_of_branch2, MIPRE.Tailored.Halting.hasPerfectZPC_iff_W,
  MIPRE.Tailored.Halting.valStar_eq_W, MIPRE.Tailored.TailoredVerifier.hasPerfectZPC_congr,
  MIPRE.Tailored.TailoredVerifier.valStar_congr,
  MIPRE.Tailored.TailoredVerifier.valStar_eq_zero_of_rejects

-- blueprint `lem:tailored-lambda`
#guard_sorry_free MIPRE.Tailored.Halting.esize_lpProg, MIPRE.Tailored.Halting.lp_cost,
  MIPRE.Tailored.Halting.exists_lp_cost_poly, MIPRE.Tailored.Halting.sampler_len_clauses,
  MIPRE.Tailored.Halting.lp_clause, MIPRE.Tailored.Halting.size_clause,
  MIPRE.Tailored.Halting.exists_lamBound, MIPRE.Tailored.Halting.Lam0,
  MIPRE.Tailored.Halting.Lam0_spec

-- blueprint `thm:tailored-halting-level`
#guard_sorry_free MIPRE.Tailored.Halting.halting_tailored,
  MIPRE.Tailored.Halting.halting_tailored_valStar, MIPRE.Tailored.Halting.hasPerfectZPC_of_halts,
  MIPRE.Tailored.Halting.valStar_le_of_not_halts, MIPRE.Tailored.Halting.A_step,
  MIPRE.Tailored.Halting.B_step

-- blueprint `lem:tailored-bridge`
#guard_sorry_free HaltingGameValue.SynchronousGame.toMIPRE,
  HaltingGameValue.SynchronousGame.toSyncStrategy, HaltingGameValue.SynchronousGame.ofSyncStrategy,
  HaltingGameValue.SynchronousGame.value_toSyncStrategy,
  HaltingGameValue.SynchronousGame.strategyValue_ofSyncStrategy,
  HaltingGameValue.SynchronousGame.gameValue_eq_syncValue,
  HaltingGameValue.SynchronousGame.gameValue_le_quantumValue,
  TailoredGameValue.TailoredGameData.syncGame, TailoredGameValue.TailoredGameData.game,
  TailoredGameValue.TailoredGameData.gameValue_le_quantumValue,
  TailoredGameValue.PermStrategy.isPVMIn_proj, TailoredGameValue.PermStrategy.toSync,
  TailoredGameValue.PermStrategy.value_toSync,
  TailoredGameValue.TailoredGameData.HasPerfectZPC.syncValue_eq_one,
  TailoredGameValue.TailoredGameData.HasPerfectZPC.gameValue_eq_one,
  TailoredGameValue.TailoredGameData.HasPerfectZPC.quantumValue_eq_one

-- blueprint `lem:tailored-conversion`
#guard_sorry_free TailoredGameValue.TailoredGameData.toGameData,
  TailoredGameValue.TailoredGameData.vecEquiv, TailoredGameValue.TailoredGameData.ansLenL,
  TailoredGameValue.TailoredGameData.acceptsN, TailoredGameValue.TailoredGameData.accN,
  TailoredGameValue.TailoredGameData.acceptsN_iff, TailoredGameValue.TailoredGameData.mem_accN,
  TailoredGameValue.TailoredGameData.quantumValue_toGameData,
  TailoredGameValue.TailoredGameData.primrec_toGameData

-- blueprint `lem:tailored-presents`
#guard_sorry_free MIPRE.Tailored.Presents.quantumValue_eq, MIPRE.Tailored.Presents.hasPerfectZPC,
  MIPRE.Tailored.Presents.accepts_iff, MIPRE.Tailored.Presents.value_padStrategy,
  MIPRE.quantumValue_congr_support, MIPRE.quantumValue_eq_of_equiv_support,
  MIPRE.Tailored.TailoredGame.quantumValue_doubled_eq_valStar,
  MIPRE.Tailored.TailoredGame.doubled_μ_self, MIPRE.Tailored.fourierProj_castLE,
  MIPRE.Tailored.fourierProj_eq_zero_of_one

-- blueprint `lem:tailored-tabulation`
#guard_sorry_free MIPRE.Tailored.primrec_tabOfT, MIPRE.Tailored.computable_tabT,
  MIPRE.Tailored.presents_tabOfT, MIPRE.Tailored.presents_tabT, MIPRE.Tailored.mu_tabOfT,
  MIPRE.Tailored.dimOf_eq_of, MIPRE.Tailored.margN_eq_of, MIPRE.Tailored.lenIs_lenRun,
  MIPRE.Tailored.lpIs_lpRun, MIPRE.Tailored.lenOf_eq_lenRun, MIPRE.Tailored.consOf_eq_lpRun

-- blueprint `lem:tailored-search`
#guard_sorry_free MIPRE.Tailored.Halting.quantumValue_tabT,
  MIPRE.Tailored.Halting.exists_searchProg, MIPRE.Tailored.Halting.search,
  MIPRE.Tailored.Halting.search_wellScoped, MIPRE.Tailored.Halting.search_spec

-- blueprint `thm:tailored-halting`
#guard_sorry_free MIPRE.Tailored.tailored_halting_reduction_of,
  MIPRE.Tailored.tailored_halting_reduction_quantum_of,
  MIPRE.Tailored.Halting.halting_tailored_search, MIPRE.Tailored.Halting.lamThreshold,
  MIPRE.Tailored.Halting.VT, MIPRE.Tailored.Halting.toData_F_code, MIPRE.Tailored.Halting.lpBuild,
  MIPRE.Tailored.Halting.lamOf, MIPRE.Tailored.Halting.descM, MIPRE.Tailored.Halting.gameOf,
  MIPRE.Tailored.Halting.presents_gameOf, MIPRE.Tailored.Halting.hasPerfectZPC_gameOf,
  MIPRE.Tailored.Halting.quantumValue_gameOf, MIPRE.Tailored.Halting.quantumValue_gameOf_le,
  MIPRE.Tailored.Halting.computable_gameOf

-- blueprint `thm:tmipstar-eq-re`
#guard_sorry_free MIPRE.Tailored.TMIPStarComputable.mipStar, MIPRE.Tailored.TMIPStarComputable.isRE,
  MIPRE.Tailored.re_subset_tmipStarComputable_of, MIPRE.Tailored.tmipStarComputable_eq_re_of

-- blueprint `lem:encoded-pvm-obs`
#guard_sorry_free MIPRE.Tailored.encObs, MIPRE.Tailored.encObs_mul_self,
  MIPRE.Tailored.commute_encObs, MIPRE.Tailored.star_encObs, MIPRE.Tailored.fourierFactor_encObs,
  MIPRE.Tailored.fourierProj_encObs, MIPRE.Tailored.commute_encObs_encObs,
  MIPRE.Tailored.encObs_merge, MIPRE.Tailored.encObs_extend

-- blueprint `lem:weyl-signed-perm`
#guard_sorry_free MIPRE.Tailored.sgn_eq_bitSign, MIPRE.Tailored.wX_eq_signedPermMatrix,
  MIPRE.Tailored.isSignedPerm_wX, MIPRE.Tailored.wZ_eq_diagonal_bitSign,
  MIPRE.Tailored.isSignedPerm_wZ, MIPRE.Tailored.isDiag_wZ, MIPRE.Tailored.trDotDual,
  MIPRE.Tailored.exists_trDotL_eq, MIPRE.Tailored.encObs_proj_trDot,
  MIPRE.Tailored.exists_encObs_proj_linear, MIPRE.Tailored.isSignedPerm_encObs_xProj,
  MIPRE.Tailored.isSignedPerm_encObs_zProj

-- blueprint `lem:controlled-signed-perm`
#guard_sorry_free MIPRE.Tailored.blockDiag, MIPRE.Tailored.isSignedPerm_blockDiag,
  MIPRE.Tailored.isDiag_blockDiag, MIPRE.Tailored.controlled_eq_blockDiag,
  MIPRE.Tailored.isSignedPerm_controlled, MIPRE.Tailored.isDiag_controlled,
  MIPRE.Tailored.encObs_controlled, MIPRE.Tailored.encObs_submatrix,
  MIPRE.Tailored.encObs_kronecker_one, MIPRE.Tailored.IsSignedPerm.kronecker_one,
  MIPRE.Tailored.IsSignedPerm.submatrix_equiv, MIPRE.Tailored.isDiag_submatrix_equiv,
  MIPRE.Tailored.isDiag_kronecker_one

-- blueprint `lem:binary-signed-perm`
#guard_sorry_free MIPRE.Tailored.univ_zmod_two, MIPRE.Tailored.observableSign_eq_bitSign,
  MIPRE.Tailored.encObs_observableToProjector,
  MIPRE.Tailored.encObs_observableToProjector_const, MIPRE.Tailored.pauliX_eq,
  MIPRE.Tailored.pauliZ_eq, MIPRE.Tailored.isSignedPerm_pauliX,
  MIPRE.Tailored.isSignedPerm_pauliZ, MIPRE.Tailored.isDiag_pauliZ,
  MIPRE.Tailored.isSignedPerm_grid

-- blueprint `lem:input-answer-bits`
#guard_sorry_free MIPRE.Tailored.PermStrategy.encObs_ansProj,
  MIPRE.Tailored.PermStrategy.encObs_ansProj_bit, MIPRE.Tailored.PermStrategy.encObs_ansProj_const

-- blueprint `lem:presentation-transport`
#guard_sorry_free MIPRE.SyncStrategy.isPVMIn, MIPRE.SyncStrategy.mul_eq_zero_of_value_eq_one,
  MIPRE.Tailored.valStar_le_of_dec, MIPRE.Tailored.permOfSync, MIPRE.Tailored.permOfSync_proj,
  MIPRE.Tailored.value_permOfSync, MIPRE.Tailored.hasPerfectZPC_of_sync

-- blueprint `lem:tailored-detyping`
#guard_sorry_free MIPRE.Tailored.accepts_eq_edgeOf, MIPRE.Tailored.TypedData.typeOf_of_edgeOf,
  MIPRE.Tailored.TypedData.detype_len_of_edgeOf,
  MIPRE.Tailored.TypedData.detype_accepts_iff_of_edgeOf,
  MIPRE.Tailored.TypedData.detype_accepts_of_edgeOf_none,
  MIPRE.Tailored.TypedData.decD_of_edgeOf, MIPRE.Tailored.TypedData.encD_of_edgeOf,
  MIPRE.Tailored.TypedData.detype_accepts_dec, MIPRE.Tailored.TypedData.detype_accepts_enc

-- blueprint `lem:intro-layout`
#guard_sorry_free MIPRE.Tailored.Intro.length_pad, MIPRE.Tailored.Intro.take_pad,
  MIPRE.Tailored.Intro.take_take_pad, MIPRE.Tailored.Intro.unpad_pad,
  MIPRE.Tailored.Intro.enc_pair, MIPRE.Tailored.Intro.dec_enc_pair,
  MIPRE.Tailored.Intro.dec_enc_read, MIPRE.Tailored.Intro.dec_enc_hide,
  MIPRE.Tailored.Intro.dec_enc_pauli, MIPRE.Tailored.Intro.length_enc_pair,
  MIPRE.Tailored.Intro.length_enc_read, MIPRE.Tailored.Intro.length_enc_hide,
  MIPRE.Tailored.Intro.length_enc_pauli, MIPRE.Tailored.Intro.dec_enc_of_ok,
  MIPRE.Tailored.Intro.length_enc_of_ok, MIPRE.Tailored.Intro.decB_enc_of_ok

-- blueprint `lem:presentation`
#guard_sorry_free MIPRE.Tailored.vecOf, MIPRE.Tailored.ofFn_vecOf, MIPRE.Tailored.presented,
  MIPRE.Tailored.okD, MIPRE.Tailored.encV, MIPRE.Tailored.length_encD_of_okD,
  MIPRE.Tailored.valStar_presented_le, MIPRE.Tailored.hasPerfectZPC_presented

-- blueprint `lem:canonical-decider-cost`
#guard_sorry_free MIPRE.Cost.Prog.pushProg_runs_le, MIPRE.Tailored.parseDIn,
  MIPRE.Tailored.parseDIn_encode, MIPRE.Tailored.canonProgT, MIPRE.Tailored.canonProgT_wellScoped,
  MIPRE.Tailored.canonProgT_runs_iff, MIPRE.Tailored.step_runs, MIPRE.Tailored.canonBound,
  MIPRE.Tailored.canonProgT_halts, MIPRE.Tailored.canonPoly, MIPRE.Tailored.canonBound_le,
  MIPRE.Tailored.dom_canonBound, MIPRE.Tailored.canonProgT_timeBound,
  MIPRE.Tailored.esize_canonProgT
-- blueprint `lem:class-sampler`
#guard_sorry_free MIPRE.Halting.SamplerFamily, MIPRE.Halting.SamplerFamily.sampProg,
  MIPRE.Halting.SamplerFamily.sampProg_runs, MIPRE.Halting.SamplerFamily.classSampler,
  MIPRE.Halting.SamplerFamily.classSampler_runs, MIPRE.Halting.SamplerFamily.Samples,
  MIPRE.Halting.SamplerFamily.samples_of_runs, MIPRE.Halting.SamplerFamily.questions_eq,
  MIPRE.Halting.SamplerFamily.qEmb, MIPRE.Halting.SamplerFamily.seedCount_eq,
  MIPRE.Halting.SamplerFamily.game_μ_qEmb, MIPRE.Halting.SamplerFamily.game_support

-- blueprint `lem:tmipstar-poly-sub`
#guard_sorry_free MIPRE.Tailored.TMIPStar.toComputable, MIPRE.Tailored.TMIPStar.isRE,
  MIPRE.Tailored.TPolyVerifier.tabP, MIPRE.Tailored.TPolyVerifier.computable_tabP,
  MIPRE.Tailored.TPolyVerifier.presents_tabP

-- blueprint `lem:tailored-extend`
#guard_sorry_free MIPRE.Tailored.TailoredGame.Extends,
  MIPRE.Tailored.TailoredGame.Extends.valStar_eq, MIPRE.Tailored.TailoredGame.Extends.hasPerfectZPC,
  MIPRE.Tailored.TailoredGame.Extends.doubled

-- blueprint `thm:tmipstar-poly-eq-re`
#guard_sorry_free MIPRE.Tailored.re_subset_tmipStar_of, MIPRE.Tailored.tmipStar_eq_re_of,
  MIPRE.Tailored.TailoredGapCompression.samplerFamily, MIPRE.Tailored.seqUniv_runs,
  MIPRE.Tailored.seqUniv_runs_rev, MIPRE.Tailored.Halting.classTV,
  MIPRE.Tailored.Halting.classTV_efficient, MIPRE.Tailored.Halting.lenIs_iff,
  MIPRE.Tailored.Halting.lpIs_iff, MIPRE.Tailored.Halting.tgame_extends,
  MIPRE.Tailored.Halting.classTV_values

-- blueprint `lem:intro-forms`
#guard_sorry_free MIPRE.Tailored.Intro.dotL, MIPRE.Tailored.Intro.dotL_eq_odd,
  MIPRE.Tailored.Intro.satisfies_iff_dotL, MIPRE.Tailored.Intro.dotL_append,
  MIPRE.Tailored.Intro.satisfies_append_iff, MIPRE.Tailored.Intro.place,
  MIPRE.Tailored.Intro.length_place, MIPRE.Tailored.Intro.dotL_place,
  MIPRE.Tailored.Intro.unit, MIPRE.Tailored.Intro.dotL_unit, MIPRE.Tailored.Intro.eqCons,
  MIPRE.Tailored.Intro.eqCons_iff, MIPRE.Tailored.Intro.guardCons,
  MIPRE.Tailored.Intro.guardCons_iff, MIPRE.Tailored.Intro.place2,
  MIPRE.Tailored.Intro.dotL_place2, MIPRE.Tailored.Intro.inputOf, MIPRE.Tailored.Intro.reindex,
  MIPRE.Tailored.Intro.dotL_split_right, MIPRE.Tailored.Intro.satisfies_reindex_iff

-- blueprint `lem:intro-register-cons`
#guard_sorry_free MIPRE.Tailored.Intro.dotL_toBits, MIPRE.Tailored.Intro.regForm,
  MIPRE.Tailored.Intro.dotL_regForm, MIPRE.Tailored.Intro.satisfies_regForms_iff,
  MIPRE.Tailored.Intro.projEqCons, MIPRE.Tailored.Intro.projEqCons_iff,
  MIPRE.Tailored.Intro.dualCons, MIPRE.Tailored.Intro.dualCons_iff

-- blueprint `lem:intro-pauli-cons`
#guard_sorry_free MIPRE.Tailored.Intro.LinCheck, MIPRE.Tailored.Intro.LinCheck.toCon,
  MIPRE.Tailored.Intro.satisfies_toCon_iff, MIPRE.Tailored.Intro.fldAt,
  MIPRE.Tailored.Intro.fieldChecks, MIPRE.Tailored.Intro.forall_fieldChecks_iff,
  MIPRE.Tailored.Intro.PauliCons.pairChecks, MIPRE.Tailored.Intro.PauliCons.pairChecks_iff,
  MIPRE.Tailored.Intro.PauliCons.pauliCons, MIPRE.Tailored.Intro.PauliCons.pauliCons_iff,
  MIPRE.Tailored.Intro.PauliCons.length_of_mem_pauliCons,
  MIPRE.Tailored.Intro.PauliCons.endpointValid_iff,
  MIPRE.Tailored.Intro.PauliCons.program_pauli_iff_cons

-- blueprint `lem:of-tnfvt`
#guard_sorry_free MIPRE.Cost.Prog.wrapHead_cost_at, MIPRE.Cost.Prog.wrapPre_cost_at,
  MIPRE.Cost.Prog.wrapCore_cost_at, MIPRE.Cost.Prog.esize_wrapCore,
  MIPRE.Tailored.TailoredVerifier.ofTNFVT,
  MIPRE.Tailored.TailoredVerifier.ofTNFVT_accepts_iff_ofTNFV,
  MIPRE.Tailored.TailoredVerifier.ofTNFVT_accepts_iff,
  MIPRE.Tailored.TailoredVerifier.ofTNFVT_game, MIPRE.Tailored.TailoredVerifier.ofTNFVT_game_D,
  MIPRE.Tailored.TailoredVerifier.valStar_ofTNFVT,
  MIPRE.Tailored.TailoredVerifier.hasPerfectPCC_ofTNFVT, MIPRE.Tailored.dom_wrapCoreCost,
  MIPRE.Tailored.dom_le_pow, MIPRE.Tailored.TailoredVerifier.ofTNFVT_isBounded

-- blueprint `lem:intro-pauli-hide`
#guard_sorry_free MIPRE.Tailored.Intro.PauliHide.answerBits_decodeBits_of_length,
  MIPRE.Tailored.Intro.PauliHide.pauliXProj, MIPRE.Tailored.Intro.PauliHide.pauliXProj_eq,
  MIPRE.Tailored.Intro.PauliHide.hideChecks, MIPRE.Tailored.Intro.PauliHide.hideChecks_iff,
  MIPRE.Tailored.Intro.PauliHide.pauliHideCons, MIPRE.Tailored.Intro.PauliHide.pauliHideConsRev,
  MIPRE.Tailored.Intro.PauliHide.pauliHideCons_iff,
  MIPRE.Tailored.Intro.PauliHide.pauliHideConsRev_iff

-- blueprint `lem:intro-aux-cons`
#guard_sorry_free MIPRE.Tailored.Intro.win, MIPRE.Tailored.Intro.win_take,
  MIPRE.Tailored.Intro.reg, MIPRE.Tailored.Intro.reg_eq_iff, MIPRE.Tailored.Intro.regEqCons_iff,
  MIPRE.Tailored.Intro.srcEqCons, MIPRE.Tailored.Intro.srcEqCons_iff, MIPRE.Tailored.Intro.auxLenR,
  MIPRE.Tailored.Intro.auxLen, MIPRE.Tailored.Intro.srcAns, MIPRE.Tailored.Intro.parsed,
  MIPRE.Tailored.Intro.srcFits, MIPRE.Tailored.Intro.sampleCons,
  MIPRE.Tailored.Intro.sampleCons_iff, MIPRE.Tailored.Intro.readCons,
  MIPRE.Tailored.Intro.readCons_iff, MIPRE.Tailored.Intro.hideReadCons,
  MIPRE.Tailored.Intro.hideReadCons_iff, MIPRE.Tailored.Intro.KerGens,
  MIPRE.Tailored.Intro.hideNextCons, MIPRE.Tailored.Intro.hideNextCons_iff,
  MIPRE.Tailored.Intro.sameCons, MIPRE.Tailored.Intro.sameCons_iff,
  MIPRE.Tailored.Intro.sourceCons, MIPRE.Tailored.Intro.sourceCons_iff,
  MIPRE.Tailored.Intro.swapCon, MIPRE.Tailored.Intro.satisfies_swapCon,
  MIPRE.Tailored.Intro.dirAux, MIPRE.Tailored.Intro.dirAux_iff, MIPRE.Tailored.Intro.auxPair,
  MIPRE.Tailored.Intro.auxPair_iff

-- blueprint `lem:intro-typed-cons`
#guard_sorry_free MIPRE.Tailored.Intro.Typed.prefixOK, MIPRE.Tailored.Intro.Typed.G,
  MIPRE.Tailored.Intro.Typed.pauliDir, MIPRE.Tailored.Intro.Typed.pauliAux,
  MIPRE.Tailored.Intro.Typed.consL, MIPRE.Tailored.Intro.Typed.lenR,
  MIPRE.Tailored.Intro.Typed.len, MIPRE.Tailored.Intro.Typed.parsedT,
  MIPRE.Tailored.Intro.Typed.readOK, MIPRE.Tailored.Intro.Typed.pauliAux_iff,
  MIPRE.Tailored.Intro.Typed.AcceptsAsInput, MIPRE.Tailored.Intro.Typed.hD_of_acceptsAsInput,
  MIPRE.Tailored.Intro.Typed.consL_iff

-- blueprint `lem:presentation-typed`
#guard_sorry_free MIPRE.Tailored.decodeQuestion_eq_some, MIPRE.Tailored.decodeQuestion_eq_none,
  MIPRE.Tailored.hasPerfectZPC_presented_typed

-- blueprint `lem:intro-presentation-sound`
#guard_sorry_free MIPRE.Tailored.Intro.Sound.tdata, MIPRE.Tailored.Intro.Sound.decT,
  MIPRE.Tailored.Intro.Sound.lenR_le_len, MIPRE.Tailored.Intro.Sound.guards_of_readOK,
  MIPRE.Tailored.Intro.Sound.pauliFormatted_parsedT, MIPRE.Tailored.Intro.Sound.tdata_sound,
  MIPRE.Tailored.Intro.Sound.H, MIPRE.Tailored.Intro.Sound.valStar_tpresented_le

-- blueprint `lem:intro-presentation-complete`
#guard_sorry_free MIPRE.Tailored.Intro.Complete.parsedT_enc,
  MIPRE.Tailored.Intro.Complete.length_encL, MIPRE.Tailored.Intro.Complete.encT,
  MIPRE.Tailored.Intro.Complete.okT, MIPRE.Tailored.Intro.Complete.tdata_complete,
  MIPRE.Tailored.Intro.Complete.hasPerfectZPC_tpresented

-- blueprint `lem:intro-kergens`
#guard_sorry_free MIPRE.Tailored.Intro.kernelGens, MIPRE.Tailored.Intro.kernelGens_correct,
  MIPRE.Tailored.Intro.linRows, MIPRE.Tailored.Intro.regKerGens,
  MIPRE.Tailored.Intro.kerGens_regKerGens

-- blueprint `lem:intro-output`
#guard_sorry_free MIPRE.Tailored.Intro.Output.quantumValue_H,
  MIPRE.Tailored.Intro.Output.valStar_presented_le_output, MIPRE.Tailored.Intro.Output.outTV,
  MIPRE.Tailored.Intro.Output.qe, MIPRE.Tailored.Intro.Output.IntroSpec,
  MIPRE.Tailored.Intro.Output.lenOf_eq_of, MIPRE.Tailored.Intro.Output.extends_presented,
  MIPRE.Tailored.Intro.Output.valStar_outTV_le, MIPRE.Tailored.Intro.Output.soundness_seven,
  MIPRE.Tailored.Intro.Output.hasPerfectZPC_outTV,
  MIPRE.Tailored.Intro.Output.acceptsAsInput_ofTNFVT, MIPRE.Tailored.Intro.Output.delta_mul_le,
  MIPRE.Tailored.Intro.Output.lenOf_le_of_isBounded,
  MIPRE.Tailored.Intro.Output.maxLen_le_of_isBounded,
  MIPRE.Tailored.Intro.Output.soundness_contract

end

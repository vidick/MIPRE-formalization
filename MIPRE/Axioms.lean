/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.CL.Basic
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
import MIPRE.TM.CookLevin.Sound
import MIPRE.LCS.MagicSquare.Strategy
import MIPRE.LCS.Strategy.Equivalence
import MIPRE.LCS.Strategy.ObservableToProjector
import MIPRE.TM.Code.Encoding.MachineCode
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

`#guard_sorry_free` below fails the build if any name it is given depends on `sorryAx`, and
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

open Lean Elab Command in
/-- `#guard_sorry_free a, b, c` fails the build if any of the named constants depends on
`sorryAx`. Used rather than `#guard_msgs in #print axioms` because it is insensitive to how
the axiom list is line-wrapped and to which of the standard axioms a proof happens to use:
three of the names below use only `propext` and `Quot.sound`, and one is axiom-free. -/
elab "#guard_sorry_free " ids:ident,* : command => do
  for id in ids.getElems do
    let n ← liftCoreM <| realizeGlobalConstNoOverload id
    let ax ← liftCoreM <| collectAxioms n
    if ax.contains ``sorryAx then
      throwErrorAt id "{n} depends on sorryAx, but the blueprint marks its proof \\leanok"

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

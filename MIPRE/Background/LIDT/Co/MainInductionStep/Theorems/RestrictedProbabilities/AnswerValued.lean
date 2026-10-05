/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
MainInductionStep/Theorems/RestrictedProbabilities/AnswerValued.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.MainInductionStep.Theorems.RestrictedProbabilities.Core
public import MIPRE.Background.LIDT.Co.MainInductionStep.Theorems.SelfImprovementAssembly.AnswerSlice
public import MIPRE.Background.LIDT.Co.MainInductionStep.Theorems.InductionParameterBounds.MainError

@[expose] public section

/-!
# Section 6 — Answer-valued restricted probability statement

The answer-valued form of the restricted-probability bookkeeping for the main induction step:
the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/MainInductionStep/Theorems/RestrictedProbabilities/AnswerValued.lean`
in the port of `planning/c6b-plan.md` (milestone M12, section "Port conventions").

## Translation

A strategy is a `SymStrat params.next 𝔓 K` or an `AnswerSymStrat params.next 𝔓 K`
(`Co/Test/StrategyCore.lean`), whose state is the symmetric model `strategy.state : SymModel 𝔓 K`;
the vendored `qBipartiteConsDefect strategy.state A B` and `bipartiteConsError strategy.state 𝒟 A B`
are `strategy.state.qBipartiteConsDefect A B` and `strategy.state.bipartiteConsError 𝒟 A B`, and
errors are real numbers (the vendored `Error := ℝ`). Every restriction keeps the state
(`xRestrictedAnswerSymStrat_state`, `xRestrictedAnswerSymStratOfAnswer_state`, by `rfl`), so each
restricted defect is a defect of `strategy.state`. The classical names (`mainInductionError`,
`sliceTransverseDirectionWeight`, `sliceConditioningLoss`, `weighted_bound_to_average`,
`weighted_embedded_average_le_full_average`, `avgOver_uniform_restrictedDiagonalSample_append`,
`one_le_k_of_mainInductionError_lt_one`, `mainInductionSuccessorBound_pred`) are the vendored
ones, imported through Co `RestrictedProbabilities/Base` and Co `InductionParameterBounds/MainError`
and reached through explicit `open` lists. No vendored statement here has a swap, density or
normalization hypothesis, so none is dropped. The vendored file-wide `respectTransparency false` is
not needed: the file sets no option.

## Two threaded hypotheses

`answerSuccessorRestrictedSliceConclusions` applies the predecessor
`AnswerMainInductionHypothesis` (Co `MainInductionStep/Statements.lean`), which quantifies only over
strategies whose model is a finite pair without abelian projections in its first player's
operators. So it takes, right after `strategy`, `hS : strategy.state.toBipartite.IsFinitePair` and
`hA : NoAbelianProj strategy.state.toBipartite.opsA`, and passes them unchanged to each slice
`xRestrictedAnswerSymStratOfAnswer params strategy x`, whose state is `strategy.state` by
definition. It does not take `1 ≤ params.d`: the hypothesis is applied, not proved, here. Its
universe binder is `AnswerMainInductionHypothesis.{uF, uP, uK}`, with `𝔓 : Type uP` and
`K : Type uK`, where the vendored one is `.{uF, uι}`. Every other declaration holds for any
symmetric model: restriction neither orthonormalizes nor solves a semidefinite program.

## Proofs that differ from the vendored ones

- The `try rfl` steps of the vendored file are `rfl` or gone, and its `calc` chains of
  `avgOver_congr` steps are `Eq.trans` and `avgOver_congr` terms.
- `AnswerRestrictedProbabilitiesStatement.ofWeightedBounds` and its answer-valued successor
  analogue rewrite the weighted bounds with `avgOver_const_mul`, as Co
  `RestrictedProbabilities/Core` does, in place of the vendored `simpa`.
- In `answerSuccessor_weighted_axisParallel_bound` the carrier's goodness is `hgood`'s
  axis-parallel and self-consistency fields, by definitional equality, with no `simpa`.
- `answerSuccessorRestrictedDiagonalSampleError_eq` uses the M12 lemma
  `restrictAnswerDiagonalAnswerMeasurement_postprocess_zero` (Co
  `SelfImprovementAssembly/AnswerSlice.lean`) and the appended-line identity
  `congrArg (DiagonalLine.mk _) hdir`, as Co `RestrictedProbabilities/Diagonal` does, in place of
  the vendored unfolding `simp`.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/inductive_step.tex`
- `blueprint/src/chapter/ch10_induction.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.MainInductionStep

open MIPStarRE.LDT (Parameters FieldModel Fq zeroCoord appendPoint embedCoord avgOver
  avgOver_congr avgOver_const_mul avgOver_uniform_comm avgOver_uniform_prod uniformDistribution
  DiagonalLine DiagonalLinePolynomial DiagonalLineAnswer RestrictedDiagonalSample
  extendRestrictedDirection)
open MIPStarRE.LDT.MainInductionStep (mainInductionError sliceTransverseDirectionWeight
  sliceConditioningLoss weighted_bound_to_average weighted_embedded_average_le_full_average
  avgOver_uniform_restrictedDiagonalSample_append one_le_k_of_mainInductionError_lt_one
  mainInductionSuccessorBound_pred)
open MIPRE.LIDT.Co (SymStrat AnswerSymStrat)

universe uF uP uK

variable {𝔓 : Type uP} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type uK} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The answer-valued slice has the same axis-parallel failure probability as the
legacy restricted slice. -/
theorem answerRestricted_axisParallelFailureProbability_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (x : Fq params) :
    (xRestrictedAnswerSymStrat params strategy x).axisParallelFailureProbability =
      (xRestrictedStrategy params strategy x).axisParallelFailureProbability :=
  rfl

/-- The answer-valued slice has the same self-consistency failure probability as
the legacy restricted slice. -/
theorem answerRestricted_selfConsistencyFailureProbability_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (x : Fq params) :
    (xRestrictedAnswerSymStrat params strategy x).selfConsistencyFailureProbability =
      (xRestrictedStrategy params strategy x).selfConsistencyFailureProbability :=
  rfl

/-- The answer-valued slice has the same verifier-visible diagonal failure
probability as the legacy restricted slice after evaluating line answers at the
base point. -/
theorem answerRestricted_diagonalFailureProbability_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (x : Fq params) :
    (xRestrictedAnswerSymStrat params strategy x).diagonalFailureProbability =
      (xRestrictedStrategy params strategy x).diagonalFailureProbability := by
  unfold AnswerSymStrat.diagonalFailureProbability RestrictedSymStrat.diagonalFailureProbability
  refine congrArg (fun s => (1 / (params.m : ℝ)) * s) (Finset.sum_congr rfl fun j _ => ?_)
  refine congrArg (strategy.state.bipartiteConsError _ _) (funext fun s => ?_)
  let ℓ : DiagonalLine params :=
    { base := s.1, direction := extendRestrictedDirection j s.2 }
  change
    postprocess ((restrictDiagonalAnswerMeasurement params strategy x ℓ).toSubMeas)
        (fun f : DiagonalLineAnswer params => f zeroCoord) =
      postprocess ((restrictDiagonalMeasurement params strategy x ℓ).toSubMeas)
        (fun f : DiagonalLinePolynomial params => f zeroCoord)
  exact (restrictDiagonalAnswerMeasurement_postprocess_zero params strategy x ℓ).trans
    (restrictDiagonalMeasurement_postprocess_zero params strategy x ℓ).symm

/-- The weighted average of the answer-valued restricted axis-parallel slice errors
is bounded by the ambient axis-parallel test error. -/
theorem answer_weighted_axisParallel_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma) :
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceTransverseDirectionWeight params *
          (xRestrictedAnswerSymStrat params strategy x).axisParallelFailureProbability) ≤
      eps :=
  weighted_axisParallel_bound params strategy eps delta gamma hgood

/-- The weighted average of the answer-valued restricted diagonal slice errors is
bounded by the ambient diagonal-line test error. -/
theorem answer_weighted_diagonal_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma) :
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceTransverseDirectionWeight params *
          (xRestrictedAnswerSymStrat params strategy x).diagonalFailureProbability) ≤ gamma :=
  le_of_eq_of_le
    (avgOver_congr _ _ _ fun x =>
      congrArg (sliceTransverseDirectionWeight params * ·)
        (answerRestricted_diagonalFailureProbability_eq params strategy x))
    (weighted_diagonal_bound params strategy eps delta gamma hgood)

/-- Data answer-valued weighted restricted axis/diagonal bounds into the public
answer-valued restricted-probabilities statement. -/
theorem AnswerRestrictedProbabilitiesStatement.ofWeightedBounds
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (haxisWeightedBound :
      avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedAnswerSymStrat params strategy x).axisParallelFailureProbability) ≤ eps)
    (hdiagonalWeightedBound :
      avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedAnswerSymStrat params strategy x).diagonalFailureProbability) ≤ gamma) :
    AnswerRestrictedProbabilitiesStatement params strategy eps delta gamma := by
  let profile : AnswerRestrictedFailureProfile params strategy :=
    { axisParallel := fun x =>
        (xRestrictedAnswerSymStrat params strategy x).axisParallelFailureProbability
      selfConsistency := fun x =>
        (xRestrictedAnswerSymStrat params strategy x).selfConsistencyFailureProbability
      diagonal := fun x =>
        (xRestrictedAnswerSymStrat params strategy x).diagonalFailureProbability
      restrictedGood := fun _ => ⟨le_rfl, le_rfl, le_rfl⟩ }
  rw [avgOver_const_mul] at haxisWeightedBound hdiagonalWeightedBound
  refine ⟨profile, weighted_bound_to_average params haxisWeightedBound, ?_,
    weighted_bound_to_average params hdiagonalWeightedBound⟩
  exact (selfConsistencyRestrictedAverage_eq params strategy).trans_le
    hgood.selfConsistencyTest

/-- Answer-valued version of `lem:restricted-probabilities`. -/
theorem answerRestrictedProbabilities
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma) :
    AnswerRestrictedProbabilitiesStatement params strategy eps delta gamma :=
  AnswerRestrictedProbabilitiesStatement.ofWeightedBounds
    params strategy eps delta gamma hgood
    (answer_weighted_axisParallel_bound params strategy eps delta gamma hgood)
    (answer_weighted_diagonal_bound params strategy eps delta gamma hgood)

/-! ### Answer-valued successor restrictions

The preceding lemmas start from an ordinary successor strategy and build the
answer-valued slice profile used in the current Section 6 successor route.  For
the simultaneous answer-valued induction theorem, the successor strategy itself
has answer-valued diagonal measurements.  The next definitions and lemmas
record the corresponding restricted-probability theorem without replacing that
diagonal measurement by an ordinary low-degree realization.
-/

/-- Slice-wise error profile obtained by restricting an answer-valued successor
strategy.

This is the answer-valued analogue of `AnswerRestrictedFailureProfile`, but
with source strategy `AnswerSymStrat params.next 𝔓 K` and slices
`xRestrictedAnswerSymStratOfAnswer`. -/
structure AnswerSuccessorRestrictedFailureProfile (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next 𝔓 K) : Type where
  /-- The axis-parallel failure bound attached to each slice height. -/
  axisParallel : Fq params → ℝ
  /-- The self-consistency failure bound attached to each slice height. -/
  selfConsistency : Fq params → ℝ
  /-- The diagonal-line failure bound attached to each slice height. -/
  diagonal : Fq params → ℝ
  /-- Each answer-valued slice is good with the recorded parameters. -/
  restrictedGood :
    ∀ x,
      (xRestrictedAnswerSymStratOfAnswer params strategy x).IsGood
        (axisParallel x)
        (selfConsistency x)
        (diagonal x)

/-- Average restricted axis-parallel error over answer-valued successor slices. -/
noncomputable def averageAnswerSuccessorRestrictedAxisParallelError
    (params : Parameters)
    [FieldModel params.q]
    {strategy : AnswerSymStrat params.next 𝔓 K}
    (profile : AnswerSuccessorRestrictedFailureProfile params strategy) : ℝ :=
  avgOver (uniformDistribution (Fq params)) profile.axisParallel

/-- Average restricted self-consistency error over answer-valued successor slices. -/
noncomputable def averageAnswerSuccessorRestrictedSelfConsistencyError
    (params : Parameters)
    [FieldModel params.q]
    {strategy : AnswerSymStrat params.next 𝔓 K}
    (profile : AnswerSuccessorRestrictedFailureProfile params strategy) : ℝ :=
  avgOver (uniformDistribution (Fq params)) profile.selfConsistency

/-- Average restricted diagonal-line error over answer-valued successor slices. -/
noncomputable def averageAnswerSuccessorRestrictedDiagonalError
    (params : Parameters)
    [FieldModel params.q]
    {strategy : AnswerSymStrat params.next 𝔓 K}
    (profile : AnswerSuccessorRestrictedFailureProfile params strategy) : ℝ :=
  avgOver (uniformDistribution (Fq params)) profile.diagonal

/-- Restricted-probabilities statement for an answer-valued successor strategy.

This is a Lean-only statement needed for the simultaneous answer-valued
induction route.  It has the same three averaged conclusions as the restricted
probabilities lemma (`\label{lem:restricted-probabilities}`), with
`xRestrictedAnswerSymStratOfAnswer` as the slice strategy. -/
structure AnswerSuccessorRestrictedProbabilitiesStatement (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ) : Prop where
  /-- There is a slice-wise answer-valued error profile realizing the three
  averaged restricted bounds. -/
  profileExists :
    ∃ profile : AnswerSuccessorRestrictedFailureProfile params strategy,
      averageAnswerSuccessorRestrictedAxisParallelError params profile ≤
          sliceConditioningLoss params * eps ∧
        averageAnswerSuccessorRestrictedSelfConsistencyError params profile ≤ delta ∧
        averageAnswerSuccessorRestrictedDiagonalError params profile ≤
          sliceConditioningLoss params * gamma

/-- The weighted average of the answer-valued successor restricted
axis-parallel slice errors is bounded by the ambient answer-valued
axis-parallel test error. -/
theorem answerSuccessor_weighted_axisParallel_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma) :
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceTransverseDirectionWeight params *
          (xRestrictedAnswerSymStratOfAnswer params strategy x).axisParallelFailureProbability)
      ≤ eps :=
  let carrier := answerSelfImprovementCarrier params.next strategy
  have hcarrier_good : carrier.IsGood eps delta carrier.diagonalFailureProbability :=
    ⟨hgood.axisParallelTest, hgood.selfConsistencyTest, le_rfl⟩
  answer_weighted_axisParallel_bound params carrier eps delta
    carrier.diagonalFailureProbability hcarrier_good

/-- Averaging the self-consistency defect over answer-valued successor
restrictions recovers the ambient answer-valued self-consistency defect. -/
theorem answerSuccessor_selfConsistencyRestrictedAverage_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next 𝔓 K) :
    avgOver (uniformDistribution (Fq params))
        (fun x =>
          (xRestrictedAnswerSymStratOfAnswer params strategy x).selfConsistencyFailureProbability) =
      strategy.selfConsistencyFailureProbability :=
  selfConsistencyRestrictedAverage_eq params (answerSelfImprovementCarrier params.next strategy)

/-- The `j`-restricted diagonal defect of the `x`-restricted answer-valued successor slice at
the sample `s` is the ambient defect at the embedded index and the sample with the height
appended to its base. -/
theorem answerSuccessorRestrictedDiagonalSampleError_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next 𝔓 K)
    (x : Fq params)
    (j : Fin params.m)
    (s : RestrictedDiagonalSample params j) :
    strategy.state.qBipartiteConsDefect
      (AnswerSymStrat.diagonalPointAnswerFamily
        (xRestrictedAnswerSymStratOfAnswer params strategy x) j s)
      (AnswerSymStrat.diagonalLineAnswerFamily
        (xRestrictedAnswerSymStratOfAnswer params strategy x) j s) =
    strategy.state.qBipartiteConsDefect
      (AnswerSymStrat.diagonalPointAnswerFamily strategy (embedCoord params j)
        (appendPoint params s.1 x, s.2))
      (AnswerSymStrat.diagonalLineAnswerFamily strategy (embedCoord params j)
        (appendPoint params s.1 x, s.2)) := by
  have hdir :
      appendPoint params (extendRestrictedDirection j s.2) zeroCoord =
        extendRestrictedDirection (params := params.next) (embedCoord params j) s.2 := by
    funext k
    by_cases hkm : k.1 < params.m
    · by_cases hk : k.1 ≤ j.1
      · simp [appendPoint, extendRestrictedDirection, embedCoord, hkm, hk]
      · simp [appendPoint, extendRestrictedDirection, embedCoord, hkm, hk]
        rfl
    · have hnotle : ¬ k.1 ≤ j.1 := fun hk => hkm (lt_of_le_of_lt hk j.2)
      simp [appendPoint, extendRestrictedDirection, embedCoord, hkm, hnotle]
      rfl
  have hline :
      DiagonalLine.appendAtHeight params
          { base := s.1, direction := extendRestrictedDirection j s.2 } x =
        ({ base := appendPoint params s.1 x,
           direction :=
             extendRestrictedDirection (params := params.next) (embedCoord params j) s.2 } :
          DiagonalLine params.next) :=
    congrArg (DiagonalLine.mk _) hdir
  refine congrArg (strategy.state.qBipartiteConsDefect _) ?_
  refine (restrictAnswerDiagonalAnswerMeasurement_postprocess_zero params strategy x _).trans ?_
  rw [hline]
  rfl

/-- Per-index diagonal-line consistency defect of the `x`-restricted answer-valued successor
slice at index `j`, averaged over the restricted diagonal sample space. -/
noncomputable def answerSuccessorDiagonalSliceIndexError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next 𝔓 K)
    (x : Fq params)
    (j : Fin params.m) : ℝ :=
  strategy.state.bipartiteConsError
    (uniformDistribution (RestrictedDiagonalSample params j))
    (AnswerSymStrat.diagonalPointAnswerFamily
      (xRestrictedAnswerSymStratOfAnswer params strategy x) j)
    (AnswerSymStrat.diagonalLineAnswerFamily
      (xRestrictedAnswerSymStratOfAnswer params strategy x) j)

/-- Per-index diagonal-line consistency defect of the ambient answer-valued successor strategy
at index `j`, averaged over the ambient restricted diagonal sample space. -/
noncomputable def answerSuccessorDiagonalIndexError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next 𝔓 K)
    (j : Fin params.next.m) : ℝ :=
  strategy.state.bipartiteConsError
    (uniformDistribution (RestrictedDiagonalSample params.next j))
    (AnswerSymStrat.diagonalPointAnswerFamily strategy j)
    (AnswerSymStrat.diagonalLineAnswerFamily strategy j)

/-- Averaging the restricted per-index diagonal error of the answer-valued successor slices
over the slice height gives the ambient per-index error at the embedded index. -/
theorem answerSuccessorDiagonalSliceIndexErrorAverage_eq_diagonalIndexError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next 𝔓 K)
    (j : Fin params.m) :
    avgOver (uniformDistribution (Fq params))
      (fun x => answerSuccessorDiagonalSliceIndexError params strategy x j) =
      answerSuccessorDiagonalIndexError params strategy (embedCoord params j) := by
  let g : RestrictedDiagonalSample params.next (embedCoord params j) → ℝ := fun s =>
    strategy.state.qBipartiteConsDefect
      (AnswerSymStrat.diagonalPointAnswerFamily strategy (embedCoord params j) s)
      (AnswerSymStrat.diagonalLineAnswerFamily strategy (embedCoord params j) s)
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => answerSuccessorDiagonalSliceIndexError params strategy x j)
      = avgOver (uniformDistribution (Fq params))
          (fun x => avgOver (uniformDistribution (RestrictedDiagonalSample params j))
            (fun s => g (appendPoint params s.1 x, s.2))) :=
        avgOver_congr _ _ _ fun x => avgOver_congr _ _ _ fun s =>
          answerSuccessorRestrictedDiagonalSampleError_eq params strategy x j s
    _ = avgOver (uniformDistribution (Fq params × RestrictedDiagonalSample params j))
          (fun xs => g (appendPoint params xs.2.1 xs.1, xs.2.2)) :=
        (avgOver_uniform_prod (α := Fq params) (β := RestrictedDiagonalSample params j)
          (fun x s => g (appendPoint params s.1 x, s.2))).symm
    _ = answerSuccessorDiagonalIndexError params strategy (embedCoord params j) :=
        avgOver_uniform_restrictedDiagonalSample_append params j g

/-- The average over slice heights of the answer-valued successor slices' diagonal failure
probability is the average over embedded indices of the ambient per-index error. -/
theorem answerSuccessorAverageRestrictedDiagonalFailure_eq_embeddedDiagonalIndices
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next 𝔓 K) :
    avgOver (uniformDistribution (Fq params))
      (fun x => (xRestrictedAnswerSymStratOfAnswer params strategy x).diagonalFailureProbability) =
    avgOver (uniformDistribution (Fin params.m))
      (fun j => answerSuccessorDiagonalIndexError params strategy (embedCoord params j)) := by
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => (xRestrictedAnswerSymStratOfAnswer params strategy x).diagonalFailureProbability)
      = avgOver (uniformDistribution (Fq params))
          (fun x => avgOver (uniformDistribution (Fin params.m))
            (fun j => answerSuccessorDiagonalSliceIndexError params strategy x j)) := by
        refine avgOver_congr _ _ _ fun x => ?_
        simp [AnswerSymStrat.diagonalFailureProbability, avgOver, uniformDistribution,
          Fintype.card_fin, answerSuccessorDiagonalSliceIndexError, Finset.mul_sum]
    _ = avgOver (uniformDistribution (Fin params.m))
          (fun j => avgOver (uniformDistribution (Fq params))
            (fun x => answerSuccessorDiagonalSliceIndexError params strategy x j)) :=
        avgOver_uniform_comm (fun x j => answerSuccessorDiagonalSliceIndexError params strategy x j)
    _ = avgOver (uniformDistribution (Fin params.m))
          (fun j => answerSuccessorDiagonalIndexError params strategy (embedCoord params j)) :=
        avgOver_congr _ _ _ fun j =>
          answerSuccessorDiagonalSliceIndexErrorAverage_eq_diagonalIndexError params strategy j

/-- The weighted average of the answer-valued successor restricted diagonal
slice errors is bounded by the ambient answer-valued diagonal-line test error. -/
theorem answerSuccessor_weighted_diagonal_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma) :
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceTransverseDirectionWeight params *
          (xRestrictedAnswerSymStratOfAnswer params strategy x).diagonalFailureProbability)
      ≤ gamma := by
  rw [avgOver_const_mul,
    answerSuccessorAverageRestrictedDiagonalFailure_eq_embeddedDiagonalIndices params strategy]
  refine (weighted_embedded_average_le_full_average params
    (answerSuccessorDiagonalIndexError params strategy)
    fun j => strategy.state.bipartiteConsError_nonneg _ _ _).trans ?_
  refine le_of_eq_of_le ?_ hgood.diagonalLineTest
  simp [AnswerSymStrat.diagonalFailureProbability, answerSuccessorDiagonalIndexError, avgOver,
    uniformDistribution, Fintype.card_fin, Finset.mul_sum]

/-- Assemble the weighted answer-valued successor restricted-probability bounds
into the averaged statement. -/
theorem AnswerSuccessorRestrictedProbabilitiesStatement.ofWeightedBounds
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (haxisWeightedBound :
      avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedAnswerSymStratOfAnswer params strategy x).axisParallelFailureProbability)
        ≤ eps)
    (hdiagonalWeightedBound :
      avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedAnswerSymStratOfAnswer params strategy x).diagonalFailureProbability)
        ≤ gamma) :
    AnswerSuccessorRestrictedProbabilitiesStatement params strategy eps delta gamma := by
  let profile : AnswerSuccessorRestrictedFailureProfile params strategy :=
    { axisParallel := fun x =>
        (xRestrictedAnswerSymStratOfAnswer params strategy x).axisParallelFailureProbability
      selfConsistency := fun x =>
        (xRestrictedAnswerSymStratOfAnswer params strategy x).selfConsistencyFailureProbability
      diagonal := fun x =>
        (xRestrictedAnswerSymStratOfAnswer params strategy x).diagonalFailureProbability
      restrictedGood := fun _ => ⟨le_rfl, le_rfl, le_rfl⟩ }
  rw [avgOver_const_mul] at haxisWeightedBound hdiagonalWeightedBound
  refine ⟨profile, weighted_bound_to_average params haxisWeightedBound, ?_,
    weighted_bound_to_average params hdiagonalWeightedBound⟩
  exact (answerSuccessor_selfConsistencyRestrictedAverage_eq params strategy).trans_le
    hgood.selfConsistencyTest

/-- Answer-valued restricted-probabilities theorem for an answer-valued
successor strategy.

This is the restricted-probability input needed by a simultaneous
answer-valued proof of the main induction theorem.  It is a construction from
the answer-valued successor strategy's own goodness hypotheses, not an
additional theorem assumption. -/
theorem answerSuccessorRestrictedProbabilities
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma) :
    AnswerSuccessorRestrictedProbabilitiesStatement params strategy eps delta gamma :=
  AnswerSuccessorRestrictedProbabilitiesStatement.ofWeightedBounds
    params strategy eps delta gamma hgood
    (answerSuccessor_weighted_axisParallel_bound params strategy eps delta gamma hgood)
    (answerSuccessor_weighted_diagonal_bound params strategy eps delta gamma hgood)

/-- Recursive predecessor conclusions for the answer-valued successor slices.

Paper origin: `references/ldt-paper/inductive_step.tex:441-454`, in the
answer-valued successor interface used by the simultaneous induction route.

This theorem is the formal content of the recursive call: from the
answer-valued restricted-probabilities theorem and the predecessor
answer-valued induction hypothesis, it obtains the main-induction conclusion
for every restricted slice.  The hypotheses `k ≥ 1` and
`400 * params.m * params.d ≤ k` are derived here from the nontrivial
successor branch, rather than being stored in a source theorem statement. The model
hypotheses `hS hA`, which the predecessor hypothesis requires of each slice, pass to the slices
unchanged, a slice having the ambient state. -/
theorem answerSuccessorRestrictedSliceConclusions
    (params : Parameters)
    [FieldModel.{uF} params.q]
    (strategy : AnswerSymStrat params.next 𝔓 K)
    (hS : strategy.state.toBipartite.IsFinitePair)
    (hA : NoAbelianProj strategy.state.toBipartite.opsA)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hinduction : AnswerMainInductionHypothesis.{uF, uP, uK} params)
    (hk_next : 400 * params.next.m * params.next.d ≤ k)
    (hsmall : mainInductionError params.next k eps delta gamma < 1) :
    ∃ profile : AnswerSuccessorRestrictedFailureProfile params strategy,
      averageAnswerSuccessorRestrictedAxisParallelError params profile ≤
          sliceConditioningLoss params * eps ∧
        averageAnswerSuccessorRestrictedSelfConsistencyError params profile ≤ delta ∧
        averageAnswerSuccessorRestrictedDiagonalError params profile ≤
          sliceConditioningLoss params * gamma ∧
        ∀ x,
          AnswerMainInductionConclusion params
            (xRestrictedAnswerSymStratOfAnswer params strategy x)
            (profile.axisParallel x)
            (profile.selfConsistency x)
            (profile.diagonal x)
            k := by
  obtain ⟨profile, haxisAverage, hselfAverage, hdiagonalAverage⟩ :=
    (answerSuccessorRestrictedProbabilities params strategy eps delta gamma hgood).profileExists
  have hk_pos : 1 ≤ k :=
    one_le_k_of_mainInductionError_lt_one params.next k eps delta gamma hsmall
  have hk_pred : 400 * params.m * params.d ≤ k :=
    mainInductionSuccessorBound_pred params hk_next
  exact ⟨profile, haxisAverage, hselfAverage, hdiagonalAverage, fun x =>
    hinduction 𝔓 K (xRestrictedAnswerSymStratOfAnswer params strategy x)
      (profile.axisParallel x) (profile.selfConsistency x) (profile.diagonal x)
      k hS hA (profile.restrictedGood x) hk_pos hk_pred⟩

end MIPRE.LIDT.Co.MainInductionStep

end

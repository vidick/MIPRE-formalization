/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
MainInductionStep/Theorems/PastingAssembly/AnswerFields.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.MainInductionStep.Theorems.PastingAssembly.Basic

@[expose] public section

/-!
# Section 6 — Pasting Assembly: Answer-Valued Fields

The answer-valued averaged family fields of the successor route, and the two assemblies that
feed them to pasting: the induction-section pasting from an explicit commutativity input, and
that commutativity input itself, for the point-equivalent ordinary carrier. This is the
counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/MainInductionStep/Theorems/PastingAssembly/AnswerFields.lean`
in the port of `planning/c6b-plan.md` (milestone M12, section "Port conventions").

## Translation

A strategy is an `AnswerSymStrat params.next 𝔓 K` (`Co/Test/StrategyCore.lean`), whose state is
the symmetric model `strategy.state : SymModel 𝔓 K`; its point-equivalent ordinary carrier is Co
`answerSelfImprovementCarrier`, a `SymStrat params.next 𝔓 K` with the same state.
`IdxPolyFamily params ι` is `IdxPolyFamily params 𝔓`, `Error` is `ℝ`, and the relations
(`ConsRel`, and the `SDDOpRel` behind `answerCommutativityPoints`) are read on
`strategy.state`. The error functions (`mainInductionError`, `mainInductionNu`,
`selfImprovementInInductionError`, `ldPastingInInductionError`, `ldPastingInInductionNu`) are
the vendored classical declarations, reached through explicit `open` lists. The vendored file-wide
`respectTransparency false` is not needed: the file sets no option.

## Dropped and threaded hypotheses

No vendored statement here has a swap, density or normalization hypothesis. The vendored proof
of `answerComMainForCarrier_ofAnswerGood` passes `carrier.isNormalized` to
`comMain_of_commutativityPoints`, whose Co counterpart takes no normalization argument.

`answerSuccessorAveragedFamilyFields_ofMainInductionHypothesis` runs Co
`answerSuccessorSelfImprovementOutputs_ofMainInductionHypothesis`, which takes the model
hypotheses `hS : strategy.state.toBipartite.IsFinitePair` and
`hA : NoAbelianProj strategy.state.toBipartite.opsA` of the predecessor
`AnswerMainInductionHypothesis` and `hd : 1 ≤ params.d` of the ported self-improvement theorem;
so it takes `hS hA hd` right after `strategy`, in the same position. Its induction hypothesis is
`AnswerMainInductionHypothesis.{uF, uP, uK}`, where the vendored one is `.{uF, uι'}`, and its
universe binder is `.{uF}` where the vendored one is `.{uι', uF}`, `𝔓` and `K` being the file's
variables, as in Co `StageDataConstructors`. The two pasting
assemblies take no new hypothesis: pasting neither orthonormalizes nor solves a semidefinite
program.

## Proofs that differ from the vendored ones

- The carrier `answerSelfImprovementCarrier params.next strategy` has the state, the point
  measurement and the axis-parallel measurement of `strategy`, so its axis-parallel and
  self-consistency failure probabilities, its completeness, consistency, strong
  self-consistency, its tensor failure expectations and the products of its point measurements
  are those of `strategy` by definitional equality: the vendored `simpa [carrier,
  answerSelfImprovementCarrier]` transfers and the `unfold … ; simp` failure-probability
  identities are dropped, the hypotheses being passed directly.
- In `answerSuccessorAveragedFamilyFields_ofMainInductionHypothesis` the four family fields are
  the Co `PastingAssembly/Basic` lemmas applied to the slice outputs as they stand, with no
  `simpa`, and the bound on `κ` is one `linarith`.
- `answerComMainForCarrier_ofAnswerGood` is one term: Co `comMain_of_commutativityPoints` on the
  carrier, applied to Co `answerCommutativityPoints` with no `change`.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/inductive_step.tex`
- `blueprint/src/chapter/ch10_induction.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.MainInductionStep

open MIPStarRE.LDT (Parameters FieldModel Point Fq uniformDistribution avgOver)
open MIPStarRE.LDT.MainInductionStep (mainInductionError mainInductionNu
  selfImprovementInInductionError ldPastingInInductionError ldPastingInInductionNu)
open MIPRE.LIDT.Co (AnswerSymStrat)

universe uP uK

variable {𝔓 : Type uP} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type uK} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Assemble the averaged polynomial family fields in the answer-valued
successor route.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551`.
The statement records exactly the conclusions obtained from the recursive
answer-valued slice measurements and the axis-parallel/self-consistency
self-improvement theorem: averaged completeness, point consistency with the
ambient answer-valued point measurement, strong self-consistency, the
slice-boundedness input for the point-equivalent ordinary carrier, and the two
scalar estimates for `κ` and `ζ`.

**Lean-only:** The final boundedness field is expressed using
`answerSelfImprovementCarrier` only because the present boundedness interface is
typed for ordinary strategies.  This theorem does not invoke
`ldPastingInInductionSection`, and does not assert that the carrier's dummy
diagonal measurement satisfies the answer-valued diagonal-line test.  This
internal construction is tracked in issue #1507.  Discharge: proved here from
the recursive answer-valued slice measurements and the answer-valued
self-improvement construction. The model hypotheses `hS hA` and `hd : 1 ≤ params.d` are those
of the self-improvement outputs (module docstring). -/
theorem answerSuccessorAveragedFamilyFields_ofMainInductionHypothesis.{uF}
    (params : Parameters)
    [FieldModel.{uF} params.q]
    (strategy : AnswerSymStrat params.next 𝔓 K)
    (hS : strategy.state.toBipartite.IsFinitePair)
    (hA : NoAbelianProj strategy.state.toBipartite.opsA)
    (hd : 1 ≤ params.d)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hinduction : AnswerMainInductionHypothesis.{uF, uP, uK} params)
    (hk_next : 400 * params.next.m * params.next.d ≤ k)
    (hsmall : mainInductionError params.next k eps delta gamma < 1) :
    ∃ family : IdxPolyFamily params 𝔓,
      ∃ kappa : ℝ,
        family.Complete strategy.state kappa ∧
          strategy.state.ConsRel (uniformDistribution (Point params.next))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
            (IdxPolyFamily.evaluatedAtNextPoint family)
            (selfImprovementInInductionError params.next eps delta gamma) ∧
          family.StronglySelfConsistent strategy.state
            (selfImprovementInInductionError params.next eps delta gamma) ∧
          IdxPolyFamily.SliceBoundednessInput
            (answerSelfImprovementCarrier params.next strategy)
            family
            (selfImprovementInInductionError params.next eps delta gamma) ∧
          kappa ≤
            ((params.m : ℝ) ^ (2 : ℕ)) *
                (mainInductionNu params.next k eps delta gamma +
                  Real.exp (-((k : ℝ) / (80000 * ((params.m : ℝ) ^ (2 : ℕ))))))
              + selfImprovementInInductionError params.next eps delta gamma ∧
          selfImprovementInInductionError params.next eps delta gamma ≤
            mainInductionNu params.next k eps delta gamma := by
  obtain ⟨profile, sliceError, -, sliceProj, sliceWitness, -, -, -, -, -, havgSigma, havgZeta,
      hcompleteSlice, hpointSlice, -, hselfCloseSlice, hboundedSlice, hdomSlice⟩ :=
    answerSuccessorSelfImprovementOutputs_ofMainInductionHypothesis
      params strategy hS hA hd eps delta gamma k hgood hinduction hk_next hsmall
  let sliceSelfError : Fq params → ℝ := fun x =>
    selfImprovementInInductionError params
      (profile.axisParallel x) (profile.selfConsistency x) (profile.diagonal x)
  let family : IdxPolyFamily params 𝔓 :=
    { meas := sliceProj
      witness := sliceWitness
      dominationTarget := fun x h =>
        IdxPolyFamily.averagedSlicePointEvaluationOperator
          (answerSelfImprovementCarrier params.next strategy) x h }
  refine ⟨family,
    avgOver (uniformDistribution (Fq params)) sliceError +
      avgOver (uniformDistribution (Fq params)) sliceSelfError,
    idxPolyFamily_complete_of_slice_bounds params strategy.state family
      sliceError sliceSelfError hcompleteSlice,
    answer_family_consistency_of_slice_bounds params strategy family
      sliceSelfError _ hpointSlice havgZeta,
    idxPolyFamily_stronglySelfConsistent_of_slice_bounds params strategy.state family
      sliceSelfError _ hselfCloseSlice havgZeta,
    idxPolyFamily_sliceBoundednessInput_of_slice_bounds params
      (answerSelfImprovementCarrier params.next strategy) family sliceSelfError _
      hboundedSlice havgZeta hdomSlice,
    by linarith,
    answer_selfImprovementInInductionError_le_mainInductionNu
      params strategy eps delta gamma k hgood hsmall
      (answer_eps_le_one_of_mainInductionError_lt_one params strategy hgood hsmall)
      (answer_delta_le_one_of_mainInductionError_lt_one params strategy hgood hsmall)
      (answer_dq_le_q_of_mainInductionError_lt_one params strategy hgood hsmall)⟩

/-- Answer-valued induction-section pasting from an explicit commutativity input.

This theorem performs the checked final assembly once the answer-valued
analogue of the Section 11 commutativity theorem has been supplied for the
point-equivalent ordinary carrier.  The hypotheses `hcom` and `herror_le` are
not source assumptions; they are the internal commutativity construction and
scalar absorption targets for the answer-valued pasting route. -/
theorem answerLdPastingInInductionSectionOfComMainAndErrorBound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params 𝔓)
    (kappa zeta : ℝ)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons :
      strategy.state.ConsRel (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (IdxPolyFamily.evaluatedAtNextPoint family)
        zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound :
      IdxPolyFamily.SliceBoundednessInput
        (answerSelfImprovementCarrier params.next strategy)
        family zeta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_nonneg : 0 ≤ zeta)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (hd : 0 < params.d)
    (hk_pos : 1 ≤ k)
    (hk : 400 * params.m * params.d ≤ k)
    (hcom :
      Commutativity.ComMainConclusion params
        (answerSelfImprovementCarrier params.next strategy) family gamma zeta)
    (herror_le :
      ldPastingInInductionError params k eps delta gamma kappa zeta ≤
        mainInductionError params.next k eps delta gamma) :
    AnswerMainInductionConclusion params.next strategy eps delta gamma k := by
  let carrier := answerSelfImprovementCarrier params.next strategy
  have haxis : carrier.axisParallelFailureProbability ≤ eps := hgood.axisParallelTest
  have hself_good : carrier.selfConsistencyFailureProbability ≤ delta :=
    hgood.selfConsistencyTest
  have hconsCarrier : family.ConsistentWithPoints carrier zeta := ⟨hcons⟩
  have hsubmeas :=
    Pasting.hAConsistency_submeas_ofComMain_of_axis_self params carrier
      eps delta gamma zeta haxis hself_good hgamma_nonneg hgamma_le
      hzeta_nonneg hzeta_le hdq_le hd family hconsCarrier hself hbound hcom k hk_pos
  have hN :=
    Pasting.ldPastingNCompleteness_ofComMain_of_axis_self params carrier
      eps delta gamma kappa zeta haxis hself_good hgamma_nonneg hgamma_le
      hzeta_nonneg hzeta_le hdq_le hd family hcomplete hconsCarrier hself hcom k hk_pos hk
  exact ⟨Pasting.constructedPastedMeasurement params family k,
    ⟨((Pasting.hAConsistency_completed params carrier eps delta gamma kappa zeta
      family k hsubmeas hN.completenessBound).offDiagonalBound).trans herror_le⟩⟩

/-- Answer-valued Section 11 commutativity input needed by the positive-degree
pasting branch.

This is a Lean-only construction target, not a source theorem and not a
hypothesis of `thm:main-induction`.  It is the precise replacement for the invalid route
through the ordinary carrier's dummy diagonal measurement: the conclusion is
the ordinary `ComMainConclusion` for the point-equivalent carrier, but the
intended proof must use the answer-valued diagonal verifier relation of
`strategy`.

The proof first establishes the Section 10 point-commutativity estimate from
the answer-valued diagonal-line test, transfers that estimate to the
point-equivalent carrier, and then invokes the Section 11 scalar chain in its
form that assumes point commutativity rather than an ordinary diagonal
`IsGood` field. -/
theorem answerComMainForCarrier_ofAnswerGood
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next 𝔓 K)
    (eps delta gamma zeta : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_nonneg : 0 ≤ gamma)
    (family : IdxPolyFamily params 𝔓)
    (hcons :
      strategy.state.ConsRel (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (IdxPolyFamily.evaluatedAtNextPoint family)
        zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound :
      IdxPolyFamily.SliceBoundednessInput
        (answerSelfImprovementCarrier params.next strategy)
        family zeta) :
    Commutativity.ComMainConclusion params
      (answerSelfImprovementCarrier params.next strategy) family gamma zeta :=
  Commutativity.comMain_of_commutativityPoints params
    (answerSelfImprovementCarrier params.next strategy) gamma zeta
    (CommutativityPoints.answerCommutativityPoints (params := params.next)
      strategy eps delta gamma hgood)
    hgamma_nonneg family ⟨hcons⟩ hself hbound

end MIPRE.LIDT.Co.MainInductionStep

end

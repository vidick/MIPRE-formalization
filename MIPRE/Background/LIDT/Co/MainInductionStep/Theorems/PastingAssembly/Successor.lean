/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
MainInductionStep/Theorems/PastingAssembly/Successor.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.MainInductionStep.Theorems.PastingAssembly.ErrorBounds
public import MIPRE.Background.LIDT.Co.MainInductionStep.Theorems.InductionParameterBounds.SelfImprovement

@[expose] public section

/-!
# Section 6 — Pasting Assembly: Successor Assembly

The final answer-valued pasting invocation, the averaged pasting data constructors, and the
ordinary successor assembly corollaries. This is the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/MainInductionStep/Theorems/PastingAssembly/Successor.lean`
in the port of `planning/c6b-plan.md` (milestone M12, section "Port conventions").

## Translation

A strategy is a `SymStrat params.next 𝔓 K` or an `AnswerSymStrat params.next 𝔓 K`
(`Co/Test/StrategyCore.lean`), whose state is the symmetric model `strategy.state : SymModel 𝔓 K`;
the point-equivalent ordinary carrier of an answer-valued strategy is Co
`answerSelfImprovementCarrier`, with the same state. `IdxPolyFamily params ι` is
`IdxPolyFamily params 𝔓`, `Measurement (Polynomial params.next) ι'` is
`Measurement (MIPStarRE.LDT.Polynomial params.next) 𝔓`, `Error` is `ℝ`, and the relations
(`ConsRel`, `bipartiteConsError`) are read on `strategy.state`. The error functions
(`mainInductionError`, `mainInductionNu`, `selfImprovementInInductionError`,
`ldPastingInInductionError`, `ldPastingInInductionNu`) and the scalar lemmas
`one_le_k_of_mainInductionError_lt_one`, `mainInductionSuccessorBound_pred`,
`ldPastingInInductionNu_le_fifth_mainInductionNu` and
`ldPastingInInductionError_le_mainInductionError_of_bounds` are the vendored classical
declarations, reached through explicit `open` lists. The vendored file-wide
`respectTransparency false` is not needed: the file sets no option.

The vendored explicit universe instantiations of the answer-valued stage records
(`AnswerSliceRestrictionData.{uι', uF}` and its siblings) and the separate carrier
`ι' : Type uι'` of `mainInductionFromAnswerStageDataOfSmallErrorDirect` and
`mainInductionFromAnswerStageDataOfSmallError` are not needed, as in Co
`StageDataConstructors`: the file declares `universe uP uK` with `𝔓 : Type uP` and `K : Type uK`,
and those two theorems keep only the binder `.{uF}` with `[FieldModel.{uF} params.q]`.

## Dropped and threaded hypotheses

No vendored statement here has a swap, density or normalization hypothesis, so none is dropped.
`answerMainInductionSuccessorNext_ofRecursiveHypothesisAndAnswerPasting` runs Co
`answerSuccessorAveragedFamilyFields_ofMainInductionHypothesis`, which takes the model hypotheses
`hS : strategy.state.toBipartite.IsFinitePair` and
`hA : NoAbelianProj strategy.state.toBipartite.opsA` of the predecessor
`AnswerMainInductionHypothesis` and `hd : 1 ≤ params.d` of the ported self-improvement theorem;
so it takes `hS hA hd` right after `strategy`, in the same position. Its induction hypothesis is
`AnswerMainInductionHypothesis.{uF, uP, uK}`, where the vendored one is `.{uF, uι}`. No other
declaration takes a new hypothesis: the pasting invocations and the averaging neither
orthonormalize nor solve a semidefinite program.

## Proofs that differ from the vendored ones

- In `answerLdPastingInInductionSectionOfSmallError` the hypotheses are passed as they stand:
  the vendored `simpa [zeta]` transfers through a local `let zeta` are dropped.
- The four `AnswerSelfImprovementData` lemmas pass the data's fields to the Co
  `PastingAssembly/Basic` lemmas directly, `hself.family.meas` being `hself.sliceProj` and
  `hself.family.witness` being `hself.sliceWitness` by definitional equality, with no `simpa`;
  the point consistency is one `trans_le` chain.
- The bound on `κ` and the scalar absorption `ldPastingInInductionError ≤ mainInductionError`,
  which the vendored `assembleAveragedPastingData` and
  `mainInductionFromAnswerStageDataOfSmallErrorDirect` prove twice (each with an `nlinarith`),
  are the new theorem `ldPastingInInductionError_le_of_averaged_bounds` (below), closed by
  `linarith`. It is public because the exposed definition `assembleAveragedPastingData` uses it.
- `assembleAveragedPastingData` builds its record from the Co `PastingAssembly/Basic` lemmas, the
  slice data's fields passed by definitional equality.

## New here

- `ldPastingInInductionError_le_of_averaged_bounds`: the scalar absorption shared by
  `assembleAveragedPastingData` and `mainInductionFromAnswerStageDataOfSmallErrorDirect`.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/inductive_step.tex`
- `references/ldt-paper/ld-pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.MainInductionStep

open MIPStarRE.LDT (Parameters FieldModel Point Fq uniformDistribution avgOver avgOver_mono)
open MIPStarRE.LDT.MainInductionStep (mainInductionError mainInductionNu
  selfImprovementInInductionError ldPastingInInductionError ldPastingInInductionNu
  one_le_k_of_mainInductionError_lt_one mainInductionSuccessorBound_pred
  ldPastingInInductionNu_le_fifth_mainInductionNu
  ldPastingInInductionError_le_mainInductionError_of_bounds)
open MIPRE.LIDT.Co (SymStrat AnswerSymStrat eps_nonneg_of_isGood delta_nonneg_of_isGood
  gamma_nonneg_of_isGood answer_gamma_nonneg_of_isGood)

universe uP uK

variable {𝔓 : Type uP} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type uK} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Answer-valued induction-section pasting theorem for the small-error
successor branch.

Paper origin: `references/ldt-paper/ld-pasting.tex:12-50` and its use in
`references/ldt-paper/inductive_step.tex:541-551`.

This is a Lean-only answer-valued analogue of the final pasting invocation
needed in the simultaneous successor proof.  Its hypotheses are the averaged
family fields already proved from the recursive answer-valued slices: averaged
completeness, consistency with the actual answer-valued point measurement,
strong self-consistency, and the boundedness input currently typed through the
point-equivalent ordinary carrier.  The conclusion is the successor
answer-valued main-induction consistency statement.

This proof uses the answer-valued point-commutativity theorem and the Section 11
scalar commutativity chain, so the diagonal-line input is the answer-valued
verifier relation itself rather than an ordinary dummy diagonal carrier.  It is
an internal successor-construction theorem, not the source theorem
`thm:ld-pasting`. -/
theorem answerLdPastingInInductionSectionOfSmallError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1)
    (family : IdxPolyFamily params 𝔓)
    (kappa : ℝ)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons :
      strategy.state.ConsRel (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (IdxPolyFamily.evaluatedAtNextPoint family)
        (selfImprovementInInductionError params.next eps delta gamma))
    (hself :
      family.StronglySelfConsistent strategy.state
        (selfImprovementInInductionError params.next eps delta gamma))
    (hbound :
      IdxPolyFamily.SliceBoundednessInput
        (answerSelfImprovementCarrier params.next strategy)
        family
        (selfImprovementInInductionError params.next eps delta gamma))
    (hkappa_le :
      kappa ≤
        ((params.m : ℝ) ^ (2 : ℕ)) *
            (mainInductionNu params.next k eps delta gamma +
              Real.exp (-((k : ℝ) / (80000 * ((params.m : ℝ) ^ (2 : ℕ))))))
          + selfImprovementInInductionError params.next eps delta gamma)
    (hzeta_le_nu :
      selfImprovementInInductionError params.next eps delta gamma ≤
        mainInductionNu params.next k eps delta gamma)
    (hk : 400 * params.m * params.d ≤ k) :
    AnswerMainInductionConclusion params.next strategy eps delta gamma k := by
  rcases Nat.eq_zero_or_pos params.d with hd | hd
  · exact answerLdPastingInInductionSectionDegreeZeroOfSmallError
      params strategy eps delta gamma k hgood hsmall family kappa hcomplete hcons hself hbound
      hkappa_le hzeta_le_nu hk hd
  have hgamma_nonneg : 0 ≤ gamma := answer_gamma_nonneg_of_isGood params.next strategy hgood
  have hzeta_nonneg : 0 ≤ selfImprovementInInductionError params.next eps delta gamma :=
    (strategy.state.bipartiteConsError_nonneg _ _ _).trans hcons.offDiagonalBound
  exact answerLdPastingInInductionSectionOfComMainAndErrorBound
    params strategy eps delta gamma k hgood family kappa _
    hcomplete hcons hself hbound hgamma_nonneg
    (answer_gamma_le_one_of_mainInductionError_lt_one params strategy hgood hsmall)
    hzeta_nonneg
    (answer_selfImprovementInInductionError_le_one_of_mainInductionError_lt_one
      params strategy hgood hsmall)
    (answer_dq_le_q_of_mainInductionError_lt_one params strategy hgood hsmall) hd
    (one_le_k_of_mainInductionError_lt_one params.next k eps delta gamma hsmall) hk
    (answerComMainForCarrier_ofAnswerGood params strategy eps delta gamma _
      hgood hgamma_nonneg family hcons hself hbound)
    (answerLdPastingInInductionError_le_mainInductionError_of_smallError
      params strategy eps delta gamma kappa k hgood hsmall hkappa_le hzeta_le_nu)

/-- Internal successor reduction from the predecessor answer-valued induction
hypothesis and the answer-valued pasting theorem.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`.

**Conditional:** This theorem is not the source successor theorem.  It records
that, once the
recursive predecessor hypothesis is available inside a genuine induction on
the dimension, all remaining slice restriction, self-improvement, averaging,
and scalar fields reduce the successor branch to
`answerLdPastingInInductionSectionOfSmallError`.  It is tracked in issue #1507.
Discharge: proved here from the predecessor answer-valued induction hypothesis
and the proved answer-valued pasting invocation. The model hypotheses `hS hA` and
`hd : 1 ≤ params.d` are those of the self-improvement outputs (module docstring). -/
theorem answerMainInductionSuccessorNext_ofRecursiveHypothesisAndAnswerPasting.{uF}
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
    AnswerMainInductionConclusion params.next strategy eps delta gamma k :=
  let ⟨family, kappa, hcomplete, hcons, hself, hbound, hkappa_le, hzeta_le_nu⟩ :=
    answerSuccessorAveragedFamilyFields_ofMainInductionHypothesis
      params strategy hS hA hd eps delta gamma k hgood hinduction hk_next hsmall
  answerLdPastingInInductionSectionOfSmallError
    params strategy eps delta gamma k hgood hsmall family kappa hcomplete hcons hself hbound
    hkappa_le hzeta_le_nu (mainInductionSuccessorBound_pred params hk_next)

namespace AnswerSelfImprovementData

/-- Averaged completeness of the family obtained from answer-valued
self-improvement data. -/
lemma complete_of_slice_bounds
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (hrestrict : AnswerSliceRestrictionData params strategy eps delta gamma)
    (hinduction : AnswerPerSliceInductionData params strategy eps delta gamma hrestrict k)
    (hself : AnswerSelfImprovementData params strategy eps delta gamma k hrestrict hinduction) :
    hself.family.Complete strategy.state
      (avgOver (uniformDistribution (Fq params)) hinduction.sliceError +
        avgOver (uniformDistribution (Fq params))
          (fun x => answerSliceSelfImprovementError params hrestrict x)) :=
  idxPolyFamily_complete_of_slice_bounds params strategy.state hself.family
    hinduction.sliceError (fun x => answerSliceSelfImprovementError params hrestrict x)
    hself.completeness

/-- Averaged point-consistency of the family obtained from answer-valued
self-improvement data, in the ordinary ambient interface. -/
lemma consistentWithPoints_of_slice_bounds
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hrestrict : AnswerSliceRestrictionData params strategy eps delta gamma)
    (hinduction : AnswerPerSliceInductionData params strategy eps delta gamma hrestrict k)
    (hself : AnswerSelfImprovementData params strategy eps delta gamma k hrestrict hinduction) :
    hself.family.ConsistentWithPoints strategy
      (selfImprovementInInductionError params.next eps delta gamma) :=
  ⟨⟨(family_answerRestrictedPointConsistencyError_eq_avg params strategy hself.family).trans_le
    ((avgOver_mono _ _ _ fun x => (hself.pointConsistency x).offDiagonalBound).trans
      (average_answerSliceSelfImprovementError_le params strategy eps delta gamma hgood
        hrestrict))⟩⟩

/-- Averaged strong self-consistency of the family obtained from answer-valued
self-improvement data. -/
lemma stronglySelfConsistent_of_slice_bounds
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hrestrict : AnswerSliceRestrictionData params strategy eps delta gamma)
    (hinduction : AnswerPerSliceInductionData params strategy eps delta gamma hrestrict k)
    (hself : AnswerSelfImprovementData params strategy eps delta gamma k hrestrict hinduction) :
    hself.family.StronglySelfConsistent strategy.state
      (selfImprovementInInductionError params.next eps delta gamma) :=
  idxPolyFamily_stronglySelfConsistent_of_slice_bounds params strategy.state hself.family
    (fun x => answerSliceSelfImprovementError params hrestrict x)
    (selfImprovementInInductionError params.next eps delta gamma)
    hself.selfCloseness
    (average_answerSliceSelfImprovementError_le params strategy eps delta gamma hgood hrestrict)

/-- Averaged boundedness of the family obtained from answer-valued
self-improvement data, in the ordinary ambient pasting interface.

**Lean-only:** This is an internal adapter for the induction-section pasting
interface, tracked in issue #1507.  Paper origin:
`references/ldt-paper/inductive_step.tex:461-551`.  Discharge: proved here by
applying `idxPolyFamily_sliceBoundednessInput_of_slice_bounds` to the
answer-valued self-improvement data. -/
lemma sliceBoundednessInput_of_slice_bounds
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hrestrict : AnswerSliceRestrictionData params strategy eps delta gamma)
    (hinduction : AnswerPerSliceInductionData params strategy eps delta gamma hrestrict k)
    (hself : AnswerSelfImprovementData params strategy eps delta gamma k hrestrict hinduction) :
    IdxPolyFamily.SliceBoundednessInput strategy hself.family
      (selfImprovementInInductionError params.next eps delta gamma) :=
  idxPolyFamily_sliceBoundednessInput_of_slice_bounds params strategy hself.family
    (fun x => answerSliceSelfImprovementError params hrestrict x)
    (selfImprovementInInductionError params.next eps delta gamma)
    hself.bounded
    (average_answerSliceSelfImprovementError_le params strategy eps delta gamma hgood hrestrict)
    hself.dominatesAveragePointOperator

end AnswerSelfImprovementData

/-- The scalar absorption shared by the two averaged pasting assemblies: if the averaged slice
induction error `σ` is at most `m²(ν + e^{-k/(80000 m²)})` and the averaged slice
self-improvement error `ζ'` at most `ζ`, then the induction-section pasting error at
`κ = σ + ζ'` and `ζ` is at most the next-stage target. -/
theorem ldPastingInInductionError_le_of_averaged_bounds
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1)
    (heps_le_one : eps ≤ 1) (hdelta_le_one : delta ≤ 1) (hgamma_le : gamma ≤ 1)
    (hdq_le_q : params.d ≤ params.q)
    (sigma zeta' : ℝ)
    (hsigma :
      sigma ≤
        ((params.m : ℝ) ^ (2 : ℕ)) *
          (mainInductionNu params.next k eps delta gamma +
            Real.exp (-((k : ℝ) / (80000 * ((params.m : ℝ) ^ (2 : ℕ)))))))
    (hzeta' : zeta' ≤ selfImprovementInInductionError params.next eps delta gamma) :
    ldPastingInInductionError params k eps delta gamma (sigma + zeta')
        (selfImprovementInInductionError params.next eps delta gamma) ≤
      mainInductionError params.next k eps delta gamma :=
  have heps_nonneg := eps_nonneg_of_isGood params.next strategy hgood
  have hdelta_nonneg := delta_nonneg_of_isGood params.next strategy hgood
  have hgamma_nonneg := gamma_nonneg_of_isGood params.next strategy hgood
  ldPastingInInductionError_le_mainInductionError_of_bounds
    params eps delta gamma k (sigma + zeta')
    (selfImprovementInInductionError params.next eps delta gamma)
    heps_nonneg hdelta_nonneg hgamma_nonneg (by linarith)
    (selfImprovementInInductionError_le_mainInductionNu
      params strategy eps delta gamma k hgood hsmall heps_le_one hdelta_le_one hdq_le_q)
    (ldPastingInInductionNu_le_fifth_mainInductionNu
      params eps delta gamma k heps_nonneg hdelta_nonneg hgamma_nonneg
      heps_le_one hdelta_le_one hgamma_le hdq_le_q)

/-- Paper origin: `references/ldt-paper/ld-pasting.tex:12-50`
(`\label{thm:ld-pasting}`) and
`references/ldt-paper/inductive_step.tex:239-342`.

The remaining averaged step from per-slice self-improvement data to the
pasting hypotheses.

This is where the paper's `E_x[σ_x]`, `E_x[ζ_x]`, and
`σ* ≤ mainInductionError` bookkeeping will eventually live. -/
noncomputable def assembleAveragedPastingData
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : selfImprovementInInductionError params.next eps delta gamma ≤ 1)
    (hdq_le_q : params.d ≤ params.q)
    (hrestrict : SliceRestrictionData params strategy eps delta gamma)
    (hinduction : PerSliceInductionData params strategy eps delta gamma hrestrict k)
    (hself : SelfImprovementData params strategy eps delta gamma k hrestrict hinduction)
    (_hk : 400 * params.m * params.d ≤ k) :
    AveragedPastingData params strategy eps delta gamma k hself :=
  have hzeta' :=
    average_sliceSelfImprovementError_le params strategy eps delta gamma hgood hrestrict
  { kappa :=
      avgOver (uniformDistribution (Fq params)) hinduction.sliceError +
        avgOver (uniformDistribution (Fq params))
          (fun x => sliceSelfImprovementError params hrestrict x)
    zeta := selfImprovementInInductionError params.next eps delta gamma
    complete :=
      idxPolyFamily_complete_of_slice_bounds params strategy.state hself.family
        hinduction.sliceError (fun x => sliceSelfImprovementError params hrestrict x)
        hself.completeness
    consistent :=
      ⟨⟨(family_pointConsistencyError_eq_avg params strategy hself).trans_le
        ((avgOver_mono _ _ _ fun x => (hself.pointConsistency x).offDiagonalBound).trans
          hzeta')⟩⟩
    selfConsistent :=
      idxPolyFamily_stronglySelfConsistent_of_slice_bounds params strategy.state hself.family
        (fun x => sliceSelfImprovementError params hrestrict x) _ hself.selfCloseness hzeta'
    bounded :=
      idxPolyFamily_sliceBoundednessInput_of_slice_bounds params strategy hself.family
        (fun x => sliceSelfImprovementError params hrestrict x) _ hself.bounded hzeta'
        hself.dominatesAveragePointOperator
    error_le :=
      ldPastingInInductionError_le_of_averaged_bounds params strategy eps delta gamma k hgood
        hsmall
        (eps_le_one_of_selfImprovementInInductionError_le_one params strategy hgood hzeta_le)
        (delta_le_one_of_selfImprovementInInductionError_le_one params strategy hgood hzeta_le)
        hgamma_le hdq_le_q _ _
        (average_sliceError_le params strategy eps delta gamma k hgood hrestrict hinduction)
        hzeta' }

/-- Assemble the averaged pasting data in the nontrivial small-error branch.

Paper origin: `references/ldt-paper/inductive_step.tex:486-551`.  The small-error
hypothesis supplies `γ ≤ 1`, `ζ ≤ 1`, and `d ≤ q`, so callers do not carry
those scalar estimates as separate proof inputs. -/
noncomputable def assembleAveragedPastingDataOfSmallError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1)
    (hrestrict : SliceRestrictionData params strategy eps delta gamma)
    (hinduction : PerSliceInductionData params strategy eps delta gamma hrestrict k)
    (hself : SelfImprovementData params strategy eps delta gamma k hrestrict hinduction)
    (hk : 400 * params.m * params.d ≤ k) :
    AveragedPastingData params strategy eps delta gamma k hself :=
  assembleAveragedPastingData params strategy eps delta gamma k hgood hsmall
    (gamma_le_one_of_mainInductionError_lt_one params strategy hgood hsmall)
    (selfImprovementInInductionError_le_one_of_mainInductionError_lt_one
      params strategy hgood hsmall)
    (dq_le_q_of_mainInductionError_lt_one params strategy hgood hsmall)
    hrestrict hinduction hself hk

/-- Direct answer-valued small-error successor assembly over an ordinary ambient
strategy.

This is the same mathematical assembly as
`mainInductionFromAnswerStageDataOfSmallError`, but it invokes the
induction-section pasting theorem directly from the answer-valued slice
self-improvement data rather than first converting that data into the legacy
`SelfImprovementData` record. -/
theorem mainInductionFromAnswerStageDataOfSmallErrorDirect.{uF}
    (params : Parameters)
    [FieldModel.{uF} params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1)
    (answerRestrict : AnswerSliceRestrictionData params strategy eps delta gamma)
    (answerInduction :
      AnswerPerSliceInductionData params strategy eps delta gamma answerRestrict k)
    (answerSelf :
      AnswerSelfImprovementData params strategy eps delta gamma k answerRestrict
        answerInduction)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : Measurement (MIPStarRE.LDT.Polynomial params.next) 𝔓,
      strategy.state.ConsRel (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next H.toSubMeas)
        (mainInductionError params.next k eps delta gamma) :=
  let ⟨H, hH⟩ :=
    ldPastingInInductionSection params strategy eps delta gamma _ _ hgood answerSelf.family
      (AnswerSelfImprovementData.complete_of_slice_bounds
        params strategy eps delta gamma k answerRestrict answerInduction answerSelf)
      (AnswerSelfImprovementData.consistentWithPoints_of_slice_bounds
        params strategy eps delta gamma k hgood answerRestrict answerInduction answerSelf)
      (AnswerSelfImprovementData.stronglySelfConsistent_of_slice_bounds
        params strategy eps delta gamma k hgood answerRestrict answerInduction answerSelf)
      (AnswerSelfImprovementData.sliceBoundednessInput_of_slice_bounds
        params strategy eps delta gamma k hgood answerRestrict answerInduction answerSelf)
      k hk
  mainInductionOfWitness params.next strategy eps delta gamma k
    ⟨_, H, hH.pointConsistency,
      ldPastingInInductionError_le_of_averaged_bounds params strategy eps delta gamma k hgood
        hsmall (eps_le_one_of_mainInductionError_lt_one params strategy hgood hsmall)
        (delta_le_one_of_mainInductionError_lt_one params strategy hgood hsmall)
        (gamma_le_one_of_mainInductionError_lt_one params strategy hgood hsmall)
        (dq_le_q_of_mainInductionError_lt_one params strategy hgood hsmall) _ _
        (average_answerSliceError_le params strategy eps delta gamma k hgood
          answerRestrict answerInduction)
        (average_answerSliceSelfImprovementError_le
          params strategy eps delta gamma hgood answerRestrict)⟩

/-- Answer-valued small-error successor assembly.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`.  This is the
internal answer-valued route through the successor proof: answer-valued
restricted slice data supply the averaged pasting fields directly, the
small-error branch supplies the scalar side conditions for averaged pasting, and
the induction-section pasting theorem produces the next-dimensional
measurement. -/
theorem mainInductionFromAnswerStageDataOfSmallError.{uF}
    (params : Parameters)
    [FieldModel.{uF} params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1)
    (answerRestrict : AnswerSliceRestrictionData params strategy eps delta gamma)
    (answerInduction :
      AnswerPerSliceInductionData params strategy eps delta gamma answerRestrict k)
    (answerSelf :
      AnswerSelfImprovementData params strategy eps delta gamma k answerRestrict
        answerInduction)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : Measurement (MIPStarRE.LDT.Polynomial params.next) 𝔓,
      strategy.state.ConsRel (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next H.toSubMeas)
        (mainInductionError params.next k eps delta gamma) :=
  mainInductionFromAnswerStageDataOfSmallErrorDirect
    params strategy eps delta gamma k hgood hsmall answerRestrict answerInduction answerSelf hk

end MIPRE.LIDT.Co.MainInductionStep

end

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
MainInductionStep/Theorems/PastingAssembly/Basic.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.MainInductionStep.Theorems.InductionParameterBounds.MainError
public import MIPRE.Background.LIDT.Co.MainInductionStep.Theorems.StageDataConstructors
public import MIPRE.Background.LIDT.Co.MainInductionStep.Theorems.AvgSliceErrors.Successor
public import MIPRE.Background.LIDT.Co.CommutativityPoints.Approximation
public import MIPRE.Background.LIDT.Co.CommutativityPoints.AnswerTheorems
public import MIPRE.Background.LIDT.Co.Pasting.Bernoulli.DegreeZero
public import MIPRE.Background.LIDT.MIPStarRE.LDT.MainInductionStep.Theorems.PastingAssembly.Basic

@[expose] public section

/-!
# Section 6 — Pasting Assembly: Averaged Family Fields

The scalar side condition `ζ ≤ 1` of the small-error branch, the averaged slice errors of the
answer-valued slice route, and the averaged family fields (completeness, point consistency,
strong self-consistency, boundedness) that the answer-valued successor route feeds to pasting.
This is the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/MainInductionStep/Theorems/PastingAssembly/Basic.lean` in
the port of `planning/c6b-plan.md` (milestone M12, section "Port conventions").

## Translation

A strategy is a `SymStrat params.next 𝔓 K` or an `AnswerSymStrat params.next 𝔓 K`
(`Co/Test/StrategyCore.lean`), whose state is the symmetric model `strategy.state : SymModel 𝔓 K`;
a state `ψ : QuantumState (ι × ι)` alone is a model `S : SymModel 𝔓 K`, in the same position.
`Polynomial params` is `MIPStarRE.LDT.Polynomial params`, `Error` is `ℝ`, `ev ψ` is `S.ev`,
`leftTensor`/`rightTensor` are `S.L`/`S.R`, `SubMeas.liftLeft` is `.liftLeft S`,
`leftPlacedSubMeas (ιB := ι)` and `rightPlacedSubMeas (ιA := ι)` are `S.leftPlacedSubMeas` and
`S.rightPlacedSubMeas`, and the quantities and relations (`subMeasMass`, `bipartiteConsError`,
`qSDD`, `sddError`, `ConsRel`, `SDDRel`, `CompletenessAtLeast`) are read on the model. The
error functions (`mainInductionError`, `mainInductionNu`, `selfImprovementInInductionError`),
`mainInductionNu_lt_one_of_mainInductionError_lt_one` and
`avgOver_uniform_pointNext_decompose` are the vendored classical declarations, reached through
explicit `open` lists. No vendored statement here has a swap, density or normalization
hypothesis, so none is dropped; no statement takes a new hypothesis. The vendored file-wide
`respectTransparency false` is not needed: the file sets no option.

## Swap use

The boundedness field of `idxPolyFamily_sliceBoundednessInput_of_slice_bounds` exchanges the two
factors of `⟨Ψ| (I - G^x) ⊗ Z^x |Ψ⟩`; the vendored proof does so with
`ev_opTensor_swap_of_density_fixed strategy.state strategy.permInvState.density_swap`, and here
with the keystone's `SymModel.ev_L_mul_R_comm`, which takes no hypothesis.

## Proofs that differ from the vendored ones

- The two `ζ ≤ 1` lemmas are one term each, `ζ ≤ ν < 1`, through Co
  `selfImprovementInInductionError_le_mainInductionNu` and the imported
  `mainInductionNu_lt_one_of_mainInductionError_lt_one`.
- `average_answerSliceSelfImprovementError_le` and `average_answerSliceError_le` are the Co
  `average_sliceSelfImprovementError_le` and `average_sliceError_le` applied to
  `SliceRestrictionData.ofAnswer` and `PerSliceInductionData.ofAnswer`, whose fields are those of
  the answer-valued data by definitional equality, so there is no `simpa`.
- `idxPolyFamily_averagedMass_eq_avg` is `S.ev_leftTensor_averageOperatorOverDistribution` by
  definitional equality, and `idxPolyFamily_complete_of_slice_bounds` averages the slice lower
  bounds with `avgOver_mono` and closes with `avgOver_sub`, `avgOver_uniform_const` and
  `linarith`.
- The three point-consistency averaging identities, which the vendored file proves three times by
  the same `calc` and `avg_congr` (whose vendored tactic is not used here), share the private
  theorem `bipartiteConsError_evaluatedAtNextPoint_eq_avg`, stated for any point-indexed
  family on `F_q^{m+1}`; each is that theorem by definitional equality of the restricted point
  measurements.
- `idxPolyFamily_stronglySelfConsistent_of_slice_bounds` and the boundedness field read the slice
  bounds through `avgOver_uniform_const` and `avgOver_mono`, with no `simpa`; the positivity of the
  slice witnesses is `averageOperatorOverDistribution_nonneg`.

## Not ported

- `ldPastingInInductionNu_le_fifth_mainInductionNu`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/inductive_step.tex`
- `blueprint/src/chapter/ch10_induction.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.MainInductionStep

open MIPStarRE.LDT (Parameters FieldModel Point Fq uniformDistribution avgOver avgOver_mono
  avgOver_congr avgOver_sub avgOver_uniform_const appendPoint truncatePoint_appendPoint
  pointHeight_appendPoint)
open MIPStarRE.LDT.MainInductionStep (mainInductionError mainInductionNu
  selfImprovementInInductionError mainInductionNu_lt_one_of_mainInductionError_lt_one)
open MIPStarRE.LDT.CommutativityPoints (avgOver_uniform_pointNext_decompose)
open MIPRE.LIDT.Co (SymStrat AnswerSymStrat)

universe uP uK

variable {𝔓 : Type uP} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type uK} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The nontrivial main-induction branch supplies the scalar side condition
`ζ ≤ 1` needed by the averaged pasting assembly.

Paper origin: `references/ldt-paper/inductive_step.tex:486-551`, where the
small-error branch is the one in which the averaged self-improvement and
pasting estimates are used. -/
lemma selfImprovementInInductionError_le_one_of_mainInductionError_lt_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    {eps delta gamma : ℝ}
    {k : ℕ}
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1) :
    selfImprovementInInductionError params.next eps delta gamma ≤ 1 :=
  (selfImprovementInInductionError_le_mainInductionNu params strategy eps delta gamma k hgood
      hsmall (eps_le_one_of_mainInductionError_lt_one params strategy hgood hsmall)
      (delta_le_one_of_mainInductionError_lt_one params strategy hgood hsmall)
      (dq_le_q_of_mainInductionError_lt_one params strategy hgood hsmall)).trans
    (mainInductionNu_lt_one_of_mainInductionError_lt_one params.next k eps delta gamma
      hsmall).le

/-- Answer-valued analogue of
`selfImprovementInInductionError_le_one_of_mainInductionError_lt_one`.

This is a scalar consequence of the small-error branch for an ambient
answer-valued strategy.  It does not use the ordinary carrier strategy and does
not assert that the answer-valued diagonal measurement is controlled by an
ordinary diagonal test. -/
lemma answer_selfImprovementInInductionError_le_one_of_mainInductionError_lt_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next 𝔓 K)
    {eps delta gamma : ℝ}
    {k : ℕ}
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1) :
    selfImprovementInInductionError params.next eps delta gamma ≤ 1 :=
  (answer_selfImprovementInInductionError_le_mainInductionNu params strategy eps delta gamma k
      hgood hsmall (answer_eps_le_one_of_mainInductionError_lt_one params strategy hgood hsmall)
      (answer_delta_le_one_of_mainInductionError_lt_one params strategy hgood hsmall)
      (answer_dq_le_q_of_mainInductionError_lt_one params strategy hgood hsmall)).trans
    (mainInductionNu_lt_one_of_mainInductionError_lt_one params.next k eps delta gamma
      hsmall).le

/-- The average of the answer-slice self-improvement errors is bounded by the
ambient induction self-improvement error.

This is the ordinary ambient version: the restricted slices use the
answer-valued interface, but the ambient strategy is an ordinary `SymStrat`. -/
lemma average_answerSliceSelfImprovementError_le
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (hrestrict : AnswerSliceRestrictionData params strategy eps delta gamma) :
    avgOver (uniformDistribution (Fq params))
        (fun x => answerSliceSelfImprovementError params hrestrict x) ≤
      selfImprovementInInductionError params.next eps delta gamma :=
  average_sliceSelfImprovementError_le params strategy eps delta gamma hgood
    (SliceRestrictionData.ofAnswer params strategy eps delta gamma hrestrict)

/-- The average recursive answer-slice induction error satisfies the same bound
as in the ordinary slice route.

The proof is a transport of the already checked ordinary averaging estimate
through the answer-valued slice-to-ordinary data conversion. -/
lemma average_answerSliceError_le
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hrestrict : AnswerSliceRestrictionData params strategy eps delta gamma)
    (hinduction : AnswerPerSliceInductionData params strategy eps delta gamma hrestrict k) :
    avgOver (uniformDistribution (Fq params)) hinduction.sliceError ≤
      ((params.m : ℝ) ^ (2 : ℕ)) *
        (mainInductionNu params.next k eps delta gamma +
          Real.exp (-((k : ℝ) / (80000 * ((params.m : ℝ) ^ (2 : ℕ)))))) :=
  average_sliceError_le params strategy eps delta gamma k hgood
    (SliceRestrictionData.ofAnswer params strategy eps delta gamma hrestrict)
    (PerSliceInductionData.ofAnswer params strategy eps delta gamma k hrestrict hinduction)

/-- The mass of the averaged polynomial family is the average of the masses of
the slice measurements.

This is the linearity calculation underlying the completeness part of the
averaged pasting assembly. -/
lemma idxPolyFamily_averagedMass_eq_avg
    (params : Parameters)
    [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓) :
    S.subMeasMass (family.averagedSubMeas.liftLeft S) =
      avgOver (uniformDistribution (Fq params))
        (fun x => S.subMeasMass ((family.meas x).toSubMeas.liftLeft S)) :=
  S.ev_leftTensor_averageOperatorOverDistribution (uniformDistribution (Fq params))
    (fun x => (family.meas x).toSubMeas.total)

/-- Averaged completeness of a slice-indexed polynomial family from pointwise
slice completeness.

This is the completeness component of the Section 6 averaging argument.  The
statement is family-level: it does not mention diagonal measurements, and hence
can be reused in the answer-valued successor route. -/
lemma idxPolyFamily_complete_of_slice_bounds
    (params : Parameters)
    [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (sliceError sliceSelfError : Fq params → ℝ)
    (hcomplete :
      ∀ x,
        S.CompletenessAtLeast ((family.meas x).toSubMeas.liftLeft S)
          ((1 - sliceError x) - sliceSelfError x)) :
    family.Complete S
      (avgOver (uniformDistribution (Fq params)) sliceError +
        avgOver (uniformDistribution (Fq params)) sliceSelfError) := by
  refine ⟨⟨?_⟩⟩
  have havg := avgOver_mono (uniformDistribution (Fq params)) _ _
    fun x => (hcomplete x).lowerBound
  rw [avgOver_sub, avgOver_sub, avgOver_uniform_const] at havg
  rw [idxPolyFamily_averagedMass_eq_avg params S family]
  linarith

/-- Averaging a bipartite consistency defect against the evaluated family over
`F_q^{m+1}` splits into the slice heights: the point `(u, x)` reads the slice `x` at `u`. -/
private theorem bipartiteConsError_evaluatedAtNextPoint_eq_avg
    (params : Parameters)
    [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (A : IdxSubMeas (Point params.next) (Fq params) 𝔓)
    (family : IdxPolyFamily params 𝔓) :
    S.bipartiteConsError (uniformDistribution (Point params.next)) A
        family.evaluatedAtNextPoint =
      avgOver (uniformDistribution (Fq params))
        (fun x =>
          S.bipartiteConsError (uniformDistribution (Point params))
            (fun u => A (appendPoint params u x))
            (polynomialEvaluationFamily params (family.meas x).toSubMeas)) := by
  refine (avgOver_uniform_pointNext_decompose params _).trans
    (avgOver_congr _ _ _ fun x => avgOver_congr _ _ _ fun u => ?_)
  simp only [IdxPolyFamily.evaluatedAtNextPoint, truncatePoint_appendPoint,
    pointHeight_appendPoint]
  rfl

/-- Point-consistency averaging for the slices of a self-improvement data record: the
consistency of the evaluated family with the ambient point measurement is the average of the
slice-wise consistencies with the restricted point measurements. -/
lemma family_pointConsistencyError_eq_avg
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    {eps delta gamma : ℝ} {k : ℕ}
    {hrestrict : SliceRestrictionData params strategy eps delta gamma}
    {hinduction : PerSliceInductionData params strategy eps delta gamma hrestrict k}
    (hself : SelfImprovementData params strategy eps delta gamma k hrestrict hinduction) :
    strategy.state.bipartiteConsError (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (IdxPolyFamily.evaluatedAtNextPoint hself.family) =
      avgOver (uniformDistribution (Fq params))
        (fun x =>
          strategy.state.bipartiteConsError (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas (xRestrictedStrategy params strategy x).pointMeasurement)
            (polynomialEvaluationFamily params (hself.sliceProj x).toSubMeas)) :=
  bipartiteConsError_evaluatedAtNextPoint_eq_avg params strategy.state
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) hself.family

/-- Point-consistency averaging for answer-valued restricted slices of an
ordinary ambient successor strategy. -/
lemma family_answerRestrictedPointConsistencyError_eq_avg
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓) :
    strategy.state.bipartiteConsError (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (IdxPolyFamily.evaluatedAtNextPoint family) =
      avgOver (uniformDistribution (Fq params))
        (fun x =>
          strategy.state.bipartiteConsError (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas
              (xRestrictedAnswerSymStrat params strategy x).pointMeasurement)
            (polynomialEvaluationFamily params (family.meas x).toSubMeas)) :=
  bipartiteConsError_evaluatedAtNextPoint_eq_avg params strategy.state
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) family

/-- Answer-valued point-consistency averaging over the last coordinate.

This is the same Fubini/reindexing calculation as
`family_pointConsistencyError_eq_avg`, but for an ambient answer-valued
successor strategy.  It is one of the identities needed to assemble the
answer-valued successor branch without replacing the diagonal-line answer
measurement by an ordinary polynomial-valued one. -/
lemma answer_family_pointConsistencyError_eq_avg
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓) :
    strategy.state.bipartiteConsError (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (IdxPolyFamily.evaluatedAtNextPoint family) =
      avgOver (uniformDistribution (Fq params))
        (fun x =>
          strategy.state.bipartiteConsError (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas
              (xRestrictedAnswerSymStratOfAnswer params strategy x).pointMeasurement)
            (polynomialEvaluationFamily params (family.meas x).toSubMeas)) :=
  bipartiteConsError_evaluatedAtNextPoint_eq_avg params strategy.state
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) family

/-- Average slice-wise point consistency for an answer-valued successor strategy.

If the slice family is point-consistent with each answer-valued restricted
strategy at error `sliceError x`, and the slice errors average to at most
`zeta`, then the evaluated family is point-consistent with the ambient
answer-valued point measurement at error `zeta`. -/
lemma answer_family_consistency_of_slice_bounds
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (sliceError : Fq params → ℝ)
    (zeta : ℝ)
    (hpoint :
      ∀ x,
        strategy.state.ConsRel (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas
            (xRestrictedAnswerSymStratOfAnswer params strategy x).pointMeasurement)
          (polynomialEvaluationFamily params (family.meas x).toSubMeas)
          (sliceError x))
    (havg : avgOver (uniformDistribution (Fq params)) sliceError ≤ zeta) :
    strategy.state.ConsRel (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (IdxPolyFamily.evaluatedAtNextPoint family)
      zeta :=
  ⟨((answer_family_pointConsistencyError_eq_avg params strategy family).trans_le
      (avgOver_mono _ _ _ fun x => (hpoint x).offDiagonalBound)).trans havg⟩

/-- Average slice-wise left/right closeness into strong self-consistency of the
slice-indexed family.

This is the strong self-consistency component of the Section 6 averaging
argument.  It depends only on the state and the slice measurements, not on the
diagonal part of a strategy. -/
lemma idxPolyFamily_stronglySelfConsistent_of_slice_bounds
    (params : Parameters)
    [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (sliceError : Fq params → ℝ)
    (zeta : ℝ)
    (hself :
      ∀ x,
        S.SDDRel (uniformDistribution Unit)
          (constSubMeasFamily (S.leftPlacedSubMeas (family.meas x).toSubMeas))
          (constSubMeasFamily (S.rightPlacedSubMeas (family.meas x).toSubMeas))
          (sliceError x))
    (havg : avgOver (uniformDistribution (Fq params)) sliceError ≤ zeta) :
    family.StronglySelfConsistent S zeta := by
  have hpointwise :
      ∀ x,
        S.qSDD ((family.meas x).toSubMeas.liftLeft S)
          ((family.meas x).toSubMeas.liftRight S) ≤ sliceError x := fun x =>
    (avgOver_uniform_const (α := Unit) _).symm.trans_le (hself x).squaredDistanceBound
  exact ⟨⟨(avgOver_mono _ _ _ hpointwise).trans havg⟩⟩

/-- Average slice-wise boundedness into the boundedness input used by the
induction-section pasting theorem.

This is the boundedness component of the Section 6 averaging argument for an
ordinary successor strategy.  The hypotheses are exactly the slice-wise
residual estimate and the paper domination condition
`E_u A^{u,x}_{g(u)} <= Z^x`.

**Lean-only:** This is an internal adapter for the induction-section pasting
interface, tracked in issue #1507.  Paper origin:
`references/ldt-paper/inductive_step.tex:461-551`.  Discharge: proved here by
averaging the slice-wise boundedness estimates and the domination condition. -/
lemma idxPolyFamily_sliceBoundednessInput_of_slice_bounds
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (sliceError : Fq params → ℝ)
    (zeta : ℝ)
    (hbounded :
      ∀ x,
        tensorFailureExpectation strategy.state (family.witness x)
          (family.meas x).toSubMeas ≤ sliceError x)
    (havg : avgOver (uniformDistribution (Fq params)) sliceError ≤ zeta)
    (hdom :
      ∀ x, ∀ g : MIPStarRE.LDT.Polynomial params,
        IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g ≤ family.witness x) :
    IdxPolyFamily.SliceBoundednessInput strategy family zeta where
  sliceOpPSD x :=
    (averageOperatorOverDistribution_nonneg _ _ fun u =>
        (strategy.pointMeasurement (appendPoint params u x)).toSubMeas.outcome_pos _).trans
      (hdom x (Classical.arbitrary _))
  sliceBoundedness :=
    (avgOver_mono _ _ _ fun x =>
        (strategy.state.ev_L_mul_R_comm _ _).trans_le (hbounded x)).trans havg
  sliceDominatesAveragedPoint := hdom

end MIPRE.LIDT.Co.MainInductionStep

end

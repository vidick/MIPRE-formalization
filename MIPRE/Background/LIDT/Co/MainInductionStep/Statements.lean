/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
MainInductionStep/Statements.lean, to the symmetric model of `planning/c6b-plan.md`; not a
vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.MainInductionStep.Defs
public import MIPRE.Background.LIDT.Co.Test.StrategyPolynomialFamilies

@[expose] public section

/-!
# Section 6 — Induction Step Data

The intermediate conclusion structures and bookkeeping statements of the induction step: the
conclusions of the induction-level self-improvement and pasting theorems, the restricted
failure profiles, and the stage data for the paper's slice restriction, slice-wise induction,
self-improvement and pasting assembly. This is the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/MainInductionStep/Statements.lean` in the port of
`planning/c6b-plan.md` (milestone M4, section "Port conventions").

A strategy is a `SymStrat params.next 𝔓 K` (`Co/Test/StrategyCore.lean`), whose state is the
symmetric model `strategy.state : SymModel 𝔓 K`; the vendored `QuantumState (ι × ι)` statements
become statements about that model, with local operators in `𝔓` (the vendored `Op ι`) placed by
`strategy.state.L` and `strategy.state.R`, and errors in `ℝ` (the vendored `Error`). The left
and right placements `leftPlacedSubMeas (ιB := ι)` and `rightPlacedSubMeas (ιA := ι)` are
`strategy.state.leftPlacedSubMeas` and `strategy.state.rightPlacedSubMeas`, and
`tensorFailureExpectation` is the one-algebra form of `Co/MainInductionStep/Defs.lean`.

`AnswerMainInductionHypothesis` quantifies over the local algebra `𝔓` and the Hilbert space `K`
of a symmetric model, in their own universes, where the vendored hypothesis quantifies over a
finite carrier `ι`.

The error constants (`mainInductionError`, `selfImprovementInInductionError`,
`ldPastingInInductionError`, `sliceConditioningLoss`) are the vendored classical declarations,
imported through `Co/MainInductionStep/Defs.lean` and named through an explicit `open` list.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/inductive_step.tex`
- `references/ldt-paper/ld-pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.MainInductionStep

open MIPStarRE.LDT (Parameters FieldModel Point Fq avgOver uniformDistribution)
open MIPStarRE.LDT.MainInductionStep (mainInductionError selfImprovementInInductionError
  ldPastingInInductionError sliceConditioningLoss)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Paper origin: `references/ldt-paper/inductive_step.tex:249-286`
(`\label{thm:self-improvement-in-induction-section}`).

Conclusion of the induction-level self-improvement theorem.

The strategy's state is the symmetric model `strategy.state`. Fields that involve placed
operators use `leftPlacedSubMeas` / `rightPlacedSubMeas` / `tensorFailureExpectation` of that
model. -/
structure SelfImprovementInInductionSectionConclusion (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (_G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (H : ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (Z : 𝔓) (eps delta gamma nu : ℝ) : Prop where
  /-- The projective submeasurement remains almost complete. -/
  completeness :
    strategy.state.CompletenessAtLeast (H.toSubMeas.liftLeft strategy.state)
      ((1 - nu) - selfImprovementInInductionError params eps delta gamma)
  /-- The projective submeasurement stays point-consistent with the original strategy. -/
  pointConsistency :
    strategy.state.ConsRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params H.toSubMeas)
      (selfImprovementInInductionError params eps delta gamma)
  /-- The output family is strongly self-consistent in the bipartite sense. -/
  strongSelfConsistency :
    strategy.state.BipartiteSSCRel (uniformDistribution Unit)
      (constSubMeasFamily H.toSubMeas)
      (selfImprovementInInductionError params eps delta gamma)
  /-- The left and right placements of the output family stay close in squared distance. -/
  selfCloseness :
    strategy.state.SDDRel (uniformDistribution Unit)
      (constSubMeasFamily (strategy.state.leftPlacedSubMeas H.toSubMeas))
      (constSubMeasFamily (strategy.state.rightPlacedSubMeas H.toSubMeas))
      (selfImprovementInInductionError params eps delta gamma)
  /-- The dual witness `Z` controls the tensor failure expectation of `H`. -/
  bounded :
    tensorFailureExpectation strategy.state Z H.toSubMeas
      ≤ selfImprovementInInductionError params eps delta gamma
  /-- Every averaged point-evaluation operator is dominated by the dual witness `Z`. -/
  dominatesAveragePointOperator :
    ∀ h : MIPStarRE.LDT.Polynomial params,
      IdxPolyFamily.averagedPointEvaluationOperator strategy h ≤ Z

/-- Paper origin: `references/ldt-paper/inductive_step.tex:299-338`
(`\label{thm:ld-pasting-in-induction-section}`).

Conclusion of the section-local pasting theorem. -/
structure LdPastingInInductionSectionConclusion (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (_family : IdxPolyFamily params 𝔓)
    (H : Measurement (MIPStarRE.LDT.Polynomial params.next) 𝔓)
    (eps delta gamma kappa zeta : ℝ) (k : ℕ) : Prop where
  /-- The pasted measurement is point-consistent with the ambient strategy. -/
  pointConsistency :
    strategy.state.ConsRel (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params.next H.toSubMeas)
      (ldPastingInInductionError params k eps delta gamma kappa zeta)

/-- Bookkeeping data `x ↦ (ε_x, δ_x, γ_x)` for the restricted strategies. -/
structure RestrictedFailureProfile (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) : Type where
  /-- The axis-parallel failure bound attached to each slice height. -/
  axisParallel : Fq params → ℝ
  /-- The self-consistency failure bound attached to each slice height. -/
  selfConsistency : Fq params → ℝ
  /-- The diagonal-line failure bound attached to each slice height. -/
  diagonal : Fq params → ℝ
  /-- Each slice-restricted strategy is good with the recorded parameters. -/
  restrictedGood :
    ∀ x,
      (xRestrictedStrategy params strategy x).IsGood
        (axisParallel x)
        (selfConsistency x)
        (diagonal x)

/-- Bookkeeping data for answer-valued restricted strategies.

This is the function-answer analogue of `RestrictedFailureProfile`: each slice is
the restricted strategy interface from `inductive_step.tex`, lines 436--455. -/
structure AnswerRestrictedFailureProfile (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) : Type where
  /-- The axis-parallel failure bound attached to each slice height. -/
  axisParallel : Fq params → ℝ
  /-- The self-consistency failure bound attached to each slice height. -/
  selfConsistency : Fq params → ℝ
  /-- The diagonal-line failure bound attached to each slice height. -/
  diagonal : Fq params → ℝ
  /-- Each answer-valued slice-restricted strategy is good with the recorded parameters. -/
  restrictedGood :
    ∀ x,
      (xRestrictedAnswerSymStrat params strategy x).IsGood
        (axisParallel x)
        (selfConsistency x)
        (diagonal x)

/-- Average restricted axis-parallel error over slices. -/
noncomputable def averageRestrictedAxisParallelError (params : Parameters)
    [FieldModel params.q]
    {strategy : SymStrat params.next 𝔓 K}
    (profile : RestrictedFailureProfile params strategy) : ℝ :=
  avgOver (uniformDistribution (Fq params)) profile.axisParallel

/-- Average restricted self-consistency error over slices. -/
noncomputable def averageRestrictedSelfConsistencyError (params : Parameters)
    [FieldModel params.q]
    {strategy : SymStrat params.next 𝔓 K}
    (profile : RestrictedFailureProfile params strategy) : ℝ :=
  avgOver (uniformDistribution (Fq params)) profile.selfConsistency

/-- Average restricted diagonal-line error over slices. -/
noncomputable def averageRestrictedDiagonalError (params : Parameters)
    [FieldModel params.q]
    {strategy : SymStrat params.next 𝔓 K}
    (profile : RestrictedFailureProfile params strategy) : ℝ :=
  avgOver (uniformDistribution (Fq params)) profile.diagonal

/-- Average restricted axis-parallel error over answer-valued slices. -/
noncomputable def averageAnswerRestrictedAxisParallelError (params : Parameters)
    [FieldModel params.q]
    {strategy : SymStrat params.next 𝔓 K}
    (profile : AnswerRestrictedFailureProfile params strategy) : ℝ :=
  avgOver (uniformDistribution (Fq params)) profile.axisParallel

/-- Average restricted self-consistency error over answer-valued slices. -/
noncomputable def averageAnswerRestrictedSelfConsistencyError (params : Parameters)
    [FieldModel params.q]
    {strategy : SymStrat params.next 𝔓 K}
    (profile : AnswerRestrictedFailureProfile params strategy) : ℝ :=
  avgOver (uniformDistribution (Fq params)) profile.selfConsistency

/-- Average restricted diagonal-line error over answer-valued slices. -/
noncomputable def averageAnswerRestrictedDiagonalError (params : Parameters)
    [FieldModel params.q]
    {strategy : SymStrat params.next 𝔓 K}
    (profile : AnswerRestrictedFailureProfile params strategy) : ℝ :=
  avgOver (uniformDistribution (Fq params)) profile.diagonal

/-- Paper origin: `references/ldt-paper/inductive_step.tex:374-412`
(`\label{lem:restricted-probabilities}`).

Bookkeeping data for the restricted-probabilities lemma.

This records a slice-wise error profile together with the three averaged bounds
that appear in the paper: the axis-parallel and diagonal branches both incur the
same conditioning loss `((m + 1) / m)`, while the self-consistency branch
restricts exactly. -/
structure RestrictedProbabilitiesStatement (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ) : Prop where
  /-- There is a slice-wise error profile realizing the three averaged restricted bounds. -/
  profileExists :
    ∃ profile : RestrictedFailureProfile params strategy,
      averageRestrictedAxisParallelError params profile ≤
          sliceConditioningLoss params * eps ∧
        averageRestrictedSelfConsistencyError params profile ≤ delta ∧
        averageRestrictedDiagonalError params profile ≤
          sliceConditioningLoss params * gamma

/-- Paper origin: `references/ldt-paper/inductive_step.tex:374-412`
(`\label{lem:restricted-probabilities}`); answer-valued variant carrying the
same axis-parallel/self-consistency/diagonal restriction bounds for the
answer-restricted slice profile.  This is an answer-valued variant of
`RestrictedProbabilitiesStatement` against `xRestrictedAnswerSymStrat` rather
than `xRestrictedStrategy`; no separate paper anchor exists for the
answer-valued variant.

Bookkeeping data for the answer-valued restricted-probabilities lemma. -/
structure AnswerRestrictedProbabilitiesStatement (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ) : Prop where
  /-- There is a slice-wise answer-valued error profile realizing the three averaged bounds. -/
  profileExists :
    ∃ profile : AnswerRestrictedFailureProfile params strategy,
      averageAnswerRestrictedAxisParallelError params profile ≤
          sliceConditioningLoss params * eps ∧
        averageAnswerRestrictedSelfConsistencyError params profile ≤ delta ∧
        averageAnswerRestrictedDiagonalError params profile ≤
          sliceConditioningLoss params * gamma

/-- Bookkeeping data for the slice-restriction step of `thm:main-induction`.

Paper origin: `references/ldt-paper/inductive_step.tex:374-412`
(`\label{lem:restricted-probabilities}`) and
`references/ldt-paper/inductive_step.tex:441-454`.

This records an explicit restricted failure profile together with the averaged
bounds extracted from `lem:restricted-probabilities`. -/
structure SliceRestrictionData (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ) where
  /-- Slice-wise failure profile `x ↦ (ε_x, δ_x, γ_x)`. -/
  profile : RestrictedFailureProfile params strategy
  /-- Averaged axis-parallel slice error bound. -/
  axisAverageBound :
    averageRestrictedAxisParallelError params profile ≤
      sliceConditioningLoss params * eps
  /-- Averaged self-consistency slice error bound. -/
  selfAverageBound :
    averageRestrictedSelfConsistencyError params profile ≤ delta
  /-- Averaged diagonal slice error bound. -/
  diagonalAverageBound :
    averageRestrictedDiagonalError params profile ≤
      sliceConditioningLoss params * gamma

/-- Answer-valued slice-restriction data record for the Section 6 induction step.

Paper origin: `references/ldt-paper/inductive_step.tex:374-412`
(`\label{lem:restricted-probabilities}`) and the recursive slice application in
`references/ldt-paper/inductive_step.tex:441-454`. -/
structure AnswerSliceRestrictionData (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ) where
  /-- Slice-wise failure profile for the answer-valued restricted strategies. -/
  profile : AnswerRestrictedFailureProfile params strategy
  /-- Averaged axis-parallel slice error bound. -/
  axisAverageBound :
    averageAnswerRestrictedAxisParallelError params profile ≤
      sliceConditioningLoss params * eps
  /-- Averaged self-consistency slice error bound. -/
  selfAverageBound :
    averageAnswerRestrictedSelfConsistencyError params profile ≤ delta
  /-- Averaged diagonal slice error bound. -/
  diagonalAverageBound :
    averageAnswerRestrictedDiagonalError params profile ≤
      sliceConditioningLoss params * gamma

/-- Explicit per-slice output of the inductive hypothesis.

Paper origin: `references/ldt-paper/inductive_step.tex:441-454`.

This is the recursion-entry data: given slice-restriction data, a proof of
`thm:main-induction` in dimension `m` is expected to produce a measurement `G^x`
for every slice height `x`. -/
structure PerSliceInductionData (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (restrictionPkg : SliceRestrictionData params strategy eps delta gamma)
    (k : ℕ) where
  /-- Slice-wise inductive error `σ_x`. -/
  sliceError : Fq params → ℝ
  /-- Slice-wise inductive measurement `G^x`. -/
  sliceMeasurement : Fq params → Measurement (MIPStarRE.LDT.Polynomial params) 𝔓
  /-- Each `G^x` satisfies the dimension-`m` point-consistency conclusion. -/
  pointConsistency :
    ∀ x,
      strategy.state.ConsRel (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas (xRestrictedStrategy params strategy x).pointMeasurement)
        (polynomialEvaluationFamily params (sliceMeasurement x).toSubMeas)
        (sliceError x)
  /-- The slice-wise error is bounded by the dimension-`m` induction target. -/
  error_le :
    ∀ x,
      sliceError x ≤
        mainInductionError params k
          (restrictionPkg.profile.axisParallel x)
          (restrictionPkg.profile.selfConsistency x)
          (restrictionPkg.profile.diagonal x)

/-- Explicit per-slice output of the inductive hypothesis for answer-valued slices.

Paper origin: `references/ldt-paper/inductive_step.tex:441-454`; answer-valued
restriction interface for the same recursive call.

This is the function-answer recursion-entry data record: the recursive call is made on
`xRestrictedAnswerSymStrat`, whose diagonal answers retain the whole restricted
function instead of only its value at the base point. -/
structure AnswerPerSliceInductionData (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (k : ℕ) where
  /-- Slice-wise inductive error `σ_x`. -/
  sliceError : Fq params → ℝ
  /-- Slice-wise inductive measurement `G^x`. -/
  sliceMeasurement : Fq params → Measurement (MIPStarRE.LDT.Polynomial params) 𝔓
  /-- Each `G^x` satisfies the dimension-`m` point-consistency conclusion. -/
  pointConsistency :
    ∀ x,
      strategy.state.ConsRel (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas
          (xRestrictedAnswerSymStrat params strategy x).pointMeasurement)
        (polynomialEvaluationFamily params (sliceMeasurement x).toSubMeas)
        (sliceError x)
  /-- The slice-wise error is bounded by the dimension-`m` induction target. -/
  error_le :
    ∀ x,
      sliceError x ≤
        mainInductionError params k
          (restrictionPkg.profile.axisParallel x)
          (restrictionPkg.profile.selfConsistency x)
          (restrictionPkg.profile.diagonal x)

/-- Paper origin: `references/ldt-paper/inductive_step.tex:7-18`
(`\label{thm:main-induction}`); answer-valued analogue.

Main-induction conclusion for a function-answer symmetric strategy.

This is the answer-valued analogue of the conclusion of `thm:main-induction`.
It is used as the explicit predecessor induction hypothesis for the
paper-faithful answer-valued restriction route: for a strategy in dimension `m`,
it supplies a global polynomial measurement consistent with the point
measurement at the Section 6 error `mainInductionError`. -/
def AnswerMainInductionConclusion (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params 𝔓 K)
    (eps delta gamma : ℝ) (k : ℕ) : Prop :=
  ∃ G : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓,
    strategy.state.ConsRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas)
      (mainInductionError params k eps delta gamma)

/-- Predicate form of the answer-valued predecessor main-induction hypothesis.

This is a Lean-only interface for the induction step in
`references/ldt-paper/inductive_step.tex:441-454`.  It is deliberately stated at
`mainInductionError` strength and for `AnswerSymStrat`, so callers can instantiate
the paper-faithful `xRestrictedAnswerSymStrat` slices without appealing to the
public main theorem.

It quantifies over every symmetric model: a local C*-algebra `𝔓 : Type v` and a Hilbert space
`K : Type w`, where the vendored hypothesis quantifies over a finite carrier `ι : Type v`. The
explicit `.{u,v,w}` universe binder keeps the three universes apart, as the vendored binder
`.{u,v}` keeps the universe of `FieldModel`'s carrier apart from that of the carrier, so that
a proof that instantiates `FieldModel.{0}` can still apply the hypothesis to a model in higher
universes. -/
def AnswerMainInductionHypothesis.{u, v, w} (params : Parameters)
    [FieldModel.{u} params.q] : Prop :=
  ∀ (𝔓 : Type v) [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
    (K : Type w) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K],
    ∀ (strategy : AnswerSymStrat params 𝔓 K) (eps delta gamma : ℝ) (k : ℕ),
      strategy.IsGood eps delta gamma →
        1 ≤ k →
          400 * params.m * params.d ≤ k →
            AnswerMainInductionConclusion params strategy eps delta gamma k

/-- The slice-local self-improvement error `ζ_x`. -/
noncomputable def sliceSelfImprovementError (params : Parameters)
    [FieldModel params.q]
    {strategy : SymStrat params.next 𝔓 K}
    {eps delta gamma : ℝ}
    (restrictionPkg : SliceRestrictionData params strategy eps delta gamma)
    (x : Fq params) : ℝ :=
  selfImprovementInInductionError params
    (restrictionPkg.profile.axisParallel x)
    (restrictionPkg.profile.selfConsistency x)
    (restrictionPkg.profile.diagonal x)

/-- The slice-local self-improvement error `ζ_x` for answer-valued slices. -/
noncomputable def answerSliceSelfImprovementError (params : Parameters)
    [FieldModel params.q]
    {strategy : SymStrat params.next 𝔓 K}
    {eps delta gamma : ℝ}
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (x : Fq params) : ℝ :=
  selfImprovementInInductionError params
    (restrictionPkg.profile.axisParallel x)
    (restrictionPkg.profile.selfConsistency x)
    (restrictionPkg.profile.diagonal x)

/-- Slice-wise output of the induction-level self-improvement stage.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551`
(`\label{thm:self-improvement-in-induction-section}` in use inside the proof of
`\label{thm:main-induction}`).

Because `xRestrictedStrategy` is a section-local restricted strategy rather than
literally a `SymStrat params` interface (its diagonal measurement carries no
reparametrization-invariance field, and it has no role-symmetrization API), this data
records directly the paper-faithful properties that will later be averaged into the
pasting inputs. -/
structure SelfImprovementData (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ) (k : ℕ)
    (restrictionPkg : SliceRestrictionData params strategy eps delta gamma)
    (inductionPkg : PerSliceInductionData params strategy eps delta gamma restrictionPkg k)
    where
  /-- Slice-wise projective submeasurement `Ĝ^x`. -/
  sliceProj : Fq params → ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝔓
  /-- Slice-wise PSD witness `Z^x`. -/
  sliceWitness : Fq params → 𝔓
  /-- Slice-wise completeness bound. -/
  completeness :
    ∀ x,
      strategy.state.CompletenessAtLeast ((sliceProj x).toSubMeas.liftLeft strategy.state)
        ((1 - inductionPkg.sliceError x) -
          sliceSelfImprovementError params restrictionPkg x)
  /-- Slice-wise consistency with the restricted point measurement. -/
  pointConsistency :
    ∀ x,
      strategy.state.ConsRel (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas (xRestrictedStrategy params strategy x).pointMeasurement)
        (polynomialEvaluationFamily params (sliceProj x).toSubMeas)
        (sliceSelfImprovementError params restrictionPkg x)
  /-- Slice-wise strong self-consistency. -/
  strongSelfConsistency :
    ∀ x,
      strategy.state.BipartiteSSCRel (uniformDistribution Unit)
        (constSubMeasFamily (sliceProj x).toSubMeas)
        (sliceSelfImprovementError params restrictionPkg x)
  /-- Slice-wise left/right closeness needed for the averaged self-consistency input. -/
  selfCloseness :
    ∀ x,
      strategy.state.SDDRel (uniformDistribution Unit)
        (constSubMeasFamily (strategy.state.leftPlacedSubMeas (sliceProj x).toSubMeas))
        (constSubMeasFamily (strategy.state.rightPlacedSubMeas (sliceProj x).toSubMeas))
        (sliceSelfImprovementError params restrictionPkg x)
  /-- Slice-wise boundedness residual. -/
  bounded :
    ∀ x,
      tensorFailureExpectation strategy.state (sliceWitness x) (sliceProj x).toSubMeas
        ≤ sliceSelfImprovementError params restrictionPkg x
  /-- Slice-wise domination of the averaged point operator. -/
  dominatesAveragePointOperator :
    ∀ x, ∀ h : MIPStarRE.LDT.Polynomial params,
      IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x h ≤ sliceWitness x

namespace SelfImprovementData

/-- The slice-indexed polynomial family obtained by collecting the improved
slice measurements `Ĝ^x` together with the slice-wise witnesses `Z^x`. -/
noncomputable def family {params : Parameters}
    [FieldModel params.q]
    {strategy : SymStrat params.next 𝔓 K}
    {eps delta gamma : ℝ} {k : ℕ}
    {restrictionPkg : SliceRestrictionData params strategy eps delta gamma}
    {inductionPkg :
      PerSliceInductionData params strategy eps delta gamma restrictionPkg k}
    (pkg : SelfImprovementData params strategy eps delta gamma k restrictionPkg inductionPkg) :
    IdxPolyFamily params 𝔓 where
  meas := pkg.sliceProj
  witness := pkg.sliceWitness
  dominationTarget := fun x g =>
    IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g

/-- The slice family of `pkg.family` is the improved slice family `Ĝ^x`. -/
@[simp] theorem family_meas {params : Parameters}
    [FieldModel params.q]
    {strategy : SymStrat params.next 𝔓 K}
    {eps delta gamma : ℝ} {k : ℕ}
    {restrictionPkg : SliceRestrictionData params strategy eps delta gamma}
    {inductionPkg :
      PerSliceInductionData params strategy eps delta gamma restrictionPkg k}
    (pkg : SelfImprovementData params strategy eps delta gamma k restrictionPkg inductionPkg) :
    pkg.family.meas = pkg.sliceProj :=
  rfl

/-- The witness of `pkg.family` is the slice witness `Z^x`. -/
@[simp] theorem family_witness {params : Parameters}
    [FieldModel params.q]
    {strategy : SymStrat params.next 𝔓 K}
    {eps delta gamma : ℝ} {k : ℕ}
    {restrictionPkg : SliceRestrictionData params strategy eps delta gamma}
    {inductionPkg :
      PerSliceInductionData params strategy eps delta gamma restrictionPkg k}
    (pkg : SelfImprovementData params strategy eps delta gamma k restrictionPkg inductionPkg)
    (x : Fq params) :
    pkg.family.witness x = pkg.sliceWitness x :=
  rfl

/-- The domination target of `pkg.family` is the averaged slice-point evaluation operator. -/
@[simp] theorem family_dominationTarget {params : Parameters}
    [FieldModel params.q]
    {strategy : SymStrat params.next 𝔓 K}
    {eps delta gamma : ℝ} {k : ℕ}
    {restrictionPkg : SliceRestrictionData params strategy eps delta gamma}
    {inductionPkg :
      PerSliceInductionData params strategy eps delta gamma restrictionPkg k}
    (pkg : SelfImprovementData params strategy eps delta gamma k restrictionPkg inductionPkg)
    (x : Fq params) (g : MIPStarRE.LDT.Polynomial params) :
    pkg.family.dominationTarget x g =
      IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g :=
  rfl

end SelfImprovementData

/-- Slice-wise output of the induction-level self-improvement stage for
answer-valued restricted strategies.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551`;
answer-valued restriction interface for the same self-improvement stage.

This mirrors `SelfImprovementData`, but its point-consistency field is stated
against `xRestrictedAnswerSymStrat`, the function-answer restricted strategy. -/
structure AnswerSelfImprovementData (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ) (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (inductionPkg :
      AnswerPerSliceInductionData params strategy eps delta gamma restrictionPkg k)
    where
  /-- Slice-wise projective submeasurement `Ĝ^x`. -/
  sliceProj : Fq params → ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝔓
  /-- Slice-wise PSD witness `Z^x`. -/
  sliceWitness : Fq params → 𝔓
  /-- Slice-wise completeness bound. -/
  completeness :
    ∀ x,
      strategy.state.CompletenessAtLeast ((sliceProj x).toSubMeas.liftLeft strategy.state)
        ((1 - inductionPkg.sliceError x) -
          answerSliceSelfImprovementError params restrictionPkg x)
  /-- Slice-wise consistency with the answer-valued restricted point measurement. -/
  pointConsistency :
    ∀ x,
      strategy.state.ConsRel (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas
          (xRestrictedAnswerSymStrat params strategy x).pointMeasurement)
        (polynomialEvaluationFamily params (sliceProj x).toSubMeas)
        (answerSliceSelfImprovementError params restrictionPkg x)
  /-- Slice-wise strong self-consistency. -/
  strongSelfConsistency :
    ∀ x,
      strategy.state.BipartiteSSCRel (uniformDistribution Unit)
        (constSubMeasFamily (sliceProj x).toSubMeas)
        (answerSliceSelfImprovementError params restrictionPkg x)
  /-- Slice-wise left/right closeness needed for the averaged self-consistency data record. -/
  selfCloseness :
    ∀ x,
      strategy.state.SDDRel (uniformDistribution Unit)
        (constSubMeasFamily (strategy.state.leftPlacedSubMeas (sliceProj x).toSubMeas))
        (constSubMeasFamily (strategy.state.rightPlacedSubMeas (sliceProj x).toSubMeas))
        (answerSliceSelfImprovementError params restrictionPkg x)
  /-- Slice-wise boundedness residual. -/
  bounded :
    ∀ x,
      tensorFailureExpectation strategy.state (sliceWitness x) (sliceProj x).toSubMeas
        ≤ answerSliceSelfImprovementError params restrictionPkg x
  /-- Slice-wise domination of the averaged point operator. -/
  dominatesAveragePointOperator :
    ∀ x, ∀ h : MIPStarRE.LDT.Polynomial params,
      IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x h ≤ sliceWitness x

namespace AnswerSelfImprovementData

/-- The slice-indexed polynomial family obtained from answer-valued restricted
self-improvement outputs. -/
noncomputable def family {params : Parameters}
    [FieldModel params.q]
    {strategy : SymStrat params.next 𝔓 K}
    {eps delta gamma : ℝ} {k : ℕ}
    {restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma}
    {inductionPkg :
      AnswerPerSliceInductionData params strategy eps delta gamma restrictionPkg k}
    (pkg :
      AnswerSelfImprovementData params strategy eps delta gamma k restrictionPkg inductionPkg) :
    IdxPolyFamily params 𝔓 where
  meas := pkg.sliceProj
  witness := pkg.sliceWitness
  dominationTarget := fun x g =>
    IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g

/-- The slice family of `pkg.family` is the improved slice family `Ĝ^x`. -/
@[simp] theorem family_meas {params : Parameters}
    [FieldModel params.q]
    {strategy : SymStrat params.next 𝔓 K}
    {eps delta gamma : ℝ} {k : ℕ}
    {restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma}
    {inductionPkg :
      AnswerPerSliceInductionData params strategy eps delta gamma restrictionPkg k}
    (pkg :
      AnswerSelfImprovementData params strategy eps delta gamma k restrictionPkg inductionPkg) :
    pkg.family.meas = pkg.sliceProj :=
  rfl

/-- The witness of `pkg.family` is the slice witness `Z^x`. -/
@[simp] theorem family_witness {params : Parameters}
    [FieldModel params.q]
    {strategy : SymStrat params.next 𝔓 K}
    {eps delta gamma : ℝ} {k : ℕ}
    {restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma}
    {inductionPkg :
      AnswerPerSliceInductionData params strategy eps delta gamma restrictionPkg k}
    (pkg :
      AnswerSelfImprovementData params strategy eps delta gamma k restrictionPkg inductionPkg)
    (x : Fq params) :
    pkg.family.witness x = pkg.sliceWitness x :=
  rfl

/-- The domination target of `pkg.family` is the averaged slice-point evaluation operator. -/
@[simp] theorem family_dominationTarget {params : Parameters}
    [FieldModel params.q]
    {strategy : SymStrat params.next 𝔓 K}
    {eps delta gamma : ℝ} {k : ℕ}
    {restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma}
    {inductionPkg :
      AnswerPerSliceInductionData params strategy eps delta gamma restrictionPkg k}
    (pkg :
      AnswerSelfImprovementData params strategy eps delta gamma k restrictionPkg inductionPkg)
    (x : Fq params) (g : MIPStarRE.LDT.Polynomial params) :
    pkg.family.dominationTarget x g =
      IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g :=
  rfl

end AnswerSelfImprovementData

/-- Paper origin: `references/ldt-paper/ld-pasting.tex:12-50`
(`\label{thm:ld-pasting}`) and
`references/ldt-paper/inductive_step.tex:239-342`.

Averaged pasting inputs distilled from the per-slice self-improvement data.

This records exactly the hypotheses needed to invoke
`thm:ld-pasting-in-induction-section` after the slice-wise self-improvement
outputs have been averaged. -/
structure AveragedPastingData (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ) (k : ℕ)
    {restrictionPkg : SliceRestrictionData params strategy eps delta gamma}
    {inductionPkg :
      PerSliceInductionData params strategy eps delta gamma restrictionPkg k}
    (selfPkg : SelfImprovementData params strategy eps delta gamma k restrictionPkg inductionPkg)
    where
  /-- Averaged completeness parameter `κ`. -/
  kappa : ℝ
  /-- Averaged self-improvement / pasting interface parameter `ζ`. -/
  zeta : ℝ
  /-- Averaged completeness of the slice family. -/
  complete : selfPkg.family.Complete strategy.state kappa
  /-- Averaged point-consistency of the slice family. -/
  consistent : selfPkg.family.ConsistentWithPoints strategy zeta
  /-- Averaged strong self-consistency of the slice family. -/
  selfConsistent : selfPkg.family.StronglySelfConsistent strategy.state zeta
  /-- Averaged boundedness input for the pasting theorem. -/
  bounded : IdxPolyFamily.SliceBoundednessInput strategy selfPkg.family zeta
  /-- Error telescoping from the induction-section pasting bound to the next-stage target. -/
  error_le :
    ldPastingInInductionError params k eps delta gamma kappa zeta ≤
      mainInductionError params.next k eps delta gamma

end MIPRE.LIDT.Co.MainInductionStep

end

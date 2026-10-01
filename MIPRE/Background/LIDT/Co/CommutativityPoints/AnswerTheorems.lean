/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
CommutativityPoints/AnswerTheorems.lean, to the symmetric model of `planning/c6b-plan.md`; not a
vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.CommutativityPoints.SharedHelpers.SharedLine
public import MIPRE.Background.LIDT.Co.Preliminaries.DistanceBounds

@[expose] public section

/-!
# Section 10 commutativity points: answer-valued diagonal measurements

This file proves the commutativity-at-points theorem using the answer-valued
diagonal-line verifier relation: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/CommutativityPoints/AnswerTheorems.lean` in the port of
`planning/c6b-plan.md` (milestone M1, section "Port conventions"). The conclusion concerns only
the point measurements, hence it can later be transferred to the ordinary carrier used by
self-improvement, but the proof does not use the carrier's inert diagonal measurement.

The strategy is an answer-valued symmetric strategy `strategy : AnswerSymStrat params 𝔓 K`: the
point answers are placed by `strategy.state.L`, the line answers by `strategy.state.R`, and the
joint operators are `K →L[ℂ] K`. The answer-valued route is ported as the vendored file has it,
parallel to the bridge theorems for `SymStrat` and not unified with them. The vendored file has
no classical content, so it is not imported; the classical names it uses come from the vendored
`Defs`, `Approximation` and `SharedHelpers/SharedLine` through the imports of
`Co/CommutativityPoints/SharedHelpers/SharedLine.lean`, named by an explicit
`open MIPStarRE.LDT.CommutativityPoints (…)` list.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/commutativity-points.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`

In this repository: `lem:co-commutativity-points` in `blueprint/src/content/08_downstream.tex`.
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.CommutativityPoints

open MIPStarRE.LDT (Parameters FieldModel Fq avgOver uniformDistribution)
open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)
open MIPStarRE.LDT.CommutativityPoints (PointPairOutcome PointDiagonalLineQuestion
  PointPairDiagonalLineQuestion sampledPointFromDiagonalQuestion
  sampledPointPairFromSharedDiagonalQuestion pointWithDiagonalLineDistribution
  pointPairSharedDiagonalLineDistribution restrictedDiagonalLinesConsistencyError
  pointDiagonalLineApproxError commutativityPointsError pointPairOutcomeSwapEquiv
  avgOver_pointPairSharedDiagonalLine_ignore_first
  avgOver_pointPairSharedDiagonalLine_ignore_second
  avgOver_pointPairSharedDiagonalLine_sampled_pair)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The point measurement, reindexed by a sampled diagonal line and a parameter
on it, for an answer-valued strategy. -/
def answerSampledPointMeasurement
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params 𝔓 K) :
    IdxSubMeas (PointDiagonalLineQuestion params) (Fq params) 𝔓 :=
  fun q =>
    (strategy.pointMeasurement (sampledPointFromDiagonalQuestion params q)).toSubMeas

/-- Evaluate an answer-valued diagonal-line measurement at the sampled
parameter. -/
noncomputable def answerSampledDiagonalLineEvaluation
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params 𝔓 K) :
    IdxSubMeas (PointDiagonalLineQuestion params) (Fq params) 𝔓 :=
  fun q =>
    postprocess ((strategy.diagonalMeasurement q.1).toSubMeas) (fun f => f q.2)

/-- The ordered point product `(A^u_a A^v_b) ⊗ I` for an answer-valued
strategy, placed by `strategy.state.L`. -/
noncomputable def answerPointMeasurementProductLeft
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params 𝔓 K) :
    IdxOpFamily (PointPairQuestion params) (PointPairOutcome params) (K →L[ℂ] K) :=
  fun uv =>
    let Au := (strategy.pointMeasurement uv.1).toSubMeas
    let Av := (strategy.pointMeasurement uv.2).toSubMeas
    OpFamily.leftPlacedOpFamily strategy.state <|
      orderedProductOpFamily Au Av

/-- The reversed point product `(A^v_b A^u_a) ⊗ I` for an answer-valued
strategy, placed by `strategy.state.L`. -/
noncomputable def answerPointMeasurementProductRight
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params 𝔓 K) :
    IdxOpFamily (PointPairQuestion params) (PointPairOutcome params) (K →L[ℂ] K) :=
  fun uv =>
    let Au := (strategy.pointMeasurement uv.1).toSubMeas
    let Av := (strategy.pointMeasurement uv.2).toSubMeas
    OpFamily.leftPlacedOpFamily strategy.state <|
      reversedProductOpFamily Au Av

/-- The ordered point product, indexed by a shared sampled line. -/
noncomputable def answerPointMeasurementProductAlongSharedLine
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params 𝔓 K) :
    IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (K →L[ℂ] K) :=
  fun q =>
    answerPointMeasurementProductLeft params strategy
      (sampledPointPairFromSharedDiagonalQuestion params q)

/-- The reversed point product, indexed by a shared sampled line. -/
noncomputable def answerPointMeasurementProductAlongSharedLineReversed
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params 𝔓 K) :
    IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (K →L[ℂ] K) :=
  fun q =>
    answerPointMeasurementProductRight params strategy
      (sampledPointPairFromSharedDiagonalQuestion params q)

/-- The mixed bridge `A^u_a ⊗ L^ℓ_[f(v)=b]`, placed by `strategy.state`. -/
noncomputable def answerPointDiagonalLineMixedProductLeft
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params 𝔓 K) :
    IdxSubMeas (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (K →L[ℂ] K) :=
  fun q =>
    let ℓ := q.1
    let tu := q.2.1
    let tv := q.2.2
    let Au := (strategy.pointMeasurement (ℓ.pointAt tu)).toSubMeas
    let Lv := answerSampledDiagonalLineEvaluation params strategy (ℓ, tv)
    tensorProductSubMeas strategy.state Au Lv

/-- The bridge `I ⊗ (L^ℓ_[f(v)=b] · L^ℓ_[f(u)=a])`, placed by `strategy.state.R`. -/
noncomputable def answerDiagonalLineProductOrdered
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params 𝔓 K) :
    IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (K →L[ℂ] K) :=
  fun q =>
    let ℓ := q.1
    let tu := q.2.1
    let tv := q.2.2
    let Lu := answerSampledDiagonalLineEvaluation params strategy (ℓ, tu)
    let Lv := answerSampledDiagonalLineEvaluation params strategy (ℓ, tv)
    OpFamily.rightPlacedOpFamily strategy.state <|
      reversedProductOpFamily Lu Lv

/-- The swapped bridge `I ⊗ (L^ℓ_[f(u)=a] · L^ℓ_[f(v)=b])`, placed by `strategy.state.R`. -/
noncomputable def answerDiagonalLineProductReversed
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params 𝔓 K) :
    IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (K →L[ℂ] K) :=
  fun q =>
    let ℓ := q.1
    let tu := q.2.1
    let tv := q.2.2
    let Lu := answerSampledDiagonalLineEvaluation params strategy (ℓ, tu)
    let Lv := answerSampledDiagonalLineEvaluation params strategy (ℓ, tv)
    OpFamily.rightPlacedOpFamily strategy.state <|
      orderedProductOpFamily Lu Lv

/-- The mixed bridge `A^v_b ⊗ L^ℓ_[f(u)=a]`, placed by `strategy.state`, with outcome `(a, b)`:
`a` indexes the line evaluation and `b` the point measurement. -/
noncomputable def answerPointDiagonalLineMixedProductRight
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params 𝔓 K) :
    IdxSubMeas (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (K →L[ℂ] K) :=
  fun q =>
    let ℓ := q.1
    let tu := q.2.1
    let tv := q.2.2
    let Av := (strategy.pointMeasurement (ℓ.pointAt tv)).toSubMeas
    let Lu := answerSampledDiagonalLineEvaluation params strategy (ℓ, tu)
    postprocess (tensorProductSubMeas strategy.state Av Lu) Prod.swap

/-- Outcome `(a, b)` of the left mixed bridge: it is `A^u_a ⊗ L^ℓ_[f(v)=b]`, the point
measurement at `u` and the answer-valued diagonal-line evaluation at `t_v`, placed by
`strategy.state.opTensor`. -/
theorem answerPointDiagonalLineMixedProductLeft_outcome
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params 𝔓 K)
    (q : PointPairDiagonalLineQuestion params)
    (a b : Fq params) :
    ((IdxSubMeas.toIdxOpFamily
        (answerPointDiagonalLineMixedProductLeft params strategy) q).outcome (a, b)) =
      strategy.state.opTensor
        ((strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome a)
        ((answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).outcome b) :=
  rfl

/-- Outcome `(a, b)` of the right mixed bridge: it is `A^v_b ⊗ L^ℓ_[f(u)=a]`, the point
measurement at `v` and the answer-valued diagonal-line evaluation at `t_u`, placed by
`strategy.state.opTensor`, the post-processing having swapped the outcome pair back. -/
theorem answerPointDiagonalLineMixedProductRight_outcome
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params 𝔓 K)
    (q : PointPairDiagonalLineQuestion params)
    (a b : Fq params) :
    ((IdxSubMeas.toIdxOpFamily
        (answerPointDiagonalLineMixedProductRight params strategy) q).outcome (a, b)) =
      strategy.state.opTensor
        ((strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b)
        ((answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a) := by
  classical
  suffices h :
      ∑ ab : Fq params × Fq params with ab.2 = a ∧ ab.1 = b,
        strategy.state.opTensor
          ((strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome ab.1)
          ((answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome ab.2) =
      strategy.state.opTensor ((strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b)
        ((answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a) by
    simpa [answerPointDiagonalLineMixedProductRight, tensorProductSubMeas,
      postprocess, Prod.swap, IdxSubMeas.toIdxOpFamily, SubMeas.toOpFamily] using h
  have hfilter :
      (Finset.univ.filter (fun ab : Fq params × Fq params => ab.2 = a ∧ ab.1 = b)) =
        {(b, a)} := by
    ext ab
    rcases ab with ⟨a', b'⟩
    simp [and_comm]
  rw [hfilter]
  simp

/-- For a good answer-valued strategy, over the shared-diagonal-line distribution, the point
measurement at the second point `v`, placed left, and the answer-valued diagonal-line evaluation at
`t_v`, placed right, are `pointDiagonalLineApproxError params gamma`-close (`SDDOpRel`): the
first point is ignored, `(ℓ, t_v)` having the law of `pointWithDiagonalLineDistribution`. -/
theorem answerSampledDiagonalLineApproximation_ignore_first
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma) :
    strategy.state.SDDOpRel
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.leftPlacedOpFamily strategy.state
          ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas))
      (fun q =>
        OpFamily.rightPlacedOpFamily strategy.state
          (SubMeas.toOpFamily (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2))))
      (pointDiagonalLineApproxError params gamma) := by
  rcases answer_sampledDiagonalLineApproximation_pointWithDiagonalLine
    params strategy eps delta gamma hgood with ⟨happrox⟩
  constructor
  calc
    strategy.state.sddErrorOp
        (pointPairSharedDiagonalLineDistribution params)
        (fun q =>
          OpFamily.leftPlacedOpFamily strategy.state
            ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas))
        (fun q =>
          OpFamily.rightPlacedOpFamily strategy.state
            (SubMeas.toOpFamily
              (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2))))
      = avgOver (pointPairSharedDiagonalLineDistribution params)
          (fun q =>
            strategy.state.qSDD
              ((IdxSubMeas.liftLeft strategy.state
                (answerSampledPointMeasurement params strategy)) (q.1, q.2.2))
              ((IdxSubMeas.liftRight strategy.state
                (answerSampledDiagonalLineEvaluation params strategy)) (q.1, q.2.2))) := rfl
    _ = avgOver (pointWithDiagonalLineDistribution params)
          (fun q =>
            strategy.state.qSDD
              ((IdxSubMeas.liftLeft strategy.state
                (answerSampledPointMeasurement params strategy)) q)
              ((IdxSubMeas.liftRight strategy.state
                (answerSampledDiagonalLineEvaluation params strategy)) q)) :=
            avgOver_pointPairSharedDiagonalLine_ignore_first params
              (fun q =>
                strategy.state.qSDD
                  ((IdxSubMeas.liftLeft strategy.state
                    (answerSampledPointMeasurement params strategy)) q)
                  ((IdxSubMeas.liftRight strategy.state
                    (answerSampledDiagonalLineEvaluation params strategy)) q))
    _ = strategy.state.sddError
          (pointWithDiagonalLineDistribution params)
          (IdxSubMeas.liftLeft strategy.state (answerSampledPointMeasurement params strategy))
          (IdxSubMeas.liftRight strategy.state
            (answerSampledDiagonalLineEvaluation params strategy)) := rfl
    _ ≤ pointDiagonalLineApproxError params gamma := happrox

/-- For a good answer-valued strategy, over the shared-diagonal-line distribution, the point
measurement at the first point `u`, placed left, and the answer-valued diagonal-line evaluation at
`t_u`, placed right, are `pointDiagonalLineApproxError params gamma`-close (`SDDOpRel`): the
second point is ignored, `(ℓ, t_u)` having the law of `pointWithDiagonalLineDistribution`. -/
theorem answerSampledDiagonalLineApproximation_ignore_second
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma) :
    strategy.state.SDDOpRel
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.leftPlacedOpFamily strategy.state
          ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas))
      (fun q =>
        OpFamily.rightPlacedOpFamily strategy.state
          (SubMeas.toOpFamily (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1))))
      (pointDiagonalLineApproxError params gamma) := by
  rcases answer_sampledDiagonalLineApproximation_pointWithDiagonalLine
    params strategy eps delta gamma hgood with ⟨happrox⟩
  constructor
  calc
    strategy.state.sddErrorOp
        (pointPairSharedDiagonalLineDistribution params)
        (fun q =>
          OpFamily.leftPlacedOpFamily strategy.state
            ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas))
        (fun q =>
          OpFamily.rightPlacedOpFamily strategy.state
            (SubMeas.toOpFamily
              (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1))))
      = avgOver (pointPairSharedDiagonalLineDistribution params)
          (fun q =>
            strategy.state.qSDD
              ((IdxSubMeas.liftLeft strategy.state
                (answerSampledPointMeasurement params strategy)) (q.1, q.2.1))
              ((IdxSubMeas.liftRight strategy.state
                (answerSampledDiagonalLineEvaluation params strategy)) (q.1, q.2.1))) := rfl
    _ = avgOver (pointWithDiagonalLineDistribution params)
          (fun q =>
            strategy.state.qSDD
              ((IdxSubMeas.liftLeft strategy.state
                (answerSampledPointMeasurement params strategy)) q)
              ((IdxSubMeas.liftRight strategy.state
                (answerSampledDiagonalLineEvaluation params strategy)) q)) :=
            avgOver_pointPairSharedDiagonalLine_ignore_second params
              (fun q =>
                strategy.state.qSDD
                  ((IdxSubMeas.liftLeft strategy.state
                    (answerSampledPointMeasurement params strategy)) q)
                  ((IdxSubMeas.liftRight strategy.state
                    (answerSampledDiagonalLineEvaluation params strategy)) q))
    _ = strategy.state.sddError
          (pointWithDiagonalLineDistribution params)
          (IdxSubMeas.liftLeft strategy.state (answerSampledPointMeasurement params strategy))
          (IdxSubMeas.liftRight strategy.state
            (answerSampledDiagonalLineEvaluation params strategy)) := rfl
    _ ≤ pointDiagonalLineApproxError params gamma := happrox

/-- **Lean-only:** A local tensor-placement comparison in the answer-valued
point-commutativity chain.

Paper origin: upstream `references/ldt-paper/commutativity_points.tex`; this is one of
the formal transport steps used to realize the mixed point/diagonal comparison
appearing in the paper.  It is internal to the answer-valued implementation
tracked in upstream issue #1507 and is not a source theorem.  Discharge: proved here from
the already formalized point-to-diagonal-line approximation and tensor-ordering
identities. -/
theorem answerOrderedLiftToMixedLine
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma) :
    strategy.state.SDDOpRel
      (pointPairSharedDiagonalLineDistribution params)
      (answerPointMeasurementProductAlongSharedLine params strategy)
      (IdxSubMeas.toIdxOpFamily (answerPointDiagonalLineMixedProductLeft params strategy))
      (pointDiagonalLineApproxError params gamma) := by
  let e := pointPairOutcomeSwapEquiv params
  let Araw : IdxOpFamily (PointPairDiagonalLineQuestion params) (Fq params × Fq params)
      (K →L[ℂ] K) :=
    fun q =>
      let Au := (strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas
      let Av := (strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas
      opFamilyOfOutcome fun ab : PointPairOutcome params =>
        (Au.liftLeft strategy.state).outcome ab.2 *
          (OpFamily.leftPlacedOpFamily strategy.state Av).outcome ab.1
  let Braw : IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params)
      (K →L[ℂ] K) :=
    fun q =>
      let Au := (strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas
      let Lv := answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2)
      opFamilyOfOutcome fun ab : PointPairOutcome params =>
        (Au.liftLeft strategy.state).outcome ab.2 *
          (OpFamily.rightPlacedOpFamily strategy.state Lv.toOpFamily).outcome ab.1
  let hbase :=
    answerSampledDiagonalLineApproximation_ignore_first params strategy eps delta gamma hgood
  let hcab :=
    MIPRE.LIDT.Co.Preliminaries.cabApproxDelta_raw
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.leftPlacedOpFamily strategy.state
          ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas))
      (fun q =>
        OpFamily.rightPlacedOpFamily strategy.state
          (SubMeas.toOpFamily (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2))))
      (fun q _b a =>
        (((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas).liftLeft
          strategy.state).outcome a)
      (pointDiagonalLineApproxError params gamma)
      hbase
      (by
        intro q b
        exact subMeas_sum_adjoint_mul_le_one
          (((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas).liftLeft strategy.state))
  have hreindexed :=
    sddOpRel_reindex e strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      Araw
      Braw
      (pointDiagonalLineApproxError params gamma)
      hcab
  let Astep :
      IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (K →L[ℂ] K) :=
    fun q =>
      ({ outcome := fun ab : PointPairOutcome params => (Araw q).outcome (e.symm ab)
         total := (Araw q).total } : OpFamily (PointPairOutcome params) (K →L[ℂ] K))
  let Bstep :
      IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (K →L[ℂ] K) :=
    fun q =>
      ({ outcome := fun ab : PointPairOutcome params => (Braw q).outcome (e.symm ab)
         total := (Braw q).total } : OpFamily (PointPairOutcome params) (K →L[ℂ] K))
  exact sddOpRel_congr_outcome strategy.state
    (pointPairSharedDiagonalLineDistribution params)
    Astep Bstep
    (answerPointMeasurementProductAlongSharedLine params strategy)
    (IdxSubMeas.toIdxOpFamily (answerPointDiagonalLineMixedProductLeft params strategy))
    (pointDiagonalLineApproxError params gamma)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Astep q).outcome (a, b)
          = strategy.state.L
              ((strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome a *
                (strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b) :=
                  liftLeft_mul_leftPlaced_outcome strategy.state
                    ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas)
                    ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas)
                    a b
        _ = (answerPointMeasurementProductAlongSharedLine params strategy q).outcome
              (a, b) := rfl)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Bstep q).outcome (a, b)
          = strategy.state.opTensor
              ((strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome a)
              ((answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).outcome b) :=
                  liftLeft_mul_rightPlaced_outcome strategy.state
                    ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas)
                    (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2))
                    a b
        _ =
            ((IdxSubMeas.toIdxOpFamily
                (answerPointDiagonalLineMixedProductLeft params strategy)) q).outcome
              (a, b) :=
              (answerPointDiagonalLineMixedProductLeft_outcome params strategy q a b).symm)
    hreindexed

/-- **Lean-only:** A local tensor-placement comparison from the mixed product to
the ordered diagonal-line product.

Paper origin: upstream `references/ldt-paper/commutativity_points.tex`; this is an
internal reindexing and tensor-ordering step in the answer-valued
point-commutativity route tracked in upstream issue #1507.  Discharge: proved here by
transporting the point-to-line comparison through the explicit ordered product
identities. -/
theorem answerOrderedLiftToLineProduct
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma) :
    strategy.state.SDDOpRel
      (pointPairSharedDiagonalLineDistribution params)
      (IdxSubMeas.toIdxOpFamily (answerPointDiagonalLineMixedProductLeft params strategy))
      (answerDiagonalLineProductOrdered params strategy)
      (pointDiagonalLineApproxError params gamma) := by
  let hbase :=
    answerSampledDiagonalLineApproximation_ignore_second params strategy eps delta gamma hgood
  have hcab :=
    MIPRE.LIDT.Co.Preliminaries.cabApproxDelta_raw
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.leftPlacedOpFamily strategy.state
          ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas))
      (fun q =>
        OpFamily.rightPlacedOpFamily strategy.state
          (SubMeas.toOpFamily (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1))))
      (fun q _a b =>
        ((answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).liftRight
          strategy.state).outcome b)
      (pointDiagonalLineApproxError params gamma)
      hbase
      (by
        intro q a
        exact subMeas_sum_adjoint_mul_le_one
          ((answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).liftRight
            strategy.state))
  let Astep : IdxOpFamily (PointPairDiagonalLineQuestion params) (Fq params × Fq params)
      (K →L[ℂ] K) :=
    fun q =>
      let Au := (strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas
      let Lv := answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2)
      ({ outcome := fun ab : Fq params × Fq params =>
           (Lv.liftRight strategy.state).outcome ab.2 *
             (OpFamily.leftPlacedOpFamily strategy.state Au).outcome ab.1
         total := ∑ ab : Fq params × Fq params,
           (Lv.liftRight strategy.state).outcome ab.2 *
             (OpFamily.leftPlacedOpFamily strategy.state Au).outcome ab.1
       } : OpFamily (Fq params × Fq params) (K →L[ℂ] K))
  let Bstep : IdxOpFamily (PointPairDiagonalLineQuestion params) (Fq params × Fq params)
      (K →L[ℂ] K) :=
    fun q =>
      let Lu := answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1)
      let Lv := answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2)
      ({ outcome := fun ab : Fq params × Fq params =>
           (Lv.liftRight strategy.state).outcome ab.2 *
             (OpFamily.rightPlacedOpFamily strategy.state (SubMeas.toOpFamily Lu)).outcome ab.1
         total := ∑ ab : Fq params × Fq params,
           (Lv.liftRight strategy.state).outcome ab.2 *
             (OpFamily.rightPlacedOpFamily strategy.state (SubMeas.toOpFamily Lu)).outcome ab.1
       } : OpFamily (Fq params × Fq params) (K →L[ℂ] K))
  exact sddOpRel_congr_outcome strategy.state
    (pointPairSharedDiagonalLineDistribution params)
    Astep Bstep
    (IdxSubMeas.toIdxOpFamily (answerPointDiagonalLineMixedProductLeft params strategy))
    (answerDiagonalLineProductOrdered params strategy)
    (pointDiagonalLineApproxError params gamma)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Astep q).outcome (a, b)
          = strategy.state.opTensor
              ((strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome a)
              ((answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).outcome b) :=
                  liftRight_mul_leftPlaced_outcome strategy.state
                    (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2))
                    ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas)
                    b a
        _ =
            ((IdxSubMeas.toIdxOpFamily
                (answerPointDiagonalLineMixedProductLeft params strategy)) q).outcome
              (a, b) :=
              (answerPointDiagonalLineMixedProductLeft_outcome params strategy q a b).symm)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Bstep q).outcome (a, b)
          = strategy.state.R
              ((answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).outcome b *
                (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a) :=
                  liftRight_mul_rightPlaced_outcome strategy.state
                    (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2))
                    (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1))
                    b a
        _ = (answerDiagonalLineProductOrdered params strategy q).outcome (a, b) := rfl)
    hcab

/-- **Lean-only:** A local tensor-placement comparison from the ordered
diagonal-line product to the reversed mixed product.

Paper origin: upstream `references/ldt-paper/commutativity_points.tex`; this is an
internal answer-valued implementation step for the point-commutativity argument
tracked in upstream issue #1507.  Discharge: proved here from the reversed
point-to-line comparison and the explicit ordered/reversed product equality. -/
theorem answerOrderedDropFromLineComparison
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma) :
    strategy.state.SDDOpRel
      (pointPairSharedDiagonalLineDistribution params)
      (answerDiagonalLineProductOrdered params strategy)
      (IdxSubMeas.toIdxOpFamily (answerPointDiagonalLineMixedProductRight params strategy))
      (pointDiagonalLineApproxError params gamma) := by
  have hrev :
      strategy.state.SDDOpRel
        (pointPairSharedDiagonalLineDistribution params)
        (answerDiagonalLineProductReversed params strategy)
        (IdxSubMeas.toIdxOpFamily (answerPointDiagonalLineMixedProductRight params strategy))
        (pointDiagonalLineApproxError params gamma) := by
    let e := pointPairOutcomeSwapEquiv params
    let Araw : IdxOpFamily (PointPairDiagonalLineQuestion params) (Fq params × Fq params)
        (K →L[ℂ] K) :=
      fun q =>
        let Lu := answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1)
        let Lv := answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2)
        opFamilyOfOutcome fun ab : PointPairOutcome params =>
          (Lu.liftRight strategy.state).outcome ab.2 *
            (OpFamily.rightPlacedOpFamily strategy.state Lv.toOpFamily).outcome ab.1
    let Braw : IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params)
        (K →L[ℂ] K) :=
      fun q =>
        let Lu := answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1)
        let Av := (strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas
        opFamilyOfOutcome fun ab : PointPairOutcome params =>
          (Lu.liftRight strategy.state).outcome ab.2 *
            (OpFamily.leftPlacedOpFamily strategy.state Av).outcome ab.1
    let hbase :=
      sddOpRel_symm strategy.state
        (pointPairSharedDiagonalLineDistribution params)
        (fun q =>
          OpFamily.leftPlacedOpFamily strategy.state
            ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas))
        (fun q =>
          OpFamily.rightPlacedOpFamily strategy.state
            (SubMeas.toOpFamily
              (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2))))
        (pointDiagonalLineApproxError params gamma)
        (answerSampledDiagonalLineApproximation_ignore_first params strategy eps delta gamma hgood)
    let hcab :=
      MIPRE.LIDT.Co.Preliminaries.cabApproxDelta_raw
        strategy.state
        (pointPairSharedDiagonalLineDistribution params)
        (fun q =>
          OpFamily.rightPlacedOpFamily strategy.state
            (SubMeas.toOpFamily
              (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2))))
        (fun q =>
          OpFamily.leftPlacedOpFamily strategy.state
            ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas))
        (fun q _b a =>
          ((answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).liftRight
            strategy.state).outcome a)
        (pointDiagonalLineApproxError params gamma)
        hbase
        (by
          intro q b
          exact subMeas_sum_adjoint_mul_le_one
            ((answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).liftRight
              strategy.state))
    have hreindexed :=
      sddOpRel_reindex e strategy.state
        (pointPairSharedDiagonalLineDistribution params)
        Araw
        Braw
        (pointDiagonalLineApproxError params gamma)
        hcab
    let Astep :
        IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params)
          (K →L[ℂ] K) :=
      fun q =>
        ({ outcome := fun ab : PointPairOutcome params => (Araw q).outcome (e.symm ab)
           total := (Araw q).total } : OpFamily (PointPairOutcome params) (K →L[ℂ] K))
    let Bstep :
        IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params)
          (K →L[ℂ] K) :=
      fun q =>
        ({ outcome := fun ab : PointPairOutcome params => (Braw q).outcome (e.symm ab)
           total := (Braw q).total } : OpFamily (PointPairOutcome params) (K →L[ℂ] K))
    exact sddOpRel_congr_outcome strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      Astep Bstep
      (answerDiagonalLineProductReversed params strategy)
      (IdxSubMeas.toIdxOpFamily (answerPointDiagonalLineMixedProductRight params strategy))
      (pointDiagonalLineApproxError params gamma)
      (by
        intro q ab
        rcases ab with ⟨a, b⟩
        calc
          (Astep q).outcome (a, b)
            = strategy.state.R
                ((answerSampledDiagonalLineEvaluation params strategy
                    (q.1, q.2.1)).outcome a *
                  (answerSampledDiagonalLineEvaluation params strategy
                    (q.1, q.2.2)).outcome b) :=
                    liftRight_mul_rightPlaced_outcome strategy.state
                      (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1))
                      (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2))
                      a b
          _ = (answerDiagonalLineProductReversed params strategy q).outcome (a, b) := rfl)
      (by
        intro q ab
        rcases ab with ⟨a, b⟩
        calc
          (Bstep q).outcome (a, b)
            = strategy.state.opTensor
                ((strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b)
                ((answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a) :=
                    liftRight_mul_leftPlaced_outcome strategy.state
                      (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1))
                      ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas)
                      a b
          _ =
              ((IdxSubMeas.toIdxOpFamily
                  (answerPointDiagonalLineMixedProductRight params strategy)) q).outcome
                (a, b) :=
                (answerPointDiagonalLineMixedProductRight_outcome params strategy q a b).symm)
      hreindexed
  exact sddOpRel_congr_outcome strategy.state
    (pointPairSharedDiagonalLineDistribution params)
    (answerDiagonalLineProductReversed params strategy)
    (IdxSubMeas.toIdxOpFamily (answerPointDiagonalLineMixedProductRight params strategy))
    (answerDiagonalLineProductOrdered params strategy)
    (IdxSubMeas.toIdxOpFamily (answerPointDiagonalLineMixedProductRight params strategy))
    (pointDiagonalLineApproxError params gamma)
    (fun q ⟨a, b⟩ =>
      congrArg strategy.state.R
        ((strategy.diagonalMeasurement q.1).postprocess_outcome_commute
          (fun f => f q.2.1) (fun f => f q.2.2) a b))
    (fun _ _ => rfl)
    hrev

/-- **Lean-only:** A local tensor-placement comparison from the reversed mixed
product back to the reversed point product.

Paper origin: upstream `references/ldt-paper/commutativity_points.tex`; this is the last
internal answer-valued transport step in the point-commutativity chain tracked
in upstream issue #1507.  Discharge: proved here from the line-to-point comparison and
the explicit tensor-placement identities. -/
theorem answerReversedDropToPointsComparison
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma) :
    strategy.state.SDDOpRel
      (pointPairSharedDiagonalLineDistribution params)
      (IdxSubMeas.toIdxOpFamily (answerPointDiagonalLineMixedProductRight params strategy))
      (answerPointMeasurementProductAlongSharedLineReversed params strategy)
      (pointDiagonalLineApproxError params gamma) := by
  let Astep : IdxOpFamily (PointPairDiagonalLineQuestion params) (Fq params × Fq params)
      (K →L[ℂ] K) :=
    fun q =>
      let Av := (strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas
      let Lu := answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1)
      ({ outcome := fun ab : Fq params × Fq params =>
           (Av.liftLeft strategy.state).outcome ab.2 *
             (OpFamily.rightPlacedOpFamily strategy.state (SubMeas.toOpFamily Lu)).outcome ab.1
         total := ∑ ab : Fq params × Fq params,
           (Av.liftLeft strategy.state).outcome ab.2 *
             (OpFamily.rightPlacedOpFamily strategy.state (SubMeas.toOpFamily Lu)).outcome ab.1
       } : OpFamily (Fq params × Fq params) (K →L[ℂ] K))
  let Bstep : IdxOpFamily (PointPairDiagonalLineQuestion params) (Fq params × Fq params)
      (K →L[ℂ] K) :=
    fun q =>
      let Au := (strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas
      let Av := (strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas
      ({ outcome := fun ab : Fq params × Fq params =>
           (Av.liftLeft strategy.state).outcome ab.2 *
             (OpFamily.leftPlacedOpFamily strategy.state Au).outcome ab.1
         total := ∑ ab : Fq params × Fq params,
           (Av.liftLeft strategy.state).outcome ab.2 *
             (OpFamily.leftPlacedOpFamily strategy.state Au).outcome ab.1
       } : OpFamily (Fq params × Fq params) (K →L[ℂ] K))
  let hbase :=
    sddOpRel_symm strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.leftPlacedOpFamily strategy.state
          ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas))
      (fun q =>
        OpFamily.rightPlacedOpFamily strategy.state
          (SubMeas.toOpFamily (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1))))
      (pointDiagonalLineApproxError params gamma)
      (answerSampledDiagonalLineApproximation_ignore_second params strategy eps delta gamma hgood)
  have hcab :=
    MIPRE.LIDT.Co.Preliminaries.cabApproxDelta_raw
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.rightPlacedOpFamily strategy.state
          (SubMeas.toOpFamily (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1))))
      (fun q =>
        OpFamily.leftPlacedOpFamily strategy.state
          ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas))
      (fun q _a b =>
        (((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas).liftLeft
          strategy.state).outcome b)
      (pointDiagonalLineApproxError params gamma)
      hbase
      (by
        intro q a
        exact subMeas_sum_adjoint_mul_le_one
          (((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas).liftLeft strategy.state))
  exact sddOpRel_congr_outcome strategy.state
    (pointPairSharedDiagonalLineDistribution params)
    Astep Bstep
    (IdxSubMeas.toIdxOpFamily (answerPointDiagonalLineMixedProductRight params strategy))
    (answerPointMeasurementProductAlongSharedLineReversed params strategy)
    (pointDiagonalLineApproxError params gamma)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Astep q).outcome (a, b)
          = strategy.state.opTensor
              ((strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b)
              ((answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a) :=
                  liftLeft_mul_rightPlaced_outcome strategy.state
                    ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas)
                    (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1))
                    b a
        _ =
            ((IdxSubMeas.toIdxOpFamily
                (answerPointDiagonalLineMixedProductRight params strategy)) q).outcome
              (a, b) :=
              (answerPointDiagonalLineMixedProductRight_outcome params strategy q a b).symm)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Bstep q).outcome (a, b)
          = strategy.state.L
              ((strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b *
                (strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome a) :=
                  liftLeft_mul_leftPlaced_outcome strategy.state
                    ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas)
                    ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas)
                    b a
        _ = (answerPointMeasurementProductAlongSharedLineReversed params strategy q).outcome
              (a, b) := rfl)
    hcab

/-- Answer-valued form of `thm:commutativity-points`.

The proof is the paper's diagonal-line bridge argument, but the diagonal-line
measurement is the answer-valued measurement of `strategy`. -/
theorem answerCommutativityPoints
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma) :
    strategy.state.SDDOpRel
      (uniformDistribution (PointPairQuestion params))
      (answerPointMeasurementProductLeft params strategy)
      (answerPointMeasurementProductRight params strategy)
      (commutativityPointsError params gamma) := by
  let δ := pointDiagonalLineApproxError params gamma
  -- The state is passed as `strategy.state.toVecState`, not through the `CoeOut` coercion: with
  -- the coercion, elaboration first tries to coerce the bridge hypotheses (0.1–0.3 s measured).
  have hleft :
      strategy.state.SDDOpRel
        (pointPairSharedDiagonalLineDistribution params)
        (answerPointMeasurementProductAlongSharedLine params strategy)
        (answerDiagonalLineProductOrdered params strategy)
        (2 * (δ + δ)) := by
    exact MIPRE.LIDT.Co.Preliminaries.stateDependentDistanceOpRel_triangle
      strategy.state.toVecState
      (pointPairSharedDiagonalLineDistribution params)
      (answerPointMeasurementProductAlongSharedLine params strategy)
      (IdxSubMeas.toIdxOpFamily (answerPointDiagonalLineMixedProductLeft params strategy))
      (answerDiagonalLineProductOrdered params strategy)
      δ δ
      (answerOrderedLiftToMixedLine params strategy eps delta gamma hgood)
      (answerOrderedLiftToLineProduct params strategy eps delta gamma hgood)
  have hright :
      strategy.state.SDDOpRel
        (pointPairSharedDiagonalLineDistribution params)
        (answerDiagonalLineProductOrdered params strategy)
        (answerPointMeasurementProductAlongSharedLineReversed params strategy)
        (2 * (δ + δ)) := by
    exact MIPRE.LIDT.Co.Preliminaries.stateDependentDistanceOpRel_triangle
      strategy.state.toVecState
      (pointPairSharedDiagonalLineDistribution params)
      (answerDiagonalLineProductOrdered params strategy)
      (IdxSubMeas.toIdxOpFamily (answerPointDiagonalLineMixedProductRight params strategy))
      (answerPointMeasurementProductAlongSharedLineReversed params strategy)
      δ δ
      (answerOrderedDropFromLineComparison params strategy eps delta gamma hgood)
      (answerReversedDropToPointsComparison params strategy eps delta gamma hgood)
  have hshared :
      strategy.state.SDDOpRel
        (pointPairSharedDiagonalLineDistribution params)
        (answerPointMeasurementProductAlongSharedLine params strategy)
        (answerPointMeasurementProductAlongSharedLineReversed params strategy)
        (2 * (2 * (δ + δ) + 2 * (δ + δ))) := by
    exact MIPRE.LIDT.Co.Preliminaries.stateDependentDistanceOpRel_triangle
      strategy.state.toVecState
      (pointPairSharedDiagonalLineDistribution params)
      (answerPointMeasurementProductAlongSharedLine params strategy)
      (answerDiagonalLineProductOrdered params strategy)
      (answerPointMeasurementProductAlongSharedLineReversed params strategy)
      (2 * (δ + δ)) (2 * (δ + δ))
      hleft hright
  have hshared' :
      strategy.state.SDDOpRel
        (pointPairSharedDiagonalLineDistribution params)
        (answerPointMeasurementProductAlongSharedLine params strategy)
        (answerPointMeasurementProductAlongSharedLineReversed params strategy)
        (commutativityPointsError params gamma) := by
    refine MIPRE.LIDT.Co.Preliminaries.stateDependentDistanceOpRel_mono
      strategy.state.toVecState
      (pointPairSharedDiagonalLineDistribution params)
      (answerPointMeasurementProductAlongSharedLine params strategy)
      (answerPointMeasurementProductAlongSharedLineReversed params strategy)
      (2 * (2 * (δ + δ) + 2 * (δ + δ)))
      (commutativityPointsError params gamma)
      ?_ hshared
    dsimp [δ, pointDiagonalLineApproxError, restrictedDiagonalLinesConsistencyError,
      commutativityPointsError]
    ring_nf
    linarith
  rcases hshared' with ⟨hshared'⟩
  constructor
  calc
    strategy.state.sddErrorOp
        (uniformDistribution (PointPairQuestion params))
        (answerPointMeasurementProductLeft params strategy)
        (answerPointMeasurementProductRight params strategy)
      = avgOver (pointPairSharedDiagonalLineDistribution params)
          (fun q =>
            strategy.state.qSDDOp
              (answerPointMeasurementProductAlongSharedLine params strategy q)
              (answerPointMeasurementProductAlongSharedLineReversed params strategy q)) :=
            (avgOver_pointPairSharedDiagonalLine_sampled_pair params
              (fun uv =>
                strategy.state.qSDDOp
                  (answerPointMeasurementProductLeft params strategy uv)
                  (answerPointMeasurementProductRight params strategy uv))).symm
    _ = strategy.state.sddErrorOp
          (pointPairSharedDiagonalLineDistribution params)
          (answerPointMeasurementProductAlongSharedLine params strategy)
          (answerPointMeasurementProductAlongSharedLineReversed params strategy) := rfl
    _ ≤ commutativityPointsError params gamma := hshared'

end MIPRE.LIDT.Co.CommutativityPoints

end

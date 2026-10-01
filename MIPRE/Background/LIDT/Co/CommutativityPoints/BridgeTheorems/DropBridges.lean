/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
CommutativityPoints/BridgeTheorems/DropBridges.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.CommutativityPoints.BridgeTheorems.LiftBridges

@[expose] public section

/-!
# Section 10 commutativity points: drop comparisons

Comparison lemmas that drop structure from the mixed line family back to the
ordered diagonal-line product, used in the drop direction of the Section 10
point-commutativity argument, and the theorem itself, `commutativityPoints`
(`thm:commutativity-points`): the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/CommutativityPoints/BridgeTheorems/DropBridges.lean` in the
port of `planning/c6b-plan.md` (milestone M1, section "Port conventions"). The strategy is a
symmetric one, `strategy : SymStrat params 𝔓 K`, with the point answers placed by
`strategy.state.L` and the line answers by `strategy.state.R`; the conclusion is the vendored one,
an `SDDOpRel` of the vector state of `strategy.state` between the two orders of a product of point
measurements. The flip of the model is not used.

As in `BridgeTheorems/LiftBridges.lean`, the hypothesis of `Preliminaries.cabApproxDelta_raw` on
a lifted submeasurement is `liftLeft_sum_adjoint_mul_le_one` / `liftRight_sum_adjoint_mul_le_one`.

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
open MIPStarRE.LDT.CommutativityPoints (PointPairOutcome PointPairDiagonalLineQuestion
  pointPairSharedDiagonalLineDistribution restrictedDiagonalLinesConsistencyError
  pointDiagonalLineApproxError commutativityPointsError pointPairOutcomeSwapEquiv
  avgOver_pointPairSharedDiagonalLine_sampled_pair)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Third replacement step: for a good strategy, over the shared-diagonal-line distribution,
the reversed line product `I ⊗ (L^ℓ_[f(u)=a] · L^ℓ_[f(v)=b])` and the right mixed bridge
`A^v_b ⊗ L^ℓ_[f(u)=a]` are `pointDiagonalLineApproxError params gamma`-close (`SDDOpRel`). -/
theorem reversedDropFromLineComparison
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma) :
    strategy.state.SDDOpRel
      (pointPairSharedDiagonalLineDistribution params)
      (diagonalLineProductReversed params strategy)
      (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductRight params strategy))
      (pointDiagonalLineApproxError params gamma) := by
  /-
  Third replacement step:
  `I ⊗ (L^ℓ_[f(u)=a] L^ℓ_[f(v)=b]) ≈ A^v_b ⊗ L^ℓ_[f(u)=a]`.
  -/
  let e := pointPairOutcomeSwapEquiv params
  let Araw :
      IdxOpFamily (PointPairDiagonalLineQuestion params)
        (Fq params × Fq params) (K →L[ℂ] K) :=
    fun q =>
      let Lu := sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)
      let Lv := sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)
      opFamilyOfOutcome fun ab : PointPairOutcome params =>
        (Lu.liftRight strategy.state).outcome ab.2 *
          (OpFamily.rightPlacedOpFamily strategy.state Lv.toOpFamily).outcome ab.1
  let Braw :
      IdxOpFamily (PointPairDiagonalLineQuestion params)
        (PointPairOutcome params) (K →L[ℂ] K) :=
    fun q =>
      let Lu := sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)
      let Av := (strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas
      opFamilyOfOutcome fun ab : PointPairOutcome params =>
        (Lu.liftRight strategy.state).outcome ab.2 *
          (OpFamily.leftPlacedOpFamily strategy.state Av.toOpFamily).outcome ab.1
  let hbase :=
    sddOpRel_symm strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.leftPlacedOpFamily strategy.state
          ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas.toOpFamily))
      (fun q =>
        OpFamily.rightPlacedOpFamily strategy.state
          (SubMeas.toOpFamily (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2))))
      (pointDiagonalLineApproxError params gamma)
      (sampledDiagonalLineApproximation_ignore_first params strategy eps delta gamma hgood)
  let hcab :=
    MIPRE.LIDT.Co.Preliminaries.cabApproxDelta_raw
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.rightPlacedOpFamily strategy.state
          (SubMeas.toOpFamily
            (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2))))
      (fun q =>
        OpFamily.leftPlacedOpFamily strategy.state
          ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas.toOpFamily))
      (fun q _b a =>
        ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).liftRight
          strategy.state).outcome a)
      (pointDiagonalLineApproxError params gamma)
      hbase
      (by
        intro q b
        exact liftRight_sum_adjoint_mul_le_one strategy.state
          (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)))
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
    (diagonalLineProductReversed params strategy)
    (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductRight params strategy))
    (pointDiagonalLineApproxError params gamma)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Astep q).outcome (a, b)
          = strategy.state.R
              ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a *
                (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).outcome b) :=
                  liftRight_mul_rightPlaced_outcome strategy.state
                    (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1))
                    (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2))
                    a b
        _ = (diagonalLineProductReversed params strategy q).outcome (a, b) :=
              (diagonalLineProductReversed_outcome params strategy q a b).symm)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Bstep q).outcome (a, b)
          = strategy.state.opTensor
              ((strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b)
              ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a) :=
                  liftRight_mul_leftPlaced_outcome strategy.state
                    (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1))
                    ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas)
                    a b
        _ =
            ((IdxSubMeas.toIdxOpFamily
                (pointDiagonalLineMixedProductRight params strategy)) q).outcome (a, b) :=
              (pointDiagonalLineMixedProductRight_outcome params strategy q a b).symm)
    hreindexed

/-- The third replacement step for the ordered line product: the ordered line product
`I ⊗ (L^ℓ_[f(v)=b] · L^ℓ_[f(u)=a])` and the right mixed bridge `A^v_b ⊗ L^ℓ_[f(u)=a]` are
`pointDiagonalLineApproxError params gamma`-close (`SDDOpRel`), the two line evaluations
commuting as postprocessings of one diagonal-line measurement. -/
theorem orderedDropFromLineComparison
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma) :
    strategy.state.SDDOpRel
      (pointPairSharedDiagonalLineDistribution params)
      (diagonalLineProductOrdered params strategy)
      (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductRight params strategy))
      (pointDiagonalLineApproxError params gamma) :=
  sddOpRel_congr_outcome strategy.state
    (pointPairSharedDiagonalLineDistribution params)
    (diagonalLineProductReversed params strategy)
    (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductRight params strategy))
    (diagonalLineProductOrdered params strategy)
    (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductRight params strategy))
    (pointDiagonalLineApproxError params gamma)
    (fun q ⟨a, b⟩ =>
      ((diagonalLineProductReversed_outcome params strategy q a b).trans
        (congrArg strategy.state.R
          ((strategy.diagonalMeasurement q.1).postprocess_outcome_commute
            (fun f => f q.2.2) (fun f => f q.2.1) b a).symm)).trans
        (diagonalLineProductOrdered_outcome params strategy q a b).symm)
    (fun _ _ => rfl)
    (reversedDropFromLineComparison params strategy eps delta gamma hgood)

/-- Final replacement step: for a good strategy, over the shared-diagonal-line distribution,
the right mixed bridge `A^v_b ⊗ L^ℓ_[f(u)=a]` and the reversed point product
`(A^v_b A^u_a) ⊗ I` are `pointDiagonalLineApproxError params gamma`-close (`SDDOpRel`). -/
theorem reversedDropToPointsComparison
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma) :
    strategy.state.SDDOpRel
      (pointPairSharedDiagonalLineDistribution params)
      (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductRight params strategy))
      (pointMeasurementProductAlongSharedLineReversed params strategy)
      (pointDiagonalLineApproxError params gamma) := by
  /-
  Final replacement step:
  `A^v_b ⊗ L^ℓ_[f(u)=a] ≈ (A^v_b A^u_a) ⊗ I`.
  -/
  let Astep : IdxOpFamily (PointPairDiagonalLineQuestion params) (Fq params × Fq params)
      (K →L[ℂ] K) :=
    fun q =>
      let Av := (strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas
      let Lu := sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)
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
             (OpFamily.leftPlacedOpFamily strategy.state Au.toOpFamily).outcome ab.1
         total := ∑ ab : Fq params × Fq params,
           (Av.liftLeft strategy.state).outcome ab.2 *
             (OpFamily.leftPlacedOpFamily strategy.state Au.toOpFamily).outcome ab.1
       } : OpFamily (Fq params × Fq params) (K →L[ℂ] K))
  let hbase :=
    sddOpRel_symm strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.leftPlacedOpFamily strategy.state
          ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas.toOpFamily))
      (fun q =>
        OpFamily.rightPlacedOpFamily strategy.state
          (SubMeas.toOpFamily (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1))))
      (pointDiagonalLineApproxError params gamma)
      (sampledDiagonalLineApproximation_ignore_second params strategy eps delta gamma hgood)
  have hcab :=
    MIPRE.LIDT.Co.Preliminaries.cabApproxDelta_raw
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.rightPlacedOpFamily strategy.state
          (SubMeas.toOpFamily (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1))))
      (fun q =>
        OpFamily.leftPlacedOpFamily strategy.state
          ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas.toOpFamily))
      (fun q _a b =>
        (((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas).liftLeft
          strategy.state).outcome b)
      (pointDiagonalLineApproxError params gamma)
      hbase
      (by
        intro q a
        exact liftLeft_sum_adjoint_mul_le_one strategy.state
          ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas))
  exact sddOpRel_congr_outcome strategy.state
    (pointPairSharedDiagonalLineDistribution params)
    Astep Bstep
    (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductRight params strategy))
    (pointMeasurementProductAlongSharedLineReversed params strategy)
    (pointDiagonalLineApproxError params gamma)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Astep q).outcome (a, b)
          = strategy.state.opTensor
              ((strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b)
              ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a) :=
                  liftLeft_mul_rightPlaced_outcome strategy.state
                    ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas)
                    (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1))
                    b a
        _ =
            ((IdxSubMeas.toIdxOpFamily
                (pointDiagonalLineMixedProductRight params strategy)) q).outcome (a, b) :=
              (pointDiagonalLineMixedProductRight_outcome params strategy q a b).symm)
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
        _ = (pointMeasurementProductAlongSharedLineReversed params strategy q).outcome (a, b) :=
              (pointMeasurementProductAlongSharedLineReversed_outcome params strategy q a b).symm)
    hcab

/-- `thm:commutativity-points`. -/
theorem commutativityPoints
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma) :
    strategy.state.SDDOpRel
      (uniformDistribution (PointPairQuestion params))
      (pointMeasurementProductLeft params strategy)
      (pointMeasurementProductRight params strategy)
      (commutativityPointsError params gamma) := by
  let δ := pointDiagonalLineApproxError params gamma
  have hleft :
      strategy.state.SDDOpRel
        (pointPairSharedDiagonalLineDistribution params)
        (pointMeasurementProductAlongSharedLine params strategy)
        (diagonalLineProductOrdered params strategy)
        (2 * (δ + δ)) :=
    MIPRE.LIDT.Co.Preliminaries.stateDependentDistanceOpRel_triangle
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (pointMeasurementProductAlongSharedLine params strategy)
      (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductLeft params strategy))
      (diagonalLineProductOrdered params strategy)
      δ δ
      (orderedLiftToMixedLine params strategy eps delta gamma hgood)
      (orderedLiftToLineProduct params strategy eps delta gamma hgood)
  have hright :
      strategy.state.SDDOpRel
        (pointPairSharedDiagonalLineDistribution params)
        (diagonalLineProductOrdered params strategy)
        (pointMeasurementProductAlongSharedLineReversed params strategy)
        (2 * (δ + δ)) :=
    MIPRE.LIDT.Co.Preliminaries.stateDependentDistanceOpRel_triangle
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (diagonalLineProductOrdered params strategy)
      (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductRight params strategy))
      (pointMeasurementProductAlongSharedLineReversed params strategy)
      δ δ
      (orderedDropFromLineComparison params strategy eps delta gamma hgood)
      (reversedDropToPointsComparison params strategy eps delta gamma hgood)
  have hshared :
      strategy.state.SDDOpRel
        (pointPairSharedDiagonalLineDistribution params)
        (pointMeasurementProductAlongSharedLine params strategy)
        (pointMeasurementProductAlongSharedLineReversed params strategy)
        (2 * (2 * (δ + δ) + 2 * (δ + δ))) :=
    MIPRE.LIDT.Co.Preliminaries.stateDependentDistanceOpRel_triangle
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (pointMeasurementProductAlongSharedLine params strategy)
      (diagonalLineProductOrdered params strategy)
      (pointMeasurementProductAlongSharedLineReversed params strategy)
      (2 * (δ + δ)) (2 * (δ + δ))
      hleft hright
  have hshared' :
      strategy.state.SDDOpRel
        (pointPairSharedDiagonalLineDistribution params)
        (pointMeasurementProductAlongSharedLine params strategy)
        (pointMeasurementProductAlongSharedLineReversed params strategy)
        (commutativityPointsError params gamma) := by
    refine MIPRE.LIDT.Co.Preliminaries.stateDependentDistanceOpRel_mono
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (pointMeasurementProductAlongSharedLine params strategy)
      (pointMeasurementProductAlongSharedLineReversed params strategy)
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
        (pointMeasurementProductLeft params strategy)
        (pointMeasurementProductRight params strategy)
      = strategy.state.sddErrorOp
          (pointPairSharedDiagonalLineDistribution params)
          (pointMeasurementProductAlongSharedLine params strategy)
          (pointMeasurementProductAlongSharedLineReversed params strategy) :=
        (avgOver_pointPairSharedDiagonalLine_sampled_pair params
          (fun uv =>
            strategy.state.qSDDOp
              (pointMeasurementProductLeft params strategy uv)
              (pointMeasurementProductRight params strategy uv))).symm
    _ ≤ commutativityPointsError params gamma := hshared'

end MIPRE.LIDT.Co.CommutativityPoints

end

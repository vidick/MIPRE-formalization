/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
CommutativityPoints/BridgeTheorems/LiftBridges.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.CommutativityPoints.SharedHelpers.SharedLine
public import MIPRE.Background.LIDT.Co.Preliminaries.DistanceBounds

@[expose] public section

/-!
# Section 10 commutativity points: lift comparisons

Comparison lemmas lifting the ordered shared-line point product to the mixed
line family, used in the lift direction of the Section 10 point-commutativity
argument: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/CommutativityPoints/BridgeTheorems/LiftBridges.lean` in the
port of `planning/c6b-plan.md` (milestone M1, section "Port conventions"). The strategy is a
symmetric one, `strategy : SymStrat params 𝔓 K`; the point answers are placed by
`strategy.state.L`, the line answers by `strategy.state.R`, and the distance relations are those of
the vector state of `strategy.state`.

Each comparison multiplies a known approximation on the left by a placed submeasurement
(`Preliminaries.cabApproxDelta_raw`), whose hypothesis `∑ b, star C_b * C_b ≤ 1` the vendored
file proves with `subMeas_sum_adjoint_mul_le_one` on the lifted, joint submeasurement. Here that
lemma is about a local submeasurement in `𝔓`, and the joint bound is transported along the
placement: `liftLeft_sum_adjoint_mul_le_one` and `liftRight_sum_adjoint_mul_le_one` (new; also used
by `BridgeTheorems/DropBridges.lean`), so that no positivity of `K →L[ℂ] K` is reproved.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

- `references/ldt-paper/commutativity-points.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.CommutativityPoints

open MIPStarRE.LDT (Parameters FieldModel Fq)
open MIPStarRE.LDT.CommutativityPoints (PointPairOutcome PointPairDiagonalLineQuestion
  pointPairSharedDiagonalLineDistribution pointDiagonalLineApproxError pointPairOutcomeSwapEquiv)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The bound of `subMeas_sum_adjoint_mul_le_one`, for a submeasurement lifted to the first
factor: the sum is the left placement of the local one. -/
theorem liftLeft_sum_adjoint_mul_le_one
    {Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (A : SubMeas Outcome 𝔓) :
    ∑ a : Outcome, star ((A.liftLeft S).outcome a) * (A.liftLeft S).outcome a ≤ 1 := by
  have h : ∑ a : Outcome, star (S.L (A.outcome a)) * S.L (A.outcome a) =
      S.L (∑ a : Outcome, star (A.outcome a) * A.outcome a) := by
    rw [← S.leftTensor_finset_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [S.leftTensor_conjTranspose, S.leftTensor_mul_leftTensor]
  exact h.le.trans (S.leftTensor_le_one (subMeas_sum_adjoint_mul_le_one A))

/-- The bound of `subMeas_sum_adjoint_mul_le_one`, for a submeasurement lifted to the second
factor: the sum is the right placement of the local one. -/
theorem liftRight_sum_adjoint_mul_le_one
    {Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (A : SubMeas Outcome 𝔓) :
    ∑ a : Outcome, star ((A.liftRight S).outcome a) * (A.liftRight S).outcome a ≤ 1 := by
  have h : ∑ a : Outcome, star (S.R (A.outcome a)) * S.R (A.outcome a) =
      S.R (∑ a : Outcome, star (A.outcome a) * A.outcome a) := by
    rw [← S.rightTensor_finset_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [S.rightTensor_conjTranspose, S.rightTensor_mul_rightTensor]
  exact h.le.trans (S.rightTensor_le_one (subMeas_sum_adjoint_mul_le_one A))

/-- Lift the ordered shared-line point product to the mixed line family. -/
theorem orderedLiftToMixedLine
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma) :
    strategy.state.SDDOpRel
      (pointPairSharedDiagonalLineDistribution params)
      (pointMeasurementProductAlongSharedLine params strategy)
      (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductLeft params strategy))
      (pointDiagonalLineApproxError params gamma) := by
  /-
  First replacement step in the paper:
  `(A^u_a A^v_b) ⊗ I ≈ A^u_a ⊗ L^ℓ_[f(v)=b]`.
  -/
  let e := pointPairOutcomeSwapEquiv params
  let Araw :
      IdxOpFamily (PointPairDiagonalLineQuestion params)
        (Fq params × Fq params) (K →L[ℂ] K) :=
    fun q =>
      let Au := (strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas
      let Av := (strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas
      opFamilyOfOutcome fun ab : PointPairOutcome params =>
        (Au.liftLeft strategy.state).outcome ab.2 *
          (OpFamily.leftPlacedOpFamily strategy.state Av.toOpFamily).outcome ab.1
  let Braw :
      IdxOpFamily (PointPairDiagonalLineQuestion params)
        (PointPairOutcome params) (K →L[ℂ] K) :=
    fun q =>
      let Au := (strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas
      let Lv := sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)
      opFamilyOfOutcome fun ab : PointPairOutcome params =>
        (Au.liftLeft strategy.state).outcome ab.2 *
          (OpFamily.rightPlacedOpFamily strategy.state Lv.toOpFamily).outcome ab.1
  let hbase :=
    sampledDiagonalLineApproximation_ignore_first params strategy eps delta gamma hgood
  let hcab :=
    MIPRE.LIDT.Co.Preliminaries.cabApproxDelta_raw
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.leftPlacedOpFamily strategy.state
          ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas.toOpFamily))
      (fun q =>
        OpFamily.rightPlacedOpFamily strategy.state
          (SubMeas.toOpFamily (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2))))
      (fun q _b a =>
        (((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas).liftLeft
          strategy.state).outcome a)
      (pointDiagonalLineApproxError params gamma)
      hbase
      (by
        intro q b
        exact liftLeft_sum_adjoint_mul_le_one strategy.state
          ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas))
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
    (pointMeasurementProductAlongSharedLine params strategy)
    (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductLeft params strategy))
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
        _ = (pointMeasurementProductAlongSharedLine params strategy q).outcome (a, b) :=
              (pointMeasurementProductAlongSharedLine_outcome params strategy q a b).symm)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Bstep q).outcome (a, b)
          = strategy.state.opTensor
              ((strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome a)
              ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).outcome b) :=
                  liftLeft_mul_rightPlaced_outcome strategy.state
                    ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas)
                    (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2))
                    a b
        _ =
            ((IdxSubMeas.toIdxOpFamily
                (pointDiagonalLineMixedProductLeft params strategy)) q).outcome (a, b) :=
              (pointDiagonalLineMixedProductLeft_outcome params strategy q a b).symm)
    hreindexed

/-- Lift the mixed line family to the ordered shared-line line product. -/
theorem orderedLiftToLineProduct
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma) :
    strategy.state.SDDOpRel
      (pointPairSharedDiagonalLineDistribution params)
      (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductLeft params strategy))
      (diagonalLineProductOrdered params strategy)
      (pointDiagonalLineApproxError params gamma) := by
  /-
  Second replacement step:
  `A^u_a ⊗ L^ℓ_[f(v)=b] ≈ I ⊗ (L^ℓ_[f(v)=b] L^ℓ_[f(u)=a])`.
  -/
  let hbase :=
    sampledDiagonalLineApproximation_ignore_second params strategy eps delta gamma hgood
  have hcab :=
    MIPRE.LIDT.Co.Preliminaries.cabApproxDelta_raw
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.leftPlacedOpFamily strategy.state
          ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas.toOpFamily))
      (fun q =>
        OpFamily.rightPlacedOpFamily strategy.state
          (SubMeas.toOpFamily (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1))))
      (fun q _a b =>
        ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).liftRight
          strategy.state).outcome b)
      (pointDiagonalLineApproxError params gamma)
      hbase
      (by
        intro q a
        exact liftRight_sum_adjoint_mul_le_one strategy.state
          (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)))
  let Astep : IdxOpFamily (PointPairDiagonalLineQuestion params) (Fq params × Fq params)
      (K →L[ℂ] K) :=
    fun q =>
      let Au := (strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas
      let Lv := sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)
      ({ outcome := fun ab : Fq params × Fq params =>
           (Lv.liftRight strategy.state).outcome ab.2 *
             (OpFamily.leftPlacedOpFamily strategy.state Au.toOpFamily).outcome ab.1
         total := ∑ ab : Fq params × Fq params,
           (Lv.liftRight strategy.state).outcome ab.2 *
             (OpFamily.leftPlacedOpFamily strategy.state Au.toOpFamily).outcome ab.1
       } : OpFamily (Fq params × Fq params) (K →L[ℂ] K))
  let Bstep : IdxOpFamily (PointPairDiagonalLineQuestion params) (Fq params × Fq params)
      (K →L[ℂ] K) :=
    fun q =>
      let Lu := sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)
      let Lv := sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)
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
    (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductLeft params strategy))
    (diagonalLineProductOrdered params strategy)
    (pointDiagonalLineApproxError params gamma)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Astep q).outcome (a, b)
          = strategy.state.opTensor
              ((strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome a)
              ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).outcome b) :=
                  liftRight_mul_leftPlaced_outcome strategy.state
                    (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2))
                    ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas)
                    b a
        _ =
            ((IdxSubMeas.toIdxOpFamily
                (pointDiagonalLineMixedProductLeft params strategy)) q).outcome (a, b) :=
              (pointDiagonalLineMixedProductLeft_outcome params strategy q a b).symm)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Bstep q).outcome (a, b)
          = strategy.state.R
              ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).outcome b *
                (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a) :=
                  liftRight_mul_rightPlaced_outcome strategy.state
                    (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2))
                    (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1))
                    b a
        _ = (diagonalLineProductOrdered params strategy q).outcome (a, b) :=
              (diagonalLineProductOrdered_outcome params strategy q a b).symm)
    hcab

end MIPRE.LIDT.Co.CommutativityPoints

end

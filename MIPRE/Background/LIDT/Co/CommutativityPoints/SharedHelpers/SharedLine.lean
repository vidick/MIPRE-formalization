/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
CommutativityPoints/SharedHelpers/SharedLine.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.CommutativityPoints.SharedHelpers.Core
public import MIPRE.Background.LIDT.MIPStarRE.LDT.CommutativityPoints.SharedHelpers.SharedLine

@[expose] public section

/-!
# Section 10 commutativity points: shared-line helpers

Compatibility lemmas between sampled point pairs and shared-diagonal line
questions, used by both the lift and drop comparisons: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/CommutativityPoints/SharedHelpers/SharedLine.lean` in the
port of `planning/c6b-plan.md` (milestone M1, section "Port conventions"). The outcome formulas
of the bridge families of `Co/CommutativityPoints/Defs.lean` and the transport of the
point/diagonal-line approximation to the shared-line distribution are stated for a symmetric
strategy `strategy : SymStrat params 𝔓 K`, with the point answers placed by
`strategy.state.L` and the line answers by `strategy.state.R`.

The classical half of the vendored file (the two decompositions of a shared-line question, the
equivalences that forget one of its two parameters, and the averaging identities over the
shared-line distribution) is not ported: this file imports the vendored file and names those
declarations through an explicit `open MIPStarRE.LDT.CommutativityPoints (…)` list.

## Not ported

- `sharedDiagonalLineQuestionOfPointPair_sampledPointPair`: classical, imported.
- `sharedDiagonalLineQuestionOfPointPair_of_line`: classical, imported.
- `pointPairSharedDiagonalLine_ignore_first_equiv`: classical, imported.
- `pointPairSharedDiagonalLine_ignore_second_equiv`: classical, imported.
- `avgOver_pointPairSharedDiagonalLine_ignore_first`: classical, imported.
- `avgOver_pointPairSharedDiagonalLine_ignore_second`: classical, imported.
- `avgOver_pointPairSharedDiagonalLine_sampled_pair`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/commutativity-points.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`

In this repository: `lem:co-commutativity-points` in `blueprint/src/content/08_downstream.tex`.
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.CommutativityPoints

open MIPStarRE.LDT (Parameters FieldModel Fq avgOver avgOver_congr)
open MIPStarRE.LDT.CommutativityPoints (PointPairDiagonalLineQuestion
  sampledPointFromDiagonalQuestion pointWithDiagonalLineDistribution
  pointPairSharedDiagonalLineDistribution pointDiagonalLineApproxError
  avgOver_pointPairSharedDiagonalLine_ignore_first
  avgOver_pointPairSharedDiagonalLine_ignore_second)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Outcome `(a, b)` of the shared-line point product, at a question `(ℓ, (t_u, t_v))` with
`u = ℓ(t_u)` and `v = ℓ(t_v)`: it is `(A^u_a A^v_b) ⊗ I`, `strategy.state.L` of the product. -/
theorem pointMeasurementProductAlongSharedLine_outcome
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (q : PointPairDiagonalLineQuestion params)
    (a b : Fq params) :
    (pointMeasurementProductAlongSharedLine params strategy q).outcome (a, b) =
      strategy.state.L
        ((strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome a *
          (strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b) :=
  rfl

/-- Outcome `(a, b)` of the reversed shared-line point product: it is `(A^v_b A^u_a) ⊗ I`,
`strategy.state.L` of the product in the opposite order. -/
theorem pointMeasurementProductAlongSharedLineReversed_outcome
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (q : PointPairDiagonalLineQuestion params)
    (a b : Fq params) :
    (pointMeasurementProductAlongSharedLineReversed params strategy q).outcome (a, b) =
      strategy.state.L
        ((strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b *
          (strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome a) :=
  rfl

/-- Outcome `(a, b)` of the left mixed bridge: it is `A^u_a ⊗ L^ℓ_[f(v)=b]`, the point
measurement at `u` and the diagonal-line evaluation at `t_v`, placed by
`strategy.state.opTensor`. -/
theorem pointDiagonalLineMixedProductLeft_outcome
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (q : PointPairDiagonalLineQuestion params)
    (a b : Fq params) :
    ((IdxSubMeas.toIdxOpFamily
        (pointDiagonalLineMixedProductLeft params strategy) q).outcome (a, b)) =
      strategy.state.opTensor
        ((strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome a)
        ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).outcome b) :=
  rfl

/-- Outcome `(a, b)` of the right mixed bridge: it is `A^v_b ⊗ L^ℓ_[f(u)=a]`, the point
measurement at `v` and the diagonal-line evaluation at `t_u`, placed by
`strategy.state.opTensor`, the post-processing having swapped the outcome pair back. -/
theorem pointDiagonalLineMixedProductRight_outcome
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (q : PointPairDiagonalLineQuestion params)
    (a b : Fq params) :
    ((IdxSubMeas.toIdxOpFamily
        (pointDiagonalLineMixedProductRight params strategy) q).outcome (a, b)) =
      strategy.state.opTensor
        ((strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b)
        ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a) := by
  classical
  suffices h :
      ∑ ab : Fq params × Fq params with ab.2 = a ∧ ab.1 = b,
        strategy.state.opTensor
          ((strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome ab.1)
          ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome ab.2) =
      strategy.state.opTensor ((strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b)
        ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a) by
    simpa [pointDiagonalLineMixedProductRight, tensorProductSubMeas,
      postprocess, Prod.swap, IdxSubMeas.toIdxOpFamily, SubMeas.toOpFamily] using h
  have hfilter :
      (Finset.univ.filter (fun ab : Fq params × Fq params => ab.2 = a ∧ ab.1 = b)) =
        {(b, a)} := by
    ext ab
    rcases ab with ⟨a', b'⟩
    simp [and_comm]
  rw [hfilter]
  simp

/-- Outcome `(a, b)` of the ordered diagonal-line product: it is
`I ⊗ (L^ℓ_[f(v)=b] · L^ℓ_[f(u)=a])`, `strategy.state.R` of the product. -/
theorem diagonalLineProductOrdered_outcome
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (q : PointPairDiagonalLineQuestion params)
    (a b : Fq params) :
    (diagonalLineProductOrdered params strategy q).outcome (a, b) =
      strategy.state.R
        ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).outcome b *
          (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a) :=
  rfl

/-- Outcome `(a, b)` of the reversed diagonal-line product: it is
`I ⊗ (L^ℓ_[f(u)=a] · L^ℓ_[f(v)=b])`, `strategy.state.R` of the product. -/
theorem diagonalLineProductReversed_outcome
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (q : PointPairDiagonalLineQuestion params)
    (a b : Fq params) :
    (diagonalLineProductReversed params strategy q).outcome (a, b) =
      strategy.state.R
        ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a *
          (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).outcome b) :=
  rfl

/-- For a good strategy, over the shared-diagonal-line distribution, the point
measurement at the second point `v`, placed left, and the diagonal-line evaluation at
`t_v`, placed right, are `pointDiagonalLineApproxError params gamma`-close (`SDDOpRel`): the
first point is ignored, `(ℓ, t_v)` having the law of `pointWithDiagonalLineDistribution`. -/
theorem sampledDiagonalLineApproximation_ignore_first
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma) :
    strategy.state.SDDOpRel
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.leftPlacedOpFamily strategy.state
          ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas))
      (fun q =>
        OpFamily.rightPlacedOpFamily strategy.state
          (SubMeas.toOpFamily (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2))))
      (pointDiagonalLineApproxError params gamma) := by
  rcases sampledDiagonalLineApproximation_pointWithDiagonalLine
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
            (SubMeas.toOpFamily (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2))))
      = avgOver (pointPairSharedDiagonalLineDistribution params)
          (fun q =>
            strategy.state.qSDD
              ((IdxSubMeas.liftLeft strategy.state (sampledPointMeasurement params strategy))
                (q.1, q.2.2))
              ((IdxSubMeas.liftRight strategy.state
                (sampledDiagonalLineEvaluation params strategy)) (q.1, q.2.2))) := rfl
    _ = avgOver (pointWithDiagonalLineDistribution params)
          (fun q =>
            strategy.state.qSDD
              ((IdxSubMeas.liftLeft strategy.state (sampledPointMeasurement params strategy)) q)
              ((IdxSubMeas.liftRight strategy.state
                (sampledDiagonalLineEvaluation params strategy)) q)) :=
            avgOver_pointPairSharedDiagonalLine_ignore_first params
              (fun q =>
                strategy.state.qSDD
                  ((IdxSubMeas.liftLeft strategy.state
                    (sampledPointMeasurement params strategy)) q)
                  ((IdxSubMeas.liftRight strategy.state
                    (sampledDiagonalLineEvaluation params strategy)) q))
    _ = strategy.state.sddError
          (pointWithDiagonalLineDistribution params)
          (IdxSubMeas.liftLeft strategy.state (sampledPointMeasurement params strategy))
          (IdxSubMeas.liftRight strategy.state
            (sampledDiagonalLineEvaluation params strategy)) := rfl
    _ ≤ pointDiagonalLineApproxError params gamma := happrox

/-- For a good strategy, over the shared-diagonal-line distribution, the point
measurement at the first point `u`, placed left, and the diagonal-line evaluation at
`t_u`, placed right, are `pointDiagonalLineApproxError params gamma`-close (`SDDOpRel`): the
second point is ignored, `(ℓ, t_u)` having the law of `pointWithDiagonalLineDistribution`. -/
theorem sampledDiagonalLineApproximation_ignore_second
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma) :
    strategy.state.SDDOpRel
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.leftPlacedOpFamily strategy.state
          ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas))
      (fun q =>
        OpFamily.rightPlacedOpFamily strategy.state
          (SubMeas.toOpFamily (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1))))
      (pointDiagonalLineApproxError params gamma) := by
  rcases sampledDiagonalLineApproximation_pointWithDiagonalLine
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
            (SubMeas.toOpFamily (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1))))
      = avgOver (pointPairSharedDiagonalLineDistribution params)
          (fun q =>
            strategy.state.qSDD
              ((IdxSubMeas.liftLeft strategy.state (sampledPointMeasurement params strategy))
                (q.1, q.2.1))
              ((IdxSubMeas.liftRight strategy.state
                (sampledDiagonalLineEvaluation params strategy)) (q.1, q.2.1))) := rfl
    _ = avgOver (pointWithDiagonalLineDistribution params)
          (fun q =>
            strategy.state.qSDD
              ((IdxSubMeas.liftLeft strategy.state (sampledPointMeasurement params strategy)) q)
              ((IdxSubMeas.liftRight strategy.state
                (sampledDiagonalLineEvaluation params strategy)) q)) :=
            avgOver_pointPairSharedDiagonalLine_ignore_second params
              (fun q =>
                strategy.state.qSDD
                  ((IdxSubMeas.liftLeft strategy.state
                    (sampledPointMeasurement params strategy)) q)
                  ((IdxSubMeas.liftRight strategy.state
                    (sampledDiagonalLineEvaluation params strategy)) q))
    _ = strategy.state.sddError
          (pointWithDiagonalLineDistribution params)
          (IdxSubMeas.liftLeft strategy.state (sampledPointMeasurement params strategy))
          (IdxSubMeas.liftRight strategy.state
            (sampledDiagonalLineEvaluation params strategy)) := rfl
    _ ≤ pointDiagonalLineApproxError params gamma := happrox

end MIPRE.LIDT.Co.CommutativityPoints

end

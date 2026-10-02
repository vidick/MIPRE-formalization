/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
CommutativityPoints/Defs.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored
file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Test.StrategyCore
public import MIPRE.Background.LIDT.MIPStarRE.LDT.CommutativityPoints.Defs

@[expose] public section

/-!
# Section 10 — Definitions

Auxiliary definitions for the commutativity-at-points argument from Section 10 of the
low individual degree paper: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/CommutativityPoints/Defs.lean` in the port of
`planning/c6b-plan.md` (milestone M1, section "Port conventions"). This file packages the
point/line bridge families used by `commutativityPoints`, over a symmetric strategy
`strategy : SymStrat params 𝔓 K`: local operators live in the C*-algebra `𝔓`, joint ones in
`K →L[ℂ] K`, and the vendored placements `leftTensor (ι₂ := ι)`, `rightTensor (ι₁ := ι)` are the
model's `strategy.state.L`, `strategy.state.R`.

The products of two submeasurements, `orderedProductOpFamily` and `reversedProductOpFamily`, are
generic over the ordered `⋆`-ring `R` of `Co/Basic/SubMeasurementCore.lean` (the vendored
`Op ι`). The bipartite bridge `tensorProductSubMeas` needs both placements, so it takes the
symmetric model `S` as an explicit argument (the vendored one is fixed by its carrier `ι × ι`).

The classical half of the vendored file (the question and outcome types, the `Fintype` instance
on diagonal lines, the sampling maps and distributions, and the error constants) is not ported:
this file imports the vendored file and names those declarations through an explicit
`open MIPStarRE.LDT.CommutativityPoints (…)` list.

## Not ported

- `PointPairOutcome`: classical, imported.
- `PointDiagonalLineQuestion`: classical, imported.
- `PointPairDiagonalLineQuestion`: classical, imported.
- `sampledPointFromDiagonalQuestion`: classical, imported.
- `sampledPointPairFromSharedDiagonalQuestion`: classical, imported.
- `pointWithDiagonalLineDistribution`: classical, imported.
- `pointWithDiagonalLineDistribution_isProbability`: classical, imported.
- `pointWithDiagonalLineDistribution_toPMF`: classical, imported.
- `sharedDiagonalLineQuestionOfPointPair`: classical, imported.
- `pointPairSharedDiagonalLineDistribution`: classical, imported.
- `pointPairSharedDiagonalLineDistribution_isProbability`: classical, imported.
- `pointPairSharedDiagonalLineDistribution_toPMF`: classical, imported.
- `restrictedDiagonalLinesConsistencyError`: classical, imported.
- `pointDiagonalLineApproxError`: classical, imported.
- `commutativityPointsError`: classical, imported.

The anonymous `Fintype (DiagonalLine params)` instance of the vendored file is classical too, and
in force here through the import.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/commutativity-points.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`

In this repository: `lem:co-commutativity-points` in `blueprint/src/content/08_downstream.tex`.
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.CommutativityPoints

open MIPStarRE.LDT (Parameters FieldModel Point Fq DiagonalLine)
open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)
open MIPStarRE.LDT.CommutativityPoints (PointPairOutcome PointDiagonalLineQuestion
  PointPairDiagonalLineQuestion sampledPointFromDiagonalQuestion
  sampledPointPairFromSharedDiagonalQuestion)

section Products

variable {R : Type*} [Ring R] [StarRing R] [PartialOrder R]

/-- Ordered product of two submeasurements viewed as a raw operator family. -/
noncomputable def orderedProductOpFamily {α β : Type*} [Fintype α] [Fintype β]
    (A : SubMeas α R) (B : SubMeas β R) :
    OpFamily (α × β) R where
  outcome := fun | (a, b) => A.outcome a * B.outcome b
  total := A.total * B.total

/-- Reversed product of two submeasurements viewed as a raw operator family. -/
noncomputable def reversedProductOpFamily {α β : Type*} [Fintype α] [Fintype β]
    (A : SubMeas α R) (B : SubMeas β R) :
    OpFamily (α × β) R where
  outcome := fun | (a, b) => B.outcome b * A.outcome a
  total := B.total * A.total

end Products

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The outcome effects of `tensorProductSubMeas` sum to its total effect. -/
theorem tensorProductSubMeas_sum_outcome {α β : Type*} [Fintype α] [Fintype β]
    (S : SymModel 𝔓 K) (A : SubMeas α 𝔓) (B : SubMeas β 𝔓) :
    ∑ ab : α × β, S.L (A.outcome ab.1) * S.R (B.outcome ab.2) =
      S.L A.total * S.R B.total := by
  rw [← A.sum_eq_total, ← B.sum_eq_total, ← S.leftTensor_finset_sum,
    ← S.rightTensor_finset_sum, Fintype.sum_mul_sum]
  exact Fintype.sum_prod_type' fun a b => S.L (A.outcome a) * S.R (B.outcome b)

/-- Tensor-product bridge `A_a ⊗ B_b`, placed by the symmetric model `S` as
`S.L A_a * S.R B_b`. -/
noncomputable def tensorProductSubMeas {α β : Type*} [Fintype α] [Fintype β]
    (S : SymModel 𝔓 K) (A : SubMeas α 𝔓) (B : SubMeas β 𝔓) :
    SubMeas (α × β) (K →L[ℂ] K) where
  outcome := fun ab =>
    match ab with
    | (a, b) => S.L (A.outcome a) * S.R (B.outcome b)
  total := S.L A.total * S.R B.total
  outcome_pos := fun ab => S.opTensor_nonneg (A.outcome_pos ab.1) (B.outcome_pos ab.2)
  sum_eq_total := tensorProductSubMeas_sum_outcome S A B
  total_le_one :=
    (S.opTensor_le_leftTensor A.total_nonneg B.total_le_one).trans
      (S.leftTensor_le_one A.total_le_one)

/-- The ordered point product `(A^u_a A^v_b) ⊗ I`, placed by `strategy.state.L`. -/
noncomputable def pointMeasurementProductLeft (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K) :
    IdxOpFamily (PointPairQuestion params) (PointPairOutcome params) (K →L[ℂ] K) :=
  fun uv =>
    let Au := (strategy.pointMeasurement uv.1).toSubMeas
    let Av := (strategy.pointMeasurement uv.2).toSubMeas
    OpFamily.leftPlacedOpFamily strategy.state <|
      orderedProductOpFamily Au Av

/-- The reversed point product `(A^v_b A^u_a) ⊗ I`, placed by `strategy.state.L`. -/
noncomputable def pointMeasurementProductRight (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K) :
    IdxOpFamily (PointPairQuestion params) (PointPairOutcome params) (K →L[ℂ] K) :=
  fun uv =>
    let Au := (strategy.pointMeasurement uv.1).toSubMeas
    let Av := (strategy.pointMeasurement uv.2).toSubMeas
    OpFamily.leftPlacedOpFamily strategy.state <|
      reversedProductOpFamily Au Av

/-- The point measurement, reindexed by a sampled diagonal line and a parameter on it. -/
def sampledPointMeasurement (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K) :
    IdxSubMeas (PointDiagonalLineQuestion params) (Fq params) 𝔓 :=
  fun q =>
    (strategy.pointMeasurement (sampledPointFromDiagonalQuestion params q)).toSubMeas

/-- Evaluate the diagonal-line measurement at the sampled parameter. -/
noncomputable def sampledDiagonalLineEvaluation (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K) :
    IdxSubMeas (PointDiagonalLineQuestion params) (Fq params) 𝔓 :=
  fun q =>
    postprocess ((strategy.diagonalMeasurement q.1).toSubMeas) (fun f => f q.2)

/-- The ordered point product `(A^u_a A^v_b) ⊗ I`, indexed by a shared sampled line. -/
noncomputable def pointMeasurementProductAlongSharedLine (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K) :
    IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (K →L[ℂ] K) :=
  fun q =>
    pointMeasurementProductLeft params strategy
      (sampledPointPairFromSharedDiagonalQuestion params q)

/-- The reversed point product `(A^v_b A^u_a) ⊗ I`, indexed by a shared sampled line. -/
noncomputable def pointMeasurementProductAlongSharedLineReversed (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K) :
    IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (K →L[ℂ] K) :=
  fun q =>
    pointMeasurementProductRight params strategy
      (sampledPointPairFromSharedDiagonalQuestion params q)

/-- The mixed bridge `A^u_a ⊗ L^ℓ_[f(v)=b]`, placed by `strategy.state`. -/
noncomputable def pointDiagonalLineMixedProductLeft (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K) :
    IdxSubMeas (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (K →L[ℂ] K) :=
  fun q =>
    let ℓ := q.1
    let tu := q.2.1
    let tv := q.2.2
    let Au := (strategy.pointMeasurement (ℓ.pointAt tu)).toSubMeas
    let Lv := sampledDiagonalLineEvaluation params strategy (ℓ, tv)
    tensorProductSubMeas strategy.state Au Lv

/-- The bridge `I ⊗ (L^ℓ_[f(v)=b] · L^ℓ_[f(u)=a])`, placed by `strategy.state.R`.
Paper's "ordered" step: `Lv * Lu` (line measurement at v times line measurement at u). -/
noncomputable def diagonalLineProductOrdered (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K) :
    IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (K →L[ℂ] K) :=
  fun q =>
    let ℓ := q.1
    let tu := q.2.1
    let tv := q.2.2
    let Lu := sampledDiagonalLineEvaluation params strategy (ℓ, tu)
    let Lv := sampledDiagonalLineEvaluation params strategy (ℓ, tv)
    OpFamily.rightPlacedOpFamily strategy.state <|
      reversedProductOpFamily Lu Lv

/-- The swapped bridge `I ⊗ (L^ℓ_[f(u)=a] · L^ℓ_[f(v)=b])`, placed by `strategy.state.R`.
Paper's "reversed" step: `Lu * Lv` (projectively swapped from ordered). -/
noncomputable def diagonalLineProductReversed (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K) :
    IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (K →L[ℂ] K) :=
  fun q =>
    let ℓ := q.1
    let tu := q.2.1
    let tv := q.2.2
    let Lu := sampledDiagonalLineEvaluation params strategy (ℓ, tu)
    let Lv := sampledDiagonalLineEvaluation params strategy (ℓ, tv)
    OpFamily.rightPlacedOpFamily strategy.state <|
      orderedProductOpFamily Lu Lv

/-- The mixed bridge `A^v_b ⊗ L^ℓ_[f(u)=a]`, placed by `strategy.state`.
Outcome `(a, b)` maps to `strategy.state.L (A^v_b) * strategy.state.R (L^ℓ_[f(u)=a])`,
i.e. `a` indexes the line evaluation and `b` indexes the point measurement. -/
noncomputable def pointDiagonalLineMixedProductRight (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K) :
    IdxSubMeas (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (K →L[ℂ] K) :=
  fun q =>
    let ℓ := q.1
    let tu := q.2.1
    let tv := q.2.2
    let Av := (strategy.pointMeasurement (ℓ.pointAt tv)).toSubMeas
    let Lu := sampledDiagonalLineEvaluation params strategy (ℓ, tu)
    postprocess (tensorProductSubMeas strategy.state Av Lu) Prod.swap

end MIPRE.LIDT.Co.CommutativityPoints

end

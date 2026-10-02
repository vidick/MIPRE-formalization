/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
Commutativity/Main/Auxiliary/HEvalTransport.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Commutativity.Transport.FullSlice.Bridges.Closeness
public import MIPRE.Background.LIDT.Co.Commutativity.Transport.FullSlice.Bridges.ClosenessXEval
public import MIPRE.Background.LIDT.Co.Commutativity.Transport.FullSlice.Bridges.QSDD
public import MIPRE.Background.LIDT.Co.Commutativity.Transport.FullSlice.ZeroBounds
public import MIPRE.Background.LIDT.Co.Commutativity.Transport.EvaluationSpecialization
public import MIPRE.Background.LIDT.Co.Commutativity.EvaluatedSliceCommutation.Averages

@[expose] public section

/-!
# Section 11 commutativity: hEval/closenessOfIP transport

Evaluated-side closeness-of-IP transport and strong `hEval` bounds
(`eq:evaluate-gcom-at-points` through `eq:don't-understand-the-numbering-system`): the
counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/Main/Auxiliary/HEvalTransport.lean` in the
port of `planning/c6b-plan.md` (milestone M7, section "Port conventions").

Provides the zero-family bounds on the evaluated-slice products, the sharp bound
`fullSlice_closenessOfIP_CAB_hEval_sqrt` and its paper-envelope estimate
`fullSlice_closenessOfIP_CAB_hEval`.

The two zero-family bounds are `sum_ev_adjoint_self_leftTensor_mul_le_one` of
`Co/Commutativity/Transport/FullSlice/ZeroBounds.lean` applied to the evaluated factors, in place
of the vendored Kronecker computation repeated per factor order. The vendored hypothesis
`hnorm : strategy.state.IsNormalized` is dropped from all four lemmas: it is a theorem of the
model (`VecState.ev_one_of_isNormalized`). `zeroEvaluatedSliceOpFamily` is generic over any type
with a zero, as `zeroFullSliceOpFamily` is: a dependant writes
`zeroEvaluatedSliceOpFamily (R := K →L[ℂ] K) params` where the vendored text has `(ι := ι)`.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Commutativity

open MIPStarRE.LDT (Parameters FieldModel avgOver_nonneg avgOver_uniform_le_const
  uniformDistribution)
open MIPStarRE.LDT.Commutativity (EvaluatedSliceQuestion EvaluatedSliceOutcome
  commDataProcessedGError)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The zero operator family on the evaluated-slice outcome space. -/
noncomputable def zeroEvaluatedSliceOpFamily {R : Type*} [Zero R]
    (params : Parameters) [FieldModel params.q] :
    OpFamily (EvaluatedSliceOutcome params) R where
  outcome := fun _ => 0
  total := 0

/-- Questionwise, the ordered evaluated-slice product has squared distance at most `1`
from the zero family. -/
lemma evaluatedSliceProductLeft_qSDDOp_zero_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (q : EvaluatedSliceQuestion params) :
    strategy.state.qSDDOp
      (evaluatedSliceProductLeft params strategy family q)
      (zeroEvaluatedSliceOpFamily (R := K →L[ℂ] K) params) ≤ 1 := by
  let A := evaluatedSliceFirstFactor params family q
  let B := evaluatedSliceSecondFactor params family q
  refine le_of_eq_of_le ?_ (sum_ev_adjoint_self_leftTensor_mul_le_one strategy.state B A
    (evaluatedPointFamily_outcome_proj params family q.1))
  change ∑ ab : _ × _, strategy.state.ev
      (star (strategy.state.L (A.outcome ab.1 * B.outcome ab.2) - 0) *
        (strategy.state.L (A.outcome ab.1 * B.outcome ab.2) - 0)) = _
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [sub_zero]

/-- Questionwise, the reversed evaluated-slice product has squared distance at most `1`
from the zero family. -/
lemma zero_qSDDOp_evaluatedSliceProductRight_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (q : EvaluatedSliceQuestion params) :
    strategy.state.qSDDOp
      (zeroEvaluatedSliceOpFamily (R := K →L[ℂ] K) params)
      (evaluatedSliceProductRight params strategy family q) ≤ 1 := by
  let A := evaluatedSliceFirstFactor params family q
  let B := evaluatedSliceSecondFactor params family q
  refine le_of_eq_of_le ?_ (sum_ev_adjoint_self_leftTensor_mul_le_one strategy.state A B
    (evaluatedPointFamily_outcome_proj params family q.2))
  change ∑ ab : _ × _, strategy.state.ev
      (star (0 - strategy.state.L (B.outcome ab.2 * A.outcome ab.1)) *
        (0 - strategy.state.L (B.outcome ab.2 * A.outcome ab.1))) = _
  rw [Fintype.sum_prod_type]
  simp only [zero_sub, star_neg, neg_mul_neg]

/-- Strong evaluated-side `hEval` transport bound.

The direct evaluated-side route transports `hEval` to `evaluatedSliceProductLeft/Right`,
rewrites the resulting `SDDOpRel` via `evaluatedSliceCommutation_qSDDOp_avg_eq`, and combines it
with the a priori bound `sddErrorOp ≤ 4` for the evaluated product families. It yields the
sharper estimate `|evaluatedSliceABAAvg - evaluatedSliceABABAvg| ≤ √ν`, where
`ν = commDataProcessedGError params gamma zeta`. The paper-envelope estimate
`fullSlice_closenessOfIP_CAB_hEval` below recovers the older `6√ζ + √ν` statement when that
displayed Section 11 bound is convenient. -/
lemma fullSlice_closenessOfIP_CAB_hEval_sqrt
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (gamma zeta : ℝ)
    (hEval :
      strategy.state.SDDOpRel
        (uniformDistribution (EvaluatedSliceQuestion params))
        (evaluatedFromFullSliceProductLeft params strategy family)
        (evaluatedFromFullSliceProductRight params strategy family)
        (commDataProcessedGError params gamma zeta)) :
    |evaluatedSliceABAAvg params strategy family -
        evaluatedSliceABABAvg params strategy family| ≤
      Real.sqrt (commDataProcessedGError params gamma zeta) := by
  set δ := commDataProcessedGError params gamma zeta
  set d := evaluatedSliceABAAvg params strategy family -
    evaluatedSliceABABAvg params strategy family
  let 𝒟 := uniformDistribution (EvaluatedSliceQuestion params)
  let P := evaluatedSliceProductLeft params strategy family
  let Q := evaluatedSliceProductRight params strategy family
  -- The averaged squared distance between the two evaluated products is `2 d`.
  have hExpand : strategy.state.sddErrorOp 𝒟 P Q = 2 * d :=
    evaluatedSliceCommutation_qSDDOp_avg_eq params strategy family
  have hδ : 2 * d ≤ δ := hExpand ▸
    (evaluatedSliceCommutation_of_evaluationSpecialization params strategy family δ
      hEval).squaredDistanceBound
  have h4 : 2 * d ≤ 4 := by
    have htri := Preliminaries.stateDependentDistanceOpRel_triangle strategy.state.toVecState 𝒟
      P (fun _ => zeroEvaluatedSliceOpFamily (R := K →L[ℂ] K) params) Q 1 1
      ⟨avgOver_uniform_le_const _ 1 fun q =>
        evaluatedSliceProductLeft_qSDDOp_zero_le_one params strategy family q⟩
      ⟨avgOver_uniform_le_const _ 1 fun q =>
        zero_qSDDOp_evaluatedSliceProductRight_le_one params strategy family q⟩
    have := htri.squaredDistanceBound
    change strategy.state.sddErrorOp 𝒟 P Q ≤ _ at this
    linarith
  have hd : 0 ≤ d := by
    have : 0 ≤ strategy.state.sddErrorOp 𝒟 P Q :=
      avgOver_nonneg 𝒟 _ fun q => Preliminaries.qSDDOp_nonneg strategy.state.toVecState _ _
    linarith
  have hδ0 : 0 ≤ δ := by linarith
  rw [abs_of_nonneg hd]
  by_cases hδ4 : δ ≤ 4
  · nlinarith [Real.sq_sqrt hδ0, Real.sqrt_nonneg δ]
  · have h2 : (2 : ℝ) ≤ Real.sqrt δ := by
      rw [show (2 : ℝ) = Real.sqrt 4 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by linarith)
    linarith

/-- Combined `closenessOfIP` chain on the evaluated side (`commutativity-G.tex` lines 301, 334,
359-360, 394, 396), stated with the paper's displayed `6√ζ + √ν` envelope. -/
lemma fullSlice_closenessOfIP_CAB_hEval
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (gamma zeta : ℝ)
    (hEval :
      strategy.state.SDDOpRel
        (uniformDistribution (EvaluatedSliceQuestion params))
        (evaluatedFromFullSliceProductLeft params strategy family)
        (evaluatedFromFullSliceProductRight params strategy family)
        (commDataProcessedGError params gamma zeta)) :
    |evaluatedSliceABAAvg params strategy family -
        evaluatedSliceABABAvg params strategy family| ≤
      6 * Real.sqrt zeta +
        Real.sqrt (commDataProcessedGError params gamma zeta) :=
  (fullSlice_closenessOfIP_CAB_hEval_sqrt params strategy family gamma zeta hEval).trans
    (le_add_of_nonneg_left (by positivity))

end MIPRE.LIDT.Co.Commutativity

end

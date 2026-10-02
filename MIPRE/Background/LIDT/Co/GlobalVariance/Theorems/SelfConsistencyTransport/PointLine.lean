/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
GlobalVariance/Theorems/SelfConsistencyTransport/PointLine.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.GlobalVariance.Theorems.SelfConsistencyTransport.Utilities

@[expose] public section

/-!
# Axis-parallel point-line self-consistency transport

The counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/GlobalVariance/Theorems/SelfConsistencyTransport/PointLine.lean`
in the port of `planning/c6b-plan.md` (milestone M6, section "Port conventions"): the point-line
consistency and rebasing interfaces used in the middle two `2ε` moves of the local-variance
transport chain in `lem:local-variance-of-points` (`expansion.tex`, lines 306--307 and 309--310).

The vendored swap of the two prover roles, `consRel_symm_of_density_fixed` applied to
`strategy.densityFixed`, is the model's theorem `SymModel.consRel_symm_of_density_fixed`, so no
swap hypothesis appears. The axis-parallel consistency hypothesis is the `axisParallelTest` field
of `IsGood` itself, the ported `axisParallelFailureProbability` being the `bipartiteConsError` of
the point and line answer families by definition.

The weighted base-sample estimate `axisParallelBaseEventApproximation_weighted_sample` is
`prop:cab-approx-delta` (`Preliminaries.cabApproxDelta` on `S.toVecState`) with the multiplier
`S.R ((G_g)^{1/2})`, as in the vendored file; the selected line event is identified with
`B^ℓ_{[f(u)=g(u)]}` at the base point by `generalizeBLeftOutcome_base`, which is new here, in
place of the vendored `simp` unfolding of both postprocessings.

## Not ported

Every declaration of the vendored file has a counterpart here.

## New here

- `generalizeBLeftOutcome_base`: at the base point of an axis-parallel test sample, the selected
  outcome of the postprocessed line answer is `B^ℓ_{[f(u)=g(u)]}`.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/expansion.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.GlobalVariance

open MIPStarRE.LDT (Parameters FieldModel Point Fq AxisParallelLine AxisParallelTestSample
  zeroCoord subCoord avgOver uniformDistribution avgOver_congr avgOver_congr_on_support)
open MIPStarRE.LDT.GlobalVariance (AxisParallelLineQuestion axisParallelLineQuestionDistribution
  axisParallelLineQuestionParameter axisParallelLineQuestionParameter_pointAt pointOnLine
  avgOver_axisParallelLineQuestionDistribution_to_axisParallelTestSample)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The `ε` consistency interface for the point-line event at the base point of
an axis-parallel test sample.

For a sample `(u,i)`, the point side is the event `A^u_{g(u)}` and the line side
is the line-answer event obtained by evaluating the line polynomial at the base
parameter and testing equality with `g(u)`. This is the consistency input that
feeds the `2ε` approximation step at `expansion.tex`, line 307; the later
edge-transport proof still has to reindex from the base-point test sampling to
an arbitrary incident pair `(ℓ,u)` (using axis-line rebasing covariance) and then
apply `prop:simeq-to-approx`/`prop:cab-approx-delta`. -/
theorem axisParallelBaseEventConsistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (g : MIPStarRE.LDT.Polynomial params) :
    strategy.state.ConsRel (uniformDistribution (AxisParallelTestSample params))
      (fun s : AxisParallelTestSample params =>
        pointConditionedEventSubMeasAtPolynomial params strategy g s.1)
      (fun s : AxisParallelTestSample params =>
        postprocess (axisParallelLineAnswerFamily strategy s)
          (fun a : Fq params => if a = g s.1 then some () else none))
      eps :=
  Preliminaries.consRelDataProcessing_questionDependent strategy.state
    (uniformDistribution (AxisParallelTestSample params))
    (axisParallelPointAnswerFamily strategy) (axisParallelLineAnswerFamily strategy) eps
    (fun s a => if a = g s.1 then some () else none) ⟨hgood.axisParallelTest⟩

/-- Point-event measurement used by the base-point point-line consistency step. -/
noncomputable def axisParallelBasePointEventMeasurement
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (g : MIPStarRE.LDT.Polynomial params) :
    IdxMeas (AxisParallelTestSample params) (Option Unit) 𝔓 :=
  fun s => (pointConditionedEventSubMeasAtPolynomial params strategy g s.1).toMeasurement
    (strategy.pointMeasurement s.1).total_eq_one

/-- Line-event measurement used by the base-point point-line consistency step. -/
noncomputable def axisParallelBaseLineEventMeasurement
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (g : MIPStarRE.LDT.Polynomial params) :
    IdxMeas (AxisParallelTestSample params) (Option Unit) 𝔓 :=
  fun s =>
    (postprocess (axisParallelLineAnswerFamily strategy s)
      (fun a : Fq params => if a = g s.1 then some () else none)).toMeasurement
      (strategy.axisParallelMeasurement { base := s.1, direction := s.2 }).total_eq_one

/-- The symmetric `2ε` approximation interface for the point-line event.

This is the orientation used in `expansion.tex`, lines 306--307 and 309--310:
the line event is placed on the left register and the point event on the right
register.  It is obtained from `axisParallelBaseEventConsistency` by first
swapping the two prover roles, a theorem of the symmetric model, then applying
`prop:simeq-to-approx`. -/
theorem axisParallelBaseEventApproximation_swapped
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (g : MIPStarRE.LDT.Polynomial params) :
    strategy.state.SDDRel (uniformDistribution (AxisParallelTestSample params))
      (IdxSubMeas.liftLeft strategy.state
        (fun s : AxisParallelTestSample params =>
          postprocess (axisParallelLineAnswerFamily strategy s)
            (fun a : Fq params => if a = g s.1 then some () else none)))
      (IdxSubMeas.liftRight strategy.state
        (fun s : AxisParallelTestSample params =>
          pointConditionedEventSubMeasAtPolynomial params strategy g s.1))
      (2 * eps) :=
  ⟨(Preliminaries.simeqToApprox strategy.state
      (uniformDistribution (AxisParallelTestSample params))
      (axisParallelBaseLineEventMeasurement params strategy g)
      (axisParallelBasePointEventMeasurement params strategy g) eps
      (strategy.state.consRel_symm_of_density_fixed _ _ _ eps
        (axisParallelBaseEventConsistency params strategy eps delta gamma hgood g))
    ).leftRightSquaredDistanceBound⟩

/-- At the base point of an axis-parallel test sample `(u,i)`, the selected outcome of the
postprocessed line answer is the line event `B^ℓ_{[f(u)=g(u)]}` of the line question
`(ℓ,u)`, `ℓ` the line through `u` in direction `i`. -/
theorem generalizeBLeftOutcome_base
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (g : MIPStarRE.LDT.Polynomial params)
    (s : AxisParallelTestSample params) :
    (postprocess (axisParallelLineAnswerFamily strategy s)
        (fun a : Fq params => if a = g s.1 then some () else none)).outcome (some ()) =
      generalizeBLeftOperatorAtPolynomial params strategy g
        ({ base := s.1, direction := s.2 }, s.1) := by
  classical
  have hparam : axisParallelLineQuestionParameter
      (({ base := s.1, direction := s.2 } : AxisParallelLine params), s.1) = zeroCoord := by
    simp [axisParallelLineQuestionParameter, subCoord, zeroCoord]
  unfold generalizeBLeftOperatorAtPolynomial generalizeBLeftEventSubMeasAtPolynomial
    axisParallelLineAnswerFamily axisParallelLineAnswerFamilyOf
  simp only [SubMeas.postprocess_outcome, hparam, ite_eq_left_iff, reduceCtorEq, imp_false,
    not_not, Finset.filter_eq', Finset.mem_univ, ite_true, Finset.sum_singleton]

/-- The selected, square-root weighted point-line approximation on the native
axis-parallel base-point sample distribution.

After `prop:cab-approx-delta` with multiplier `S.R ((G_g)^{1/2})`, the swapped
base-event approximation gives the paper's line-306 to line-307 move at a
sample `(u,i)`: the line question is represented by the rebased line with base
`u` and direction `i`. -/
theorem axisParallelBaseEventApproximation_weighted_sample
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (g : MIPStarRE.LDT.Polynomial params) :
    avgOver (uniformDistribution (AxisParallelTestSample params))
      (fun s =>
        let qu : AxisParallelLineQuestion params :=
          ({ base := s.1, direction := s.2 }, s.1)
        let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
          weightedPointConditionedRightOperatorAtPolynomial params strategy G g s.1
        strategy.state.ev (star D * D)) ≤
      2 * eps := by
  classical
  let S := strategy.state
  let lineEvent : AxisParallelTestSample params → Option Unit → K →L[ℂ] K := fun s =>
    (IdxSubMeas.liftLeft S (fun s : AxisParallelTestSample params =>
      postprocess (axisParallelLineAnswerFamily strategy s)
        (fun a : Fq params => if a = g s.1 then some () else none)) s).outcome
  let pointEvent : AxisParallelTestSample params → Option Unit → K →L[ℂ] K := fun s =>
    (IdxSubMeas.liftRight S (fun s : AxisParallelTestSample params =>
      pointConditionedEventSubMeasAtPolynomial params strategy g s.1) s).outcome
  have hAB := (qSDDCore_optionUnit_some_le S.toVecState
      (uniformDistribution (AxisParallelTestSample params)) lineEvent pointEvent).trans
    (axisParallelBaseEventApproximation_swapped params strategy eps delta gamma hgood
      g).squaredDistanceBound
  have hcab := Preliminaries.cabApproxDelta S.toVecState
    (uniformDistribution (AxisParallelTestSample params))
    (fun s (_ : Unit) => lineEvent s (some ())) (fun s (_ : Unit) => pointEvent s (some ()))
    (fun _ _ (_ : Unit) => S.R (polynomialWeightSqrtOperator params G g)) (2 * eps) hAB
    fun _ _ => (Fintype.sum_unique _).trans_le
      (rightPolynomialWeightSqrt_contraction S params G g)
  refine le_of_eq_of_le (avgOver_congr _ _ _ fun s => ?_) hcab
  have hline : lineEvent s (some ()) =
      S.L (generalizeBLeftOperatorAtPolynomial params strategy g
        ({ base := s.1, direction := s.2 }, s.1)) :=
    congrArg S.L (generalizeBLeftOutcome_base params strategy g s)
  have hpoint : pointEvent s (some ()) =
      S.R (pointConditionedOutcomeOperatorAtPolynomial params strategy g s.1) :=
    congrArg S.R (pointConditionedEventSubMeasAtPolynomial_some params strategy g s.1)
  rw [VecState.qSDDCore, Fintype.sum_prod_type, Fintype.sum_unique, Fintype.sum_unique, hline,
    hpoint,
    S.rightTensor_mul_leftTensor_eq_opTensor, S.rightTensor_mul_rightTensor]
  rfl

/-- Rebasing an incident axis-parallel line question at its sampled point does
not change the evaluated line event operator.

The left operator is the event `f(t)=g(ℓ(t))` for the line measurement on `ℓ`.
After rebasing `ℓ` at `t`, the sampled point is the new base point and the same
event is read as `f(0)=g(ℓ(t))`.  This is exactly the strategy's axis-parallel
measurement covariance, via `AxisParallelCovariantMeasurement.reparamInvariant`,
and is the operator-level reindexing used in `expansion.tex:300-307`. -/
theorem generalizeBLeftOperatorAtPolynomial_rebaseAt_pointAt
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (g : MIPStarRE.LDT.Polynomial params)
    (ℓ : AxisParallelLine params) (t : Fq params) :
    generalizeBLeftOperatorAtPolynomial params strategy g (ℓ, ℓ.pointAt t) =
      generalizeBLeftOperatorAtPolynomial params strategy g
        (AxisParallelLine.rebaseAt ℓ t, ℓ.pointAt t) := by
  unfold generalizeBLeftOperatorAtPolynomial generalizeBLeftEventSubMeasAtPolynomial
  rw [axisParallelLineQuestionParameter_pointAt]
  have hparam_rebase :
      axisParallelLineQuestionParameter
        (AxisParallelLine.rebaseAt ℓ t, ℓ.pointAt t) = zeroCoord := by
    simp [axisParallelLineQuestionParameter, AxisParallelLine.rebaseAt, AxisParallelLine.pointAt,
      subCoord, zeroCoord]
  rw [hparam_rebase]
  have h := AxisParallelCovariantMeasurement.reparamInvariant strategy.axisParallelMeasurement
      ℓ t (g (ℓ.pointAt t))
  simp only [postprocess, ite_eq_left_iff, reduceCtorEq, imp_false, not_not] at h ⊢
  convert h.symm

/-- Weighted version of
`generalizeBLeftOperatorAtPolynomial_rebaseAt_pointAt`.

Tensoring the line event with the fixed polynomial weight `(G_g)^{1/2}` preserves
the rebasing equality.  This is the exact weighted operator identity needed to
transport the `2ε` base-point estimate to arbitrary incident line questions in
steps 2 and 5 of `lem:local-variance-of-points`. -/
theorem weightedGeneralizeBLeftOperatorAtPolynomial_rebaseAt_pointAt
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (g : MIPStarRE.LDT.Polynomial params)
    (ℓ : AxisParallelLine params) (t : Fq params) :
    weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g (ℓ, ℓ.pointAt t) =
      weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g
        (AxisParallelLine.rebaseAt ℓ t, ℓ.pointAt t) :=
  congrArg (fun X => strategy.state.opTensor X (polynomialWeightSqrtOperator params G g))
    (generalizeBLeftOperatorAtPolynomial_rebaseAt_pointAt params strategy g ℓ t)

/-- The weighted line-to-point approximation after reindexing the base-point test
sample to an arbitrary incident line question.

This is the paper's step 5 (`expansion.tex`, line 309--310), before coupling the
line question with the second endpoint of the hypercube-edge presentation: for
`v ∈ ℓ`, `B^ℓ_[f(v)=g(v)] ⊗ (G_g)^{1/2}` is `2ε`-close to
`I ⊗ (G_g)^{1/2} A^v_{g(v)}`. -/
theorem axisParallelPointLineConsistency_weighted_leftToRightLineQuestion
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (g : MIPStarRE.LDT.Polynomial params) :
    avgOver (axisParallelLineQuestionDistribution params)
      (fun qu =>
        let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
          weightedPointConditionedRightOperatorAtPolynomial params strategy G g qu.2
        strategy.state.ev (star D * D)) ≤
      2 * eps := by
  let F : AxisParallelTestSample params → ℝ := fun s =>
    let qu : AxisParallelLineQuestion params := ({ base := s.1, direction := s.2 }, s.1)
    let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
      weightedPointConditionedRightOperatorAtPolynomial params strategy G g s.1
    strategy.state.ev (star D * D)
  calc
    avgOver (axisParallelLineQuestionDistribution params)
        (fun qu =>
          let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
            weightedPointConditionedRightOperatorAtPolynomial params strategy G g qu.2
          strategy.state.ev (star D * D))
      = avgOver (axisParallelLineQuestionDistribution params)
          (fun qu => F (qu.2, qu.1.direction)) := by
          apply avgOver_congr_on_support
          intro qu hqu
          have hline : pointOnLine (params := params) qu := by
            simpa [axisParallelLineQuestionDistribution] using hqu
          rcases qu with ⟨ℓ, u⟩
          rcases hline with ⟨t, ht⟩
          change ℓ.pointAt t = u at ht
          subst u
          dsimp only [F]
          rw [weightedGeneralizeBLeftOperatorAtPolynomial_rebaseAt_pointAt]
          rfl
    _ = avgOver (uniformDistribution (AxisParallelTestSample params)) F :=
        avgOver_axisParallelLineQuestionDistribution_to_axisParallelTestSample params F
    _ ≤ 2 * eps := axisParallelBaseEventApproximation_weighted_sample
      params strategy eps delta gamma hgood G g

/-- The reverse weighted point-to-line approximation after incident-line
reindexing.

This is the paper's step 2 (`expansion.tex`, line 306--307):
`I ⊗ (G_g)^{1/2} A^u_{g(u)}` is `2ε`-close to
`B^ℓ_[f(u)=g(u)] ⊗ (G_g)^{1/2}` for an incident line question `(ℓ,u)`. -/
theorem axisParallelPointLineConsistency_weighted_rightToLeftLineQuestion
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (g : MIPStarRE.LDT.Polynomial params) :
    avgOver (axisParallelLineQuestionDistribution params)
      (fun qu =>
        let D := weightedPointConditionedRightOperatorAtPolynomial params strategy G g qu.2 -
          weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
        strategy.state.ev (star D * D)) ≤
      2 * eps :=
  (avgOver_congr _ _ _ fun qu =>
      ev_adjoint_sub_swap strategy.state.toVecState
        (weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu)
        (weightedPointConditionedRightOperatorAtPolynomial params strategy G g qu.2)).trans_le
    (axisParallelPointLineConsistency_weighted_leftToRightLineQuestion
      params strategy eps delta gamma hgood G g)

end MIPRE.LIDT.Co.GlobalVariance

end

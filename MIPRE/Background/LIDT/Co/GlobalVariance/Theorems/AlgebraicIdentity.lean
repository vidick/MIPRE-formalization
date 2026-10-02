/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
GlobalVariance/Theorems/AlgebraicIdentity.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.ExpansionHypercubeGraph.Theorems.Results
public import MIPRE.Background.LIDT.Co.Preliminaries.CauchySchwarz
public import MIPRE.Background.LIDT.Co.Preliminaries.CompletionTransfer
public import MIPRE.Background.LIDT.Co.Preliminaries.ComparisonCore
public import MIPRE.Background.LIDT.Co.Preliminaries.PolynomialAgreement
public import MIPRE.Background.LIDT.Co.Preliminaries.SelfConsistency.Extensions
public import MIPRE.Background.LIDT.Co.GlobalVariance.Theorems.Averaging
public import MIPRE.Background.LIDT.Co.GlobalVariance.Theorems.Statements
public import MIPRE.Background.LIDT.Co.Test.StrategyFailures
public import MIPRE.Background.LIDT.MIPStarRE.LDT.GlobalVariance.Theorems.AlgebraicIdentity

@[expose] public section

/-!
# Section 8 global variance: algebraic identities and variance reductions

The counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/GlobalVariance/Theorems/AlgebraicIdentity.lean` in the port
of `planning/c6b-plan.md` (milestone M6, section "Port conventions"): the local-to-global transfer
for the point-conditioned variances (`pointConditionedExpansionTransfer`), the algebra of the
weight `(G_g)^{1/2}` and of the weighted operators `A ⊗ (G_g)^{1/2}`, the projective expansion of
the `lem:generalize-b` deviation into the line-collision residual
(`generalizeBDeviationAtPolynomial_eq_collisionResidual`), and the identities between the
weighted squared-norm deviations and the point-conditioned variances.

`opTensor` is `strategy.state.opTensor`, `leftTensor (ι₂ := ι)` is `strategy.state.L`, `ᴴ` is
`star`, and the vendored second state `ψbi` is a vector state `V : VecState K`, as in
`Defs/Families.lean`.

**The weighted state.** The vendored point-conditioned variances evaluate the family
`u ↦ A^u_{g(u)} ⊗ 1` on the weighted state `(1 ⊗ √G_g) ρ (1 ⊗ √G_g)ᴴ`; the ported ones are the
variances of the weighted family `u ↦ A^u_{g(u)} ⊗ (G_g)^{1/2}` on the strategy's own state
(`Defs/Operators.lean`, module docstring). So the vendored bridge between the two,
`weightedPolynomialState_ev_leftTensor`, is not needed, and its consumer
`weightedNormDeviation_eq_pointConditionedDifferenceAvg` is translated with the variance summand
of the weighted family on its right side, where it holds by definition; the two identities with
the variances and the local-to-global transfer become one-line consequences, and
`pointConditionedExpansionTransfer` is `ExpansionHypercubeGraph.localToGlobal` itself.

## Not ported

- `globalVarianceOfPoints_bound_of_local`: classical, imported.
- `generalizeB_right_event_implies_left_event`: classical, imported.
- `weightedPolynomialState_ev_leftTensor`: the weighted state `(1 ⊗ √G_g) ρ (1 ⊗ √G_g)ᴴ` is not
  ported (a vector state has no density, and the weighted vector is not normalized); the
  point-conditioned variances are those of the weighted family on the strategy's state, so no
  move between the two states is needed.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/expansion.tex`
- `blueprint/src/chapter/ch06_variance.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.GlobalVariance

open MIPStarRE.LDT (Parameters FieldModel Point Distribution AxisLinePolynomial avgOver
  avgOver_nonneg avgOver_congr_on_support)
open MIPStarRE.LDT.ExpansionHypercubeGraph (rerandomizeCoord independentPointPair)
open MIPStarRE.LDT.GlobalVariance (AxisParallelLineQuestion pointOnLine
  axisParallelLineQuestionParameter axisParallelLineQuestionDistribution
  generalizeB_right_event_implies_left_event)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! # Algebraic identities and variance reductions -/

/-- `lem:local-to-global` for the point-conditioned variances at a fixed polynomial. -/
theorem pointConditionedExpansionTransfer
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (g : MIPStarRE.LDT.Polynomial params) :
    pointConditionedGlobalVarianceAtPolynomial params strategy G g ≤
      (params.m : ℝ) * pointConditionedLocalVarianceAtPolynomial params strategy G g :=
  ExpansionHypercubeGraph.localToGlobal params _ _

/-! ## Algebraic norm/variance reductions -/

/-- The weight `(G_g)^{1/2}` is self-adjoint. -/
theorem polynomialWeightSqrtOperator_conjTranspose
    (params : Parameters)
    [FieldModel params.q]
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) (g : MIPStarRE.LDT.Polynomial params) :
    star (polynomialWeightSqrtOperator params G g) =
      polynomialWeightSqrtOperator params G g :=
  (CFC.sqrt_nonneg (G.outcome g)).isSelfAdjoint.star_eq

/-- The weight `(G_g)^{1/2}` squares to `G_g`. -/
theorem polynomialWeightSqrtOperator_mul_self
    (params : Parameters)
    [FieldModel params.q]
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) (g : MIPStarRE.LDT.Polynomial params) :
    polynomialWeightSqrtOperator params G g *
        polynomialWeightSqrtOperator params G g =
      G.outcome g :=
  CFC.sqrt_mul_sqrt_self (G.outcome g) (G.outcome_pos g)

/-- The difference of the two weighted point-conditioned operators factors as
the tensor product of the point-operator difference and the square root of the
polynomial outcome. -/
theorem weightedPointConditionedOperator_sub
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) (g : MIPStarRE.LDT.Polynomial params)
    (u v : Point params) :
    weightedPointConditionedOperatorAtPolynomial params strategy G g u -
        weightedPointConditionedOperatorAtPolynomial params strategy G g v =
      strategy.state.opTensor
        (pointConditionedOutcomeOperatorAtPolynomial params strategy g u -
          pointConditionedOutcomeOperatorAtPolynomial params strategy g v)
        (polynomialWeightSqrtOperator params G g) :=
  strategy.state.opTensor_sub_left _ _ _

/-- The square of the weighted point-conditioned difference is the tensor of
the squared point-operator difference with the polynomial outcome. -/
theorem weightedPointConditionedOperator_sq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) (g : MIPStarRE.LDT.Polynomial params)
    (u v : Point params) :
    let D := weightedPointConditionedOperatorAtPolynomial params strategy G g u -
        weightedPointConditionedOperatorAtPolynomial params strategy G g v
    star D * D =
      strategy.state.opTensor
        (star (pointConditionedOutcomeOperatorAtPolynomial params strategy g u -
          pointConditionedOutcomeOperatorAtPolynomial params strategy g v) *
            (pointConditionedOutcomeOperatorAtPolynomial params strategy g u -
              pointConditionedOutcomeOperatorAtPolynomial params strategy g v))
        (G.outcome g) := by
  dsimp only
  rw [weightedPointConditionedOperator_sub, strategy.state.conjTranspose_opTensor,
    strategy.state.opTensor_mul, polynomialWeightSqrtOperator_conjTranspose,
    polynomialWeightSqrtOperator_mul_self]

/-- On an incident line question, the left `lem:generalize-b` event is the right event plus the
residual line-collision event. -/
theorem generalizeBLeftOperator_eq_right_add_collision
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (g : MIPStarRE.LDT.Polynomial params)
    (qu : AxisParallelLineQuestion params)
    (hline : pointOnLine (params := params) qu) :
    generalizeBLeftOperatorAtPolynomial params strategy g qu =
      generalizeBRightOperatorAtPolynomial params strategy g qu +
        generalizeBCollisionOperatorAtPolynomial params strategy g qu := by
  classical
  unfold generalizeBLeftOperatorAtPolynomial generalizeBRightOperatorAtPolynomial
    generalizeBCollisionOperatorAtPolynomial
  unfold generalizeBLeftEventSubMeasAtPolynomial generalizeBRightEventSubMeasAtPolynomial
    generalizeBCollisionEventSubMeasAtPolynomial
  cases qu with
  | mk ℓ u =>
      simp only [generalizeBCollisionEventProjMeasAtPolynomial, ProjMeas.postprocess_toSubMeas,
        SubMeas.postprocess_outcome, Finset.sum_filter]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro x _
      by_cases hq :
          x.poly = (MIPStarRE.LDT.Polynomial.restrictToAxisParallelLine params g ℓ).poly
      · have hp : x (axisParallelLineQuestionParameter (ℓ, u)) = g u :=
          generalizeB_right_event_implies_left_event params g (ℓ, u) hline x hq
        simp [hp, hq]
      · by_cases hp : x (axisParallelLineQuestionParameter (ℓ, u)) = g u <;> simp [hp, hq]

/-- On an incident line question, the squared difference of the two `lem:generalize-b` events is
the residual line-collision event, a projection. -/
theorem generalizeBLineDifference_sq_eq_collision
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (g : MIPStarRE.LDT.Polynomial params)
    (qu : AxisParallelLineQuestion params)
    (hline : pointOnLine (params := params) qu) :
    star (generalizeBLeftOperatorAtPolynomial params strategy g qu -
        generalizeBRightOperatorAtPolynomial params strategy g qu) *
        (generalizeBLeftOperatorAtPolynomial params strategy g qu -
          generalizeBRightOperatorAtPolynomial params strategy g qu) =
      generalizeBCollisionOperatorAtPolynomial params strategy g qu := by
  have hsub :
      generalizeBLeftOperatorAtPolynomial params strategy g qu -
          generalizeBRightOperatorAtPolynomial params strategy g qu =
        generalizeBCollisionOperatorAtPolynomial params strategy g qu := by
    rw [generalizeBLeftOperator_eq_right_add_collision params strategy g qu hline]
    abel
  rw [hsub]
  change star ((generalizeBCollisionEventProjMeasAtPolynomial params strategy g qu).outcome
      (some ())) *
      (generalizeBCollisionEventProjMeasAtPolynomial params strategy g qu).outcome
        (some ()) =
    (generalizeBCollisionEventProjMeasAtPolynomial params strategy g qu).outcome (some ())
  rw [(generalizeBCollisionEventProjMeasAtPolynomial params strategy g qu).outcome_hermitian
    (some ())]
  exact (generalizeBCollisionEventProjMeasAtPolynomial params strategy g qu).proj (some ())

/-- Projective expansion for the pointwise `lem:generalize-b` deviation.

For incident line questions, the right event `f = g|_ℓ` is a subevent of the
left event `f(u)=g(u)`.  Since `B^ℓ` is projective, the squared difference is
exactly the residual line-collision event `f(u)=g(u) ∧ f≠g|_ℓ`, with the
right-register square root collapsed to `G_g`. -/
theorem generalizeBDeviationAtPolynomial_eq_collisionResidual
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (V : VecState K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (g : MIPStarRE.LDT.Polynomial params) :
    generalizeBDeviationAtPolynomial params strategy V G g =
      generalizeBCollisionResidual params strategy V G g := by
  unfold generalizeBDeviationAtPolynomial generalizeBCollisionResidual
  apply avgOver_congr_on_support
  intro qu hqu
  have hline : pointOnLine (params := params) qu := by
    simpa [axisParallelLineQuestionDistribution] using hqu
  dsimp only
  rw [weightedGeneralizeBLeftOperatorAtPolynomial, weightedGeneralizeBRightOperatorAtPolynomial,
    strategy.state.opTensor_sub_left, strategy.state.conjTranspose_opTensor,
    strategy.state.opTensor_mul, polynomialWeightSqrtOperator_conjTranspose,
    polynomialWeightSqrtOperator_mul_self,
    generalizeBLineDifference_sq_eq_collision params strategy g qu hline]

/-- The averaged weighted squared differences are the averaged variance summands of the weighted
family `u ↦ A^u_{g(u)} ⊗ (G_g)^{1/2}`. The vendored right side is the variance summand of the
family `u ↦ A^u_{g(u)} ⊗ 1` on the weighted state; here the weight sits in the family (module
docstring), and the identity holds by definition. -/
theorem weightedNormDeviation_eq_pointConditionedDifferenceAvg
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) (g : MIPStarRE.LDT.Polynomial params)
    (𝒟 : Distribution (Point params × Point params)) :
    avgOver 𝒟 (fun uv =>
        let D := weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1 -
          weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2
        strategy.state.ev (star D * D)) =
      avgOver 𝒟 (fun uv =>
        strategy.state.ev
          (ExpansionHypercubeGraph.pointDifferenceSquaredOperator
            (fun u => weightedPointConditionedOperatorAtPolynomial params strategy G g u)
            uv.1 uv.2)) :=
  rfl

/-- The edgewise weighted squared-difference expression is exactly twice the
local variance of the point-conditioned family on the weighted state. This is
`eq:equivalent-local-variance` unpacked at a fixed polynomial. -/
theorem localVarianceDeviationAtPolynomial_eq_two_pointConditionedLocalVarianceAtPolynomial
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) (g : MIPStarRE.LDT.Polynomial params) :
    localVarianceDeviationAtPolynomial params strategy strategy.state G g =
      2 * pointConditionedLocalVarianceAtPolynomial params strategy G g := by
  unfold localVarianceDeviationAtPolynomial pointConditionedLocalVarianceAtPolynomial
    ExpansionHypercubeGraph.localVariance
  rw [← mul_assoc, show (2 : ℝ) * (1 / 2 : ℝ) = 1 by norm_num, one_mul]
  exact weightedNormDeviation_eq_pointConditionedDifferenceAvg params strategy G g
    (rerandomizeCoord params)

/-- The independent-points weighted squared-difference expression is exactly
twice the global variance of the point-conditioned family on the weighted state. -/
theorem globalVarianceDeviationAtPolynomial_eq_two_pointConditionedGlobalVarianceAtPolynomial
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) (g : MIPStarRE.LDT.Polynomial params) :
    globalVarianceDeviationAtPolynomial params strategy strategy.state G g =
      2 * pointConditionedGlobalVarianceAtPolynomial params strategy G g := by
  unfold globalVarianceDeviationAtPolynomial pointConditionedGlobalVarianceAtPolynomial
    ExpansionHypercubeGraph.globalVariance
  rw [← mul_assoc, show (2 : ℝ) * (1 / 2 : ℝ) = 1 by norm_num, one_mul]
  exact weightedNormDeviation_eq_pointConditionedDifferenceAvg params strategy G g
    (independentPointPair params)

/-- A bound on the edgewise weighted norm expression implies the corresponding
bound on the local variance. The factor `1/2` in `localVariance` only strengthens
the estimate. -/
theorem pointConditionedLocalVarianceAtPolynomial_le_of_deviation
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) {g : MIPStarRE.LDT.Polynomial params}
    {η : ℝ}
    (hdev : localVarianceDeviationAtPolynomial params strategy strategy.state G g ≤ η) :
    pointConditionedLocalVarianceAtPolynomial params strategy G g ≤ η := by
  have heq :=
    localVarianceDeviationAtPolynomial_eq_two_pointConditionedLocalVarianceAtPolynomial
      params strategy G g
  have hnonneg : 0 ≤ pointConditionedLocalVarianceAtPolynomial params strategy G g :=
    mul_nonneg (by norm_num)
      (avgOver_nonneg (rerandomizeCoord params) _ fun uv =>
        strategy.state.ev_adjoint_self_nonneg
          (weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1 -
            weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2))
  linarith

/-- Pointwise local-to-global transfer for the paper's weighted squared-norm
form: the independent-points expression is at most `m` times the edge expression.
This combines `lem:local-to-global` with the two exact norm/variance identities
above, so no independent global-deviation hypothesis is needed. -/
theorem globalVarianceDeviationAtPolynomial_le_m_localVarianceDeviationAtPolynomial
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) (g : MIPStarRE.LDT.Polynomial params) :
    globalVarianceDeviationAtPolynomial params strategy strategy.state G g ≤
      (params.m : ℝ) *
        localVarianceDeviationAtPolynomial params strategy strategy.state G g := by
  rw [globalVarianceDeviationAtPolynomial_eq_two_pointConditionedGlobalVarianceAtPolynomial,
    localVarianceDeviationAtPolynomial_eq_two_pointConditionedLocalVarianceAtPolynomial,
    mul_left_comm]
  exact mul_le_mul_of_nonneg_left (pointConditionedExpansionTransfer params strategy G g)
    (by norm_num)

end MIPRE.LIDT.Co.GlobalVariance

end

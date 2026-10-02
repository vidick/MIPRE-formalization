/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
GlobalVariance/Theorems/CollisionExpansion.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.GlobalVariance.Theorems.AlgebraicIdentity
public import MIPRE.Background.LIDT.MIPStarRE.LDT.GlobalVariance.Theorems.CollisionExpansion

@[expose] public section

/-!
# Section 8 global variance: collision expansion and Schwartz–Zippel bounds

The counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/GlobalVariance/Theorems/CollisionExpansion.lean` in the
port of `planning/c6b-plan.md` (milestone M6, section "Port conventions"): the `lem:generalize-b`
wrappers (`generalizeB_of_pointwise`, `generalizeB`), the expansion of the line-collision
residual over line/parameter seeds, and its Schwartz–Zippel bound by `m·d/q`
(`generalizeBPointwiseSchwartzZippel`, `generalizeBFromSchwartzZippel`).

`opTensor` is `strategy.state.opTensor`, `ev ψ` is `V.ev` or `strategy.state.ev`, and the
vendored second state `ψbi` is a vector state `V : VecState K` in the same argument position, as
in `Defs/Families.lean` and `Theorems/Statements.lean`; callers pass `strategy.state`. The
normalization `ev 1 = 1` of the strategy's state is the keystone's hypothesis-free
`ev_one_of_isNormalized`, so the vendored `strategy.isNormalized` argument disappears.

The reparametrizations of the line-question distribution and the Schwartz–Zippel coefficient
bound are statements about distributions and polynomials alone; this file imports the vendored
file for them and names them through an explicit `open` list.

## Not ported

- `axisParallelLineQuestionParameterEquiv`: classical, imported.
- `avgOver_axisParallelLineQuestionDistribution`: classical, imported.
- `axisParallelLinePointParamEquiv`: classical, imported.
- `avgOver_axisParallelLinePointParam`: classical, imported.
- `avgOver_axisParallelLineQuestionDistribution_to_axisParallelTestSample`: classical, imported.
- `generalizeBLineCollisionCoefficient_le`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/expansion.tex`
- `blueprint/src/chapter/ch06_variance.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.GlobalVariance

open MIPStarRE.LDT (Parameters FieldModel Fq AxisParallelLine AxisLinePolynomial avgOver
  uniformDistribution avgOver_congr avgOver_mono avgOver_sum avgOver_mul_const
  avgOver_uniform_prod avgOver_uniform_le_const)
open MIPStarRE.LDT.GlobalVariance (axisParallelLineQuestionDistribution
  axisParallelLineQuestionParameter_pointAt avgOver_axisParallelLineQuestionDistribution
  avgOver_polynomialDistribution_le_of_pointwise generalizeBError
  generalizeBLineCollisionCoefficient_le)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- `lem:generalize-b` from its pointwise deviation bound: the aggregated families are close in
`SDDRel`, and the polynomial average of the deviations obeys the same bound. -/
theorem generalizeB_of_pointwise
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (V : VecState K)
    (hpoint :
      ∀ g : MIPStarRE.LDT.Polynomial params,
        generalizeBDeviationAtPolynomial params strategy V G g ≤ generalizeBError params) :
    GeneralizeBStatement params strategy V G where
  aggregateFamilyComparison :=
    sddRel_unit_family_of_pointwise V
      (axisParallelLineQuestionDistribution params)
      (generalizeBLeftFamily params strategy G)
      (generalizeBRightFamily params strategy G)
      (fun qu g => weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu)
      (fun qu g => weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu)
      (fun _ => rfl) (fun _ => rfl) (generalizeBError params) hpoint
  pointwiseNormBound := hpoint
  averagedNormBound :=
    avgOver_polynomialDistribution_le_of_pointwise params
      (fun g => generalizeBDeviationAtPolynomial params strategy V G g)
      (generalizeBError params) hpoint

/-- `lem:generalize-b`. -/
theorem generalizeB
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (_eps _delta _gamma : ℝ)
    (_hgood : strategy.IsGood _eps _delta _gamma)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (V : VecState K)
    (hpoint :
      ∀ g : MIPStarRE.LDT.Polynomial params,
        generalizeBDeviationAtPolynomial params strategy V G g ≤ generalizeBError params) :
    GeneralizeBStatement params strategy V G :=
  -- The analytic pointwise estimate is an explicit input here. In the
  -- self-improvement pipeline it is supplied as an explicit theorem
  -- hypothesis.
  generalizeB_of_pointwise params strategy G V hpoint

/-- Expanding the postprocessed collision event at the seeded question
`(ℓ, ℓ(t))` gives the line-answer sum from `expansion.tex`, lines 283--286. -/
theorem generalizeBCollisionSeed_integrand
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (V : VecState K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (g : MIPStarRE.LDT.Polynomial params)
    (ℓ : AxisParallelLine params) (t : Fq params) :
    V.ev (strategy.state.opTensor
        (generalizeBCollisionOperatorAtPolynomial params strategy g (ℓ, ℓ.pointAt t))
        (G.outcome g)) =
      ∑ f : AxisLinePolynomial params,
        (if f t = (MIPStarRE.LDT.Polynomial.restrictToAxisParallelLine params g ℓ) t ∧
            f.poly ≠ (MIPStarRE.LDT.Polynomial.restrictToAxisParallelLine params g ℓ).poly then
          (1 : ℝ)
        else 0) *
          V.ev (strategy.state.opTensor
            ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f)
            (G.outcome g)) := by
  classical
  simp only [generalizeBCollisionOperatorAtPolynomial,
    generalizeBCollisionEventSubMeasAtPolynomial, generalizeBCollisionEventProjMeasAtPolynomial,
    ProjMeas.postprocess_toSubMeas, SubMeas.postprocess_outcome,
    axisParallelLineQuestionParameter_pointAt,
    MIPStarRE.LDT.Polynomial.restrictToAxisParallelLine_apply]
  rw [strategy.state.opTensor_sum_left_finset, V.ev_finset_sum]
  simp [Finset.sum_filter]

/-- Positivity of the tensor mass appearing in the line-collision expansion. -/
theorem generalizeBLineCollisionTensorMass_nonneg
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (g : MIPStarRE.LDT.Polynomial params) (ℓ : AxisParallelLine params)
    (f : AxisLinePolynomial params) :
    0 ≤ strategy.state.ev (strategy.state.opTensor
      ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f) (G.outcome g)) :=
  strategy.state.ev_nonneg_of_psd _
    (strategy.state.opTensor_nonneg
      ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome_pos f) (G.outcome_pos g))

/-- The total tensor mass left after summing over line answers is at most one.

This is the normalization half of `expansion.tex`, lines 286--288: the
left-register line measurement sums to its total operator, the right-register
operator is the single submeasurement outcome `G_g ≤ 1`, and the strategy state
is normalized. -/
theorem generalizeBLineCollisionTensorMass_sum_le_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (g : MIPStarRE.LDT.Polynomial params) (ℓ : AxisParallelLine params) :
    (∑ f : AxisLinePolynomial params,
      strategy.state.ev (strategy.state.opTensor
        ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f) (G.outcome g))) ≤ 1 := by
  set B := (strategy.axisParallelMeasurement ℓ).toSubMeas
  rw [← strategy.state.ev_sum, ← strategy.state.opTensor_sum_left_univ, B.sum_eq_total,
    ← strategy.state.ev_one_of_isNormalized]
  exact strategy.state.ev_mono _ _
    ((strategy.state.opTensor_le_leftTensor B.total_nonneg (G.outcome_le_one g)).trans
      (strategy.state.leftTensor_le_one B.total_le_one))

/-- Commuting the uniform parameter average past the finite sum over line answers.

This is the purely finite-sum bookkeeping between the paper's seed average over
`(ℓ,t)` and the coefficient-weighted display in `expansion.tex`, lines 286--288. -/
theorem generalizeBSeedCollisionExpansion_eq_lineCollisionExpansion
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (V : VecState K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (g : MIPStarRE.LDT.Polynomial params) :
    generalizeBSeedCollisionExpansion params strategy V G g =
      generalizeBLineCollisionExpansion params strategy V G g := by
  unfold generalizeBSeedCollisionExpansion generalizeBLineCollisionExpansion
  rw [avgOver_uniform_prod (α := AxisParallelLine params) (β := Fq params)
    (f := fun ℓ t => ∑ f : AxisLinePolynomial params,
      (if f t = (MIPStarRE.LDT.Polynomial.restrictToAxisParallelLine params g ℓ) t ∧
          f.poly ≠ (MIPStarRE.LDT.Polynomial.restrictToAxisParallelLine params g ℓ).poly then
        (1 : ℝ)
      else 0) *
        V.ev (strategy.state.opTensor
          ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f) (G.outcome g)))]
  refine avgOver_congr _ _ _ fun ℓ => ?_
  rw [avgOver_sum]
  exact Finset.sum_congr rfl fun f _ => avgOver_mul_const _ _ _

/-- The incident-question collision residual is exactly the uniform line/parameter
seed expansion from `expansion.tex`, lines 286--288.

The proof reindexes the axis-parallel line-test distribution by `(ℓ,t)` with
sampled point `u = ℓ(t)`, then expands the `ProjMeas.postprocess` fiber for the
collision event `f(t) = g|_ℓ(t)` and `f ≠ g|_ℓ`. -/
theorem generalizeBCollisionResidual_eq_seedCollisionExpansion
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (g : MIPStarRE.LDT.Polynomial params) :
    generalizeBCollisionResidual params strategy strategy.state G g =
      generalizeBSeedCollisionExpansion params strategy strategy.state G g := by
  unfold generalizeBCollisionResidual generalizeBSeedCollisionExpansion
  rw [avgOver_axisParallelLineQuestionDistribution]
  exact avgOver_congr _ _ _ fun ℓt =>
    generalizeBCollisionSeed_integrand params strategy strategy.state G g ℓt.1 ℓt.2

/-- The explicit line/parameter collision expansion is bounded by `m*d/q`.

This proves the Schwartz--Zippel and normalization parts of the residual estimate
from `expansion.tex`, lines 286--288.  The preceding
`generalizeBCollisionResidual_eq_seedCollisionExpansion` theorem supplies the
incident-question/postprocess identity needed to apply this bound to the original
collision residual. -/
theorem generalizeBLineCollisionExpansion_le_error
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (g : MIPStarRE.LDT.Polynomial params) :
    generalizeBLineCollisionExpansion params strategy strategy.state G g ≤
      generalizeBError params := by
  have hδ_nonneg : 0 ≤ generalizeBError params := by
    dsimp [generalizeBError]
    positivity
  unfold generalizeBLineCollisionExpansion
  refine avgOver_uniform_le_const _ _ fun ℓ => ?_
  calc
    _ ≤ ∑ f : AxisLinePolynomial params, generalizeBError params *
          strategy.state.ev (strategy.state.opTensor
            ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f) (G.outcome g)) :=
        Finset.sum_le_sum fun f _ =>
          mul_le_mul_of_nonneg_right (generalizeBLineCollisionCoefficient_le params g ℓ f)
            (generalizeBLineCollisionTensorMass_nonneg params strategy G g ℓ f)
    _ = generalizeBError params * ∑ f : AxisLinePolynomial params,
          strategy.state.ev (strategy.state.opTensor
            ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f) (G.outcome g)) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ generalizeBError params :=
        mul_le_of_le_one_right hδ_nonneg
          (generalizeBLineCollisionTensorMass_sum_le_one params strategy G g ℓ)

/-- The uniform line/parameter seed collision expansion is bounded by `m*d/q`.

The proof first commutes the finite seed average into the coefficient-weighted
line expansion, then applies the Schwartz--Zippel coefficient bound and tensor
normalization estimate above. -/
theorem generalizeBSeedCollisionExpansion_le_error
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (g : MIPStarRE.LDT.Polynomial params) :
    generalizeBSeedCollisionExpansion params strategy strategy.state G g ≤
      generalizeBError params := by
  rw [generalizeBSeedCollisionExpansion_eq_lineCollisionExpansion]
  exact generalizeBLineCollisionExpansion_le_error params strategy G g

/-- The pointwise collision residual in `lem:generalize-b` is bounded by `m*d/q`.

This combines the incident-question reindexing with the seed/line expansion,
Schwartz--Zippel coefficient bound, and submeasurement-normalization estimate
from `expansion.tex`, lines 281--288. -/
theorem generalizeBCollisionResidual_le_error
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (g : MIPStarRE.LDT.Polynomial params) :
    generalizeBCollisionResidual params strategy strategy.state G g ≤
      generalizeBError params := by
  rw [generalizeBCollisionResidual_eq_seedCollisionExpansion]
  exact generalizeBSeedCollisionExpansion_le_error params strategy G g

/-- Pointwise Schwartz--Zippel bound for the strategy-state form of
`lem:generalize-b`.

This is the paper's estimate at `expansion.tex`, lines 281--288, after the
projective expansion converts the squared norm into the collision residual. -/
theorem generalizeBPointwiseSchwartzZippel
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (g : MIPStarRE.LDT.Polynomial params) :
    generalizeBDeviationAtPolynomial params strategy strategy.state G g ≤
      generalizeBError params := by
  rw [generalizeBDeviationAtPolynomial_eq_collisionResidual]
  exact generalizeBCollisionResidual_le_error params strategy G g

/-- `lem:generalize-b` for the strategy state, with the pointwise
Schwartz--Zippel estimate discharged internally.  The good-strategy hypothesis is
kept in the statement to match the paper context of `expansion.tex`,
lines 271--288, although the algebraic Schwartz--Zippel proof itself does not
use `ε`, `δ`, or `γ`. -/
theorem generalizeBFromSchwartzZippel
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (_eps _delta _gamma : ℝ)
    (_hgood : strategy.IsGood _eps _delta _gamma)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    GeneralizeBStatement params strategy strategy.state G :=
  generalizeB_of_pointwise params strategy G strategy.state
    (generalizeBPointwiseSchwartzZippel params strategy G)

end MIPRE.LIDT.Co.GlobalVariance

end

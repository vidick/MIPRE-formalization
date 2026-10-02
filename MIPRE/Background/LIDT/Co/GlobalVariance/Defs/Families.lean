/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
GlobalVariance/Defs/Families.lean, to the symmetric model of `planning/c6b-plan.md`; not a
vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.GlobalVariance.Defs.Operators
public import MIPRE.Background.LIDT.MIPStarRE.LDT.GlobalVariance.Defs.Families

@[expose] public section

/-!
# Section 8 global variance: operator families

The counterpart of `MIPRE/Background/LIDT/MIPStarRE/LDT/GlobalVariance/Defs/Families.lean` in
the port of `planning/c6b-plan.md` (milestone M6, section "Port conventions"): positivity and
normalization of the weighted operators `A ⊗ (G_g)^{1/2}`, the aggregated one-outcome families
of `lem:generalize-b`, `lem:local-variance-of-points` and `lem:global-variance-of-points`, and
the squared-norm deviations those lemmas control.

The weighted operators are joint operators `S.L A * S.R (G_g)^{1/2}` of a symmetric model `S`,
so the two lemmas that bound them for an arbitrary local `A` take the model as an explicit first
argument (`weightedPolynomialOperator_pos S params G g hA`), as M1's and M3's placement helpers
do. The positivity and the bound `≤ 1` are the keystone's `SymModel.opTensor_nonneg` and
`SymModel.opTensor_le_one`; the bound `(G_g)^{1/2} ≤ 1` is operator monotonicity of `CFC.sqrt`
(`CFC.sqrt_le_sqrt`) in place of the vendored spectral argument.

The deviations evaluate joint operators of the strategy's model against a second state `ψbi` on
the same space; they use only that state, so `ψbi` is a vector state `V : VecState K` (section
"Same-space and bipartite quantities" of the plan), and a caller passes the strategy's model
`strategy.state`, which coerces to it.

The four error terms at the end of the vendored file (`generalizeBError` and the three displayed
errors of `lem:local-variance-of-points` and `lem:global-variance-of-points`) are real-valued
functions of the parameters alone: this file imports the vendored file for them, and the ported
files of `GlobalVariance` name them through explicit `open MIPStarRE.LDT.GlobalVariance (…)`
lists.

## Not ported

- `generalizeBError`: classical, imported.
- `localVarianceTransportChainError`: classical, imported.
- `localVarianceOfPointsError`: classical, imported.
- `globalVarianceOfPointsError`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/expansion.tex`
- `blueprint/src/chapter/ch06_variance.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.GlobalVariance

open MIPStarRE.LDT (Parameters FieldModel Point Fq AxisParallelLine AxisLinePolynomial avgOver
  uniformDistribution)
open MIPStarRE.LDT.ExpansionHypercubeGraph (rerandomizeCoord independentPointPair)
open MIPStarRE.LDT.GlobalVariance (AxisParallelLineQuestion PointPairQuestion
  axisParallelLineQuestionDistribution polynomialDistribution)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- `CFC.sqrt (G.outcome g) ≤ 1` when `G` is a submeasurement: `CFC.sqrt` is operator monotone
and `CFC.sqrt 1 = 1`. -/
lemma cfc_sqrt_outcome_le_one (params : Parameters) [FieldModel params.q]
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) (g : MIPStarRE.LDT.Polynomial params) :
    CFC.sqrt (G.outcome g) ≤ 1 :=
  (CFC.sqrt_le_sqrt _ _ (G.outcome_le_one g)).trans_eq CFC.sqrt_one

/-- A weighted operator `A ⊗ (G_g)^{1/2}` of a positive local operator `A` is positive. -/
theorem weightedPolynomialOperator_pos (S : SymModel 𝔓 K) (params : Parameters)
    [FieldModel params.q]
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (g : MIPStarRE.LDT.Polynomial params)
    {A : 𝔓} (hA : 0 ≤ A) :
    0 ≤ S.opTensor A (polynomialWeightSqrtOperator params G g) :=
  S.opTensor_nonneg hA (CFC.sqrt_nonneg (G.outcome g))

/-- A weighted operator `A ⊗ (G_g)^{1/2}` of an effect `0 ≤ A ≤ 1` is at most `1`. -/
theorem weightedPolynomialOperator_le_one (S : SymModel 𝔓 K) (params : Parameters)
    [FieldModel params.q]
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (g : MIPStarRE.LDT.Polynomial params)
    {A : 𝔓}
    (hA_pos : 0 ≤ A) (hA_le_one : A ≤ 1) :
    S.opTensor A (polynomialWeightSqrtOperator params G g) ≤ 1 :=
  S.opTensor_le_one hA_pos hA_le_one (cfc_sqrt_outcome_le_one params G g)

/-- The weighted point operator `A^u_{g(u)} ⊗ (G_g)^{1/2}` is positive. -/
theorem weightedPointConditionedOperatorAtPolynomial_pos (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (g : MIPStarRE.LDT.Polynomial params) (u : Point params) :
    0 ≤ weightedPointConditionedOperatorAtPolynomial params strategy G g u :=
  weightedPolynomialOperator_pos strategy.state params G g
    ((strategy.pointMeasurement u).outcome_pos (g u))

/-- The weighted point operator `A^u_{g(u)} ⊗ (G_g)^{1/2}` is at most `1`. -/
theorem weightedPointConditionedOperatorAtPolynomial_le_one (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (g : MIPStarRE.LDT.Polynomial params) (u : Point params) :
    weightedPointConditionedOperatorAtPolynomial params strategy G g u ≤ 1 :=
  weightedPolynomialOperator_le_one strategy.state params G g
    ((strategy.pointMeasurement u).outcome_pos (g u))
    (Measurement.outcome_le_one (strategy.pointMeasurement u).toMeasurement (g u))

/-- The squared norm expression controlled by `lem:generalize-b` for a fixed `g`,
evaluated on the vector state `V` (the vendored bipartite state `ψbi`). -/
noncomputable def generalizeBDeviationAtPolynomial (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (V : VecState K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (g : MIPStarRE.LDT.Polynomial params) : ℝ :=
  avgOver (axisParallelLineQuestionDistribution params)
    (fun qu =>
      let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
               weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu
      V.ev (star D * D))

/-- The polynomial-averaged deviation controlled by `lem:generalize-b`. -/
noncomputable def generalizeBDeviation (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (V : VecState K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) : ℝ :=
  avgOver (polynomialDistribution params)
    (fun g => generalizeBDeviationAtPolynomial params strategy V G g)

/-- The line-collision residual obtained after expanding the projective line
measurement in `lem:generalize-b` and moving the polynomial weight from
`(G_g)^{1/2}` to `G_g`.  The remaining analytic step is to bound this
quantity by Schwartz--Zippel and the submeasurement property of `G`.

Paper origin: `references/ldt-paper/expansion.tex:273-288`
(`\label{lem:generalize-b}`). -/
noncomputable def generalizeBCollisionResidual (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (V : VecState K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (g : MIPStarRE.LDT.Polynomial params) : ℝ :=
  avgOver (axisParallelLineQuestionDistribution params)
    (fun qu =>
      V.ev (strategy.state.opTensor
        (generalizeBCollisionOperatorAtPolynomial params strategy g qu)
        (G.outcome g)))

/-- Uniform line/parameter seed expansion of the `lem:generalize-b` collision residual.

This is the paper's `expansion.tex`, lines 286--288, after replacing an
incident line question `(ℓ,u)` by a line `ℓ` and affine parameter `t` with
`u = ℓ(t)`, but before commuting the finite average over `t` past the finite
sum over line answers `f`.  The vendored file proves the equality from the original collision
residual to this seed expansion in `generalizeBCollisionResidual_eq_seedCollisionExpansion`. -/
noncomputable def generalizeBSeedCollisionExpansion (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (V : VecState K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (g : MIPStarRE.LDT.Polynomial params) : ℝ :=
  avgOver (uniformDistribution (AxisParallelLine params × Fq params))
    (fun ℓt =>
      ∑ f : AxisLinePolynomial params,
        (if f ℓt.2 = (MIPStarRE.LDT.Polynomial.restrictToAxisParallelLine params g ℓt.1) ℓt.2 ∧
            f.poly ≠
              (MIPStarRE.LDT.Polynomial.restrictToAxisParallelLine params g ℓt.1).poly then
          (1 : ℝ)
        else 0) *
          V.ev (strategy.state.opTensor
            ((strategy.axisParallelMeasurement ℓt.1).toSubMeas.outcome f)
            (G.outcome g)))

/-- Explicit line/parameter expansion of the `lem:generalize-b` collision residual.

This is the commuted finite-sum form of `generalizeBSeedCollisionExpansion`: for
fixed `ℓ` and `f`, the coefficient is the fraction of parameters where the line
answer `f` both collides with `g|_ℓ` at `t` and is not equal to `g|_ℓ`. -/
noncomputable def generalizeBLineCollisionExpansion (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (V : VecState K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (g : MIPStarRE.LDT.Polynomial params) : ℝ :=
  avgOver (uniformDistribution (AxisParallelLine params))
    (fun ℓ =>
      ∑ f : AxisLinePolynomial params,
        avgOver (uniformDistribution (Fq params))
          (fun t =>
            if f t = (MIPStarRE.LDT.Polynomial.restrictToAxisParallelLine params g ℓ) t ∧
                f.poly ≠ (MIPStarRE.LDT.Polynomial.restrictToAxisParallelLine params g ℓ).poly then
              (1 : ℝ)
            else 0) *
          V.ev (strategy.state.opTensor
            ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f)
            (G.outcome g)))

/-- Aggregated family for the left-hand side of `lem:generalize-b`: the uniform polynomial
average of `B^ℓ_{[f(u)=g(u)]} ⊗ (G_g)^{1/2}`, as a one-outcome family of joint operators. -/
noncomputable def generalizeBLeftFamily (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    IdxSubMeas (AxisParallelLineQuestion params) Unit (K →L[ℂ] K) :=
  fun qu =>
    let F : MIPStarRE.LDT.Polynomial params → K →L[ℂ] K :=
      fun g => weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
    SubMeas.singleOutcome
      (averageOperatorOverDistribution
        (uniformDistribution (MIPStarRE.LDT.Polynomial params)) F)
      (averageOperatorOverDistribution_nonneg
        (uniformDistribution (MIPStarRE.LDT.Polynomial params)) F
        (fun g => weightedPolynomialOperator_pos strategy.state params G g
          ((generalizeBLeftEventSubMeasAtPolynomial params strategy g qu).outcome_pos (some ()))))
      (averageOperatorOverDistribution_uniform_le_one F
        (fun g => weightedPolynomialOperator_le_one strategy.state params G g
          ((generalizeBLeftEventSubMeasAtPolynomial params strategy g qu).outcome_pos (some ()))
          (SubMeas.outcome_le_one
            (generalizeBLeftEventSubMeasAtPolynomial params strategy g qu) (some ()))))

/-- Aggregated family for the right-hand side of `lem:generalize-b`: the uniform polynomial
average of `B^ℓ_{[f = g|_ℓ]} ⊗ (G_g)^{1/2}`, as a one-outcome family of joint operators. -/
noncomputable def generalizeBRightFamily (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    IdxSubMeas (AxisParallelLineQuestion params) Unit (K →L[ℂ] K) :=
  fun qu =>
    let F : MIPStarRE.LDT.Polynomial params → K →L[ℂ] K :=
      fun g => weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu
    SubMeas.singleOutcome
      (averageOperatorOverDistribution
        (uniformDistribution (MIPStarRE.LDT.Polynomial params)) F)
      (averageOperatorOverDistribution_nonneg
        (uniformDistribution (MIPStarRE.LDT.Polynomial params)) F
        (fun g => weightedPolynomialOperator_pos strategy.state params G g
          ((generalizeBRightEventSubMeasAtPolynomial params strategy g qu).outcome_pos
            (some ()))))
      (averageOperatorOverDistribution_uniform_le_one F
        (fun g => weightedPolynomialOperator_le_one strategy.state params G g
          ((generalizeBRightEventSubMeasAtPolynomial params strategy g qu).outcome_pos
            (some ()))
          (SubMeas.outcome_le_one
            (generalizeBRightEventSubMeasAtPolynomial params strategy g qu) (some ()))))

/-- Aggregated family for `A^u_[g(u)] ⊗ (G_g)^{1/2}`, the uniform polynomial average at the
first point of a pair, as a one-outcome family of joint operators. -/
noncomputable def localVarianceLeftFamily (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    IdxSubMeas (PointPairQuestion params) Unit (K →L[ℂ] K) :=
  fun uv =>
    let F : MIPStarRE.LDT.Polynomial params → K →L[ℂ] K :=
      fun g => weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1
    SubMeas.singleOutcome
      (averageOperatorOverDistribution
        (uniformDistribution (MIPStarRE.LDT.Polynomial params)) F)
      (averageOperatorOverDistribution_nonneg
        (uniformDistribution (MIPStarRE.LDT.Polynomial params)) F
        (fun g => weightedPointConditionedOperatorAtPolynomial_pos params strategy G g uv.1))
      (averageOperatorOverDistribution_uniform_le_one F
        (fun g => weightedPointConditionedOperatorAtPolynomial_le_one params strategy G g uv.1))

/-- Aggregated family for `A^v_[g(v)] ⊗ (G_g)^{1/2}`, the uniform polynomial average at the
second point of a pair, as a one-outcome family of joint operators. -/
noncomputable def localVarianceRightFamily (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    IdxSubMeas (PointPairQuestion params) Unit (K →L[ℂ] K) :=
  fun uv =>
    let F : MIPStarRE.LDT.Polynomial params → K →L[ℂ] K :=
      fun g => weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2
    SubMeas.singleOutcome
      (averageOperatorOverDistribution
        (uniformDistribution (MIPStarRE.LDT.Polynomial params)) F)
      (averageOperatorOverDistribution_nonneg
        (uniformDistribution (MIPStarRE.LDT.Polynomial params)) F
        (fun g => weightedPointConditionedOperatorAtPolynomial_pos params strategy G g uv.2))
      (averageOperatorOverDistribution_uniform_le_one F
        (fun g => weightedPointConditionedOperatorAtPolynomial_le_one params strategy G g uv.2))

/-- The same weighted operator on the first independently sampled point. -/
noncomputable def globalVarianceLeftFamily (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    IdxSubMeas (PointPairQuestion params) Unit (K →L[ℂ] K) :=
  localVarianceLeftFamily params strategy G

/-- The same weighted operator on the second independently sampled point. -/
noncomputable def globalVarianceRightFamily (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    IdxSubMeas (PointPairQuestion params) Unit (K →L[ℂ] K) :=
  localVarianceRightFamily params strategy G

/-- The edgewise squared norm expression in `lem:local-variance-of-points`,
evaluated on the vector state `V` (the vendored bipartite state `ψbi`). -/
noncomputable def localVarianceDeviationAtPolynomial (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (V : VecState K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (g : MIPStarRE.LDT.Polynomial params) : ℝ :=
  avgOver (rerandomizeCoord params)
    (fun uv =>
      let D := weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1 -
               weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2
      V.ev (star D * D))

/-- The independently sampled squared norm expression in `lem:global-variance-of-points`,
evaluated on the vector state `V` (the vendored bipartite state `ψbi`). -/
noncomputable def globalVarianceDeviationAtPolynomial (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (V : VecState K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (g : MIPStarRE.LDT.Polynomial params) : ℝ :=
  avgOver (independentPointPair params)
    (fun uv =>
      let D := weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1 -
               weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2
      V.ev (star D * D))

/-- The polynomial-averaged local squared norm expression. -/
noncomputable def localVarianceDeviation (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (V : VecState K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) : ℝ :=
  avgOver (polynomialDistribution params)
    (fun g => localVarianceDeviationAtPolynomial params strategy V G g)

end MIPRE.LIDT.Co.GlobalVariance

end

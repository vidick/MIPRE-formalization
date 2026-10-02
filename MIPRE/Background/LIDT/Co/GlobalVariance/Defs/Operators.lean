/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
GlobalVariance/Defs/Operators.lean, to the symmetric model of `planning/c6b-plan.md`; not a
vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.GlobalVariance.Defs.Core
public import MIPRE.Background.LIDT.Co.Test.StrategyCore

@[expose] public section

/-!
# Section 8 global variance: weighted operators and variance families

The counterpart of `MIPRE/Background/LIDT/MIPStarRE/LDT/GlobalVariance/Defs/Operators.lean` in
the port of `planning/c6b-plan.md` (milestone M6, section "Port conventions"): the weight
`(G_g)^{1/2}` of a polynomial submeasurement, the point and axis-line event operators of
`lem:local-variance-of-points` and `lem:generalize-b`, their weighted bipartite forms
`A ⊗ (G_g)^{1/2}`, and the point-conditioned local and global variances.

Local operators live in the local algebra `𝔓` of a symmetric strategy
`strategy : SymStrat params 𝔓 K`, and joint ones in `K →L[ℂ] K`: `opTensor A B` is
`strategy.state.opTensor A B = S.L A * S.R B` and `rightTensor B` is `strategy.state.R B`. The
square root `(G_g)^{1/2}` is `CFC.sqrt` in the C⋆-algebra `𝔓`, as the vendored file takes it in
the matrix algebra.

**The weighted state.** The vendored point-conditioned variances evaluate the left-placed family
`u ↦ A^u_{g(u)} ⊗ 1` on the weighted state `ρ_g = W ρ Wᴴ`, `W = 1 ⊗ (G_g)^{1/2}`, which is not
normalized (`weightedPolynomialState`). A vector state has no density, and the weighted vector
`W Ψ` is not a unit vector, so it is not a `VecState`. Since `ev_{WρWᴴ}(X) = ev_ρ(Wᴴ X W)` and
`Wᴴ (A_u - A_v)ᴴ (A_u - A_v) W = ((A_u - A_v) W)ᴴ ((A_u - A_v) W)`, with `(A_u ⊗ 1) W =
A_u ⊗ (G_g)^{1/2}`, the vendored variance on `ρ_g` is the variance on the strategy's own state of
the weighted family `u ↦ A^u_{g(u)} ⊗ (G_g)^{1/2}` (`weightedPointConditionedOperatorAtPolynomial`).
So `pointConditionedLocalVarianceAtPolynomial` and `pointConditionedGlobalVarianceAtPolynomial`
are defined that way, as the plan's note "For M6" prescribes (`Co/ExpansionHypercubeGraph/
Theorems/Results.lean`, module docstring), and `localToGlobal` applies to them unchanged.

## Not ported

- `weightedPolynomialState`: a vector state has no density, and the weighted vector
  `(1 ⊗ (G_g)^{1/2}) Ψ` is not normalized; the variances on it are the variances of the weighted
  family on the strategy's state (`pointConditionedLocalVarianceAtPolynomial`,
  `pointConditionedGlobalVarianceAtPolynomial`).

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/expansion.tex`
- `blueprint/src/chapter/ch06_variance.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.GlobalVariance

open MIPStarRE.LDT (Parameters FieldModel Point Fq AxisLinePolynomial avgOver)
open MIPStarRE.LDT.GlobalVariance (AxisParallelLineQuestion axisParallelLineQuestionParameter
  polynomialDistribution)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ## Weighted operators and variance families -/

/-- The operator `(G_g)^{1/2}` used throughout `expansion.tex`.
Uses `CFC.sqrt` (continuous functional calculus) to compute the square root of the positive
operator `G.outcome g` in the local algebra. -/
noncomputable def polynomialWeightSqrtOperator (params : Parameters) [FieldModel params.q]
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (g : MIPStarRE.LDT.Polynomial params) : 𝔓 :=
  CFC.sqrt (G.outcome g)

/-- The concrete operator `A^u_{g(u)}` for a fixed polynomial `g`. -/
noncomputable def pointConditionedOutcomeOperatorAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (g : MIPStarRE.LDT.Polynomial params) (u : Point params) : 𝔓 :=
  (strategy.pointMeasurement u).toSubMeas.outcome (g u)

/-- The two-outcome point event selecting the answer `g(u)`.

This is the submeasurement form of the point operator used in the first and last
steps of `lem:local-variance-of-points` (`expansion.tex`, lines 305 and 311).
Its `some ()` outcome is exactly `A^u_{g(u)}`; the `none` outcome is the
complementary point-answer mass. -/
noncomputable def pointConditionedEventSubMeasAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (g : MIPStarRE.LDT.Polynomial params) (u : Point params) : SubMeas (Option Unit) 𝔓 :=
  postprocess ((strategy.pointMeasurement u).toSubMeas)
    (fun a : Fq params => if a = g u then some () else none)

/-- The selected outcome of `pointConditionedEventSubMeasAtPolynomial` is
`A^u_{g(u)}`. -/
@[simp] lemma pointConditionedEventSubMeasAtPolynomial_some (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (g : MIPStarRE.LDT.Polynomial params) (u : Point params) :
    (pointConditionedEventSubMeasAtPolynomial params strategy g u).outcome (some ()) =
      pointConditionedOutcomeOperatorAtPolynomial params strategy g u := by
  classical
  unfold pointConditionedEventSubMeasAtPolynomial pointConditionedOutcomeOperatorAtPolynomial
  simp only [postprocess]
  refine Finset.sum_eq_single (g u) ?_ ?_
  · intro a ha hne
    simp [hne] at ha
  · simp

/-- The paper's weighted operator `A^u_{g(u)} ⊗ (G_g)^{1/2}`, the joint operator
`S.L (A^u_{g(u)}) * S.R ((G_g)^{1/2})` of the strategy's model. -/
noncomputable def weightedPointConditionedOperatorAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (g : MIPStarRE.LDT.Polynomial params) (u : Point params) : K →L[ℂ] K :=
  strategy.state.opTensor
    (pointConditionedOutcomeOperatorAtPolynomial params strategy g u)
    (polynomialWeightSqrtOperator params G g)

/-- The right-register intermediate `I ⊗ (G_g)^{1/2} A^u_{g(u)}`
from the first and last self-consistency moves of
`lem:local-variance-of-points` (`expansion.tex`, lines 306 and 310). -/
noncomputable def weightedPointConditionedRightOperatorAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (g : MIPStarRE.LDT.Polynomial params) (u : Point params) : K →L[ℂ] K :=
  strategy.state.R
    (polynomialWeightSqrtOperator params G g *
      pointConditionedOutcomeOperatorAtPolynomial params strategy g u)

/-- The local variance of `A(g)` on the weighted state `|ψ_g⟩ = (I ⊗ √G_g)|ψ⟩`.

The vendored definition evaluates the left-placed family `u ↦ A^u_{g(u)} ⊗ 1` on the
unnormalized weighted state; here it is, equivalently, the local variance of the weighted family
`u ↦ A^u_{g(u)} ⊗ (G_g)^{1/2}` on the strategy's state (module docstring). -/
noncomputable def pointConditionedLocalVarianceAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (g : MIPStarRE.LDT.Polynomial params) : ℝ :=
  ExpansionHypercubeGraph.localVariance params
    (fun u => weightedPointConditionedOperatorAtPolynomial params strategy G g u)
    strategy.state.toVecState

/-- The global variance of `A(g)` on the weighted state `|ψ_g⟩ = (I ⊗ √G_g)|ψ⟩`.

As for `pointConditionedLocalVarianceAtPolynomial`, it is the global variance of the weighted
family `u ↦ A^u_{g(u)} ⊗ (G_g)^{1/2}` on the strategy's state (module docstring). -/
noncomputable def pointConditionedGlobalVarianceAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (g : MIPStarRE.LDT.Polynomial params) : ℝ :=
  ExpansionHypercubeGraph.globalVariance params
    (fun u => weightedPointConditionedOperatorAtPolynomial params strategy G g u)
    strategy.state.toVecState

/-- The polynomial-averaged local variance of the conditioned points family. -/
noncomputable def pointConditionedLocalVariance (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) : ℝ :=
  avgOver (polynomialDistribution params)
    (fun g => pointConditionedLocalVarianceAtPolynomial params strategy G g)

/-- The polynomial-averaged global variance of the conditioned points family. -/
noncomputable def pointConditionedGlobalVariance (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) : ℝ :=
  avgOver (polynomialDistribution params)
    (fun g => pointConditionedGlobalVarianceAtPolynomial params strategy G g)

/-- The `Option Unit` event submeasurement selecting axis-line answers that
match `g(u)` at the queried point `u` on the left side of `lem:generalize-b`. -/
noncomputable def generalizeBLeftEventSubMeasAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (g : MIPStarRE.LDT.Polynomial params)
    (qu : AxisParallelLineQuestion params) : SubMeas (Option Unit) 𝔓 :=
  let (ℓ, u) := qu
  postprocess
    ((strategy.axisParallelMeasurement ℓ).toSubMeas)
    (fun f : AxisLinePolynomial params =>
      if f (axisParallelLineQuestionParameter qu) = g u then
        some ()
      else
        none)

/-- The `Option Unit` event submeasurement selecting axis-line answers that
match the restriction of `g` to `ℓ` on the right side of `lem:generalize-b`. -/
noncomputable def generalizeBRightEventSubMeasAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (g : MIPStarRE.LDT.Polynomial params)
    (qu : AxisParallelLineQuestion params) : SubMeas (Option Unit) 𝔓 :=
  let ℓ := qu.1
  let gRestricted := MIPStarRE.LDT.Polynomial.restrictToAxisParallelLine params g ℓ
  postprocess
    ((strategy.axisParallelMeasurement ℓ).toSubMeas)
    (fun f : AxisLinePolynomial params =>
      if f.poly = gRestricted.poly then
        some ()
      else
        none)

/-- The residual projective `Option Unit` event from the proof of
`lem:generalize-b`: axis-line answers that collide with `g` at the sampled point
`u`, but are not the restricted polynomial `g|_ℓ`.  After the
projective-measurement expansion, the squared difference is controlled by this
collision event. -/
noncomputable def generalizeBCollisionEventProjMeasAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (g : MIPStarRE.LDT.Polynomial params)
    (qu : AxisParallelLineQuestion params) : ProjMeas (Option Unit) 𝔓 :=
  let (ℓ, u) := qu
  let gRestricted := MIPStarRE.LDT.Polynomial.restrictToAxisParallelLine params g ℓ
  ProjMeas.postprocess (strategy.axisParallelMeasurement ℓ)
    (fun f : AxisLinePolynomial params =>
      if f (axisParallelLineQuestionParameter qu) = g u ∧ f.poly ≠ gRestricted.poly then
        some ()
      else
        none)

/-- The residual event above, forgetting projectivity to a submeasurement.  Keeping
this definition as the `toSubMeas` of `generalizeBCollisionEventProjMeasAtPolynomial`
prevents the projective and submeasurement views from drifting apart. -/
noncomputable def generalizeBCollisionEventSubMeasAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (g : MIPStarRE.LDT.Polynomial params)
    (qu : AxisParallelLineQuestion params) : SubMeas (Option Unit) 𝔓 :=
  (generalizeBCollisionEventProjMeasAtPolynomial params strategy g qu).toSubMeas

/-- The event operator for the residual line-collision event in `lem:generalize-b`. -/
noncomputable def generalizeBCollisionOperatorAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (g : MIPStarRE.LDT.Polynomial params)
    (qu : AxisParallelLineQuestion params) : 𝔓 :=
  (generalizeBCollisionEventSubMeasAtPolynomial params strategy g qu).outcome (some ())

/-- The event operator `B^ℓ_{[f(u)=g(u)]}`: sum of axis-line measurement
outcomes `f` that evaluate to the same value as `g` at point `u`. -/
noncomputable def generalizeBLeftOperatorAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (g : MIPStarRE.LDT.Polynomial params)
    (qu : AxisParallelLineQuestion params) : 𝔓 :=
  (generalizeBLeftEventSubMeasAtPolynomial params strategy g qu).outcome (some ())

/-- The event operator `B^ℓ_{[f = g|_ℓ]}`: sum of axis-line measurement
outcomes `f` that agree with `g` restricted to line `ℓ`. -/
noncomputable def generalizeBRightOperatorAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (g : MIPStarRE.LDT.Polynomial params)
    (qu : AxisParallelLineQuestion params) : 𝔓 :=
  (generalizeBRightEventSubMeasAtPolynomial params strategy g qu).outcome (some ())

/-- The weighted left operator `B^ℓ_{[f(u)=g(u)]} ⊗ (G_g)^{1/2}` in `lem:generalize-b`,
a joint operator of the strategy's model. -/
noncomputable def weightedGeneralizeBLeftOperatorAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (g : MIPStarRE.LDT.Polynomial params)
    (qu : AxisParallelLineQuestion params) : K →L[ℂ] K :=
  strategy.state.opTensor
    (generalizeBLeftOperatorAtPolynomial params strategy g qu)
    (polynomialWeightSqrtOperator params G g)

/-- The weighted right operator `B^ℓ_{[f = g|_ℓ]} ⊗ (G_g)^{1/2}` in `lem:generalize-b`,
a joint operator of the strategy's model. -/
noncomputable def weightedGeneralizeBRightOperatorAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (g : MIPStarRE.LDT.Polynomial params)
    (qu : AxisParallelLineQuestion params) : K →L[ℂ] K :=
  strategy.state.opTensor
    (generalizeBRightOperatorAtPolynomial params strategy g qu)
    (polynomialWeightSqrtOperator params G g)

end MIPRE.LIDT.Co.GlobalVariance

end

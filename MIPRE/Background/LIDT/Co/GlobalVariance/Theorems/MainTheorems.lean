/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
GlobalVariance/Theorems/MainTheorems.lean, to the symmetric model of `planning/c6b-plan.md`; not
a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.GlobalVariance.Theorems.TransportChain.SumForm

@[expose] public section

/-!
# Main variance theorem reductions

The counterpart of `MIPRE/Background/LIDT/MIPStarRE/LDT/GlobalVariance/Theorems/MainTheorems.lean`
in the port of `planning/c6b-plan.md` (milestone M6, section "Port conventions"): the high-level
reductions for `lem:local-variance-of-points`, `lem:global-variance-of-points` and their
polynomial-sum forms, which combine the algebraic identities, the local-to-global transfer and the
six-step transport chain of the preceding modules into the statement records of
`Theorems/Statements.lean`, and the paper-facing `globalVarianceOfPoints`.

The vendored second state `ψbi` of the records is the strategy's model `strategy.state`, which
coerces to a `VecState K`. No statement here carries a swap or normalization hypothesis, and the
file-wide `backward.isDefEq.respectTransparency false` of the vendored file is not needed.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/expansion.tex`, lines 292--353
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.GlobalVariance

open MIPStarRE.LDT (Parameters FieldModel)
open MIPStarRE.LDT.ExpansionHypercubeGraph (rerandomizeCoord independentPointPair)
open MIPStarRE.LDT.GlobalVariance (localVarianceOfPointsError globalVarianceOfPointsError
  localVarianceTransportChainError globalVarianceOfPoints_bound_of_local
  avgOver_polynomialDistribution_le_of_pointwise)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ## Strategy-state reductions -/

/-- Strict reduction for `lem:local-variance-of-points` on the strategy state.

The local-variance bound is not a separate hypothesis: it is derived from the edgewise weighted
squared-norm estimate through
`localVarianceDeviationAtPolynomial_eq_two_pointConditionedLocalVarianceAtPolynomial`. The
remaining analytic input is exactly the paper's six-step edge transport bound. -/
theorem localVarianceOfPointsFromEdgeDeviation
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hedge :
      ∀ g : MIPStarRE.LDT.Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state G g ≤
          localVarianceOfPointsError params eps delta) :
    LocalVarianceOfPointsStatement params strategy strategy.state G eps delta :=
  have hvar := fun g => pointConditionedLocalVarianceAtPolynomial_le_of_deviation
    params strategy G (hedge g)
  { aggregateEdgeComparison :=
      sddRel_unit_family_of_pointwise strategy.state.toVecState (rerandomizeCoord params)
        (localVarianceLeftFamily params strategy G) (localVarianceRightFamily params strategy G)
        (fun uv g => weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1)
        (fun uv g => weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2)
        (fun _ => rfl) (fun _ => rfl) _ hedge
    pointwiseEdgeNormBound := hedge
    pointwiseLocalVarianceBound := hvar
    averagedLocalVarianceBound :=
      avgOver_polynomialDistribution_le_of_pointwise params _ _ hvar }

/-- Reduction for `lem:global-variance-of-points` on the strategy state.

The independent-points norm bound follows from the local edge norm estimate by
`lem:local-to-global` on the weighted family and the exact norm/variance identities. The remaining
analytic input is the local edge transport estimate of `lem:local-variance-of-points`. -/
theorem globalVarianceOfPointsFromLocalDeviation
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hlocalDev :
      ∀ g : MIPStarRE.LDT.Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state G g ≤
          localVarianceOfPointsError params eps delta) :
    GlobalVarianceOfPointsStatement params strategy strategy.state G eps delta :=
  have hglobalNorm :=
    globalVarianceOfPoints_bound_of_local params eps delta _ _
      (globalVarianceDeviationAtPolynomial_le_m_localVarianceDeviationAtPolynomial
        params strategy G)
      hlocalDev
  have hglobalVariance :=
    globalVarianceOfPoints_bound_of_local params eps delta _ _
      (pointConditionedExpansionTransfer params strategy G)
      (localVarianceOfPointsFromEdgeDeviation params strategy eps delta G
        hlocalDev).pointwiseLocalVarianceBound
  { aggregateGlobalComparison :=
      sddRel_unit_family_of_pointwise strategy.state.toVecState (independentPointPair params)
        (globalVarianceLeftFamily params strategy G)
        (globalVarianceRightFamily params strategy G)
        (fun uv g => weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1)
        (fun uv g => weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2)
        (fun _ => rfl) (fun _ => rfl) _ hglobalNorm
    pointwiseGlobalNormBound := hglobalNorm
    pointwiseExpansionTransfer := pointConditionedExpansionTransfer params strategy G
    pointwiseGlobalVarianceBound := hglobalVariance
    averagedGlobalVarianceBound :=
      avgOver_polynomialDistribution_le_of_pointwise params _ _ hglobalVariance }

/-- Sum-level local-to-global transfer for the polynomial-indexed squared-norm form of
`lem:global-variance-of-points`: the independent-points deviation summed over all polynomials is
at most `m` times the edge-deviation sum, the unnormalized analogue of
`globalVarianceDeviationAtPolynomial_le_m_localVarianceDeviationAtPolynomial`. -/
theorem globalVarianceDeviation_sum_le_m_mul_localVarianceDeviation_sum
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    (∑ g : MIPStarRE.LDT.Polynomial params,
      globalVarianceDeviationAtPolynomial params strategy strategy.state G g) ≤
      (params.m : ℝ) *
        ∑ g : MIPStarRE.LDT.Polynomial params,
          localVarianceDeviationAtPolynomial params strategy strategy.state G g :=
  (Finset.sum_le_sum fun g _ =>
      globalVarianceDeviationAtPolynomial_le_m_localVarianceDeviationAtPolynomial
        params strategy G g).trans_eq
    (Finset.mul_sum _ _ _).symm

/-- A polynomial-sum local-variance bound implies the corresponding sum-form global-variance
bound with the paper's `24m(ε + δ + md/q)` error term.

The hypothesis `hlocal` is the paper's `eq:equivalent-local-variance` (`expansion.tex`, lines
317--321); the conclusion is the sum-form squared-norm bound underlying
`eq:global-variance-of-points-equation` (`expansion.tex`, lines 325--353). -/
theorem globalVarianceDeviation_sum_le_of_localVarianceDeviation_sum_le
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hlocal :
      (∑ g : MIPStarRE.LDT.Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state G g) ≤
        localVarianceOfPointsError params eps delta) :
    (∑ g : MIPStarRE.LDT.Polynomial params,
      globalVarianceDeviationAtPolynomial params strategy strategy.state G g) ≤
      globalVarianceOfPointsError params eps delta := by
  refine (globalVarianceDeviation_sum_le_m_mul_localVarianceDeviation_sum params strategy G).trans
    ((mul_le_mul_of_nonneg_left hlocal (Nat.cast_nonneg _)).trans_eq ?_)
  simp only [globalVarianceOfPointsError, localVarianceOfPointsError]
  ring

/-- Strategy-state reduction for `lem:local-variance-of-points` from the post-triangle six-step
transport-chain bound `2δ + 2ε + md/q + md/q + 2ε + 2δ` (`prop:triangle-inequality-for-approx_delta`
with `k = 6`), absorbed into the public `24(ε + δ + md/q)` error. -/
theorem localVarianceOfPointsFromTransportChainBound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hchain :
      ∀ g : MIPStarRE.LDT.Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state G g ≤
          localVarianceTransportChainError params eps delta) :
    LocalVarianceOfPointsStatement params strategy strategy.state G eps delta :=
  localVarianceOfPointsFromEdgeDeviation params strategy eps delta G fun g =>
    (hchain g).trans
      (localVarianceTransportChainError_le_localVarianceOfPointsError params strategy hgood)

/-- Strategy-state global-variance reduction from the post-triangle six-step local-variance
transport-chain bound. -/
theorem globalVarianceOfPointsFromTransportChainBound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hchain :
      ∀ g : MIPStarRE.LDT.Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state G g ≤
          localVarianceTransportChainError params eps delta) :
    GlobalVarianceOfPointsStatement params strategy strategy.state G eps delta :=
  globalVarianceOfPointsFromLocalDeviation params strategy eps delta G fun g =>
    (hchain g).trans
      (localVarianceTransportChainError_le_localVarianceOfPointsError params strategy hgood)

/-- Paper origin: `references/ldt-paper/expansion.tex:325-353`
(`\label{lem:global-variance-of-points}`).

The global variance lemma for the point measurements: for a good strategy and a polynomial
submeasurement `G`, the independent-points comparison holds with error `24m(ε + δ + md/q)`. The
local and global variance estimates are conclusions, not hypotheses. -/
theorem globalVarianceOfPoints
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    GlobalVarianceOfPointsStatement params strategy strategy.state G eps delta :=
  globalVarianceOfPointsFromTransportChainBound params strategy eps delta gamma hgood G
    (localVarianceTransportChainBound params strategy eps delta gamma hgood G)

end MIPRE.LIDT.Co.GlobalVariance

end

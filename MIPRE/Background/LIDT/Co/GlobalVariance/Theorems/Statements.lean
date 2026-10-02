/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
GlobalVariance/Theorems/Statements.lean, to the symmetric model of `planning/c6b-plan.md`; not a
vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.GlobalVariance.Defs.Families

@[expose] public section

/-!
# Section 8 global variance: statement structures

The counterpart of `MIPRE/Background/LIDT/MIPStarRE/LDT/GlobalVariance/Theorems/Statements.lean`
in the port of `planning/c6b-plan.md` (milestone M6, section "Port conventions"): the conclusion
structures of `lem:generalize-b`, `lem:local-variance-of-points` and
`lem:global-variance-of-points`.

The vendored structures take a strategy and a second bipartite state `ψbi`, on which the
aggregated families are compared and the deviations evaluated. Both uses are same-space (section
"Same-space and bipartite quantities" of the plan), so `ψbi` is a vector state `V : VecState K`
in the same argument position, as in `Defs/Families.lean`; a caller passes the strategy's model
`strategy.state`, which coerces to it. `SDDRel ψbi` is `V.SDDRel`. The point-conditioned
variances do not mention `ψbi` and are those of `Defs/Operators.lean`, the variances of the
weighted family on the strategy's own state.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/expansion.tex`
- `blueprint/src/chapter/ch06_variance.tex`
-/

namespace MIPRE.LIDT.Co.GlobalVariance

open MIPStarRE.LDT (Parameters FieldModel)
open MIPStarRE.LDT.ExpansionHypercubeGraph (rerandomizeCoord independentPointPair)
open MIPStarRE.LDT.GlobalVariance (axisParallelLineQuestionDistribution generalizeBError
  localVarianceOfPointsError globalVarianceOfPointsError)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ## Statement structures -/

/-- Paper origin: `references/ldt-paper/expansion.tex:273-291`
(`\label{lem:generalize-b}`).

Conclusion statement for `lem:generalize-b`.
`V` is the vendored bipartite state `ψbi` (passed as `strategy.state` by callers). -/
structure GeneralizeBStatement (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K) (V : VecState K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) : Prop where
  /-- The aggregated left and right `generalize-b` families are close in `SDDRel`. -/
  aggregateFamilyComparison :
    V.SDDRel
      (axisParallelLineQuestionDistribution params)
      (generalizeBLeftFamily params strategy G)
      (generalizeBRightFamily params strategy G)
      (generalizeBError params)
  /-- Each fixed polynomial satisfies the claimed deviation bound. -/
  pointwiseNormBound :
    ∀ g : MIPStarRE.LDT.Polynomial params,
      generalizeBDeviationAtPolynomial params strategy V G g ≤ generalizeBError params
  /-- The polynomial average of the deviations satisfies the same bound. -/
  averagedNormBound :
    generalizeBDeviation params strategy V G ≤ generalizeBError params

/-- Paper origin: `references/ldt-paper/expansion.tex:292-324`
(`\label{lem:local-variance-of-points}`).

Conclusion statement for `lem:local-variance-of-points`. -/
structure LocalVarianceOfPointsStatement (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K) (V : VecState K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) (eps delta : ℝ) : Prop where
  /-- The aggregated edge families are close in `SDDRel`. -/
  aggregateEdgeComparison :
    V.SDDRel
      (rerandomizeCoord params)
      (localVarianceLeftFamily params strategy G)
      (localVarianceRightFamily params strategy G)
      (localVarianceOfPointsError params eps delta)
  /-- Each fixed polynomial satisfies the edgewise squared-difference bound. -/
  pointwiseEdgeNormBound :
    ∀ g : MIPStarRE.LDT.Polynomial params,
      localVarianceDeviationAtPolynomial params strategy V G g ≤
        localVarianceOfPointsError params eps delta
  /-- Each fixed polynomial satisfies the local-variance bound. -/
  pointwiseLocalVarianceBound :
    ∀ g : MIPStarRE.LDT.Polynomial params,
      pointConditionedLocalVarianceAtPolynomial params strategy G g ≤
        localVarianceOfPointsError params eps delta
  /-- The polynomial average of the local variances satisfies the same bound. -/
  averagedLocalVarianceBound :
    pointConditionedLocalVariance params strategy G ≤
      localVarianceOfPointsError params eps delta

/-- Paper origin: `references/ldt-paper/expansion.tex:325-353`
(`\label{lem:global-variance-of-points}`).

Conclusion statement for `lem:global-variance-of-points`. -/
structure GlobalVarianceOfPointsStatement (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K) (V : VecState K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) (eps delta : ℝ) : Prop where
  /-- The aggregated global families are close in `SDDRel`. -/
  aggregateGlobalComparison :
    V.SDDRel
      (independentPointPair params)
      (globalVarianceLeftFamily params strategy G)
      (globalVarianceRightFamily params strategy G)
      (globalVarianceOfPointsError params eps delta)
  /-- Each fixed polynomial satisfies the global squared-difference bound. -/
  pointwiseGlobalNormBound :
    ∀ g : MIPStarRE.LDT.Polynomial params,
      globalVarianceDeviationAtPolynomial params strategy V G g ≤
        globalVarianceOfPointsError params eps delta
  /-- Each fixed polynomial satisfies the local-to-global transfer estimate. -/
  pointwiseExpansionTransfer :
    ∀ g : MIPStarRE.LDT.Polynomial params,
      pointConditionedGlobalVarianceAtPolynomial params strategy G g ≤
        (params.m : ℝ) *
          pointConditionedLocalVarianceAtPolynomial params strategy G g
  /-- Each fixed polynomial satisfies the claimed global-variance bound. -/
  pointwiseGlobalVarianceBound :
    ∀ g : MIPStarRE.LDT.Polynomial params,
      pointConditionedGlobalVarianceAtPolynomial params strategy G g ≤
        globalVarianceOfPointsError params eps delta
  /-- The polynomial average of the global variances satisfies the same bound. -/
  averagedGlobalVarianceBound :
    pointConditionedGlobalVariance params strategy G ≤
      globalVarianceOfPointsError params eps delta

end MIPRE.LIDT.Co.GlobalVariance

end

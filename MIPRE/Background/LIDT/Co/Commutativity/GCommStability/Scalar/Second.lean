/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
Commutativity/GCommStability/Scalar/Second.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Commutativity.GCommStability.Scalar.Common

@[expose] public section

/-!
# Section 11 commutativity: second scalar stability bound

The mirrored scalar stability defect and its Cauchy--Schwarz boundedness proof: the counterpart
of `MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/GCommStability/Scalar/Second.lean` in the
port of `planning/c6b-plan.md` (milestone M7, section "Port conventions").

The mirrored slice submeasurement `gCommStabilityTwoR` lives in the local C*-algebra `𝔓`, and
the scalar defect is stated with the placements `strategy.state.L` and `strategy.state.R`. The
vendored hypothesis `hnorm : strategy.state.IsNormalized` of `gCommStabilityTwo_scalar` is
dropped, as the port conventions drop `hψ : ψ.IsNormalized`: the first Cauchy–Schwarz factor is
bounded by the keystone's `SymModel.sum_ev_leftTensor_outcome_le_one`, which takes no
normalization hypothesis. Callers omit that argument, which stood between `zeta` and `family`.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Commutativity

open MIPStarRE.LDT (Parameters FieldModel Point Fq avgOver uniformDistribution
  uniformDistribution_weight_sum_le_one)
open GCommStability.Scalar

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The paper's mirrored slice submeasurement
`R'^x_g = E_{v,y} \sum_b G^{v,y}_b G^x_g G^{v,y}_b`. -/
noncomputable def gCommStabilityTwoR
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (x : Fq params) :
    SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓 :=
  averageIdxSubMeas
    (uniformDistribution (Point params.next))
    (fun vy =>
      postprocess
        (sandwichByOuterSubMeas
          (evaluatedPointFamily params family vy)
          (G x))
        Prod.snd)
    (uniformDistribution_weight_sum_le_one (Point params.next))

/-- Named scalar defect for the boundedness half of the second paper stability claim.

For fixed `x`, this is the post-transport mirror analogue of
`commutativity-G.tex`, equation `eq:bound-this-right-now!`, with the slice
sandwich `R'^x_g` in place of `R^y_g`.  It is the scalar after the
`commutativityPoints` transport and after collapsing the `b`-indexed
left-register sandwich into `R'^x_g`; it is not literally the uncollapsed
paper expression `eq:g-comm-stab7`.  Concretely,
`gCommStabilityTwoR` averages the left-register sandwich
`E_{v,y} \sum_b G_b^{v,y} G_g^x G_b^{v,y}`, the factor
`(1 - (G x).total)` is the paper's left-register `(I-G^x)`, and
`IdxPolyFamily.averagedSlicePointEvaluationOperator` is the right-register
average `E_u A^{u,x}_{g(u)}`.  Thus each summand has tensor placement
`(R'_g{}^x (I-G^x)) ⊗ E_u A^{u,x}_{g(u)}`.  The `6√(γ(m+1))` transport loss is
a separate estimate. -/
noncomputable def gCommStabilityTwoScalarDefect
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (x : Fq params) : ℝ :=
  ∑ g : MIPStarRE.LDT.Polynomial params,
    strategy.state.ev
      (strategy.state.L ((gCommStabilityTwoR params family G x).outcome g * (1 - (G x).total)) *
        strategy.state.R (IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g))

/-- Direct boundedness proof for the second paper scalar stability estimate.

This is the `Z^x` boundedness half of
`references/ldt-paper/commutativity-G.tex`, `clm:g-comm-stability2` (lines
185--221), after the right-register point-commutation transport and after the
`b`-indexed left-register sandwich is collapsed into
`gCommStabilityTwoScalarDefect`.  It bounds the post-transport mirror scalar by
`√ζ`.  The separate `6√(γ(m+1))` transport loss is not proved here; a full
paper-budget theorem must combine this post-transport bound with the distinct
`commutativityPoints` transport estimate. The vendored theorem asks for a normalized
state. -/
theorem gCommStabilityTwo_scalar
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (zeta : ℝ)
    (family : IdxPolyFamily params 𝔓)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    |avgOver (uniformDistribution (Fq params))
      (gCommStabilityTwoScalarDefect params strategy family G)| ≤ Real.sqrt zeta :=
  (MIPStarRE.LDT.Preliminaries.avgOver_abs_le_sqrt_of_pointwise
    (uniformDistribution (Fq params))
    (gCommStabilityTwoScalarDefect params strategy family G)
    (fun x => hbound.storedResidual G x)
    (fun x => scalar_pointwise_cauchy_schwarz_bound params strategy zeta family G hG hbound
      (gCommStabilityTwoR params family G x) x
      (strategy.state.sum_ev_leftTensor_outcome_le_one (gCommStabilityTwoR params family G x)))
    (storedResidual_nonneg params strategy family G zeta hbound)
    (by simpa using uniformDistribution_weight_sum_le_one (Fq params))).trans
    (Real.sqrt_le_sqrt (hbound.storedBoundedResidualBound G hG))

end MIPRE.LIDT.Co.Commutativity

end

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
Commutativity/GCommStability/Scalar/First.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Commutativity.GCommStability.Scalar.Common

@[expose] public section

/-!
# Section 11 commutativity: first scalar stability bound

The first scalar stability defect and its Cauchy--Schwarz boundedness proof: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/GCommStability/Scalar/First.lean` in the port
of `planning/c6b-plan.md` (milestone M7, section "Port conventions").

The slice submeasurement `gCommStabilityR` lives in the local C*-algebra `𝔓`, and the scalar
defect is stated with the placements `strategy.state.L` and `strategy.state.R`. The vendored
hypothesis `hnorm : strategy.state.IsNormalized` of `gCommStability_scalar` is dropped, as the
port conventions drop `hψ : ψ.IsNormalized`: the first Cauchy–Schwarz factor is bounded by the
keystone's `SymModel.sum_ev_leftTensor_outcome_le_one`, which takes no normalization hypothesis.
Callers omit that argument, which stood between `zeta` and `family`.

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

/-- The paper's slice submeasurement `R^y_g = E_{u,x} \sum_a G^{u,x}_a G^y_g G^{u,x}_a`. -/
noncomputable def gCommStabilityR
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) (y : Fq params) :
    SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓 :=
  averageIdxSubMeas
    (uniformDistribution (Point params.next))
    (fun ux =>
      postprocess
        (sandwichByOuterSubMeas
          (evaluatedPointFamily params family ux)
          ((family.meas y).toSubMeas))
        Prod.snd)
    (uniformDistribution_weight_sum_le_one (Point params.next))

/-- Named scalar defect for the first paper stability claim.

For fixed `y`, this is the collapsed scalar from `commutativity-G.tex`,
equation `eq:bound-this-right-now!`: `gCommStabilityR` contains the averaged
left-register sandwich `R_g^y = E_{u,x} \sum_a G_a^{u,x} G_g^y G_a^{u,x}`,
the factor `(1 - (G y).total)` is the paper's left-register `(I - G^y)`, and
`IdxPolyFamily.averagedSlicePointEvaluationOperator` is the right-register
average `E_v A^{v,y}_{g(v)}`.  Thus each summand has tensor placement
`(R_g^y (I-G^y)) ⊗ E_v A^{v,y}_{g(v)}`.  This is the scalar expression bounded
by `gCommStability_scalar`, not the overlap `SDDOpRel` package. -/
noncomputable def gCommStabilityScalarDefect
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (y : Fq params) : ℝ :=
  ∑ g : MIPStarRE.LDT.Polynomial params,
    strategy.state.ev
      (strategy.state.L ((gCommStabilityR params family y).outcome g * (1 - (G y).total)) *
        strategy.state.R (IdxPolyFamily.averagedSlicePointEvaluationOperator strategy y g))

/-- Direct boundedness proof for the first paper scalar stability estimate.

This is the Cauchy--Schwarz/`Z^y` part of
`references/ldt-paper/commutativity-G.tex`, `clm:g-comm-stability` (lines
135--179).  It is intentionally separate from the overlap-style
`gCommStability_overlap` theorem: the overlap theorem bounds an internal
`SDDOpRel` package, while this theorem uses `SliceBoundednessInput` to control
the paper scalar defect after the finite marginalization/reindexing step. The vendored theorem
asks for a normalized state. -/
theorem gCommStability_scalar
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (zeta : ℝ)
    (family : IdxPolyFamily params 𝔓)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    |avgOver (uniformDistribution (Fq params))
      (gCommStabilityScalarDefect params strategy family G)| ≤ Real.sqrt zeta :=
  (MIPStarRE.LDT.Preliminaries.avgOver_abs_le_sqrt_of_pointwise
    (uniformDistribution (Fq params))
    (gCommStabilityScalarDefect params strategy family G)
    (fun y => hbound.storedResidual G y)
    (fun y => scalar_pointwise_cauchy_schwarz_bound params strategy zeta family G hG hbound
      (gCommStabilityR params family y) y
      (strategy.state.sum_ev_leftTensor_outcome_le_one (gCommStabilityR params family y)))
    (storedResidual_nonneg params strategy family G zeta hbound)
    (by simpa using uniformDistribution_weight_sum_le_one (Fq params))).trans
    (Real.sqrt_le_sqrt (hbound.storedBoundedResidualBound G hG))

end MIPRE.LIDT.Co.Commutativity

end

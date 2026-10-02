/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
Commutativity/ScalarApproximation/ProcessedG.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Commutativity.ScalarApproximation.ProcessedG.MainChain

@[expose] public section

/-!
# Processed `G` scalar approximation

The public statement of `lem:comm-data-processed-g`, the paper-facing scalar approximation
theorem: the counterpart of `Commutativity/ScalarApproximation/ProcessedG.lean` under
`MIPRE/Background/LIDT/MIPStarRE/LDT/` in the port of `planning/c6b-plan.md` (milestone M7,
section "Port conventions"). The ten-step scalar chain itself is
`evaluatedSlice_scalar_chain_bound` of `ProcessedG/MainChain`; this file rewrites the averaged
`sddErrorOp` of the evaluated-slice products into the chain's two scalar terms
(`evaluatedSliceCommutation_qSDDOp_avg_eq`) and supplies the postprocessed self-consistency
(`evaluatedPointFamily_selfConsistency_of_stronglySelfConsistent`).

The vendored hypothesis `hnorm : strategy.state.IsNormalized` is dropped from both lemmas, as the
port conventions drop `hψ : ψ.IsNormalized` (normalization is a theorem of the model,
`VecState.ev_one_of_isNormalized`): in `commDataProcessedG_of_commutativityPoints` it stood
between `gamma zeta` and `hcomm`, in `commDataProcessedG` between `eps delta gamma zeta` and
`hgood`. Callers pass `params strategy gamma zeta hcomm hgamma_nonneg family hcons hself hbound`
and `params strategy eps delta gamma zeta hgood family hcons hself hbound`. The nonnegativity of
`gamma` in `commDataProcessedG` is `gamma_nonneg_of_isGood`, which the vendored proof inlines.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Commutativity

open MIPStarRE.LDT (Parameters FieldModel Point Fq uniformDistribution)
open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)
open MIPStarRE.LDT.CommutativityPoints (commutativityPointsError)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ### Scalar approximation chain (proof of `lem:comm-data-processed-g`)

The paper's proof (`commutativity-G.tex`, lines 72–131) converts `E[∑ ABAB]` into `E[∑ ABA]`
through a ten-step scalar chain, packaged as `evaluatedSlice_scalar_chain_bound`: Phase 1
(eq:gcom8 → eq:gcom9) costs `2√ζ + √ζ`; Phase 2 (eq:gcom9 → eq:gcom10, with the point swap of
`commutativityPoints`) `2√ζ + 6√(γ(m+1)) + √ζ + 6√(γ(m+1))`; Phase 3 (reversing the
`eq:add-an-a` insertions) `2√ζ + 2√ζ`; Phase 4 (postprocessed self-consistency twice, then the
exact swap identity `avgBAB = avgABA`) `√ζ + √ζ`. Total `12√ζ + 12√(γ(m+1))`, and
`2 · total ≤ 48m(√γ + √ζ)`. -/

/-- Section 11 scalar chain from an already established point-commutativity
estimate.

This is the internal form needed when the point-commutativity theorem has been
proved by a route other than the ordinary `SymStrat.IsGood` diagonal-line
field. -/
lemma commDataProcessedG_of_commutativityPoints
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (gamma zeta : ℝ)
    (hcomm :
      strategy.state.SDDOpRel
        (uniformDistribution (PointPairQuestion params.next))
        (CommutativityPoints.pointMeasurementProductLeft params.next strategy)
        (CommutativityPoints.pointMeasurementProductRight params.next strategy)
        (commutativityPointsError params.next gamma))
    (hgamma_nonneg : 0 ≤ gamma)
    (family : IdxPolyFamily params 𝔓)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    CommDataProcessedGConclusion params strategy family gamma zeta :=
  ⟨(evaluatedSliceCommutation_qSDDOp_avg_eq params strategy family).trans_le <|
    evaluatedSlice_scalar_chain_bound params strategy gamma zeta hcomm hgamma_nonneg family
      (fun x => (family.meas x).toSubMeas) (fun _ => rfl) hcons hself hbound
      (evaluatedPointFamily_selfConsistency_of_stronglySelfConsistent
        params strategy family zeta hself)⟩

/-- Paper origin: `references/ldt-paper/commutativity-G.tex`
(`\label{lem:comm-data-processed-g}`).

The paper statement is formulated directly for the family `family.meas`; the
auxiliary family used by the scalar chain is introduced inside the proof. -/
lemma commDataProcessedG
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma zeta : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params 𝔓)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    CommDataProcessedGConclusion params strategy family gamma zeta :=
  commDataProcessedG_of_commutativityPoints params strategy gamma zeta
    (CommutativityPoints.commutativityPoints params.next strategy eps delta gamma hgood)
    (gamma_nonneg_of_isGood params.next strategy hgood) family hcons hself hbound

end MIPRE.LIDT.Co.Commutativity

end

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
Commutativity/GCommStability/OverlapOne.lean, to the symmetric model of `planning/c6b-plan.md`;
not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Commutativity.ScalarApproximation.Pointwise

@[expose] public section

/-!
# Section 11 commutativity: `G`-stability overlap (step one)

First overlap-averaging step for the `G`-stability argument: averaging the common overlap term
over `Point params.next` reduces to a single-coordinate integral. This is the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/GCommStability/OverlapOne.lean` in the port
of `planning/c6b-plan.md` (milestone M7, section "Port conventions").

The relations are `strategy.state.SDDOpRel`, a vector-state relation on joint operators, and
`sddOpRel_of_sqrt_bound_from_half_one` takes a vector state `V : VecState K` in place of the
vendored one-space state `ψ`. The vendored hypothesis `hnorm : strategy.state.IsNormalized` of
`gCommOverlapTerm_le_one`, `gCommStability_raw_le_one_of` and `gCommStability_overlap` is
dropped, as the port conventions drop `hψ : ψ.IsNormalized`: a vector state has `ev 1 = 1`
(`VecState.ev_one_of_isNormalized`). Callers omit that argument.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

namespace MIPRE.LIDT.Co.Commutativity

open MIPStarRE.LDT (Parameters FieldModel Point Fq pointHeight Distribution avgOver avgOver_mono
  avgOver_uniform_fst avgOver_uniform_snd avgOver_uniform_le_const uniformDistribution)
open MIPStarRE.LDT.Commutativity (EvaluatedSliceQuestion)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Averaging the common overlap term over `Point params.next` depends only on
the final coordinate `x : F_q`. -/
lemma gCommOverlap_avgOver_point
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    avgOver (uniformDistribution (Point params.next))
      (fun w => gCommOverlapTerm params strategy G (pointHeight params w)) =
    avgOver (uniformDistribution (Fq params))
      (fun x => gCommOverlapTerm params strategy G x) :=
  MIPStarRE.LDT.CommutativityPoints.avgOver_uniform_pointNext_height params
    (fun x => gCommOverlapTerm params strategy G x)

/-- Averaging the overlap term over evaluated-slice questions through the
first point coordinate marginalizes to the uniform `x : F_q` average. -/
lemma gCommOverlap_avgOver_fst
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => gCommOverlapTerm params strategy G (pointHeight params q.1)) =
    avgOver (uniformDistribution (Fq params))
      (fun x => gCommOverlapTerm params strategy G x) :=
  (avgOver_uniform_fst (β := Point params.next)
    (fun w => gCommOverlapTerm params strategy G (pointHeight params w))).trans
    (gCommOverlap_avgOver_point params strategy G)

/-- The common overlap term is always at most `1`. The vendored lemma asks for a normalized
state. -/
lemma gCommOverlapTerm_le_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (x : Fq params) :
    gCommOverlapTerm params strategy G x ≤ 1 :=
  (strategy.state.ev_mono _ _ <| strategy.state.opTensor_le_one
    (sub_nonneg.2 (G x).total_le_one) (sub_le_self 1 (G x).total_nonneg)
    (G x).total_le_one).trans_eq strategy.state.ev_one_of_isNormalized

/-- Any pointwise defect bound by the common overlap term inherits a raw
`zeta / 2` estimate after marginalizing to the slice SSC defect of `G`. -/
lemma gCommStability_raw_le_half_of
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (zeta : ℝ)
    (family : IdxPolyFamily params 𝔓)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    {Outcome : Type*} [Fintype Outcome]
    (A B : IdxOpFamily (EvaluatedSliceQuestion params) Outcome (K →L[ℂ] K))
    (point : EvaluatedSliceQuestion params → Point params.next)
    (hmarg :
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => gCommOverlapTerm params strategy G (pointHeight params (point q))) =
      avgOver (uniformDistribution (Fq params))
        (fun x => gCommOverlapTerm params strategy G x))
    (hpointwise : ∀ q,
      strategy.state.qSDDOp (A q) (B q) ≤
        gCommOverlapTerm params strategy G (pointHeight params (point q))) :
    strategy.state.sddErrorOp
      (uniformDistribution (EvaluatedSliceQuestion params))
      A B ≤
    zeta / 2 :=
  calc strategy.state.sddErrorOp (uniformDistribution (EvaluatedSliceQuestion params)) A B
      ≤ avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => gCommOverlapTerm params strategy G (pointHeight params (point q))) :=
        avgOver_mono _ _ _ hpointwise
    _ = avgOver (uniformDistribution (Fq params))
          (fun x => gCommOverlapTerm params strategy G x) := hmarg
    _ ≤ strategy.state.bipartiteSSCError (uniformDistribution (Fq params)) G :=
        avgOver_mono _ _ _ (gCommStability_ssc_point params strategy G)
    _ ≤ zeta / 2 := (gCommStability_sliceSSC params strategy zeta family G hG hself).overlapBound

/-- Any pointwise defect bound by the common overlap term is trivially at most
`1`. The vendored lemma asks for a normalized state. -/
lemma gCommStability_raw_le_one_of
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    {Outcome : Type*} [Fintype Outcome]
    (A B : IdxOpFamily (EvaluatedSliceQuestion params) Outcome (K →L[ℂ] K))
    (point : EvaluatedSliceQuestion params → Point params.next)
    (hpointwise : ∀ q,
      strategy.state.qSDDOp (A q) (B q) ≤
        gCommOverlapTerm params strategy G (pointHeight params (point q))) :
    strategy.state.sddErrorOp
      (uniformDistribution (EvaluatedSliceQuestion params))
      A B ≤
    1 :=
  (avgOver_mono _ _ _ hpointwise).trans <| avgOver_uniform_le_const _ 1 fun q =>
    gCommOverlapTerm_le_one params strategy G (pointHeight params (point q))

/-- Upgrade raw `zeta / 2` and `1` bounds to the displayed `sqrt zeta` relation. The vendored
one-space state `ψ` is a vector state `V`. -/
lemma sddOpRel_of_sqrt_bound_from_half_one
    {Question Outcome : Type*}
    [Fintype Outcome]
    (V : VecState K)
    (𝒟 : Distribution Question)
    (A B : IdxOpFamily Question Outcome (K →L[ℂ] K))
    (zeta : ℝ)
    (hz_nonneg : 0 ≤ zeta)
    (hhalf : V.sddErrorOp 𝒟 A B ≤ zeta / 2)
    (hone : V.sddErrorOp 𝒟 A B ≤ 1) :
    V.SDDOpRel 𝒟 A B (Real.sqrt zeta) := by
  refine ⟨?_⟩
  have hsq := Real.sq_sqrt hz_nonneg
  have hsqrt_nonneg := Real.sqrt_nonneg zeta
  by_cases hz1 : zeta ≤ 1
  · exact hhalf.trans (by nlinarith)
  · exact hone.trans (by nlinarith)

/-- Overlap-only version of the first stability estimate.

This is not the paper's boundedness-driven scalar proof of
`clm:g-comm-stability`: it bounds the current SDD package through the slice SSC
overlap term `⟨Ψ,(I-G^y)⊗G^y Ψ⟩`. It remains useful as an internal overlap
lemma while the scalar-chain API is being completed. The vendored theorem asks for a
normalized state. -/
theorem gCommStability_overlap
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (zeta : ℝ)
    (family : IdxPolyFamily params 𝔓)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    strategy.state.SDDOpRel
      (uniformDistribution (EvaluatedSliceQuestion params))
      (commDataProcessedGStabilityOneLeft params strategy family G)
      (commDataProcessedGStabilityOneRight params strategy family G)
      (Real.sqrt zeta) := by
  have hz_nonneg : 0 ≤ zeta :=
    (strategy.state.sddError_nonneg (uniformDistribution (Fq params)) _ _).trans
      hself.sliceSelfConsistency.squaredDistanceBound
  have hpointwise := gCommStability_pointwise_bound params strategy family G hG
  exact sddOpRel_of_sqrt_bound_from_half_one strategy.state.toVecState
    (uniformDistribution (EvaluatedSliceQuestion params))
    (commDataProcessedGStabilityOneLeft params strategy family G)
    (commDataProcessedGStabilityOneRight params strategy family G)
    zeta hz_nonneg
    (gCommStability_raw_le_half_of params strategy zeta family G hG hself _ _ Prod.snd
      ((avgOver_uniform_snd (α := Point params.next)
        (fun w => gCommOverlapTerm params strategy G (pointHeight params w))).trans
        (gCommOverlap_avgOver_point params strategy G))
      hpointwise)
    (gCommStability_raw_le_one_of params strategy G _ _ Prod.snd hpointwise)

end MIPRE.LIDT.Co.Commutativity

end

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
GlobalVariance/Theorems/SelfConsistencyTransport/Point.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.GlobalVariance.Theorems.SelfConsistencyTransport.Utilities

@[expose] public section

/-!
# Point-event self-consistency transport

The counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/GlobalVariance/Theorems/SelfConsistencyTransport/Point.lean`
in the port of `planning/c6b-plan.md` (milestone M6, section "Port conventions"): the point
self-consistency endpoints of the six-step local-variance transport chain in
`lem:local-variance-of-points` (`expansion.tex`, lines 300--311). These are the first and last
`2δ` moves; the point-line `2ε` moves live in `PointLine.lean`.

The vendored proofs apply the two notions of self-consistency to a permutation-invariant state,
`strategy.permInvState`; here the swap symmetry is a theorem of the model and that argument
disappears (`Preliminaries.twoNotionsOfSelfConsistency`,
`Preliminaries.twoNotionsOfSelfConsistencyAfterEvaluation`). The self-consistency hypothesis
`BipartiteSSCRel` is the `selfConsistencyTest` field of `IsGood` itself.

The proofs are shorter than the vendored ones. The single-polynomial endpoint
`pointConditionedEventSelfConsistency_weighted_point` is one nonnegative summand of the grouped
endpoint `pointConditionedEventSelfConsistency_weighted_point_sum`, so it is derived from it
rather than from a separate application of `cabApproxDelta`; the grouped endpoint is
`cabApproxDelta_sum_from_sdd` on the lifted point measurements, with the bridges
`S.rightTensor_mul_leftTensor_eq_opTensor` and `S.rightTensor_mul_rightTensor`.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/expansion.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.GlobalVariance

open MIPStarRE.LDT (Parameters FieldModel Point Fq avgOver uniformDistribution avgOver_congr
  avgOver_nonneg)
open MIPStarRE.LDT.ExpansionHypercubeGraph (rerandomizeCoord)
open MIPStarRE.LDT.GlobalVariance (avgOver_rerandomizeCoord_fst avgOver_rerandomizeCoord_snd)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ## Good-strategy interfaces for the local-variance transport chain -/

/-- The `2δ` self-consistency interface for the point event `A^u_{g(u)}`.

This is the evaluated, two-outcome version of the first/last moves in
`lem:local-variance-of-points` (`expansion.tex`, lines 305--306 and 310--311):
postprocess the point measurement by the event `a = g(u)`, then apply
`prop:two-notions-of-self-consistency-after-evaluation` to the good-strategy
self-consistency branch. -/
theorem pointConditionedEventSelfConsistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (g : MIPStarRE.LDT.Polynomial params) :
    strategy.state.SDDRel (uniformDistribution (Point params))
      (IdxSubMeas.liftLeft strategy.state
        (fun u : Point params => pointConditionedEventSubMeasAtPolynomial params strategy g u))
      (IdxSubMeas.liftRight strategy.state
        (fun u : Point params => pointConditionedEventSubMeasAtPolynomial params strategy g u))
      (2 * delta) :=
  Preliminaries.twoNotionsOfSelfConsistencyAfterEvaluation strategy.state
    (uniformDistribution (Point params))
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta
    (fun u a => if a = g u then some () else none) ⟨hgood.selfConsistencyTest⟩

/-- Grouped-by-evaluation-value endpoint for the first self-consistency move in
`lem:local-variance-of-points`.

This is the sum-level analogue of `pointConditionedEventSelfConsistency_weighted_point`.
It follows the transport at `references/ldt-paper/expansion.tex`, lines
305--306, but first groups all polynomials with the same value `g(u)`. The
multiplier family is `0` away from the fiber `a = g(u)` and is
`S.R ((G_g)^{1/2})` on that fiber, so the `cabApproxDelta` contraction is supplied
by the submeasurement inequality `∑_{g : g(u)=a} G_g ≤ I`. Consequently the
bound is `2δ` for the polynomial sum, with no polynomial-cardinality loss. -/
theorem pointConditionedEventSelfConsistency_weighted_point_sum
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    (∑ g : MIPStarRE.LDT.Polynomial params,
      avgOver (uniformDistribution (Point params))
        (fun u =>
          let D := weightedPointConditionedOperatorAtPolynomial params strategy G g u -
            weightedPointConditionedRightOperatorAtPolynomial params strategy G g u
          strategy.state.ev (star D * D))) ≤
      2 * delta :=
  cabApproxDelta_sum_from_sdd params strategy.state
    (uniformDistribution (Point params)) (fun u => u)
    (fun u a => strategy.state.L ((strategy.pointMeasurement u).toSubMeas.outcome a))
    (fun u a => strategy.state.R ((strategy.pointMeasurement u).toSubMeas.outcome a))
    (fun u g => weightedPointConditionedOperatorAtPolynomial params strategy G g u)
    (fun u g => weightedPointConditionedRightOperatorAtPolynomial params strategy G g u)
    G (2 * delta)
    (Preliminaries.twoNotionsOfSelfConsistency strategy.state
      (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta
      ⟨hgood.selfConsistencyTest⟩).squaredDistanceBound
    (fun _ _ => strategy.state.rightTensor_mul_leftTensor_eq_opTensor _ _)
    (fun _ _ => strategy.state.rightTensor_mul_rightTensor _ _)

/-- The first self-consistency move in `lem:local-variance-of-points`, after
applying `prop:cab-approx-delta` with the multiplier `S.R ((G_g)^{1/2})` but
before pulling the point marginal to the hypercube-edge distribution.

This proves the weighted native-distribution version of `expansion.tex`,
lines 305--306:
`A^u_{g(u)} ⊗ (G_g)^{1/2} ≈_{2δ} I ⊗ (G_g)^{1/2} A^u_{g(u)}`. It is one nonnegative summand of
`pointConditionedEventSelfConsistency_weighted_point_sum`. -/
theorem pointConditionedEventSelfConsistency_weighted_point
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (g : MIPStarRE.LDT.Polynomial params) :
    avgOver (uniformDistribution (Point params))
      (fun u =>
        let D := weightedPointConditionedOperatorAtPolynomial params strategy G g u -
          weightedPointConditionedRightOperatorAtPolynomial params strategy G g u
        strategy.state.ev (star D * D)) ≤
      2 * delta :=
  (Finset.single_le_sum
      (f := fun g : MIPStarRE.LDT.Polynomial params =>
        avgOver (uniformDistribution (Point params))
          (fun u =>
            let D := weightedPointConditionedOperatorAtPolynomial params strategy G g u -
              weightedPointConditionedRightOperatorAtPolynomial params strategy G g u
            strategy.state.ev (star D * D)))
      (fun _ _ => avgOver_nonneg _ _ fun _ => strategy.state.ev_adjoint_self_nonneg _)
      (Finset.mem_univ g)).trans
    (pointConditionedEventSelfConsistency_weighted_point_sum params strategy eps delta gamma
      hgood G)

/-- Sum-level first self-consistency endpoint on the hypercube-edge sampler.

This is the `u`-endpoint version of `references/ldt-paper/expansion.tex`, lines
305--306, after grouping polynomials by the common value `g(u)` before applying
`cabApproxDelta`. It is the edge-distribution form of
`pointConditionedEventSelfConsistency_weighted_point_sum`. -/
theorem pointConditionedEventSelfConsistency_weighted_leftEdge_sum
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    (∑ g : MIPStarRE.LDT.Polynomial params,
      avgOver (rerandomizeCoord params)
        (fun uv =>
          let D := weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1 -
            weightedPointConditionedRightOperatorAtPolynomial params strategy G g uv.1
          strategy.state.ev (star D * D))) ≤
      2 * delta :=
  (Finset.sum_congr rfl fun g _ =>
      avgOver_rerandomizeCoord_fst params
        (fun u =>
          let D := weightedPointConditionedOperatorAtPolynomial params strategy G g u -
            weightedPointConditionedRightOperatorAtPolynomial params strategy G g u
          strategy.state.ev (star D * D))).trans_le
    (pointConditionedEventSelfConsistency_weighted_point_sum params strategy eps delta gamma
      hgood G)

/-- The final weighted self-consistency move on the target endpoint of the
hypercube edge distribution.

This is the symmetric line-310 to line-311 substep of
`lem:local-variance-of-points`: after the second marginal reindexing,
`I ⊗ (G_g)^{1/2} A^v_{g(v)}` is `2δ`-close to
`A^v_{g(v)} ⊗ (G_g)^{1/2}`. -/
theorem pointConditionedEventSelfConsistency_weighted_rightEdge
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (g : MIPStarRE.LDT.Polynomial params) :
    avgOver (rerandomizeCoord params)
      (fun uv =>
        let D := weightedPointConditionedRightOperatorAtPolynomial params strategy G g uv.2 -
          weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2
        strategy.state.ev (star D * D)) ≤
      2 * delta := by
  rw [avgOver_rerandomizeCoord_snd params
    (fun u =>
      let D := weightedPointConditionedRightOperatorAtPolynomial params strategy G g u -
        weightedPointConditionedOperatorAtPolynomial params strategy G g u
      strategy.state.ev (star D * D))]
  exact (avgOver_congr _ _ _ fun u =>
      ev_adjoint_sub_swap strategy.state.toVecState
        (weightedPointConditionedOperatorAtPolynomial params strategy G g u)
        (weightedPointConditionedRightOperatorAtPolynomial params strategy G g u)).trans_le
    (pointConditionedEventSelfConsistency_weighted_point params strategy eps delta gamma
      hgood G g)

/-- Sum-level final self-consistency endpoint on the hypercube-edge sampler.

This is the `v`-endpoint version of `references/ldt-paper/expansion.tex`, lines
310--311. The second marginal of `rerandomizeCoord` is uniform, and the squared
difference is unchanged after swapping the two endpoint operators. -/
theorem pointConditionedEventSelfConsistency_weighted_rightEdge_sum
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    (∑ g : MIPStarRE.LDT.Polynomial params,
      avgOver (rerandomizeCoord params)
        (fun uv =>
          let D := weightedPointConditionedRightOperatorAtPolynomial params strategy G g uv.2 -
            weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2
          strategy.state.ev (star D * D))) ≤
      2 * delta :=
  (Finset.sum_congr rfl fun g _ =>
      (avgOver_rerandomizeCoord_snd params
        (fun u =>
          let D := weightedPointConditionedRightOperatorAtPolynomial params strategy G g u -
            weightedPointConditionedOperatorAtPolynomial params strategy G g u
          strategy.state.ev (star D * D))).trans
        (avgOver_congr _ _ _ fun u =>
          ev_adjoint_sub_swap strategy.state.toVecState
            (weightedPointConditionedOperatorAtPolynomial params strategy G g u)
            (weightedPointConditionedRightOperatorAtPolynomial params strategy G g u))).trans_le
    (pointConditionedEventSelfConsistency_weighted_point_sum params strategy eps delta gamma
      hgood G)

end MIPRE.LIDT.Co.GlobalVariance

end

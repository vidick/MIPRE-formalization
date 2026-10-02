/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
GlobalVariance/Theorems/TransportChain/Core.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.GlobalVariance.Theorems.SelfConsistencyTransport.Point
public import MIPRE.Background.LIDT.Co.GlobalVariance.Theorems.SelfConsistencyTransport.PointLine
public import MIPRE.Background.LIDT.MIPStarRE.LDT.GlobalVariance.Theorems.TransportChain.Core

@[expose] public section

/-!
# Six-step local-variance transport-chain assembly

The counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/GlobalVariance/Theorems/TransportChain/Core.lean` in the
port of `planning/c6b-plan.md` (milestone M6, section "Port conventions"): the six steps of
`lem:local-variance-of-points` (`expansion.tex`, lines 305--311) assembled into a single
triangle-inequality bound on the hypercube-edge distribution, the transport estimate
`localVarianceTransportChainBound`.

The six steps are one-outcome raw operator families (`singletonOpFamily`, generic over the
ring of operators) chained by `Preliminaries.sddOpRel_chain` on the vector state of the
strategy's model. Each step bound is a ported endpoint of `SelfConsistencyTransport/Point.lean`,
`SelfConsistencyTransport/PointLine.lean` or `CollisionExpansion.lean`, pulled back along the
classical reindexings of the line-pair sample space; none of them takes a swap or normalization
hypothesis, and neither does anything here. The six step families are a vector `![…]` rather than
the vendored `if`-chain, and each step bound is a term.

The reindexings of the line-pair presentation `TransportQuestion` (the four marginal identities,
the pair reparametrization and its comparison with `rerandomizeCoord`) are statements about
distributions alone: this file imports the vendored file for them and names them through an
explicit `open` list.

## Not ported

- `TransportQuestion`: classical, imported.
- `avgOver_transport_leftQuestion`: classical, imported.
- `avgOver_transport_rightQuestion`: classical, imported.
- `avgOver_transport_leftPoint`: classical, imported.
- `avgOver_transport_rightPoint`: classical, imported.
- `addCoordLeftEquiv`: classical, imported.
- `transportQuestionEquiv_symm_pair`: classical, imported.
- `avgOver_transport_pointPair`: classical, imported.
- `avgOver_axisParallelTestSample_update_eq_rerandomizeCoord`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/expansion.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.GlobalVariance

open MIPStarRE.LDT (Parameters FieldModel Point Fq Distribution AxisParallelLine avgOver
  uniformDistribution avgOver_congr)
open MIPStarRE.LDT.ExpansionHypercubeGraph (rerandomizeCoord)
open MIPStarRE.LDT.GlobalVariance (TransportQuestion axisParallelLineQuestionDistribution
  generalizeBError localVarianceTransportChainError localVarianceOfPointsError
  avgOver_transport_leftQuestion avgOver_transport_rightQuestion avgOver_transport_leftPoint
  avgOver_transport_rightPoint avgOver_transport_pointPair
  avgOver_axisParallelTestSample_update_eq_rerandomizeCoord)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The one-outcome raw operator family `q ↦ {X q}`, whose single outcome and total are both
`X q`. -/
def singletonOpFamily {Question R : Type*} (X : Question → R) : IdxOpFamily Question Unit R :=
  fun q => { outcome := fun _ => X q, total := X q }

/-- A bound on the averaged squared distance `E_q ev((X q - Y q)† (X q - Y q))` is an
`SDDOpRel` bound between the one-outcome families of `X` and `Y`. -/
theorem sddOpRel_singleton_of_bound {Question : Type*}
    (V : VecState K) (𝒟 : Distribution Question)
    (X Y : Question → K →L[ℂ] K) (δ : ℝ)
    (h : avgOver 𝒟 (fun q => V.ev (star (X q - Y q) * (X q - Y q))) ≤ δ) :
    V.SDDOpRel 𝒟 (singletonOpFamily X) (singletonOpFamily Y) δ :=
  ⟨le_of_eq_of_le (avgOver_congr _ _ _ fun q =>
    Fintype.sum_unique fun _ : Unit => V.ev (star (X q - Y q) * (X q - Y q))) h⟩

/-- The weighted exact-restriction operator `B^ℓ_{[f = g|_ℓ]} ⊗ (G_g)^{1/2}` depends on the
line question only through its line. -/
theorem weightedGeneralizeBRightOperatorAtPolynomial_point_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (g : MIPStarRE.LDT.Polynomial params)
    (ℓ : AxisParallelLine params) (u v : Point params) :
    weightedGeneralizeBRightOperatorAtPolynomial params strategy G g (ℓ, u) =
      weightedGeneralizeBRightOperatorAtPolynomial params strategy G g (ℓ, v) :=
  rfl

/-- The six-step transport chain of `lem:local-variance-of-points` on the line-pair
presentation: for a line `ℓ` and two of its parameters `t, t'`,
`A^{ℓ(t)}_{g} ⊗ (G_g)^{1/2}` and `A^{ℓ(t')}_{g} ⊗ (G_g)^{1/2}` are
`6 (4ε + 4δ + 2md/q)`-close.

The steps (`expansion.tex`, lines 305--311) are the point self-consistency (`2δ`), the
point-to-line consistency (`2ε`), `lem:generalize-b` forward and reverse (`md/q` each), the
line-to-point consistency (`2ε`) and the point self-consistency again (`2δ`), combined by
`prop:triangle-inequality-for-approx_delta` with `k = 6`. -/
theorem localVarianceTransportLinePairBound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (g : MIPStarRE.LDT.Polynomial params) :
    avgOver (uniformDistribution (TransportQuestion params))
      (fun q =>
        let D := weightedPointConditionedOperatorAtPolynomial params strategy G g
            (q.1.1.pointAt q.1.2) -
          weightedPointConditionedOperatorAtPolynomial params strategy G g
            (q.1.1.pointAt q.2)
        strategy.state.ev (star D * D)) ≤
      localVarianceTransportChainError params eps delta := by
  classical
  let V : VecState K := strategy.state.toVecState
  let A0 : TransportQuestion params → K →L[ℂ] K := fun q =>
    weightedPointConditionedOperatorAtPolynomial params strategy G g (q.1.1.pointAt q.1.2)
  let A1 : TransportQuestion params → K →L[ℂ] K := fun q =>
    weightedPointConditionedRightOperatorAtPolynomial params strategy G g (q.1.1.pointAt q.1.2)
  let A2 : TransportQuestion params → K →L[ℂ] K := fun q =>
    weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g
      (q.1.1, q.1.1.pointAt q.1.2)
  let A3 : TransportQuestion params → K →L[ℂ] K := fun q =>
    weightedGeneralizeBRightOperatorAtPolynomial params strategy G g
      (q.1.1, q.1.1.pointAt q.1.2)
  let A4 : TransportQuestion params → K →L[ℂ] K := fun q =>
    weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g
      (q.1.1, q.1.1.pointAt q.2)
  let A5 : TransportQuestion params → K →L[ℂ] K := fun q =>
    weightedPointConditionedRightOperatorAtPolynomial params strategy G g (q.1.1.pointAt q.2)
  let A6 : TransportQuestion params → K →L[ℂ] K := fun q =>
    weightedPointConditionedOperatorAtPolynomial params strategy G g (q.1.1.pointAt q.2)
  let 𝒟 := uniformDistribution (TransportQuestion params)
  have h01 : V.SDDOpRel 𝒟 (singletonOpFamily A0) (singletonOpFamily A1) (2 * delta) :=
    sddOpRel_singleton_of_bound V 𝒟 A0 A1 _
      ((avgOver_transport_leftPoint params fun u =>
          let D := weightedPointConditionedOperatorAtPolynomial params strategy G g u -
            weightedPointConditionedRightOperatorAtPolynomial params strategy G g u
          V.ev (star D * D)).trans_le
        (pointConditionedEventSelfConsistency_weighted_point
          params strategy eps delta gamma hgood G g))
  have h12 : V.SDDOpRel 𝒟 (singletonOpFamily A1) (singletonOpFamily A2) (2 * eps) :=
    sddOpRel_singleton_of_bound V 𝒟 A1 A2 _
      ((avgOver_transport_leftQuestion params fun qu =>
          let D := weightedPointConditionedRightOperatorAtPolynomial params strategy G g qu.2 -
            weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
          V.ev (star D * D)).trans_le
        (axisParallelPointLineConsistency_weighted_rightToLeftLineQuestion
          params strategy eps delta gamma hgood G g))
  have h23 : V.SDDOpRel 𝒟 (singletonOpFamily A2) (singletonOpFamily A3)
      (generalizeBError params) :=
    sddOpRel_singleton_of_bound V 𝒟 A2 A3 _
      ((avgOver_transport_leftQuestion params fun qu =>
          let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
            weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu
          V.ev (star D * D)).trans_le
        (generalizeBPointwiseSchwartzZippel params strategy G g))
  have h34 : V.SDDOpRel 𝒟 (singletonOpFamily A3) (singletonOpFamily A4)
      (generalizeBError params) :=
    sddOpRel_singleton_of_bound V 𝒟 A3 A4 _
      ((avgOver_transport_rightQuestion params fun qu =>
          let D := weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu -
            weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
          V.ev (star D * D)).trans_le
        (generalizeBReversePointwiseBound params strategy V G
          (generalizeBFromSchwartzZippel params strategy eps delta gamma hgood G) g))
  have h45 : V.SDDOpRel 𝒟 (singletonOpFamily A4) (singletonOpFamily A5) (2 * eps) :=
    sddOpRel_singleton_of_bound V 𝒟 A4 A5 _
      ((avgOver_transport_rightQuestion params fun qu =>
          let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
            weightedPointConditionedRightOperatorAtPolynomial params strategy G g qu.2
          V.ev (star D * D)).trans_le
        (axisParallelPointLineConsistency_weighted_leftToRightLineQuestion
          params strategy eps delta gamma hgood G g))
  have h56 : V.SDDOpRel 𝒟 (singletonOpFamily A5) (singletonOpFamily A6) (2 * delta) :=
    sddOpRel_singleton_of_bound V 𝒟 A5 A6 _
      (((avgOver_congr _ _ _ fun q => ev_adjoint_sub_swap V (A6 q) (A5 q)).trans
          (avgOver_transport_rightPoint params fun u =>
            let D := weightedPointConditionedOperatorAtPolynomial params strategy G g u -
              weightedPointConditionedRightOperatorAtPolynomial params strategy G g u
            V.ev (star D * D))).trans_le
        (pointConditionedEventSelfConsistency_weighted_point
          params strategy eps delta gamma hgood G g))
  let families : Fin 7 → IdxOpFamily (TransportQuestion params) Unit (K →L[ℂ] K) :=
    ![singletonOpFamily A0, singletonOpFamily A1, singletonOpFamily A2, singletonOpFamily A3,
      singletonOpFamily A4, singletonOpFamily A5, singletonOpFamily A6]
  let errors : Fin 6 → ℝ :=
    ![2 * delta, 2 * eps, generalizeBError params, generalizeBError params, 2 * eps, 2 * delta]
  have hchain := Preliminaries.sddOpRel_chain V 𝒟 6 families errors fun i => by
    fin_cases i
    exacts [h01, h12, h23, h34, h45, h56]
  have hsum : ((6 : ℕ) : ℝ) * ∑ i : Fin 6, errors i =
      localVarianceTransportChainError params eps delta := by
    rw [Fin.sum_univ_six]
    simp only [errors, localVarianceTransportChainError, Matrix.cons_val, Nat.cast_ofNat]
    ring
  exact le_of_eq_of_le (avgOver_congr _ _ _ fun q =>
      (Fintype.sum_unique fun _ : Unit => V.ev (star (A0 q - A6 q) * (A0 q - A6 q))).symm)
    (hchain.squaredDistanceBound.trans_eq hsum)

/-- The paper's six-step edge transport estimate in the native
`rerandomizeCoord` presentation.

The triangle chain is proved on the line-pair presentation above; this theorem
reindexes that presentation back to the hypercube-edge sampler
`u, i, x ↦ (u, u[i ↦ x])`, which is exactly `rerandomizeCoord`. -/
theorem localVarianceTransportChainBound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (g : MIPStarRE.LDT.Polynomial params) :
    localVarianceDeviationAtPolynomial params strategy strategy.state G g ≤
      localVarianceTransportChainError params eps delta := by
  let f : Point params × Point params → ℝ := fun uv =>
    let D := weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1 -
      weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2
    strategy.state.ev (star D * D)
  exact le_of_eq_of_le
    ((avgOver_transport_pointPair params f).trans
      (avgOver_axisParallelTestSample_update_eq_rerandomizeCoord params f)).symm
    (localVarianceTransportLinePairBound params strategy eps delta gamma hgood G g)

/-- The post-triangle six-step transport error is absorbed by the paper's
`24(ε + δ + md/q)` slack from `lem:local-variance-of-points`.

This is only the scalar arithmetic after applying
`prop:triangle-inequality-for-approx_delta` with `k = 6` to the estimates at
`references/ldt-paper/expansion.tex`, lines 305--311; it does not assert the
transport estimates themselves. -/
theorem localVarianceTransportChainError_le_localVarianceOfPointsError
    (params : Parameters)
    [FieldModel params.q]
    {eps delta gamma : ℝ}
    (strategy : SymStrat params 𝔓 K)
    (hgood : strategy.IsGood eps delta gamma) :
    localVarianceTransportChainError params eps delta ≤
      localVarianceOfPointsError params eps delta := by
  have heps_nonneg := eps_nonneg_of_isGood params strategy hgood
  have hdelta_nonneg := delta_nonneg_of_isGood params strategy hgood
  have hgen_nonneg : 0 ≤ generalizeBError params := by
    dsimp only [generalizeBError]
    positivity
  dsimp only [localVarianceTransportChainError, localVarianceOfPointsError]
  linarith

end MIPRE.LIDT.Co.GlobalVariance

end

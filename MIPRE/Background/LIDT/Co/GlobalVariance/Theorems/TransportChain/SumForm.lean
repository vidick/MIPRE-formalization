/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
GlobalVariance/Theorems/TransportChain/SumForm.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.GlobalVariance.Theorems.TransportChain.Core
public import MIPRE.Background.LIDT.Co.GlobalVariance.Theorems.SelfConsistencyTransportSum
public import MIPRE.Background.LIDT.Co.GlobalVariance.Theorems.PolynomialSumBounds

@[expose] public section

/-!
# Sum-form local-variance chain

The counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/GlobalVariance/Theorems/TransportChain/SumForm.lean` in the
port of `planning/c6b-plan.md` (milestone M6, section "Port conventions"): the polynomial-sum
reverse `lem:generalize-b` bound and the assembly of the six-step chain summed over all
polynomials, `localVarianceDeviation_sum_le_localVarianceOfPointsError`, which closes
`eq:equivalent-local-variance` with no factor of the number of polynomials.

The six sum-form step bounds are
1. `pointConditionedEventSelfConsistency_weighted_point_sum` (`2δ`),
2. `axisParallelPointLineConsistency_weighted_rightToLeftLineQuestion_sum` (`2ε`),
3. `generalizeBDeviationAtPolynomial_polysum_le_error` (`md/q`, forward),
4. `generalizeBReversePointwiseBound_polysum_le_error` (`md/q`, reverse; below),
5. `axisParallelPointLineConsistency_weighted_leftToRightLineQuestion_sum` (`2ε`),
6. the first again, through `ev_adjoint_sub_swap` (`2δ`).

The vendored proof telescopes the six operator differences pointwise with
`ev_sum_conjTranspose_mul_sum_le`, then sums over `g`, averages and swaps the sums by hand. Here
the polynomial `g` is the outcome of a raw operator family, `q ↦ (g ↦ A_i g q)`, so that a step's
`SDDOpRel` error is exactly its sum over `g` of averaged squared distances (after `avgOver_sum`),
and the six steps are chained by `Preliminaries.sddOpRel_chain`, as the per-polynomial chain of
`TransportChain/Core.lean` is. Each step bound is a term: a classical reindexing of the line-pair
sample space followed by a ported sum-form endpoint. No statement here carries a swap or
normalization hypothesis.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/expansion.tex`, lines 305--321
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.GlobalVariance

open MIPStarRE.LDT (Parameters FieldModel Point avgOver uniformDistribution avgOver_congr
  avgOver_sum)
open MIPStarRE.LDT.GlobalVariance (TransportQuestion axisParallelLineQuestionDistribution
  generalizeBError localVarianceTransportChainError localVarianceOfPointsError
  avgOver_transport_leftQuestion avgOver_transport_rightQuestion avgOver_transport_leftPoint
  avgOver_transport_rightPoint avgOver_transport_pointPair
  avgOver_axisParallelTestSample_update_eq_rerandomizeCoord)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Reverse `lem:generalize-b` bound summed over all polynomials: the reverse squared distance
equals the forward one by `ev_adjoint_sub_swap`, so this is
`generalizeBDeviationAtPolynomial_polysum_le_error`. The sum-form step 4 (`md/q`, reverse) of the
six-step local-variance chain. -/
theorem generalizeBReversePointwiseBound_polysum_le_error
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    (∑ g : MIPStarRE.LDT.Polynomial params,
      avgOver (axisParallelLineQuestionDistribution params)
        (fun qu =>
          let D := weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu -
            weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
          strategy.state.ev (star D * D))) ≤
      generalizeBError params :=
  (Finset.sum_congr rfl fun g _ => avgOver_congr _ _ _ fun qu =>
      ev_adjoint_sub_swap strategy.state.toVecState
        (weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu)
        (weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu)).trans_le
    (generalizeBDeviationAtPolynomial_polysum_le_error params strategy G)

/-- **Chain assembly for `eq:equivalent-local-variance`**: the local-variance deviations summed
over all polynomials are at most `localVarianceOfPointsError = 24(ε + δ + md/q)`.

The six steps of `lem:local-variance-of-points` (`expansion.tex`, lines 305--311), each summed
over `g` with its sum-form bound, are chained with `k = 6` on the line-pair presentation
`TransportQuestion`, which is then reindexed to the hypercube-edge sampler `rerandomizeCoord`; the
transport-chain error `6 (4ε + 4δ + 2md/q)` is absorbed into `localVarianceOfPointsError`. -/
theorem localVarianceDeviation_sum_le_localVarianceOfPointsError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    (∑ g : MIPStarRE.LDT.Polynomial params,
      localVarianceDeviationAtPolynomial params strategy strategy.state G g) ≤
      localVarianceOfPointsError params eps delta := by
  classical
  let V : VecState K := strategy.state.toVecState
  let 𝒟 := uniformDistribution (TransportQuestion params)
  let Poly := MIPStarRE.LDT.Polynomial params
  let A0 : Poly → TransportQuestion params → K →L[ℂ] K := fun g q =>
    weightedPointConditionedOperatorAtPolynomial params strategy G g (q.1.1.pointAt q.1.2)
  let A1 : Poly → TransportQuestion params → K →L[ℂ] K := fun g q =>
    weightedPointConditionedRightOperatorAtPolynomial params strategy G g (q.1.1.pointAt q.1.2)
  let A2 : Poly → TransportQuestion params → K →L[ℂ] K := fun g q =>
    weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g
      (q.1.1, q.1.1.pointAt q.1.2)
  let A3 : Poly → TransportQuestion params → K →L[ℂ] K := fun g q =>
    weightedGeneralizeBRightOperatorAtPolynomial params strategy G g
      (q.1.1, q.1.1.pointAt q.1.2)
  let A4 : Poly → TransportQuestion params → K →L[ℂ] K := fun g q =>
    weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g
      (q.1.1, q.1.1.pointAt q.2)
  let A5 : Poly → TransportQuestion params → K →L[ℂ] K := fun g q =>
    weightedPointConditionedRightOperatorAtPolynomial params strategy G g (q.1.1.pointAt q.2)
  let A6 : Poly → TransportQuestion params → K →L[ℂ] K := fun g q =>
    weightedPointConditionedOperatorAtPolynomial params strategy G g (q.1.1.pointAt q.2)
  -- the polynomial as the outcome of a raw operator family
  let fam : (Poly → TransportQuestion params → K →L[ℂ] K) →
      IdxOpFamily (TransportQuestion params) Poly (K →L[ℂ] K) :=
    fun X q => { outcome := fun g => X g q, total := 0 }
  have hfam : ∀ (X Y : Poly → TransportQuestion params → K →L[ℂ] K) (δ : ℝ),
      (∑ g, avgOver 𝒟 (fun q => V.ev (star (X g q - Y g q) * (X g q - Y g q)))) ≤ δ →
        V.SDDOpRel 𝒟 (fam X) (fam Y) δ :=
    fun X Y δ h => ⟨le_of_eq_of_le (avgOver_sum _ _) h⟩
  have h01 : V.SDDOpRel 𝒟 (fam A0) (fam A1) (2 * delta) :=
    hfam A0 A1 _ ((Finset.sum_congr rfl fun g _ =>
        avgOver_transport_leftPoint params fun u =>
          let D := weightedPointConditionedOperatorAtPolynomial params strategy G g u -
            weightedPointConditionedRightOperatorAtPolynomial params strategy G g u
          V.ev (star D * D)).trans_le
      (pointConditionedEventSelfConsistency_weighted_point_sum
        params strategy eps delta gamma hgood G))
  have h12 : V.SDDOpRel 𝒟 (fam A1) (fam A2) (2 * eps) :=
    hfam A1 A2 _ ((Finset.sum_congr rfl fun g _ =>
        avgOver_transport_leftQuestion params fun qu =>
          let D := weightedPointConditionedRightOperatorAtPolynomial params strategy G g qu.2 -
            weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
          V.ev (star D * D)).trans_le
      (axisParallelPointLineConsistency_weighted_rightToLeftLineQuestion_sum
        params strategy eps delta gamma hgood G))
  have h23 : V.SDDOpRel 𝒟 (fam A2) (fam A3) (generalizeBError params) :=
    hfam A2 A3 _ ((Finset.sum_congr rfl fun g _ =>
        avgOver_transport_leftQuestion params fun qu =>
          let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
            weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu
          V.ev (star D * D)).trans_le
      (generalizeBDeviationAtPolynomial_polysum_le_error params strategy G))
  have h34 : V.SDDOpRel 𝒟 (fam A3) (fam A4) (generalizeBError params) :=
    hfam A3 A4 _ ((Finset.sum_congr rfl fun g _ =>
        avgOver_transport_rightQuestion params fun qu =>
          let D := weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu -
            weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
          V.ev (star D * D)).trans_le
      (generalizeBReversePointwiseBound_polysum_le_error params strategy G))
  have h45 : V.SDDOpRel 𝒟 (fam A4) (fam A5) (2 * eps) :=
    hfam A4 A5 _ ((Finset.sum_congr rfl fun g _ =>
        avgOver_transport_rightQuestion params fun qu =>
          let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
            weightedPointConditionedRightOperatorAtPolynomial params strategy G g qu.2
          V.ev (star D * D)).trans_le
      (axisParallelPointLineConsistency_weighted_leftToRightLineQuestion_sum
        params strategy eps delta gamma hgood G))
  have h56 : V.SDDOpRel 𝒟 (fam A5) (fam A6) (2 * delta) :=
    hfam A5 A6 _ ((Finset.sum_congr rfl fun g _ =>
        (avgOver_congr _ _ _ fun q => ev_adjoint_sub_swap V (A6 g q) (A5 g q)).trans
          (avgOver_transport_rightPoint params fun u =>
            let D := weightedPointConditionedOperatorAtPolynomial params strategy G g u -
              weightedPointConditionedRightOperatorAtPolynomial params strategy G g u
            V.ev (star D * D))).trans_le
      (pointConditionedEventSelfConsistency_weighted_point_sum
        params strategy eps delta gamma hgood G))
  let families : Fin 7 → IdxOpFamily (TransportQuestion params) Poly (K →L[ℂ] K) :=
    ![fam A0, fam A1, fam A2, fam A3, fam A4, fam A5, fam A6]
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
  -- each deviation, reindexed from `rerandomizeCoord` to the line-pair presentation
  have hreindex : ∀ g : Poly,
      localVarianceDeviationAtPolynomial params strategy strategy.state G g =
        avgOver 𝒟 (fun q => V.ev (star (A0 g q - A6 g q) * (A0 g q - A6 g q))) := fun g =>
    let f : Point params × Point params → ℝ := fun uv =>
      let D := weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1 -
        weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2
      strategy.state.ev (star D * D)
    ((avgOver_transport_pointPair params f).trans
      (avgOver_axisParallelTestSample_update_eq_rerandomizeCoord params f)).symm
  calc
    _ = ∑ g : Poly, avgOver 𝒟 (fun q => V.ev (star (A0 g q - A6 g q) * (A0 g q - A6 g q))) :=
        Finset.sum_congr rfl fun g _ => hreindex g
    _ = V.sddErrorOp 𝒟 (families 0) (families (Fin.last 6)) := (avgOver_sum _ _).symm
    _ ≤ localVarianceTransportChainError params eps delta :=
        hchain.squaredDistanceBound.trans_eq hsum
    _ ≤ localVarianceOfPointsError params eps delta :=
        localVarianceTransportChainError_le_localVarianceOfPointsError params strategy hgood

end MIPRE.LIDT.Co.GlobalVariance

end

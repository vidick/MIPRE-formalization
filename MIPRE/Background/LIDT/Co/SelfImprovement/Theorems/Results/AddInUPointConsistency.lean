/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
SelfImprovement/Theorems/Results/AddInUPointConsistency.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Basic.SubMeasurementFamilies
public import MIPRE.Background.LIDT.Co.GlobalVariance.Defs.Families
public import MIPRE.Background.LIDT.Co.Preliminaries.SelfConsistency.DataProcessing
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Statements
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Results.AddInUDiagonalAndDefs.Residual
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Results.AddInUDiagonalAndDefs.ScalarChain
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Results.AddInUStep34AndTransfer.Transfer
public import MIPStarRE.LDT.SelfImprovement.Theorems.Thresholds.Final
public import MIPStarRE.LDT.SelfImprovement.Theorems.Results.AddInUPointConsistency

@[expose] public section

/-!
# Off-diagonal add-in-u selection for helper point consistency

The `add-in-u` specialization with `Outcome = Fq params`, `M = A` (the point measurement) and the
off-diagonal selection `S_u = {(a, h) : h(u) ≠ a}` used in the proof of the helper-stage
`A`-consistency bound (`eq:explicit-bound-for-A-consistency`): the counterpart of the vendored
`SelfImprovement/Theorems/Results/AddInUPointConsistency.lean` (under
`MIPRE/Background/LIDT/MIPStarRE/LDT/`) in the port of `planning/c6b-plan.md` (milestone M10,
section "Port conventions").

## Contents

- `pointConsistencyAddInUCSChainQ0` … `Q4`: the selected Cauchy--Schwarz chain at the
  off-diagonal selection, with its endpoint identifications.
- `pointConsistencyAddInU_transfer_of_selected_chain_bounds` and
  `pointConsistencyAddInU_transfer_of_selected_chain_selfConsistency_globalVariance`: the
  selection-dependent transfer, from four step bounds and from point self-consistency with the
  global-variance sum bound.
- `addInULeftQuantity_pointConsistencySelection_eq_off_diagonal_avg`,
  `addInURightQuantity_pointConsistencySelection_eq_zero`: the left side is the averaged
  off-diagonal mass, the right side vanishes by projectivity of the point measurement.
- `pointConsistencyAddInU_off_diagonal_avg_le_of_transfer` and its `_helper_error_` form.

A strategy is a `SymStrat params 𝔓 K`; the point measurement and `T`, `H` are local (in `𝔓`), and
every scalar is `strategy.state.ev` of a joint operator `strategy.state.opTensor X Y`. The
vendored `opTensor 0 Y = 0` step, proved entrywise there, is `zero_mul` after `map_zero` here. No
statement of the vendored file carries a swap, density or normalization hypothesis, so no
statement changed; the file sets no option, the vendored file-wide `respectTransparency false`
not being needed.

The vendored module is imported for its two classical declarations; the classical threshold
`helper_point_consistency_error_le_selfImprovementHelperError` comes from the vendored
`Thresholds/Helper.lean` through `Thresholds/Final.lean`, as in the vendored file.

## Not ported

- `pointConsistencyAddInUSelection`: classical, imported.
- `pointConsistencyAddInUSelection_pairs_sum`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/self_improvement.tex` lines 420–437
- `blueprint/src/chapter/ch07_self_improvement.tex` lines 155–179
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.SelfImprovement

open MIPStarRE.LDT (Parameters FieldModel Point Fq avgOver uniformDistribution avgOver_congr
  avgOver_uniform_const)
open MIPStarRE.LDT.SelfImprovement (addInUSelectionPairs selfImprovementVarianceError
  addInUError selfImprovementHelperError pointConsistencyAddInUSelection
  pointConsistencyAddInUSelection_pairs_sum
  two_sqrt_two_delta_add_two_sqrt_selfImprovementVarianceError_le_addInUError
  helper_point_consistency_error_le_selfImprovementHelperError)
open MIPRE.LIDT.Co.GlobalVariance (pointConditionedOutcomeOperatorAtPolynomial
  globalVarianceDeviationAtPolynomial)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ### Off-diagonal selected scalar chain -/

/-- The off-diagonal point-consistency specialization of the selected add-in-u
chain endpoint `Q₀`. -/
noncomputable def pointConsistencyAddInUCSChainQ0
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) : ℝ :=
  addInUSelectedCSChainQ0 params strategy
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
    T
    (pointConsistencyAddInUSelection params)

/-- The off-diagonal point-consistency specialization of the selected add-in-u
chain scalar `Q₁`. -/
noncomputable def pointConsistencyAddInUCSChainQ1
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) : ℝ :=
  addInUSelectedCSChainQ1 params strategy
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
    T
    (pointConsistencyAddInUSelection params)

/-- The off-diagonal point-consistency specialization of the selected add-in-u
chain scalar `Q₂`. -/
noncomputable def pointConsistencyAddInUCSChainQ2
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) : ℝ :=
  addInUSelectedCSChainQ2 params strategy
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
    T
    (pointConsistencyAddInUSelection params)

/-- The off-diagonal point-consistency specialization of the selected add-in-u
chain scalar `Q₃`. -/
noncomputable def pointConsistencyAddInUCSChainQ3
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) : ℝ :=
  addInUSelectedCSChainQ3 params strategy
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
    T
    (pointConsistencyAddInUSelection params)

/-- The off-diagonal point-consistency specialization of the selected add-in-u
chain endpoint `Q₄`. -/
noncomputable def pointConsistencyAddInUCSChainQ4
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) : ℝ :=
  addInUSelectedCSChainQ4 params strategy
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
    T
    (pointConsistencyAddInUSelection params)

/-- The off-diagonal selected-chain endpoint `Q₀` is the corresponding generic
add-in-u left quantity with the averaged sandwiched polynomial submeasurement. -/
theorem pointConsistencyAddInUCSChainQ0_eq_leftQuantity_averagedSandwiched
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    addInULeftQuantity params strategy
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (averagedSandwichedPolynomialSubMeas params strategy T)
        (pointConsistencyAddInUSelection params) =
      pointConsistencyAddInUCSChainQ0 params strategy T :=
  addInUSelectedCSChainQ0_eq_leftQuantity_averagedSandwiched params strategy
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) T
    (pointConsistencyAddInUSelection params)

/-- The off-diagonal selected-chain endpoint `Q₄` is the corresponding generic
add-in-u right quantity. -/
theorem pointConsistencyAddInUCSChainQ4_eq_rightQuantity
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    addInURightQuantity params strategy
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        T
        (pointConsistencyAddInUSelection params) =
      pointConsistencyAddInUCSChainQ4 params strategy T :=
  addInUSelectedCSChainQ4_eq_rightQuantity params strategy
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) T
    (pointConsistencyAddInUSelection params)

/-- Point-consistency add-in-u transfer assembled from the four selected scalar
chain estimates.

This theorem is the off-diagonal counterpart of the diagonal chain assembly:
once the four selected Cauchy--Schwarz moves are available with total error at
most `addInUError`, it gives the theorem-side transfer hypothesis consumed by
`pointConsistencyAddInU_off_diagonal_avg_le_of_transfer`. -/
theorem pointConsistencyAddInU_transfer_of_selected_chain_bounds
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (η01 η12 η23 η34 : ℝ)
    (h01 :
      |pointConsistencyAddInUCSChainQ0 params strategy T -
        pointConsistencyAddInUCSChainQ1 params strategy T| ≤ η01)
    (h12 :
      |pointConsistencyAddInUCSChainQ1 params strategy T -
        pointConsistencyAddInUCSChainQ2 params strategy T| ≤ η12)
    (h23 :
      |pointConsistencyAddInUCSChainQ2 params strategy T -
        pointConsistencyAddInUCSChainQ3 params strategy T| ≤ η23)
    (h34 :
      |pointConsistencyAddInUCSChainQ3 params strategy T -
        pointConsistencyAddInUCSChainQ4 params strategy T| ≤ η34)
    (hsum : η01 + η12 + η23 + η34 ≤ addInUError params eps delta) :
    |addInULeftQuantity params strategy
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (averagedSandwichedPolynomialSubMeas params strategy T)
        (pointConsistencyAddInUSelection params) -
      addInURightQuantity params strategy
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        T
        (pointConsistencyAddInUSelection params)| ≤ addInUError params eps delta :=
  add_in_u_selected_transfer_of_cs_chain params strategy eps delta
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) T
    (pointConsistencyAddInUSelection params) η01 η12 η23 η34 h01 h12 h23 h34 hsum

/-- Point-consistency add-in-u transfer with the two self-consistency moves and
the two selected global-variance moves supplied by the proved Cauchy--Schwarz
bounds.

This is the theorem-side form of the off-diagonal application of
`lem:add-in-u`: the first two selected moves use bipartite self-consistency of
the point measurement, while the last two use the global-variance sum bound for
the polynomial submeasurement `T`. -/
theorem pointConsistencyAddInU_transfer_of_selected_chain_selfConsistency_globalVariance
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hssc : strategy.state.BipartiteSSCRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta)
    (hglobal :
      (∑ g : MIPStarRE.LDT.Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤
          selfImprovementVarianceError params eps delta) :
    |addInULeftQuantity params strategy
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (averagedSandwichedPolynomialSubMeas params strategy T)
        (pointConsistencyAddInUSelection params) -
      addInURightQuantity params strategy
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        T
        (pointConsistencyAddInUSelection params)| ≤ addInUError params eps delta := by
  have hsteps :=
    addInU_selected_cs_chain_step34_abs_le_sqrt_of_globalVarianceDeviation_sum_le params strategy
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) T
      (pointConsistencyAddInUSelection params) hglobal
  exact pointConsistencyAddInU_transfer_of_selected_chain_bounds params strategy eps delta T
    _ _ _ _
    (addInU_selected_cs_chain_step1_abs_le_sqrt_two_delta params strategy
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) T
      (pointConsistencyAddInUSelection params) delta hssc)
    (addInU_selected_cs_chain_step2_abs_le_sqrt_two_delta params strategy
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) T
      (pointConsistencyAddInUSelection params) delta hssc)
    hsteps.1 hsteps.2 (by
      have := two_sqrt_two_delta_add_two_sqrt_selfImprovementVarianceError_le_addInUError
        params eps delta heps hdelta
      linarith)

/-- The left side of the helper point-consistency `add-in-u` application is the
averaged off-diagonal helper-agreement mass.

This is exactly the scalar quantity on the left of
`eq:explicit-bound-for-A-consistency`, written through the generic theorem-side
`addInULeftQuantity` interface for the off-diagonal selection. -/
theorem addInULeftQuantity_pointConsistencySelection_eq_off_diagonal_avg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (H : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    addInULeftQuantity params strategy
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        H
        (pointConsistencyAddInUSelection params) =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : MIPStarRE.LDT.Polynomial params,
          ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
            strategy.state.ev
              (strategy.state.opTensor ((strategy.pointMeasurement u).outcome a)
                (H.outcome h))) :=
  avgOver_congr (uniformDistribution (Point params)) _ _ fun u =>
    (strategy.state.ev_finset_sum _ _).trans
      (pointConsistencyAddInUSelection_pairs_sum params u fun a h =>
        strategy.state.ev
          (strategy.state.opTensor ((strategy.pointMeasurement u).outcome a) (H.outcome h)))

/-- The right side of the helper point-consistency `add-in-u` application is
identically zero by projectivity of the point measurement.

For every selected pair `(a, h)` with `h u ≠ a`, the inner sandwich contains the
factor `A^u_{h(u)} A^u_a = 0`, so every summand vanishes. -/
theorem addInURightQuantity_pointConsistencySelection_eq_zero
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    addInURightQuantity params strategy
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        T
        (pointConsistencyAddInUSelection params) = 0 := by
  classical
  have hpoint : ∀ u : Point params,
      strategy.state.ev
        (addInURightOperatorAtPoint params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          T
          (pointConsistencyAddInUSelection params) u) = 0 := by
    intro u
    refine (strategy.state.ev_finset_sum _ _).trans (Finset.sum_eq_zero fun ah hh => ?_)
    have hh' : ah.2 u ≠ ah.1 := (Finset.mem_filter.1 hh).2
    have hortho :
        pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 u *
            (strategy.pointMeasurement u).outcome ah.1 = 0 :=
      (strategy.pointMeasurement u).outcome_orthogonal (ah.2 u) ah.1 hh'
    change strategy.state.ev
        (strategy.state.L
          (pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 u *
            (strategy.pointMeasurement u).outcome ah.1 *
            pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 u) *
          strategy.state.R (T.outcome ah.2)) = 0
    rw [hortho, zero_mul, map_zero, zero_mul, strategy.state.ev_zero]
  change avgOver (uniformDistribution (Point params)) (fun u =>
      strategy.state.ev
        (addInURightOperatorAtPoint params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          T
          (pointConsistencyAddInUSelection params) u)) = 0
  rw [avgOver_congr (uniformDistribution (Point params)) _ (fun _ => 0) hpoint,
    avgOver_uniform_const]

/-- Any theorem-side `add-in-u` transfer bound for the off-diagonal selection
immediately bounds the averaged helper off-diagonal mass by `addInUError`.

This is the exact theorem-side wrapper needed to connect a future generic
selection-dependent transfer theorem to the helper `A`-consistency route. -/
theorem pointConsistencyAddInU_off_diagonal_avg_le_of_transfer
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (H : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (htransfer :
      |addInULeftQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          H
          (pointConsistencyAddInUSelection params) -
        addInURightQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          T
          (pointConsistencyAddInUSelection params)| ≤ addInUError params eps delta) :
    avgOver (uniformDistribution (Point params)) (fun u =>
      ∑ h : MIPStarRE.LDT.Polynomial params,
        ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
          strategy.state.ev
            (strategy.state.opTensor ((strategy.pointMeasurement u).outcome a)
              (H.outcome h))) ≤ addInUError params eps delta := by
  rw [addInURightQuantity_pointConsistencySelection_eq_zero,
    addInULeftQuantity_pointConsistencySelection_eq_off_diagonal_avg, sub_zero] at htransfer
  exact (abs_le.mp htransfer).2

/-- Helper-stage point-consistency bound from the off-diagonal `add-in-u`
transfer estimate.

The preceding theorem gives the natural bound `addInUError`, which is equal to
`4 * sqrt ζ_variance` after rewriting by `Real.sqrt_eq_rpow`.  This wrapper
applies the numerical absorption from `self_improvement.tex`, lines 438--443, so that the
resulting off-diagonal helper mass is already bounded by the helper-stage error
`selfImprovementHelperError`.  The only remaining analytic input is the
selection-dependent `add-in-u` transfer inequality for
`pointConsistencyAddInUSelection`. -/
theorem pointConsistencyAddInU_off_diagonal_avg_le_helper_error_of_transfer
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (H : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (htransfer :
      |addInULeftQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          H
          (pointConsistencyAddInUSelection params) -
        addInURightQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          T
          (pointConsistencyAddInUSelection params)| ≤ addInUError params eps delta) :
    avgOver (uniformDistribution (Point params)) (fun u =>
      ∑ h : MIPStarRE.LDT.Polynomial params,
        ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
          strategy.state.ev
            (strategy.state.opTensor ((strategy.pointMeasurement u).outcome a)
              (H.outcome h))) ≤ selfImprovementHelperError params eps delta :=
  (pointConsistencyAddInU_off_diagonal_avg_le_of_transfer params strategy eps delta T H
    htransfer).trans (by
      simpa [addInUError, Real.sqrt_eq_rpow] using
        helper_point_consistency_error_le_selfImprovementHelperError
          params eps delta heps hdelta)

end MIPRE.LIDT.Co.SelfImprovement

end

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
SelfImprovement/Theorems/Results/BoundednessTransport/PointConsistencyLiteral.lean, to the
symmetric model of `planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Results.BoundednessTransport.PointConsistency

@[expose] public section

/-!
# Boundedness transport literal point-consistency estimates

The literal-threshold point-consistency transports, at `selfImprovementError`, obtained from the
natural-error estimates of `BoundednessTransport/PointConsistency.lean`: the counterpart of the
vendored `SelfImprovement/Theorems/Results/BoundednessTransport/PointConsistencyLiteral.lean`
(under `MIPRE/Background/LIDT/MIPStarRE/LDT/`) in the port of `planning/c6b-plan.md` (milestone
M10, section "Port conventions").

## Contents

- `final_fields_point_consistency_totalGap` and `…_totalGap_of_total_difference`: the natural
  error with an explicit total-overlap displacement `η`, absorbed into `selfImprovementError`
  under a numerical hypothesis.
- `final_fields_point_consistency_natural_of_total_le`, `…_of_total_expectation_le` and
  `…_of_total_operator_le`: the natural error when the projective replacement has no larger
  right total (pointwise, as one scalar, or as an operator inequality).
- `final_fields_point_consistency_of_total_expectation_le_of_small_errors`,
  `…_of_total_operator_le_of_small_errors` and `…_totalGap_of_data_processing`: the same at
  `selfImprovementError`, through the classical absorption
  `final_fields_projective_residual_error_le_selfImprovementError` of the vendored
  `Thresholds/Final.lean`.

The translation is that of `BoundednessTransport/PointConsistency.lean`. The vendored
`sddRel_liftRight_of_liftLeft_permInv strategy.permInvState …` is M8's
`MakingMeasurementsProjective.sddRel_liftRight_of_liftLeft_permInv strategy.state …`, and the
vendored `strategy.isNormalized` argument of `Preliminaries.triangleSub_right_subMeas_total_le` is
dropped, the ported lemma taking none. No statement of the vendored file carries a swap, density
or normalization hypothesis, so no statement changed; the file sets no option, the vendored
file-wide `respectTransparency false` not being needed. The error constants
(`selfImprovementHelperError`, `selfImprovementDataProcessingError`, `selfImprovementError`) are
the vendored classical ones.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/self_improvement.tex` lines 747--755
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.SelfImprovement

open MIPStarRE.LDT (Parameters FieldModel Point avgOver uniformDistribution
  uniformDistribution_weight_sum_le_one)
open MIPStarRE.LDT.SelfImprovement (selfImprovementHelperError
  selfImprovementDataProcessingError selfImprovementError
  final_fields_projective_residual_error_le_selfImprovementError)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Literal-threshold point-consistency transport from the helper output to the
projective output.

This theorem isolates the numerical absorption needed to turn the natural
error
`selfImprovementHelperError + sqrt selfImprovementDataProcessingError + η`
into the final `selfImprovementError` threshold.  The analytic content is
contained in `final_fields_point_consistency_totalGap_natural`. -/
theorem final_fields_point_consistency_totalGap
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta η : ℝ)
    {Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    {H : ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    (hhelperPoint :
      strategy.state.ConsRel (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params Hhat)
        (selfImprovementHelperError params eps delta))
    (hdata :
      strategy.state.SDDRel (uniformDistribution (Point params))
        (IdxSubMeas.liftLeft strategy.state (polynomialEvaluationFamily params Hhat))
        (IdxSubMeas.liftLeft strategy.state (polynomialEvaluationFamily params H.toSubMeas))
        (selfImprovementDataProcessingError params eps delta))
    (hTotal :
      avgOver (uniformDistribution (Point params)) (fun u =>
        |strategy.state.ev
            (strategy.state.L
              (((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u).total) *
              strategy.state.R
                (((polynomialEvaluationFamily params H.toSubMeas) u).total)) -
          strategy.state.ev
            (strategy.state.L
              (((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u).total) *
              strategy.state.R
                (((polynomialEvaluationFamily params Hhat) u).total))|) ≤ η)
    (habsorb :
      selfImprovementHelperError params eps delta +
          Real.sqrt (selfImprovementDataProcessingError params eps delta) + η ≤
        selfImprovementError params eps delta) :
    strategy.state.ConsRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params H.toSubMeas)
      (selfImprovementError params eps delta) :=
  SymModel.ConsRel.mono habsorb
    (final_fields_point_consistency_totalGap_natural params strategy eps delta η
      hhelperPoint hdata hTotal)

/-- Literal-threshold point-consistency transport from a right-register total
difference bound.

This is the `selfImprovementError`-absorbed companion to
`final_fields_point_consistency_totalGap_natural_of_total_difference`. -/
theorem final_fields_point_consistency_totalGap_of_total_difference
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta η : ℝ)
    {Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    {H : ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    (hhelperPoint :
      strategy.state.ConsRel (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params Hhat)
        (selfImprovementHelperError params eps delta))
    (hdata :
      strategy.state.SDDRel (uniformDistribution (Point params))
        (IdxSubMeas.liftLeft strategy.state (polynomialEvaluationFamily params Hhat))
        (IdxSubMeas.liftLeft strategy.state (polynomialEvaluationFamily params H.toSubMeas))
        (selfImprovementDataProcessingError params eps delta))
    (hTotal :
      |strategy.state.ev (strategy.state.R H.toSubMeas.total) -
        strategy.state.ev (strategy.state.R Hhat.total)| ≤ η)
    (habsorb :
      selfImprovementHelperError params eps delta +
          Real.sqrt (selfImprovementDataProcessingError params eps delta) + η ≤
        selfImprovementError params eps delta) :
    strategy.state.ConsRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params H.toSubMeas)
      (selfImprovementError params eps delta) :=
  SymModel.ConsRel.mono habsorb
    (final_fields_point_consistency_totalGap_natural_of_total_difference
      params strategy eps delta η hhelperPoint hdata hTotal)

/-- Natural-error point-consistency transport under monotone total overlap.

If the projective replacement has no larger right-register total overlap with
the point measurement than the helper submeasurement, then the submeasurement
triangle argument is at the paper-natural error threshold
`selfImprovementHelperError + sqrt selfImprovementDataProcessingError`. -/
theorem final_fields_point_consistency_natural_of_total_le
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    {Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    {H : ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    (hhelperPoint :
      strategy.state.ConsRel (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params Hhat)
        (selfImprovementHelperError params eps delta))
    (hdata :
      strategy.state.SDDRel (uniformDistribution (Point params))
        (IdxSubMeas.liftLeft strategy.state (polynomialEvaluationFamily params Hhat))
        (IdxSubMeas.liftLeft strategy.state (polynomialEvaluationFamily params H.toSubMeas))
        (selfImprovementDataProcessingError params eps delta))
    (hTotalLe :
      ∀ u : Point params,
        strategy.state.ev
            (strategy.state.L
              (((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u).total) *
              strategy.state.R
                (((polynomialEvaluationFamily params H.toSubMeas) u).total)) ≤
          strategy.state.ev
            (strategy.state.L
              (((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u).total) *
              strategy.state.R
                (((polynomialEvaluationFamily params Hhat) u).total))) :
    strategy.state.ConsRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params H.toSubMeas)
      (selfImprovementHelperError params eps delta +
        Real.sqrt (selfImprovementDataProcessingError params eps delta)) :=
  Preliminaries.triangleSub_right_subMeas_total_le strategy.state
    (uniformDistribution (Point params)) (uniformDistribution_weight_sum_le_one (Point params))
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
    (polynomialEvaluationFamily params Hhat)
    (polynomialEvaluationFamily params H.toSubMeas)
    (selfImprovementHelperError params eps delta)
    (selfImprovementDataProcessingError params eps delta) hhelperPoint
    (MakingMeasurementsProjective.sddRel_liftRight_of_liftLeft_permInv strategy.state
      (uniformDistribution (Point params)) _ _ _ hdata)
    hTotalLe

/-- Natural-error point-consistency transport from a scalar right-total
monotonicity hypothesis.

Since the point measurement is complete and postprocessing preserves total
operators, this monotonicity condition is equivalent to a single scalar
comparison of right-register expectations. -/
theorem final_fields_point_consistency_natural_of_total_expectation_le
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    {Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    {H : ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    (hhelperPoint :
      strategy.state.ConsRel (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params Hhat)
        (selfImprovementHelperError params eps delta))
    (hdata :
      strategy.state.SDDRel (uniformDistribution (Point params))
        (IdxSubMeas.liftLeft strategy.state (polynomialEvaluationFamily params Hhat))
        (IdxSubMeas.liftLeft strategy.state (polynomialEvaluationFamily params H.toSubMeas))
        (selfImprovementDataProcessingError params eps delta))
    (hTotalLe :
      strategy.state.ev (strategy.state.R H.toSubMeas.total) ≤
        strategy.state.ev (strategy.state.R Hhat.total)) :
    strategy.state.ConsRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params H.toSubMeas)
      (selfImprovementHelperError params eps delta +
        Real.sqrt (selfImprovementDataProcessingError params eps delta)) :=
  final_fields_point_consistency_natural_of_total_le params strategy eps delta hhelperPoint hdata
    fun u => by
      rw [pointMeasurement_total_evalFamily_total_ev_eq_rightTensor params strategy
          H.toSubMeas u,
        pointMeasurement_total_evalFamily_total_ev_eq_rightTensor params strategy Hhat u]
      exact hTotalLe

/-- Literal-threshold point-consistency transport from scalar right-total
monotonicity and the standard small-error hypotheses. -/
theorem final_fields_point_consistency_of_total_expectation_le_of_small_errors
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : ℝ) ≤ (params.q : ℝ))
    {Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    {H : ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    (hhelperPoint :
      strategy.state.ConsRel (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params Hhat)
        (selfImprovementHelperError params eps delta))
    (hdata :
      strategy.state.SDDRel (uniformDistribution (Point params))
        (IdxSubMeas.liftLeft strategy.state (polynomialEvaluationFamily params Hhat))
        (IdxSubMeas.liftLeft strategy.state (polynomialEvaluationFamily params H.toSubMeas))
        (selfImprovementDataProcessingError params eps delta))
    (hTotalLe :
      strategy.state.ev (strategy.state.R H.toSubMeas.total) ≤
        strategy.state.ev (strategy.state.R Hhat.total)) :
    strategy.state.ConsRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params H.toSubMeas)
      (selfImprovementError params eps delta) :=
  SymModel.ConsRel.mono
    (final_fields_projective_residual_error_le_selfImprovementError
      params eps delta heps heps_le_one hdelta hdelta_le_one hd_le_q)
    (final_fields_point_consistency_natural_of_total_expectation_le
      params strategy eps delta hhelperPoint hdata hTotalLe)

/-- Natural-error point-consistency transport from operator right-total
monotonicity.

The operator inequality `H.total ≤ Hhat.total` implies the scalar right-total
comparison after placing both operators on the right tensor factor and taking
expectation in the shared state. -/
theorem final_fields_point_consistency_natural_of_total_operator_le
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    {Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    {H : ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    (hhelperPoint :
      strategy.state.ConsRel (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params Hhat)
        (selfImprovementHelperError params eps delta))
    (hdata :
      strategy.state.SDDRel (uniformDistribution (Point params))
        (IdxSubMeas.liftLeft strategy.state (polynomialEvaluationFamily params Hhat))
        (IdxSubMeas.liftLeft strategy.state (polynomialEvaluationFamily params H.toSubMeas))
        (selfImprovementDataProcessingError params eps delta))
    (hTotalLe : H.toSubMeas.total ≤ Hhat.total) :
    strategy.state.ConsRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params H.toSubMeas)
      (selfImprovementHelperError params eps delta +
        Real.sqrt (selfImprovementDataProcessingError params eps delta)) :=
  final_fields_point_consistency_natural_of_total_expectation_le
    params strategy eps delta hhelperPoint hdata
    (strategy.state.ev_mono _ _ (strategy.state.rightTensor_mono hTotalLe))

/-- Literal-threshold point-consistency transport from operator right-total
monotonicity and the standard small-error hypotheses.

This is the operator-order version of
`final_fields_point_consistency_of_total_expectation_le_of_small_errors`. -/
theorem final_fields_point_consistency_of_total_operator_le_of_small_errors
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : ℝ) ≤ (params.q : ℝ))
    {Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    {H : ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    (hhelperPoint :
      strategy.state.ConsRel (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params Hhat)
        (selfImprovementHelperError params eps delta))
    (hdata :
      strategy.state.SDDRel (uniformDistribution (Point params))
        (IdxSubMeas.liftLeft strategy.state (polynomialEvaluationFamily params Hhat))
        (IdxSubMeas.liftLeft strategy.state (polynomialEvaluationFamily params H.toSubMeas))
        (selfImprovementDataProcessingError params eps delta))
    (hTotalLe : H.toSubMeas.total ≤ Hhat.total) :
    strategy.state.ConsRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params H.toSubMeas)
      (selfImprovementError params eps delta) :=
  SymModel.ConsRel.mono
    (final_fields_projective_residual_error_le_selfImprovementError
      params eps delta heps heps_le_one hdelta hdelta_le_one hd_le_q)
    (final_fields_point_consistency_natural_of_total_operator_le
      params strategy eps delta hhelperPoint hdata hTotalLe)

/-- Literal-threshold point-consistency transport with the data-processing
estimate.

This is the theorem required by upstream issue #1240.  The remaining analytical
route is carried by `final_fields_point_consistency_natural_of_total_le`
and the standard small-error absorption bound; no additional
`sqrt (#F_q * selfImprovementDataProcessingError)` term is absorbed here. -/
theorem final_fields_point_consistency_totalGap_of_data_processing
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : ℝ) ≤ (params.q : ℝ))
    {Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    {H : ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    (hhelperPoint :
      strategy.state.ConsRel (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params Hhat)
        (selfImprovementHelperError params eps delta))
    (hdata :
      strategy.state.SDDRel (uniformDistribution (Point params))
        (IdxSubMeas.liftLeft strategy.state (polynomialEvaluationFamily params Hhat))
        (IdxSubMeas.liftLeft strategy.state (polynomialEvaluationFamily params H.toSubMeas))
        (selfImprovementDataProcessingError params eps delta))
    (hTotalLe :
      strategy.state.ev (strategy.state.R H.toSubMeas.total) ≤
        strategy.state.ev (strategy.state.R Hhat.total)) :
    strategy.state.ConsRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params H.toSubMeas)
      (selfImprovementError params eps delta) :=
  final_fields_point_consistency_of_total_expectation_le_of_small_errors
    params strategy eps delta heps heps_le_one hdelta hdelta_le_one hd_le_q
    hhelperPoint hdata hTotalLe

end MIPRE.LIDT.Co.SelfImprovement

end

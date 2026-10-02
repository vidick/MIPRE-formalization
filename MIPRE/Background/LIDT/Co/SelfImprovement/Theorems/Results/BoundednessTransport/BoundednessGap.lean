/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
SelfImprovement/Theorems/Results/BoundednessTransport/BoundednessGap.lean, to the symmetric model
of `planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Results.BoundednessTransport.PointConsistencyLiteral

@[expose] public section

/-!
# Boundedness transport boundedness-gap estimates

The helper boundedness-gap decomposition, its data-processing transport, and the final
projective-residual boundedness constructors of the self-improvement proof: the counterpart of
the vendored `SelfImprovement/Theorems/Results/BoundednessTransport/BoundednessGap.lean` (under
`MIPRE/Background/LIDT/MIPStarRE/LDT/`) in the port of `planning/c6b-plan.md` (milestone M10,
section "Port conventions").

## Contents

- `helper_boundedness_gap_eq_upper_gap_add_off_diagonal_avg`: the helper gap is
  `⟨Z ⊗ I⟩ - ⟨I ⊗ H.total⟩` plus the averaged off-diagonal mass; with it the helper-stage bounds
  `helper_boundedness_gap_le_selfImprovementHelperError`, `…_of_pointConsistencyAddInU_transfer`
  and `…_of_helper_outputs`, and the comparison
  `helper_upper_gap_rightTensor_le_three_sqrt_delta_of_helper_outputs`.
- `helper_boundedness_gap_transport_through_data_processing`: replacing `Hhat` by the projective
  `H` costs `√ε`.
- `projective_boundedness_gap_le_helper_boundedness_gap`: the SDP dual-slack comparison.
- `final_fields_projective_residual_bound_natural`, `…_bound`, `…_of_small_errors` and
  `…_of_helper_outputs`: the projective residual at the natural and the literal error.
- `final_fields_bounded`: `1 ≤ Z` gives `BoundedByOperator` at every nonnegative tolerance.

The translation is that of `BoundednessTransport/PointConsistency.lean`: a strategy is a
`SymStrat params 𝔓 K`, `opTensor A B` is `strategy.state.opTensor A B`, `leftTensor (ι₂ := ι) X`
and `rightTensor (ι₁ := ι) X` are `strategy.state.L X` and `strategy.state.R X`, `ev strategy.state`
is `strategy.state.ev`, the lifts `F.liftLeft`, `F.liftRight` are `IdxSubMeas.liftLeft
strategy.state F`, `IdxSubMeas.liftRight strategy.state F` (and `SubMeas.liftLeft S A` for a single
submeasurement), `helperUpperOperator params Z` is `helperUpperOperator strategy.state params Z`,
and `Error` is `ℝ`.

The vendored swap `strategy.permInvState.swap_ev Hhat.total` is the keystone's
`strategy.state.ev_L_eq_ev_R Hhat.total`; the vendored `sddRel_liftRight_of_liftLeft_permInv
strategy.permInvState …` is M8's `MakingMeasurementsProjective.sddRel_liftRight_of_liftLeft_permInv
strategy.state …`; the vendored `strategy.isNormalized` argument of
`Preliminaries.easyApproxFromApproxDelta` is dropped, the ported lemma taking none. In
`final_fields_bounded` the vendored `(ψ : QuantumState (ι × ι))` is the model `(S : SymModel 𝔓 K)`,
an explicit first argument, and `Matrix.PosSemidef.one.nonneg` is `zero_le_one`. The hypotheses
`hslack : ∀ h, T_h A_h = T_h Z` are SDP complementary slackness passed through, of unchanged
shape. No statement of the vendored file carries a swap, density or normalization hypothesis, so
no statement changed beyond the translation; the file sets no option, the vendored file-wide
`respectTransparency false` not being needed.

The classical threshold lemmas `helper_boundedness_error_le_selfImprovementHelperError` (vendored
`Thresholds/Helper.lean`) and `final_fields_projective_residual_error_le_selfImprovementError`
(vendored `Thresholds/Final.lean`) are imported; the imports mirror the vendored one.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/self_improvement.tex` lines 612--613 and 742--755
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.SelfImprovement

open MIPStarRE.LDT (Parameters FieldModel Point Fq avgOver uniformDistribution avgOver_congr
  avgOver_sum uniformDistribution_weight_sum_le_one)
open MIPStarRE.LDT.SelfImprovement (addInUError selfImprovementVarianceError
  selfImprovementHelperError selfImprovementDataProcessingError selfImprovementError
  pointConsistencyAddInUSelection helper_boundedness_error_le_selfImprovementHelperError
  final_fields_projective_residual_error_le_selfImprovementError)
open MIPRE.LIDT.Co.GlobalVariance (pointConditionedOutcomeOperatorAtPolynomial)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Algebraic decomposition of the helper boundedness gap.

The scalar gap `⟨Z ⊗ I - helperAgreementAverageOperator⟩` is the sum of
`⟨Z ⊗ I⟩ - ⟨I ⊗ H.total⟩` and the off-diagonal average produced by
`helper_boundedness_slack_average_ev_eq_off_diagonal_avg`. -/
theorem helper_boundedness_gap_eq_upper_gap_add_off_diagonal_avg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (H : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (Z : 𝔓) :
    helperBoundednessGap params strategy H Z =
      (strategy.state.ev (helperUpperOperator strategy.state params Z) -
          strategy.state.ev (strategy.state.R H.total)) +
        avgOver (uniformDistribution (Point params)) (fun u =>
          ∑ h : MIPStarRE.LDT.Polynomial params,
            ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
              strategy.state.ev
                (strategy.state.opTensor ((strategy.pointMeasurement u).outcome a)
                  (H.outcome h))) := by
  rw [← helper_boundedness_slack_average_ev_eq_off_diagonal_avg params strategy H,
    helperBoundednessGap, helperBoundednessOperator, strategy.state.ev_sub]
  ring

/-- Helper-stage boundedness from the scalar comparison and the off-diagonal estimate.

The comparison `⟨Z ⊗ I⟩ - ⟨I ⊗ Hhat.total⟩ ≤ 3 √δ` and the off-diagonal estimate
`≤ 4 √ζ_variance` give the helper threshold, by
`helper_boundedness_error_le_selfImprovementHelperError`. -/
theorem helper_boundedness_gap_le_selfImprovementHelperError
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    {Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Z : 𝔓}
    (hZ_vs_H :
      strategy.state.ev (helperUpperOperator strategy.state params Z) -
          strategy.state.ev (strategy.state.R Hhat.total) ≤
        3 * Real.sqrt delta)
    (hoffdiag :
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : MIPStarRE.LDT.Polynomial params,
          ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
            strategy.state.ev
              (strategy.state.opTensor ((strategy.pointMeasurement u).outcome a)
                (Hhat.outcome h))) ≤
        4 * Real.sqrt (selfImprovementVarianceError params eps delta)) :
    helperBoundednessGap params strategy Hhat Z ≤
      selfImprovementHelperError params eps delta := by
  rw [helper_boundedness_gap_eq_upper_gap_add_off_diagonal_avg]
  exact (add_le_add hZ_vs_H hoffdiag).trans
    (helper_boundedness_error_le_selfImprovementHelperError params eps delta heps hdelta)

/-- Helper-stage boundedness from the scalar comparison and the point-consistency `add-in-u`
transfer: the off-diagonal estimate of `pointConsistencyAddInU_off_diagonal_avg_le_of_transfer`
composed with `helper_boundedness_gap_le_selfImprovementHelperError`. -/
theorem helper_boundedness_gap_le_selfImprovementHelperError_of_pointConsistencyAddInU_transfer
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    {T Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Z : 𝔓}
    (hZ_vs_H :
      strategy.state.ev (helperUpperOperator strategy.state params Z) -
          strategy.state.ev (strategy.state.R Hhat.total) ≤
        3 * Real.sqrt delta)
    (htransfer :
      |addInULeftQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          Hhat
          (pointConsistencyAddInUSelection params) -
        addInURightQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          T
          (pointConsistencyAddInUSelection params)| ≤ addInUError params eps delta) :
    helperBoundednessGap params strategy Hhat Z ≤
      selfImprovementHelperError params eps delta := by
  have hoffdiag :=
    pointConsistencyAddInU_off_diagonal_avg_le_of_transfer
      params strategy eps delta T Hhat htransfer
  exact helper_boundedness_gap_le_selfImprovementHelperError
    params strategy eps delta heps hdelta hZ_vs_H
    (hoffdiag.trans_eq (congrArg (4 * ·) (Real.sqrt_eq_rpow _).symm))

/-- Convert the helper-completeness `Hhat`-versus-`Z` comparison to the right-placed total
comparison used in the boundedness gap.

The helper-completeness paragraph proves `⟨Z ⊗ I⟩ - 3√δ ≤ subMeasMass (Hhat.liftLeft S)`; the
swap symmetry of the model, `S.ev_L_eq_ev_R`, turns the left-placed total into the right-placed
one. -/
theorem helper_upper_gap_rightTensor_le_three_sqrt_delta_of_helper_outputs
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    {T : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Z : 𝔓}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hssc : strategy.state.BipartiteSSCRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta)
    (hslack :
      ∀ h : MIPStarRE.LDT.Polynomial params,
        T.toSubMeas.outcome h * averagedPointOperator params strategy h =
          T.toSubMeas.outcome h * Z) :
    strategy.state.ev (helperUpperOperator strategy.state params Z) -
        strategy.state.ev (strategy.state.R Hhat.total) ≤
      3 * Real.sqrt delta := by
  have hleft :=
    helper_hhat_vs_z_of_self_consistency_and_complementary_slackness
      params strategy eps delta hhelper hssc hslack
  have hswap := strategy.state.ev_L_eq_ev_R Hhat.total
  change strategy.state.ev (strategy.state.L Z) - 3 * Real.sqrt delta ≤
    strategy.state.ev (strategy.state.L Hhat.total) at hleft
  change strategy.state.ev (strategy.state.L Z) - _ ≤ _
  linarith

/-- Helper-stage boundedness from the helper comparison and the point-consistency `add-in-u`
transfer.

Complementary slackness `hslack` and the off-diagonal transfer `htransfer` remain explicit
hypotheses, as in the vendored statement. -/
theorem helper_boundedness_gap_le_selfImprovementHelperError_of_helper_outputs
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    {T : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Z : 𝔓}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hssc : strategy.state.BipartiteSSCRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta)
    (hslack :
      ∀ h : MIPStarRE.LDT.Polynomial params,
        T.toSubMeas.outcome h * averagedPointOperator params strategy h =
          T.toSubMeas.outcome h * Z)
    (htransfer :
      |addInULeftQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          Hhat
          (pointConsistencyAddInUSelection params) -
        addInURightQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          T.toSubMeas
          (pointConsistencyAddInUSelection params)| ≤ addInUError params eps delta) :
    helperBoundednessGap params strategy Hhat Z ≤
      selfImprovementHelperError params eps delta :=
  helper_boundedness_gap_le_selfImprovementHelperError_of_pointConsistencyAddInU_transfer
    params strategy eps delta heps hdelta
    (helper_upper_gap_rightTensor_le_three_sqrt_delta_of_helper_outputs
      params strategy eps delta hhelper hssc hslack)
    htransfer

/-- Transport the helper boundedness gap through the data-processing approximation between
`Hhat` and `H`: replacing the helper polynomial family in the point-agreement average by the
projective family costs at most `√ε` (Proposition `easy-approx-from-approx-delta`). -/
theorem helper_boundedness_gap_transport_through_data_processing
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (H : ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (Z : 𝔓)
    (ε : ℝ)
    (hdata :
      strategy.state.SDDRel (uniformDistribution (Point params))
        (IdxSubMeas.liftLeft strategy.state (polynomialEvaluationFamily params Hhat))
        (IdxSubMeas.liftLeft strategy.state (polynomialEvaluationFamily params H.toSubMeas))
        ε) :
    helperBoundednessGap params strategy H.toSubMeas Z ≤
      helperBoundednessGap params strategy Hhat Z + Real.sqrt ε := by
  have happrox :=
    Preliminaries.easyApproxFromApproxDelta strategy.state.toVecState
      (uniformDistribution (Point params))
      (uniformDistribution_weight_sum_le_one (Point params))
      (IdxSubMeas.liftRight strategy.state (polynomialEvaluationFamily params Hhat))
      (IdxSubMeas.liftRight strategy.state (polynomialEvaluationFamily params H.toSubMeas))
      (IdxSubMeas.liftLeft strategy.state (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      ε
      (MakingMeasurementsProjective.sddRel_liftRight_of_liftLeft_permInv strategy.state
        (uniformDistribution (Point params)) (polynomialEvaluationFamily params Hhat)
        (polynomialEvaluationFamily params H.toSubMeas) ε hdata)
  have hterm : ∀ G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓,
      strategy.state.ev (helperAgreementAverageOperator params strategy G) =
        avgOver (uniformDistribution (Point params)) (fun u =>
          ∑ a : Fq params, strategy.state.toVecState.ev
            ((IdxSubMeas.liftRight strategy.state (polynomialEvaluationFamily params G) u).outcome
                a *
              (IdxSubMeas.liftLeft strategy.state
                (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u).outcome a)) := fun G =>
    (helper_agreement_average_ev_eq_avg params strategy G).trans <|
      avgOver_congr (uniformDistribution (Point params)) _ _ fun _ =>
        Finset.sum_congr rfl fun _ _ => congrArg strategy.state.ev
          (strategy.state.rightTensor_mul_leftTensor_eq_opTensor _ _).symm
  rw [← hterm, ← hterm] at happrox
  rw [helperBoundednessGap, helperBoundednessGap, helperBoundednessOperator,
    helperBoundednessOperator, strategy.state.ev_sub, strategy.state.ev_sub]
  linarith [le_abs_self
    (strategy.state.ev (helperAgreementAverageOperator params strategy Hhat) -
      strategy.state.ev (helperAgreementAverageOperator params strategy H.toSubMeas))]

/-- Compare the final projective residual with the helper boundedness gap for the same
projective family.

This is the SDP dual-slack step of the projective boundedness paragraph: `Z ⊗ H_h` dominates
`(E_u A^u_{h(u)}) ⊗ H_h` for each polynomial `h`, and summing turns `Z ⊗ (I - H)` into the
helper-stage defect `Z ⊗ I - E_u Σ_a A^u_a ⊗ H_[h(u)=a]`. -/
theorem projective_boundedness_gap_le_helper_boundedness_gap
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (H : ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (Z : 𝔓)
    (hdual :
      ∀ h : MIPStarRE.LDT.Polynomial params,
        0 ≤ sdpDualSlackOperator params strategy Z h) :
    projectiveBoundednessGap params strategy H Z ≤
      helperBoundednessGap params strategy H.toSubMeas Z := by
  have hprojective_eq :
      projectiveBoundednessGap params strategy H Z =
        strategy.state.ev (strategy.state.L Z) -
          ∑ h : MIPStarRE.LDT.Polynomial params,
            strategy.state.ev (strategy.state.opTensor Z (H.toSubMeas.outcome h)) := by
    rw [projectiveBoundednessGap, projectiveResidualOperator, ← strategy.state.rightTensor_sub,
      strategy.state.rightTensor_one, mul_sub, mul_one, strategy.state.ev_sub,
      ← H.toSubMeas.sum_eq_total, ← strategy.state.ev_sum]
    exact congrArg (fun X => strategy.state.ev (strategy.state.L Z) - strategy.state.ev X)
      (strategy.state.opTensor_sum_right_univ Z _)
  have hhelper_eq :
      helperBoundednessGap params strategy H.toSubMeas Z =
        strategy.state.ev (strategy.state.L Z) -
          ∑ h : MIPStarRE.LDT.Polynomial params,
            strategy.state.ev
              (strategy.state.opTensor (averagedPointOperator params strategy h)
                (H.toSubMeas.outcome h)) := by
    rw [helperBoundednessGap, helperBoundednessOperator, strategy.state.ev_sub,
      helper_agreement_average_ev_eq_polynomial_sum, avgOver_sum]
    refine congrArg (strategy.state.ev (strategy.state.L Z) - ·)
      (Finset.sum_congr rfl fun h _ => ?_)
    exact (strategy.state.ev_opTensor_averageOperatorOverDistribution_left
      (uniformDistribution (Point params))
      (pointConditionedOutcomeOperatorAtPolynomial params strategy h)
      (H.toSubMeas.outcome h)).symm
  have hsum_le :
      (∑ h : MIPStarRE.LDT.Polynomial params,
          strategy.state.ev
            (strategy.state.opTensor (averagedPointOperator params strategy h)
              (H.toSubMeas.outcome h))) ≤
        ∑ h : MIPStarRE.LDT.Polynomial params,
          strategy.state.ev (strategy.state.opTensor Z (H.toSubMeas.outcome h)) :=
    Finset.sum_le_sum fun h _ => strategy.state.ev_mono _ _ <|
      strategy.state.opTensor_mono_left (sub_nonneg.mp (hdual h)) (H.toSubMeas.outcome_pos h)
  rw [hprojective_eq, hhelper_eq]
  linarith

/-- Natural-error projective-residual construction.

Given the helper-stage boundedness estimate for `Hhat`, the dual-slack comparison and the
data-processing transport give the final projective residual at the natural error
`selfImprovementHelperError + √selfImprovementDataProcessingError`.

**Paper source:** `references/ldt-paper/self_improvement.tex` lines 742--755. -/
theorem final_fields_projective_residual_bound_natural
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    {T : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    {H : ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Z : 𝔓}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hhelperBounded :
      helperBoundednessGap params strategy Hhat Z ≤
        selfImprovementHelperError params eps delta)
    (hdata :
      strategy.state.SDDRel (uniformDistribution (Point params))
        (IdxSubMeas.liftLeft strategy.state (polynomialEvaluationFamily params Hhat))
        (IdxSubMeas.liftLeft strategy.state (polynomialEvaluationFamily params H.toSubMeas))
        (selfImprovementDataProcessingError params eps delta)) :
    projectiveBoundednessGap params strategy H Z ≤
      selfImprovementHelperError params eps delta +
        Real.sqrt (selfImprovementDataProcessingError params eps delta) :=
  (projective_boundedness_gap_le_helper_boundedness_gap params strategy H Z
      hhelper.sdpWitness.dualFeasible).trans <|
    (helper_boundedness_gap_transport_through_data_processing params strategy Hhat H Z
      (selfImprovementDataProcessingError params eps delta) hdata).trans <|
      add_le_add_left hhelperBounded _

/-- Literal-threshold projective-residual construction: the natural bound followed by a
separately named numerical absorption `habsorb`.

**Paper source:** `references/ldt-paper/self_improvement.tex` lines 742--755. -/
theorem final_fields_projective_residual_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    {T : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    {H : ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Z : 𝔓}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hhelperBounded :
      helperBoundednessGap params strategy Hhat Z ≤
        selfImprovementHelperError params eps delta)
    (hdata :
      strategy.state.SDDRel (uniformDistribution (Point params))
        (IdxSubMeas.liftLeft strategy.state (polynomialEvaluationFamily params Hhat))
        (IdxSubMeas.liftLeft strategy.state (polynomialEvaluationFamily params H.toSubMeas))
        (selfImprovementDataProcessingError params eps delta))
    (habsorb :
      selfImprovementHelperError params eps delta +
          Real.sqrt (selfImprovementDataProcessingError params eps delta) ≤
        selfImprovementError params eps delta) :
    projectiveBoundednessGap params strategy H Z ≤
      selfImprovementError params eps delta :=
  le_trans
    (final_fields_projective_residual_bound_natural params strategy eps delta
      hhelper hhelperBounded hdata)
    habsorb

/-- Literal-threshold projective-residual construction under the standard unit-interval
smallness hypotheses, the absorption being
`final_fields_projective_residual_error_le_selfImprovementError`.

**Paper source:** `references/ldt-paper/self_improvement.tex` lines 742--755. -/
theorem final_fields_projective_residual_bound_of_small_errors
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : ℝ) ≤ (params.q : ℝ))
    {T : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    {H : ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Z : 𝔓}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hhelperBounded :
      helperBoundednessGap params strategy Hhat Z ≤
        selfImprovementHelperError params eps delta)
    (hdata :
      strategy.state.SDDRel (uniformDistribution (Point params))
        (IdxSubMeas.liftLeft strategy.state (polynomialEvaluationFamily params Hhat))
        (IdxSubMeas.liftLeft strategy.state (polynomialEvaluationFamily params H.toSubMeas))
        (selfImprovementDataProcessingError params eps delta)) :
    projectiveBoundednessGap params strategy H Z ≤
      selfImprovementError params eps delta :=
  final_fields_projective_residual_bound params strategy eps delta hhelper hhelperBounded hdata
    (final_fields_projective_residual_error_le_selfImprovementError params eps delta
      heps heps_le_one hdelta hdelta_le_one hd_le_q)

/-- Final projective-residual construction from helper outputs and the point-consistency
`add-in-u` transfer: the helper-stage bound of
`helper_boundedness_gap_le_selfImprovementHelperError_of_helper_outputs`, then
`final_fields_projective_residual_bound_of_small_errors`.

**Paper source:** `references/ldt-paper/self_improvement.tex` lines 742--755. -/
theorem final_fields_projective_residual_bound_of_helper_outputs
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : ℝ) ≤ (params.q : ℝ))
    {T : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    {H : ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Z : 𝔓}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hssc : strategy.state.BipartiteSSCRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta)
    (hslack :
      ∀ h : MIPStarRE.LDT.Polynomial params,
        T.toSubMeas.outcome h * averagedPointOperator params strategy h =
          T.toSubMeas.outcome h * Z)
    (htransfer :
      |addInULeftQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          Hhat
          (pointConsistencyAddInUSelection params) -
        addInURightQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          T.toSubMeas
          (pointConsistencyAddInUSelection params)| ≤ addInUError params eps delta)
    (hdata :
      strategy.state.SDDRel (uniformDistribution (Point params))
        (IdxSubMeas.liftLeft strategy.state (polynomialEvaluationFamily params Hhat))
        (IdxSubMeas.liftLeft strategy.state (polynomialEvaluationFamily params H.toSubMeas))
        (selfImprovementDataProcessingError params eps delta)) :
    projectiveBoundednessGap params strategy H Z ≤
      selfImprovementError params eps delta :=
  final_fields_projective_residual_bound_of_small_errors
    params strategy eps delta heps heps_le_one hdelta hdelta_le_one hd_le_q hhelper
    (helper_boundedness_gap_le_selfImprovementHelperError_of_helper_outputs
      params strategy eps delta heps hdelta hhelper hssc hslack htransfer)
    hdata

/-- Final-fields constructor for the `BoundedByOperator` conclusion.

If `1 ≤ Z`, the left-placed mass of any submeasurement is dominated by `Z ⊗ I`: `A.total ≤ 1 ≤ Z`
lifts by monotonicity of `S.L` and of `ev`, so `bndError (A.liftLeft S) (Z ⊗ I) = 0` and the
boundedness statement holds at any nonnegative tolerance. -/
theorem final_fields_bounded
    {α : Type*} [Fintype α]
    (S : SymModel 𝔓 K)
    (A : SubMeas α 𝔓)
    {Z : 𝔓}
    (hOne : (1 : 𝔓) ≤ Z)
    {ε : ℝ}
    (hε : 0 ≤ ε) :
    S.BoundedByOperator (A.liftLeft S) (S.L Z) ε := by
  refine ⟨S.leftTensor_nonneg (zero_le_one.trans hOne), ?_⟩
  have hev : S.ev (S.L A.total) ≤ S.ev (S.L Z) :=
    S.ev_mono _ _ (S.leftTensor_mono (A.total_le_one.trans hOne))
  change max 0 (S.ev (S.L A.total) - S.ev (S.L Z)) ≤ ε
  rw [max_eq_left (by linarith)]
  exact hε

end MIPRE.LIDT.Co.SelfImprovement

end

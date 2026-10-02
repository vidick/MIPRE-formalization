/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
SelfImprovement/Theorems/Results/SelfImprovementTop/Core.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Basic.SubMeasurementFamilies
public import MIPRE.Background.LIDT.Co.MakingMeasurementsProjective.Orthonormalization
public import MIPRE.Background.LIDT.Co.Preliminaries.SelfConsistency.DataProcessing
public import MIPRE.Background.LIDT.MIPStarRE.LDT.SelfImprovement.Theorems.Thresholds.Final
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Statements
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Results.CommonHelpers
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Results.HelperCompleteness.Bracketed
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Results.HelperSSC.Assembly
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Results.BoundednessTransport.BoundednessGap
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Results.SelfImprovementTop.FinalFields
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.AddInUFullStatement

@[expose] public section

/-!
# Self-improvement theorem variants

The helper lemma `selfImprovementHelper` and the theorem `selfImprovement`
(`thm:self-improvement`), the top of milestone M10: the counterpart of the vendored
`SelfImprovement/Theorems/Results/SelfImprovementTop/Core.lean` (under
`MIPRE/Background/LIDT/MIPStarRE/LDT/`) in the port of `planning/c6b-plan.md` (section "Port
conventions").

## Contents

- `self_improvement_helper_with_slackness_of_sdp_statement_with_slackness` and
  `self_improvement_helper_with_slackness`: the slackness-carrying helper conclusion, from a
  given SDP statement and from the SDP producer.
- `selfImprovementHelper`: `lem:self-improvement-helper`, the four helper conclusions.
- `selfImprovement_of_error_ge_one`: the trivial large-error branch.
- `selfImprovement`: `thm:self-improvement`.
- `selfImprovement_of_axisParallel_selfConsistency`: the same, with `gamma` free.

## Translation

A strategy is a `SymStrat params 𝔓 K`, `Polynomial params` is
`MIPStarRE.LDT.Polynomial params`, `Z : MIPStarRE.Quantum.Op ι` is `Z : 𝔓`, `Error` is `ℝ`,
`ev strategy.state (leftTensor (ι₂ := ι) X)` is `strategy.state.ev (strategy.state.L X)` (and
`rightTensor`, `R`), `A.liftLeft` is `A.liftLeft strategy.state`, and the relations
(`ConsRel`, `BipartiteSSCRel`, `SDDRel`, `CompletenessAtLeast`) are read on `strategy.state`.
Swap symmetry and normalization are theorems of the model: the four vendored
`strategy.permInvState.swap_ev` rewrites are `strategy.state.ev_L_eq_ev_R`,
`ev_one_of_isNormalized strategy.state strategy.isNormalized` is
`strategy.state.ev_one_of_isNormalized`, `bipartiteConsError_uniform_le_one` takes no
normalization, and M3's `Preliminaries.completenessTransferProjectiveP`,
`completenessTransferSelfConsistentA` and `selfConsistencyImpliesDataProcessing` take neither
`strategy.permInvState` nor `strategy.isNormalized`. The vendored `change` steps between
`constSubMeasFamily A.liftLeft`, `IdxSubMeas.liftLeft (constSubMeasFamily A)` and M8's
`constSubMeasFamily (A.map S.L)` hold by definitional equality and are gone. The vendored
file-wide `respectTransparency false` is not needed, and the file sets no option.

## Proofs that differ from the vendored ones

- `selfImprovement` is split, for elaboration time, into the private
  `selfImprovement_main` (the branch `eps ≤ 1`, `delta ≤ 1`, `d ≤ q`) and
  `selfImprovement_totalDifference` (the two completeness transfers giving the bound on
  `|⟨ψ, I ⊗ H.total⟩ - ⟨ψ, I ⊗ Hhat.total⟩|`); its three large-error branches share one
  `hlarge`, `1 ≤ finalStagePowerSum → 1 ≤ selfImprovementError` by
  `one_le_mul_of_one_le_of_one_le`, in place of three `nlinarith` calls.
- The `addInU` point transfer, computed twice in the vendored file (in `selfImprovementHelper`
  and in `selfImprovement`), is the private `helper_pointTransfer`.
- The vendored `simpa [SymStrat.selfConsistencyFailureProbability] using
  hgood.selfConsistencyTest` is `⟨hgood.selfConsistencyTest⟩`, and the zero-measurement
  computations of `selfImprovement_of_error_ge_one` are `map_zero`/`map_one` and `ev_zero`/
  `ev_one_of_isNormalized` on the placements, in place of entrywise `simp`.

## Three new hypotheses

The vendored in-core orthonormalization (`MakingMeasurementsProjective.orthonormalization ψ
permInvState isNormalized`, finite-dimensional, at any `ζ ≥ 0`) is M8's Theorem G,
`MakingMeasurementsProjective.orthonormalization S hS hA Hhat ζ hζ`, and the vendored SDP
producer (finite-dimensional Slater duality) is M9's summed form, Theorem 10, through Co
`sdp_statement_with_slackness params strategy hS`. So, each placed right after `strategy`, as M8
places `hS hA` right after `S`:

- `hS : strategy.state.toBipartite.IsFinitePair`, for Theorem 10 (the SDP, which uses the
  faithful trace of a finite pair) and for Theorem G. `self_improvement_helper_with_slackness`
  and `selfImprovementHelper` take `hS` only, since they do not orthonormalize;
- `hA : NoAbelianProj strategy.state.toBipartite.opsA`, for Theorem G (T1, orthonormalization
  without abelian projections);
- `hd : 1 ≤ params.d`, which gives `ζ = selfImprovementHelperError params eps delta > 0`
  (`selfImprovementHelperError_pos`), T1's hypothesis being strict. The case `ζ = 0` is neither
  proved nor needed. Only the main branch (`eps ≤ 1`, `delta ≤ 1`, `d ≤ q`) uses `hd`; the
  large-error branches are the vendored ones.

`selfImprovement` and `selfImprovement_of_axisParallel_selfConsistency` take all three. M13
discharges `hS` and `hA` for the doubled model `D(M)` (`Doubling.isFinitePair`,
`Doubling.noAbelianProj_iff`), and M14 supplies `hd` from `SoundIn`. M4's
`AnswerMainInductionHypothesis` carries `hS` and `hA` but not `1 ≤ params.d`: M12 must thread
`hd` as a hypothesis on `params`, which is constant along the induction, only `m` changing.

## Not ported

Every declaration of the vendored file has a counterpart here.

## New here

- `selfImprovementHelperError_pos`: `0 < selfImprovementHelperError params eps delta` when
  `1 ≤ params.d`, the `ζ > 0` of the in-core orthonormalization.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/self_improvement.tex`
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.SelfImprovement

open MIPStarRE.LDT (Parameters FieldModel Point avgOver uniformDistribution
  uniformDistribution_weight_sum_le_one avgOver_uniform_const)
open MIPStarRE.LDT.GlobalVariance (localVarianceOfPointsError)
open MIPStarRE.LDT.SelfImprovement (addInUError selfImprovementVarianceError
  selfImprovementHelperError selfImprovementOrthogonalizationError
  selfImprovementDataProcessingError selfImprovementError pointConsistencyAddInUSelection
  selfImprovementHelperError_eq selfImprovementHelperError_nonneg one_le_m_cast d_q_ratio_nonneg
  selfImprovementDataProcessingError_eq
  final_fields_point_consistency_total_difference_error_le_selfImprovementError
  finalStagePowerSum selfImprovementError_eq_finalStagePowerSum)
open MIPRE.LIDT.Co.GlobalVariance (localVarianceDeviationAtPolynomial
  localVarianceDeviation_sum_le_localVarianceOfPointsError)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The helper-stage threshold `100 m (√ε + √δ + √(d/q))` is positive when `1 ≤ d`, since
`m ≥ 1` and `q > 0`. This is the `ζ > 0` that M8's Theorem G needs at the in-core
orthonormalization of `selfImprovement`. No sign hypothesis on `eps` or `delta` is needed, the
square roots being nonnegative. -/
theorem selfImprovementHelperError_pos (params : Parameters) [FieldModel params.q]
    (eps delta : ℝ) (hd : 1 ≤ params.d) :
    0 < selfImprovementHelperError params eps delta := by
  rw [selfImprovementHelperError_eq]
  have hdq : 0 < Real.sqrt ((params.d : ℝ) / (params.q : ℝ)) :=
    Real.sqrt_pos.2 (div_pos (by exact_mod_cast hd) params.q_cast_pos)
  have hm := one_le_m_cast params
  have := Real.sqrt_nonneg eps
  have := Real.sqrt_nonneg delta
  exact mul_pos (by linarith) (by linarith)

/-- Conditional form of the helper lemma from a slackness-carrying SDP
conclusion.

This is the companion to `selfImprovementHelper` when the Section 9
strong-duality conclusion has already been supplied as
`SdpStatementWithSlackness`.  The helper output therefore carries the
complementary-slackness equations needed by the helper-completeness chain. -/
theorem self_improvement_helper_with_slackness_of_sdp_statement_with_slackness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (hsdp : SdpStatementWithSlackness params strategy)
    (hgood : strategy.IsGood eps delta gamma)
    (_nu : ℝ)
    -- These arguments keep the slackness-carrying conclusion aligned with the
    -- helper theorem; the constructed SDP measurement is independent of `G`.
    (_G : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓) :
    ∃ T : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓,
      ∃ H : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓, ∃ Z : 𝔓,
        SelfImprovementHelperConclusionWithSlackness params strategy T H Z eps delta :=
  let ⟨T, Z, hsdpPair⟩ := hsdp.witness
  ⟨T, averagedSandwichedPolynomialSubMeas params strategy T.toSubMeas, Z,
    { toHelperConclusion :=
        { sdpWitness := hsdpPair.toSdpOptimalPair
          averagedConstruction := rfl
          addInUVarianceBound := addInU params strategy eps delta gamma hgood T }
      complementarySlackness := hsdpPair.complementarySlackness }⟩

/-- Helper lemma driven by the Section 9 SDP statement with complementary
slackness.

This applies the Section 9 statement `sdp_statement_with_slackness`, which
records the strong-duality conclusion with complementary slackness. The vendored producer is
unconditional (finite-dimensional Slater duality); the port's is M9's summed form, Theorem 10,
which uses the faithful trace of a finite pair, hence `hS`. -/
theorem self_improvement_helper_with_slackness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (hS : strategy.state.toBipartite.IsFinitePair)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (nu : ℝ)
    (G : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓) :
    ∃ T : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓,
      ∃ H : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓, ∃ Z : 𝔓,
        SelfImprovementHelperConclusionWithSlackness params strategy T H Z eps delta :=
  self_improvement_helper_with_slackness_of_sdp_statement_with_slackness
    params strategy eps delta gamma
    (sdp_statement_with_slackness params strategy hS)
    hgood nu G

/-- The point-consistency `addInU` transfer of a slackness-carrying helper conclusion: the
selection-dependent transfer of `addInUFullStatement_of_isGood` at the point measurement and
the point-consistency selection, read on `Hhat` through `averagedConstruction`. -/
private theorem helper_pointTransfer
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    {T : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓} {Z : 𝔓}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta) :
    |addInULeftQuantity params strategy
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        Hhat
        (pointConsistencyAddInUSelection params) -
      addInURightQuantity params strategy
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        T.toSubMeas
        (pointConsistencyAddInUSelection params)| ≤ addInUError params eps delta := by
  rw [hhelper.averagedConstruction]
  exact (addInUFullStatement_of_isGood params strategy eps delta gamma hgood T)
    |>.selectionDependentTransfer (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (pointConsistencyAddInUSelection params)

/-- Paper origin: `references/ldt-paper/self_improvement.tex:24-60`
(`\label{lem:self-improvement-helper}`).

Self-improvement helper lemma for a polynomial measurement `G` consistent with
the point measurement. It produces a polynomial submeasurement `H` and a
positive semidefinite witness `Z` satisfying the four conclusions of the paper:
completeness, consistency with `A`, strong self-consistency, and boundedness.
The boundedness conclusion is split into positivity of `Z`, pointwise domination
of the averaged point measurement, and the state-dependent gap estimate.  The
strong-self-consistency branch is proved in this file and is not exposed as an
additional public hypothesis.

The port takes `hS`, for the SDP producer (Theorem 10); it does not orthonormalize, so it takes
neither `hA` nor `1 ≤ params.d`. -/
theorem selfImprovementHelper
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (hS : strategy.state.toBipartite.IsFinitePair)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (nu : ℝ)
    (G : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hcons :
      strategy.state.ConsRel (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas) nu) :
    ∃ H : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓, ∃ Z : 𝔓,
      SelfImprovementHelperStatement params strategy H Z eps delta nu := by
  obtain ⟨T, Hhat, Z, hhelperWithSlackness⟩ :=
    self_improvement_helper_with_slackness params strategy hS eps delta gamma hgood nu G
  have hhelper := hhelperWithSlackness.toHelperConclusion
  have heps : 0 ≤ eps := eps_nonneg_of_isGood params strategy hgood
  have hdelta : 0 ≤ delta := delta_nonneg_of_isGood params strategy hgood
  have hpointSSC :
      strategy.state.BipartiteSSCRel (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta :=
    ⟨hgood.selfConsistencyTest⟩
  have hpointTransfer := helper_pointTransfer params strategy eps delta gamma hgood hhelper
  refine ⟨Hhat, Z,
    { completeness :=
        helper_completeness_of_self_consistency_helper_slackness_input_consistency
          params strategy G eps delta nu heps hdelta hhelperWithSlackness hpointSSC hcons
      pointConsistency :=
        helper_point_consistency_of_pointConsistencyAddInU_transfer
          params strategy eps delta heps hdelta hpointTransfer
      strongSelfConsistency := ?_
      positiveSemidefiniteWitness := hhelper.sdpWitness.dualPositive
      dualDominatesAveragedPoint := hhelper.sdpWitness.dualFeasible
      boundednessGap :=
        helper_boundedness_gap_le_selfImprovementHelperError_of_helper_outputs
          params strategy eps delta heps hdelta hhelper hpointSSC
          (fun h => (hhelperWithSlackness.complementarySlackness h).symm)
          hpointTransfer }⟩
  by_cases hd_le_q : (params.d : ℝ) ≤ (params.q : ℝ)
  · have hlocal :=
      localVarianceDeviation_sum_le_localVarianceOfPointsError
        params strategy eps delta gamma hgood T.toSubMeas
    exact
      helper_strong_self_consistency_of_helper_conclusion
        params strategy eps delta heps hdelta hd_le_q hhelper
        (helper_ssc_bounds_of_scalarTransports_pointTransfer
          params strategy eps delta hhelper hpointSSC hlocal
          (helperDeleteAQuantity_abs_sub_clonedQuantity_le_sqrt
            params strategy eps delta T.toSubMeas hlocal)
          (helperDeleteAClonedQuantity_abs_sub_moveOverVQuantity_le_sqrt_two_delta
            params strategy delta T.toSubMeas hpointSSC)
          (fun h => helper_slackness_eq_of_helper_with_slackness
            params strategy eps delta hhelperWithSlackness h)
          hpointTransfer)
  · have hhelperError_ge_one : 1 ≤ selfImprovementHelperError params eps delta := by
      have hdq_ge_one : 1 ≤ ((params.d : ℝ) / (params.q : ℝ)) :=
        (one_le_div₀ params.q_cast_pos).2 (le_of_lt (lt_of_not_ge hd_le_q))
      have hsqrt_dq_ge_one : 1 ≤ Real.sqrt ((params.d : ℝ) / (params.q : ℝ)) :=
        Real.one_le_sqrt.2 hdq_ge_one
      rw [selfImprovementHelperError_eq]
      nlinarith [one_le_m_cast params, Real.sqrt_nonneg eps, Real.sqrt_nonneg delta]
    have hmatch_nonneg : 0 ≤ strategy.state.qBipartiteMatchMass Hhat Hhat :=
      strategy.state.qBipartiteMatchMass_nonneg Hhat Hhat
    have hmass_le_one : strategy.state.ev (strategy.state.L Hhat.total) ≤ 1 :=
      (strategy.state.ev_mono _ _ (strategy.state.leftTensor_le_one Hhat.total_le_one)).trans_eq
        strategy.state.ev_one_of_isNormalized
    refine ⟨le_trans (le_of_eq_of_le (avgOver_uniform_const (α := Unit) _) ?_)
      hhelperError_ge_one⟩
    change max 0 (strategy.state.ev (strategy.state.L Hhat.total) -
      strategy.state.qBipartiteMatchMass Hhat Hhat) ≤ 1
    exact max_le zero_le_one (by linarith)

/-- Internal large-error fallback for `selfImprovement`.

When the literal threshold `selfImprovementError` is at least `1`, the paper
conclusion is trivial: take the zero projective submeasurement and the identity
dual witness. -/
theorem selfImprovement_of_error_ge_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta gamma nu : ℝ)
    (_hgood : strategy.IsGood eps delta gamma)
    (G : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓)
    (herror_ge_one : 1 ≤ selfImprovementError params eps delta)
    (hnu_nonneg : 0 ≤ nu) :
    ∃ H : ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝔓, ∃ Z : 𝔓,
      SelfImprovementConclusion params strategy G H Z eps delta gamma nu := by
  have hL0 : strategy.state.L 0 = 0 := map_zero _
  have hR0 : strategy.state.R 0 = 0 := map_zero _
  refine ⟨MakingMeasurementsProjective.zeroProjSubMeas, 1,
    { completeness := ⟨?_⟩
      pointConsistency :=
        SymModel.ConsRel.mono herror_ge_one
          ⟨strategy.state.bipartiteConsError_uniform_le_one
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
            (polynomialEvaluationFamily params
              (MakingMeasurementsProjective.zeroProjSubMeas (R := 𝔓)).toSubMeas)⟩
      selfCloseness := ⟨?_⟩
      positiveSemidefiniteWitness := zero_le_one
      dualDominatesAveragedPoint := fun g =>
        sub_nonneg.mpr (averagedPointOperator_le_one params strategy g)
      projectiveResidualBound := ?_ }⟩
  · change (1 - nu) - selfImprovementError params eps delta ≤ strategy.state.ev (strategy.state.L 0)
    rw [hL0, strategy.state.ev_zero]
    linarith
  · change avgOver (uniformDistribution Unit) (fun _ => ∑ a,
      strategy.state.ev (star (strategy.state.L 0 - strategy.state.R 0) *
        (strategy.state.L 0 - strategy.state.R 0))) ≤ selfImprovementError params eps delta
    simp only [hL0, hR0, sub_zero, mul_zero, strategy.state.ev_zero, Finset.sum_const_zero,
      avgOver_uniform_const]
    linarith
  · change strategy.state.ev (strategy.state.L 1 * strategy.state.R (1 - 0)) ≤
      selfImprovementError params eps delta
    rw [sub_zero, map_one, map_one, mul_one, strategy.state.ev_one_of_isNormalized]
    exact herror_ge_one

/-- The total-difference bound of the main branch of `selfImprovement`, from the helper's strong
self-consistency and the orthonormalization SDD bound: the two completeness transfers (projective
and self-consistent), each moved to the second factor by `ev_L_eq_ev_R`. Split out of
`selfImprovement` for elaboration time. -/
private theorem selfImprovement_totalDifference
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    {Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    {H : ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    (hhelperSSC :
      strategy.state.BipartiteSSCRel (uniformDistribution Unit)
        (constSubMeasFamily Hhat)
        (selfImprovementHelperError params eps delta))
    (horth :
      strategy.state.SDDRel (uniformDistribution Unit)
        (constSubMeasFamily (Hhat.liftLeft strategy.state))
        (constSubMeasFamily (H.toSubMeas.liftLeft strategy.state))
        (selfImprovementOrthogonalizationError params eps delta)) :
    |strategy.state.ev (strategy.state.R H.toSubMeas.total) -
      strategy.state.ev (strategy.state.R Hhat.total)| ≤
        selfImprovementHelperError params eps delta +
          2 * Real.sqrt (selfImprovementOrthogonalizationError params eps delta) := by
  have hprojectiveUpperGap :
      strategy.state.ev (strategy.state.R H.toSubMeas.total) -
        strategy.state.ev (strategy.state.R Hhat.total) ≤
          2 * Real.sqrt (selfImprovementOrthogonalizationError params eps delta) := by
    have hcomp :=
      (Preliminaries.completenessTransferProjectiveP strategy.state.toVecState
        (uniformDistribution Unit) (uniformDistribution_weight_sum_le_one Unit)
        (constSubMeasFamily (Hhat.liftLeft strategy.state))
        (fun _ => H.liftLeft strategy.state)
        (selfImprovementOrthogonalizationError params eps delta) horth).completenessTransfer
    change avgOver (uniformDistribution Unit)
        (fun _ => strategy.state.ev (strategy.state.L Hhat.total)) ≥
      avgOver (uniformDistribution Unit)
        (fun _ => strategy.state.ev (strategy.state.L H.toSubMeas.total)) - _ at hcomp
    rw [avgOver_uniform_const, avgOver_uniform_const,
      strategy.state.ev_L_eq_ev_R, strategy.state.ev_L_eq_ev_R] at hcomp
    linarith
  have hhelperUpperGap :
      strategy.state.ev (strategy.state.R Hhat.total) -
        strategy.state.ev (strategy.state.R H.toSubMeas.total) ≤
          selfImprovementHelperError params eps delta +
            2 * Real.sqrt (selfImprovementOrthogonalizationError params eps delta) := by
    have hcomp :=
      Preliminaries.completenessTransferSelfConsistentA
        strategy.state (uniformDistribution Unit)
        (uniformDistribution_weight_sum_le_one Unit)
        (constSubMeasFamily Hhat) (constSubMeasFamily H.toSubMeas)
        (selfImprovementHelperError params eps delta)
        (selfImprovementOrthogonalizationError params eps delta)
        hhelperSSC horth
    change avgOver (uniformDistribution Unit)
        (fun _ => strategy.state.ev (strategy.state.L H.toSubMeas.total)) ≥
      avgOver (uniformDistribution Unit)
        (fun _ => strategy.state.ev (strategy.state.L Hhat.total)) - _ - _ at hcomp
    rw [avgOver_uniform_const, avgOver_uniform_const,
      strategy.state.ev_L_eq_ev_R, strategy.state.ev_L_eq_ev_R] at hcomp
    linarith
  exact abs_le.mpr ⟨by linarith, by
    linarith [selfImprovementHelperError_nonneg params eps delta]⟩

/-- The main branch of `selfImprovement` (`eps ≤ 1`, `delta ≤ 1`, `d ≤ q`): the helper with
slackness, the helper's strong self-consistency, M8's orthonormalization (Theorem G, at
`ζ = selfImprovementHelperError params eps delta > 0` by `hd`), data processing and the
final-fields assembly. Split out of `selfImprovement` for elaboration time. -/
private theorem selfImprovement_main
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (hS : strategy.state.toBipartite.IsFinitePair)
    (hA : NoAbelianProj strategy.state.toBipartite.opsA)
    (hd : 1 ≤ params.d)
    (eps delta gamma nu : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (G : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hcons : strategy.state.ConsRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas) nu)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : ℝ) ≤ (params.q : ℝ)) :
    ∃ H : ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝔓, ∃ Z : 𝔓,
      SelfImprovementConclusion params strategy G H Z eps delta gamma nu := by
  obtain ⟨T, Hhat, Z, hhelperWithSlackness⟩ :=
    self_improvement_helper_with_slackness params strategy hS eps delta gamma hgood nu G
  have hhelper := hhelperWithSlackness.toHelperConclusion
  have hpointSSC :
      strategy.state.BipartiteSSCRel (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta :=
    ⟨hgood.selfConsistencyTest⟩
  have htransfer := helper_pointTransfer params strategy eps delta gamma hgood hhelper
  have hhelperCompleteness :
      strategy.state.CompletenessAtLeast (Hhat.liftLeft strategy.state)
        ((1 - nu) - selfImprovementHelperError params eps delta) :=
    helper_completeness_of_self_consistency_helper_slackness_input_consistency
      params strategy G eps delta nu heps hdelta hhelperWithSlackness hpointSSC hcons
  have hlocal :=
    localVarianceDeviation_sum_le_localVarianceOfPointsError
      params strategy eps delta gamma hgood T.toSubMeas
  have hslack :
      ∀ h : MIPStarRE.LDT.Polynomial params,
        T.toSubMeas.outcome h * averagedPointOperator params strategy h =
          T.toSubMeas.outcome h * Z :=
    fun h =>
      helper_slackness_eq_of_helper_with_slackness
        params strategy eps delta hhelperWithSlackness h
  have hhelperSSC :
      strategy.state.BipartiteSSCRel (uniformDistribution Unit)
        (constSubMeasFamily Hhat)
        (selfImprovementHelperError params eps delta) :=
    helper_strong_self_consistency_of_helper_conclusion
      params strategy eps delta heps hdelta hd_le_q hhelper
      (helper_ssc_bounds_of_scalarTransports_pointTransfer
        params strategy eps delta hhelper hpointSSC hlocal
        (helperDeleteAQuantity_abs_sub_clonedQuantity_le_sqrt
          params strategy eps delta T.toSubMeas hlocal)
        (helperDeleteAClonedQuantity_abs_sub_moveOverVQuantity_le_sqrt_two_delta
          params strategy delta T.toSubMeas hpointSSC)
        hslack htransfer)
  obtain ⟨H, horth⟩ :=
    MIPRE.LIDT.Co.MakingMeasurementsProjective.orthonormalization strategy.state hS hA
      Hhat (selfImprovementHelperError params eps delta)
      (selfImprovementHelperError_pos params eps delta hd) hhelperSSC
  have horth' :
      strategy.state.SDDRel (uniformDistribution Unit)
        (constSubMeasFamily (Hhat.liftLeft strategy.state))
        (constSubMeasFamily (H.toSubMeas.liftLeft strategy.state))
        (selfImprovementOrthogonalizationError params eps delta) := horth
  have hTotalDiff :=
    selfImprovement_totalDifference params strategy eps delta hhelperSSC horth'
  have horthPoint :
      strategy.state.SDDRel (uniformDistribution (Point params))
        (IdxSubMeas.liftLeft strategy.state
          (IdxProjSubMeas.toIdxSubMeas (fun _ : Point params => H)))
        (IdxSubMeas.liftLeft strategy.state (fun _ : Point params => Hhat))
        (selfImprovementOrthogonalizationError params eps delta) :=
    sddRel_uniform_const strategy.state.toVecState
      (H.toSubMeas.liftLeft strategy.state) (Hhat.liftLeft strategy.state) _
      (Preliminaries.sddRel_symm strategy.state.toVecState _ _ _ _ horth')
  have hdataRev :
      strategy.state.SDDRel (uniformDistribution (Point params))
        (IdxSubMeas.liftLeft strategy.state
          (polynomialEvaluationFamily params H.toSubMeas))
        (IdxSubMeas.liftLeft strategy.state (polynomialEvaluationFamily params Hhat))
        (selfImprovementDataProcessingError params eps delta) := by
    rw [selfImprovementDataProcessingError_eq params eps delta]
    exact Preliminaries.selfConsistencyImpliesDataProcessing
      strategy.state (uniformDistribution (Point params))
      (uniformDistribution_weight_sum_le_one (Point params))
      (fun _ : Point params => Hhat) (fun _ : Point params => H)
      (selfImprovementHelperError params eps delta)
      (selfImprovementOrthogonalizationError params eps delta)
      (fun u g => g u)
      (bipartiteSSCRel_uniform_const strategy.state Hhat _ hhelperSSC) horthPoint
  have hfinal : SelfImprovementFinalFields params strategy H Z eps delta nu :=
    final_fields_of_helper_outputs_of_total_difference
      params strategy eps delta nu
      (selfImprovementHelperError params eps delta +
        2 * Real.sqrt (selfImprovementOrthogonalizationError params eps delta))
      heps heps_le_one hdelta hdelta_le_one hd_le_q
      hhelper hhelperCompleteness hhelperSSC hpointSSC hslack htransfer
      horth' (Preliminaries.sddRel_symm strategy.state.toVecState _ _ _ _ hdataRev)
      hTotalDiff
      (by
        linarith [final_fields_point_consistency_total_difference_error_le_selfImprovementError
          params eps delta heps heps_le_one hdelta hdelta_le_one hd_le_q])
  exact ⟨H, Z,
    { completeness := hfinal.completeness
      pointConsistency := hfinal.pointConsistency
      selfCloseness := hfinal.selfCloseness
      positiveSemidefiniteWitness := hhelper.sdpWitness.dualPositive
      dualDominatesAveragedPoint := hhelper.sdpWitness.dualFeasible
      projectiveResidualBound := hfinal.projectiveResidualBound }⟩
/--
Formal statement corresponding to the blueprint theorem `thm:self-improvement`,
with the input consistency hypothesis from the LDT paper.

The theorem assumes a measurement `G` whose polynomial evaluation family is
consistent with the point measurement at error `nu`. It must produce a
projective polynomial submeasurement satisfying the four self-improvement
conclusions. The paper and blueprint impose the `(eps, delta, gamma)`-good
strategy condition as a standing hypothesis for the self-improvement section
(`blueprint/src/chapter/ch07_self_improvement.tex`, line 4); Lean records it
here as the explicit hypothesis `hgood`. The source-facing theorem remains
visible with the paper statement; the intermediate estimates are assembled by
named internal construction lemmas rather than hidden in a conditional theorem
with extra hypotheses.

The port adds three hypotheses after `strategy`: `hS` (the model is a finite pair), for the SDP
(Theorem 10) and the orthonormalization (Theorem G); `hA` (no abelian projections in the first
player's operators), for Theorem G; and `hd : 1 ≤ params.d`, which makes the orthonormalization
error `ζ = selfImprovementHelperError params eps delta` positive, as Theorem G (through T1)
requires. M13 discharges `hS` and `hA` for the doubled model, M14 supplies `hd`. -/
theorem selfImprovement
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (hS : strategy.state.toBipartite.IsFinitePair)
    (hA : NoAbelianProj strategy.state.toBipartite.opsA)
    (hd : 1 ≤ params.d)
    (eps delta gamma nu : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (G : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hcons : strategy.state.ConsRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas) nu) :
    ∃ H : ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝔓, ∃ Z : 𝔓,
      SelfImprovementConclusion params strategy G H Z eps delta gamma nu := by
  have heps : 0 ≤ eps := eps_nonneg_of_isGood params strategy hgood
  have hdelta : 0 ≤ delta := delta_nonneg_of_isGood params strategy hgood
  have hnu_nonneg : 0 ≤ nu :=
    (strategy.state.bipartiteConsError_nonneg (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas)).trans hcons.offDiagonalBound
  -- The large-error branches: once one of `eps`, `delta`, `d/q` exceeds `1`, the power sum is at
  -- least `1`, so `selfImprovementError = 3000 m (…) ≥ 1`.
  have hlarge : 1 ≤ finalStagePowerSum params eps delta (1 / (32 : ℝ)) →
      ∃ H : ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝔓, ∃ Z : 𝔓,
        SelfImprovementConclusion params strategy G H Z eps delta gamma nu := fun hsum =>
    selfImprovement_of_error_ge_one params strategy eps delta gamma nu hgood G
      ((selfImprovementError_eq_finalStagePowerSum params eps delta).symm ▸
        one_le_mul_of_one_le_of_one_le (by linarith [one_le_m_cast params]) hsum)
      hnu_nonneg
  have hpow_eps : 0 ≤ Real.rpow eps (1 / (32 : ℝ)) := Real.rpow_nonneg heps _
  have hpow_delta : 0 ≤ Real.rpow delta (1 / (32 : ℝ)) := Real.rpow_nonneg hdelta _
  have hpow_dq : 0 ≤ Real.rpow ((params.d : ℝ) / (params.q : ℝ)) (1 / (32 : ℝ)) :=
    Real.rpow_nonneg (d_q_ratio_nonneg params) _
  by_cases heps_le_one : eps ≤ 1
  · by_cases hdelta_le_one : delta ≤ 1
    · by_cases hd_le_q : (params.d : ℝ) ≤ (params.q : ℝ)
      · exact selfImprovement_main params strategy hS hA hd eps delta gamma nu hgood G hcons
          heps heps_le_one hdelta hdelta_le_one hd_le_q
      · have hdq_pow_ge_one : 1 ≤ Real.rpow ((params.d : ℝ) / (params.q : ℝ)) (1 / (32 : ℝ)) :=
          Real.one_le_rpow ((one_le_div₀ params.q_cast_pos).2 (le_of_not_ge hd_le_q))
            (by positivity)
        exact hlarge (by unfold finalStagePowerSum; linarith)
    · have hdelta_pow_ge_one : 1 ≤ Real.rpow delta (1 / (32 : ℝ)) :=
        Real.one_le_rpow (le_of_not_ge hdelta_le_one) (by positivity)
      exact hlarge (by unfold finalStagePowerSum; linarith)
  · have heps_pow_ge_one : 1 ≤ Real.rpow eps (1 / (32 : ℝ)) :=
      Real.one_le_rpow (le_of_not_ge heps_le_one) (by positivity)
    exact hlarge (by unfold finalStagePowerSum; linarith)

/-- Self-improvement only uses the axis-parallel and point self-consistency
parts of the good-strategy hypothesis.

Paper origin: `references/ldt-paper/self_improvement.tex:24-60` and
`references/ldt-paper/self_improvement.tex:631-811`.

The displayed Section 9 construction is written in terms of the point
measurement \(A^u\), the input polynomial measurement \(G\), and the scalar
bounds `eps` and `delta`; the diagonal-line error parameter `gamma` is part of
the paper's standing good-strategy context but does not occur in
`selfImprovementError` or in `SelfImprovementConclusion`.  This wrapper makes
that independence explicit: it supplies the diagonal component of `IsGood` by
taking the actual diagonal failure as the auxiliary parameter, applies the
source theorem, and then reindexes the conclusion at the caller's `gamma`.

It takes `selfImprovement`'s three model hypotheses `hS`, `hA` and `hd`, after `strategy`. -/
theorem selfImprovement_of_axisParallel_selfConsistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (hS : strategy.state.toBipartite.IsFinitePair)
    (hA : NoAbelianProj strategy.state.toBipartite.opsA)
    (hd : 1 ≤ params.d)
    (eps delta gamma nu : ℝ)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself : strategy.selfConsistencyFailureProbability ≤ delta)
    (G : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hcons : strategy.state.ConsRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas) nu) :
    ∃ H : ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝔓, ∃ Z : 𝔓,
      SelfImprovementConclusion params strategy G H Z eps delta gamma nu :=
  let ⟨H, Z, hHZ⟩ := selfImprovement params strategy hS hA hd eps delta
    strategy.diagonalFailureProbability nu ⟨haxis, hself, le_rfl⟩ G hcons
  ⟨H, Z,
    { completeness := hHZ.completeness
      pointConsistency := hHZ.pointConsistency
      selfCloseness := hHZ.selfCloseness
      positiveSemidefiniteWitness := hHZ.positiveSemidefiniteWitness
      dualDominatesAveragedPoint := hHZ.dualDominatesAveragedPoint
      projectiveResidualBound := hHZ.projectiveResidualBound }⟩

end MIPRE.LIDT.Co.SelfImprovement

end

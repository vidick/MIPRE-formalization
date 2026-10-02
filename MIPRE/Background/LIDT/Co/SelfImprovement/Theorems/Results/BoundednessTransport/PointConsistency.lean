/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
SelfImprovement/Theorems/Results/BoundednessTransport/PointConsistency.lean, to the symmetric
model of `planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.MakingMeasurementsProjective.ProjectivizationChain.Basic
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Results.BoundednessTransport.Decomposition

@[expose] public section

/-!
# Boundedness transport point-consistency estimates

The point-consistency consequences of the helper-agreement off-diagonal decomposition, and the
natural-error transports of point consistency from the helper output to the projective output of
self-improvement: the counterpart of the vendored
`SelfImprovement/Theorems/Results/BoundednessTransport/PointConsistency.lean` (under
`MIPRE/Background/LIDT/MIPStarRE/LDT/`) in the port of `planning/c6b-plan.md` (milestone M10,
section "Port conventions").

## Contents

- `opTensor_one_left_eq_rightTensor`: `S.opTensor 1 B = S.R B`, kept under its vendored name with
  the model `S` an explicit first argument.
- `pointMeasurement_total_evalFamily_total_opTensor_ev_eq_rightTensor` and its `S.L · * S.R ·`
  form: the total-overlap term of the point measurement against an evaluation family is
  `ev (S.R G.total)`.
- `helper_point_consistency_error_eq_off_diagonal_avg`: the bipartite consistency defect of the
  point measurement against `polynomialEvaluationFamily params H` is the averaged off-diagonal
  mass; with it, `helper_point_consistency_of_pointConsistencyAddInU_transfer` and
  `helper_point_consistency_of_selected_chain_selfConsistency_globalVariance`.
- `final_fields_point_consistency_totalGap_natural`, `…_of_total_difference`,
  `final_fields_total_difference_le_sqrt_card_data` and `…_of_data_processing`: the
  submeasurement triangle at the natural error, with the total-overlap displacement explicit,
  as a single scalar difference, or bounded by `√(#F_q · ε)`.

A strategy is a `SymStrat params 𝔓 K`; the point measurement, `H` and `Hhat` are local (in `𝔓`).
The vendored `opTensor A B` is `strategy.state.opTensor A B`, `leftTensor (ι₂ := ι) X *
rightTensor (ι₁ := ι) Y` is `strategy.state.L X * strategy.state.R Y` (the named carrier arguments
dropped), `ev strategy.state` is `strategy.state.ev`, the lifted families `F.liftLeft`,
`F.liftRight` are `IdxSubMeas.liftLeft strategy.state F`, `IdxSubMeas.liftRight strategy.state F`,
and `Error` is `ℝ`.

The two vendored transports from left to right lifts (`sddRel_liftRight_of_liftLeft_permInv
strategy.permInvState …`) call M8's `MakingMeasurementsProjective.sddRel_liftRight_of_liftLeft_permInv
strategy.state …`, which needs no permutation invariance, swap symmetry being a theorem of the
model; the two vendored `strategy.isNormalized` arguments (of
`Preliminaries.triangleSub_right_subMeas_totalGap` and
`Preliminaries.subMeas_total_ev_gap_abs_le_sqrt_card_qSDD`) are dropped, since the ported lemmas
take none. No statement of the vendored file carries a swap, density or normalization hypothesis,
so no statement changed; the file sets no option, the vendored file-wide
`respectTransparency false` not being needed. The argument `S : SubMeas …` of the two
`pointMeasurement_total_evalFamily_total_*` lemmas is named `G` here, `S` being the model.

The imports mirror the vendored ones, with the Co `ProjectivizationChain/Basic` in place of the
vendored file (which it imports for its classical declarations).

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/self_improvement.tex` lines 435 and 747--755
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.SelfImprovement

open MIPStarRE.LDT (Parameters FieldModel Point Fq avgOver uniformDistribution avgOver_congr
  avgOver_const_mul avgOver_uniform_const uniformDistribution_weight_sum_le_one)
open MIPStarRE.LDT.Preliminaries (avgOver_abs_le_sqrt_of_pointwise)
open MIPStarRE.LDT.SelfImprovement (addInUError selfImprovementVarianceError
  selfImprovementHelperError selfImprovementDataProcessingError pointConsistencyAddInUSelection)
open MIPRE.LIDT.Co.GlobalVariance (globalVarianceDeviationAtPolynomial)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The tensor product with the identity on the left register is the right tensor
placement. -/
theorem opTensor_one_left_eq_rightTensor (S : SymModel 𝔓 K) (B : 𝔓) :
    S.opTensor 1 B = S.R B :=
  (congrArg (· * S.R B) S.leftTensor_one).trans (one_mul _)

/-- The point measurement is complete and polynomial evaluation preserves the
right-register total, so the tensor total has the same expectation as the right
placement of the original total. -/
theorem pointMeasurement_total_evalFamily_total_opTensor_ev_eq_rightTensor
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (u : Point params) :
    strategy.state.ev
        (strategy.state.opTensor
          (((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u).total)
          (((polynomialEvaluationFamily params G) u).total)) =
      strategy.state.ev (strategy.state.R G.total) := by
  have hA_total : ((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u).total = 1 :=
    (strategy.pointMeasurement u).total_eq_one
  rw [hA_total]
  exact congrArg strategy.state.ev (opTensor_one_left_eq_rightTensor strategy.state G.total)

/-- Left and right tensor placements of the point-measurement and evaluation
totals reduce to the right-register total expectation. -/
theorem pointMeasurement_total_evalFamily_total_ev_eq_rightTensor
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (u : Point params) :
    strategy.state.ev
        (strategy.state.L (((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u).total) *
          strategy.state.R (((polynomialEvaluationFamily params G) u).total)) =
      strategy.state.ev (strategy.state.R G.total) :=
  pointMeasurement_total_evalFamily_total_opTensor_ev_eq_rightTensor params strategy G u

/-- The helper-stage consistency defect is exactly the averaged off-diagonal
mass appearing in the point-consistency `add-in-u` calculation.

This is the same algebraic identity as
`helper_boundedness_slack_average_ev_eq_off_diagonal_avg`, read as a
`ConsRel` defect for the point measurement against the polynomial-evaluation
family of `H`. -/
theorem helper_point_consistency_error_eq_off_diagonal_avg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (H : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    strategy.state.bipartiteConsError (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params H) =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : MIPStarRE.LDT.Polynomial params,
          ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
            strategy.state.ev
              (strategy.state.opTensor ((strategy.pointMeasurement u).outcome a)
                (H.outcome h))) := by
  refine avgOver_congr (uniformDistribution (Point params)) _ _ fun u => ?_
  have hdiff_eq := helperAgreementOperatorAtPoint_ev_slack_eq_off_diagonal_sum params strategy H u
  have hdiff_nonneg :
      0 ≤ strategy.state.ev (strategy.state.R H.total) -
          strategy.state.ev (helperAgreementOperatorAtPoint params strategy H u) := by
    rw [hdiff_eq]
    exact Finset.sum_nonneg fun h _ => Finset.sum_nonneg fun a _ =>
      strategy.state.ev_nonneg_of_psd _
        (strategy.state.opTensor_nonneg ((strategy.pointMeasurement u).outcome_pos a)
          (H.outcome_pos h))
  have hmatch :
      strategy.state.qBipartiteMatchMass
          ((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u)
          ((polynomialEvaluationFamily params H) u) =
        strategy.state.ev (helperAgreementOperatorAtPoint params strategy H u) :=
    (strategy.state.ev_sum _).symm
  rw [SymModel.qBipartiteConsDefect,
    pointMeasurement_total_evalFamily_total_opTensor_ev_eq_rightTensor, hmatch,
    max_eq_right hdiff_nonneg, hdiff_eq]

/-- Helper-stage point consistency from the point-consistency `add-in-u`
transfer hypothesis.

The transfer bound controls the off-diagonal mass
`E_u ∑_h ∑_{a ≠ h(u)} ⟨ψ, A^u_a ⊗ Hhat_h ψ⟩`.  The preceding algebraic
identity identifies this mass with the `ConsRel` defect for the point
measurement and the polynomial-evaluation family of `Hhat`. -/
theorem helper_point_consistency_of_pointConsistencyAddInU_transfer
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    {T Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    (htransfer :
      |addInULeftQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          Hhat
          (pointConsistencyAddInUSelection params) -
        addInURightQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          T
          (pointConsistencyAddInUSelection params)| ≤ addInUError params eps delta) :
    strategy.state.ConsRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params Hhat)
      (selfImprovementHelperError params eps delta) :=
  ⟨(helper_point_consistency_error_eq_off_diagonal_avg params strategy Hhat).trans_le
    (pointConsistencyAddInU_off_diagonal_avg_le_helper_error_of_transfer
      params strategy eps delta heps hdelta T Hhat htransfer)⟩

/-- Helper-stage point consistency obtained directly from the selected
add-in-`u` chain.

The hypotheses are the two analytic inputs used by the selected four-step
chain: bipartite self-consistency for the point measurement, and the
global-variance sum bound for the polynomial submeasurement `T`.  The helper
submeasurement is the averaged sandwiched polynomial submeasurement built from
`T`, exactly as in the helper-stage application. -/
theorem helper_point_consistency_of_selected_chain_selfConsistency_globalVariance
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
    strategy.state.ConsRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params
        (averagedSandwichedPolynomialSubMeas params strategy T))
      (selfImprovementHelperError params eps delta) :=
  helper_point_consistency_of_pointConsistencyAddInU_transfer params strategy eps delta heps
    hdelta (T := T)
    (pointConsistencyAddInU_transfer_of_selected_chain_selfConsistency_globalVariance
      params strategy eps delta heps hdelta T hssc hglobal)

/-- Natural-error transport of point consistency from the helper output to the
projective output, with the submeasurement total-overlap displacement stated
explicitly.

The measurement-valued right-register triangle lemma has no total-overlap term:
both right-register totals are the identity.  In the present application
`polynomialEvaluationFamily params Hhat` and
`polynomialEvaluationFamily params H.toSubMeas` are only submeasurements, so
the total-overlap term
`⟨ψ, A^u_{\mathrm{tot}} ⊗ H^u_{\mathrm{tot}} ψ⟩` must also be transported.
This theorem separates that displacement as the parameter `η`; the remaining
contribution is exactly the square root of the data-processing SDD error.  The
upstream note `docs/paper-gaps/issue-1093-submeasurement-triangle-total-overlap.tex`
records the corresponding discrepancy with the measurement-valued paper step. -/
theorem final_fields_point_consistency_totalGap_natural
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
                (((polynomialEvaluationFamily params Hhat) u).total))|) ≤ η) :
    strategy.state.ConsRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params H.toSubMeas)
      (selfImprovementHelperError params eps delta +
        Real.sqrt (selfImprovementDataProcessingError params eps delta) + η) :=
  Preliminaries.triangleSub_right_subMeas_totalGap strategy.state
    (uniformDistribution (Point params)) (uniformDistribution_weight_sum_le_one (Point params))
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
    (polynomialEvaluationFamily params Hhat)
    (polynomialEvaluationFamily params H.toSubMeas)
    (selfImprovementHelperError params eps delta)
    (selfImprovementDataProcessingError params eps delta) η hhelperPoint
    (MakingMeasurementsProjective.sddRel_liftRight_of_liftLeft_permInv strategy.state
      (uniformDistribution (Point params)) _ _ _ hdata)
    hTotal

/-- Natural-error point-consistency transport when the total-overlap
displacement is supplied as a single right-register total difference.

Since the point measurement is complete and
`polynomialEvaluationFamily params H` has the same total as `H`, the averaged
total-overlap term in `final_fields_point_consistency_totalGap_natural` is
independent of the point `u`.  This theorem records the corresponding reduction
of the upstream issue #1226 obstruction to the scalar difference between the totals of
the two right-register submeasurements. -/
theorem final_fields_point_consistency_totalGap_natural_of_total_difference
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
        strategy.state.ev (strategy.state.R Hhat.total)| ≤ η) :
    strategy.state.ConsRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params H.toSubMeas)
      (selfImprovementHelperError params eps delta +
        Real.sqrt (selfImprovementDataProcessingError params eps delta) + η) := by
  refine final_fields_point_consistency_totalGap_natural params strategy eps delta η
    hhelperPoint hdata ?_
  rw [avgOver_congr (uniformDistribution (Point params)) _
      (fun _ => |strategy.state.ev (strategy.state.R H.toSubMeas.total) -
        strategy.state.ev (strategy.state.R Hhat.total)|) fun u => by
      rw [pointMeasurement_total_evalFamily_total_ev_eq_rightTensor params strategy
          H.toSubMeas u,
        pointMeasurement_total_evalFamily_total_ev_eq_rightTensor params strategy Hhat u],
    avgOver_uniform_const]
  exact hTotal

/-- The data-processing SDD comparison controls the total-overlap displacement
which appears in the submeasurement form of the point-consistency triangle.

For each point `u`, the right-register total difference is the sum of the
field-answer differences in the two postprocessed polynomial families.  The
finite-outcome Cauchy--Schwarz estimate
`subMeas_total_ev_gap_abs_le_sqrt_card_qSDD`, averaged over `u`, bounds this
single scalar by
`sqrt (#F_q * ε)`.  The factor `#F_q` records the cost of passing from the
outcomewise state-dependent distance to the total operator. -/
theorem final_fields_total_difference_le_sqrt_card_data
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (ε : ℝ)
    {Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    {H : ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    (hdata :
      strategy.state.SDDRel (uniformDistribution (Point params))
        (IdxSubMeas.liftLeft strategy.state (polynomialEvaluationFamily params Hhat))
        (IdxSubMeas.liftLeft strategy.state (polynomialEvaluationFamily params H.toSubMeas))
        ε) :
    |strategy.state.ev (strategy.state.R H.toSubMeas.total) -
      strategy.state.ev (strategy.state.R Hhat.total)| ≤
      Real.sqrt ((Fintype.card (Fq params) : ℝ) * ε) := by
  set 𝒟 := uniformDistribution (Point params)
  set totalGap : ℝ := |strategy.state.ev (strategy.state.R H.toSubMeas.total) -
      strategy.state.ev (strategy.state.R Hhat.total)|
  set g : Point params → ℝ := fun u => (Fintype.card (Fq params) : ℝ) *
    strategy.state.qSDD
      (IdxSubMeas.liftRight strategy.state (polynomialEvaluationFamily params Hhat) u)
      (IdxSubMeas.liftRight strategy.state (polynomialEvaluationFamily params H.toSubMeas) u)
  have hdata_right := MakingMeasurementsProjective.sddRel_liftRight_of_liftLeft_permInv
    strategy.state 𝒟 _ _ _ hdata
  have hpoint (u : Point params) : |totalGap| ≤ Real.sqrt (g u) := by
    have hgap := Preliminaries.subMeas_total_ev_gap_abs_le_sqrt_card_qSDD strategy.state.toVecState
      (IdxSubMeas.liftRight strategy.state (polynomialEvaluationFamily params Hhat) u)
      (IdxSubMeas.liftRight strategy.state (polynomialEvaluationFamily params H.toSubMeas) u)
    rw [abs_sub_comm, ← Real.sqrt_mul (Nat.cast_nonneg _)] at hgap
    rw [abs_abs]
    exact hgap
  have havg := avgOver_abs_le_sqrt_of_pointwise 𝒟 (fun _ => totalGap) g hpoint
    (fun _ => mul_nonneg (Nat.cast_nonneg _) (strategy.state.qSDD_nonneg _ _))
    (uniformDistribution_weight_sum_le_one (Point params))
  rw [avgOver_uniform_const, abs_abs] at havg
  refine havg.trans (Real.sqrt_le_sqrt ?_)
  rw [avgOver_const_mul]
  exact mul_le_mul_of_nonneg_left hdata_right.squaredDistanceBound (Nat.cast_nonneg _)

/-- Natural-error point-consistency transport with the total-overlap
displacement bounded internally from the data-processing SDD estimate.

The price of eliminating the explicit total-difference hypothesis is the
additional term `sqrt (#F_q * selfImprovementDataProcessingError)`. -/
theorem final_fields_point_consistency_totalGap_natural_of_data_processing
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
        (selfImprovementDataProcessingError params eps delta)) :
    strategy.state.ConsRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params H.toSubMeas)
      (selfImprovementHelperError params eps delta +
        Real.sqrt (selfImprovementDataProcessingError params eps delta) +
        Real.sqrt ((Fintype.card (Fq params) : ℝ) *
          selfImprovementDataProcessingError params eps delta)) :=
  final_fields_point_consistency_totalGap_natural_of_total_difference
    params strategy eps delta
    (Real.sqrt ((Fintype.card (Fq params) : ℝ) *
      selfImprovementDataProcessingError params eps delta))
    hhelperPoint hdata
    (final_fields_total_difference_le_sqrt_card_data
      params strategy (selfImprovementDataProcessingError params eps delta) hdata)

end MIPRE.LIDT.Co.SelfImprovement

end

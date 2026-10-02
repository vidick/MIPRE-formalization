/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
SelfImprovement/Theorems/Results/HelperSSC/Assembly.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Results.HelperSSC.PostDeleteA
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Results.BoundednessTransport.BoundednessGap

@[expose] public section

/-!
# Helper strong self-consistency bounds: residual assembly

Residual lower-bound reductions, scalar-chain bound constructors, and the final helper-stage
strong self-consistency assembly theorems: the counterpart of the vendored
`SelfImprovement/Theorems/Results/HelperSSC/Assembly.lean` (under
`MIPRE/Background/LIDT/MIPStarRE/LDT/`) in the port of `planning/c6b-plan.md` (milestone M10,
section "Port conventions").

## Contents

- `helper_residualLowerBound_of_offDiagonal_bound` and
  `helper_residualLowerBound_of_paper_chain_bound`: the residual lower bound of
  `HelperStrongSelfConsistencyBounds` from a bound on the bare off-diagonal quantity.
- `helperMoveOverVQuantity_lower_of_pointConsistencyAddInU_transfer`: the `eq:move-over-v`
  lower bound, from complementary slackness, dual feasibility and the point-consistency transfer.
- `helperOffDiagonalBareQuantity_le_paper_chain_of_scalar_transports`: the residual chain
  `7√ζ_variance + √(2δ) + md/q` from the scalar transports.
- The four constructors of `HelperStrongSelfConsistencyBounds`
  (`…_offDiagonal`, `…_paperChain`, `…_scalarTransports`,
  `helper_ssc_bounds_of_scalarTransports_pointTransfer`), and the closing
  `helper_strong_self_consistency_of_helper_conclusion`.

A strategy is a `SymStrat params 𝔓 K`; the polynomial measurement `T`, the helper `Hhat`, the
dual witness `Z` and the point projectors live in `𝔓`, and every scalar is `strategy.state.ev`
of a joint operator `strategy.state.opTensor X Y`; `rightTensor (ι₁ := ι) X` is
`strategy.state.R X`, `subMeasMass strategy.state Hhat.liftLeft` is
`strategy.state.subMeasMass (Hhat.liftLeft strategy.state)`, `BipartiteSSCRel strategy.state …`
and `qBipartiteMatchMass strategy.state …` are the `SymModel` declarations, and `Error` is `ℝ`.

**Complementary slackness.** The hypothesis `hslack : ∀ h, T_h A_h = T_h Z` of
`helperMoveOverVQuantity_lower_of_pointConsistencyAddInU_transfer` and
`helper_ssc_bounds_of_scalarTransports_pointTransfer` keeps its vendored shape in `𝔓`. In the
`eq:move-over-v` computation it rewrites `T_h A_h` to `T_h Z` in the right factor of
`∑_{h'} ∑_h ev(H^u_{h'} ⊗ T_h A_h)`, and `∑_h T_h Z = Z` comes from `T.total_eq_one`, with
`one_mul` and `Finset.sum_mul` for the vendored `Matrix.one_mul` and `Matrix.mul_sum`.
`helper_strong_self_consistency_of_helper_conclusion` calls no SDP producer (its SDP witness
arrives inside `SelfImprovementHelperConclusion`), so it keeps its vendored hypotheses.

**Swap and density uses.** The vendored `ev_opTensor_swap_of_density_fixed strategy.state
strategy.densityFixed _ _` (vendored line 388) is the keystone's
`strategy.state.ev_opTensor_swap_of_density_fixed _ _`, and the vendored
`strategy.permInvState.swap_ev Hhat.total` (vendored line 419) is
`strategy.state.ev_L_eq_ev_R Hhat.total`. No statement of the vendored file carries a swap,
density or normalization hypothesis, so no statement changed beyond the translation.

**Proofs that differ from the vendored ones.**
- In `helperMoveOverVQuantity_lower_of_pointConsistencyAddInU_transfer` the agreement average is
  computed per polynomial, `avg_v ev(A^v_{h(v)} ⊗ H_h) = ev(A_h ⊗ H_h) = avg_u ev(A_h ⊗ H^u_h)`,
  through Co `ev_opTensor_averageOperatorOverDistribution_left`/`_right`, without the vendored
  exchange of the two point averages (`avgOver_uniform_comm`); the identity
  `E_v T_h A^v_{h(v)} = T_h A_h` is `Finset.mul_sum` and `mul_smul_comm` on the definition.
- In `helper_strong_self_consistency_of_helper_conclusion` the closing `simpa` through the
  defect definitions is `avgOver_uniform_const` on `Unit`, the defect being
  `max 0 (mass - match)` by definition.
- `helper_residualLowerBound_of_paper_chain_bound` rewrites `addInUError` with
  `Real.sqrt_eq_rpow` and closes by `linarith`.
- `helperOffDiagonalBareQuantity_le_paper_chain_of_scalar_transports` collects the five Co
  identities and bounds it needs and closes by one `linarith`, without the vendored local
  abbreviations and `simpa` steps.
- The four vendored `lemma`s are `theorem`s, and the three constructors that only apply other
  constructors are terms.

The file sets no option, the vendored file-wide `respectTransparency false` not being needed.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/self_improvement.tex`
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.SelfImprovement

open MIPStarRE.LDT (Parameters FieldModel Point Fq avgOver uniformDistribution avgOver_congr
  avgOver_mono avgOver_sum avgOver_uniform_prod avgOver_uniform_const)
open MIPStarRE.LDT.GlobalVariance (localVarianceOfPointsError)
open MIPStarRE.LDT.SelfImprovement (selfImprovementVarianceError addInUError
  selfImprovementHelperError selfConsistencyAddInUSelection pointConsistencyAddInUSelection
  helper_strong_self_consistency_error_le_selfImprovementHelperError
  selfImprovementHelperError_nonneg)
open MIPRE.LIDT.Co.GlobalVariance (pointConditionedOutcomeOperatorAtPolynomial
  localVarianceDeviationAtPolynomial)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Reduce the residual lower bound to the off-diagonal residual scalar
bound.

For the actual helper output, the equality
`Hhat = E_u A^u_{h(u)} T_h A^u_{h(u)}` identifies the left-hand side of
`HelperStrongSelfConsistencyBounds.residualLowerBound` with the
off-diagonal quantity isolated by
`helper_mass_sub_release_eq_polynomial_off_diagonal`.  Thus the remaining
analytic work may be stated as a bound on that concrete polynomial-pair sum,
rather than as a direct bound on the record field itself. -/
theorem helper_residualLowerBound_of_offDiagonal_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    {T : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Z : 𝔓}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hoffdiag :
      helperOffDiagonalBareQuantity params strategy T.toSubMeas ≤
        (11 * Real.sqrt (selfImprovementVarianceError params eps delta) +
            Real.sqrt (2 * delta) +
            ((params.m : ℝ) * (params.d : ℝ) / (params.q : ℝ))) -
          addInUError params eps delta) :
    strategy.state.subMeasMass (Hhat.liftLeft strategy.state) -
        addInURightQuantity params strategy
          (sandwichedPolynomialSubMeasAt params strategy T.toSubMeas)
          T.toSubMeas
          (selfConsistencyAddInUSelection params) ≤
      (11 * Real.sqrt (selfImprovementVarianceError params eps delta) +
          Real.sqrt (2 * delta) +
          ((params.m : ℝ) * (params.d : ℝ) / (params.q : ℝ))) -
        addInUError params eps delta := by
  rw [hhelper.averagedConstruction, helper_mass_sub_release_eq_polynomial_off_diagonal]
  exact hoffdiag

/-- Reduce the residual lower bound to the paper-shaped residual-chain bound.

After `eq:release-the-kraken`, `eq:threw-in-h-prime`, `eq:delete-an-A`, and
`eq:move-over-v`, the paper bounds the expanded residual by
`7√ζ_variance + √(2δ) + md/q`.  Since
`addInUError = 4√ζ_variance`, this is exactly the pre-absorption bound
`11√ζ_variance + √(2δ) + md/q - addInUError`. -/
theorem helper_residualLowerBound_of_paper_chain_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    {T : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Z : 𝔓}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hoffdiag :
      helperOffDiagonalBareQuantity params strategy T.toSubMeas ≤
        7 * Real.sqrt (selfImprovementVarianceError params eps delta) +
          Real.sqrt (2 * delta) +
          ((params.m : ℝ) * (params.d : ℝ) / (params.q : ℝ))) :
    strategy.state.subMeasMass (Hhat.liftLeft strategy.state) -
        addInURightQuantity params strategy
          (sandwichedPolynomialSubMeasAt params strategy T.toSubMeas)
          T.toSubMeas
          (selfConsistencyAddInUSelection params) ≤
      (11 * Real.sqrt (selfImprovementVarianceError params eps delta) +
          Real.sqrt (2 * delta) +
          ((params.m : ℝ) * (params.d : ℝ) / (params.q : ℝ))) -
        addInUError params eps delta := by
  refine helper_residualLowerBound_of_offDiagonal_bound params strategy eps delta hhelper ?_
  have hsqrt : Real.rpow (selfImprovementVarianceError params eps delta) (1 / 2 : ℝ) =
      Real.sqrt (selfImprovementVarianceError params eps delta) :=
    (Real.sqrt_eq_rpow _).symm
  rw [addInUError, hsqrt]
  linarith

-- This transport lower bound expands the post-delete and move-over-v scalar
-- quantities before applying the variance-transfer estimates.
/-- Paper line `eq:move-over-v` yields a lower bound on the moved quantity in
terms of the helper mass and the explicit `A`-consistency defect.

This is the algebraic/slackness part of `self_improvement.tex:579-589`: average
over `v`, replace `T_h · E_v A^v_{h(v)}` by `T_h · Z` using complementary
slackness, collapse the `T`-sum to `Z`, compare `Z` to the averaged point
operator by dual feasibility, and then subtract the off-diagonal helper
agreement defect controlled by the point-consistency `add-in-u` transfer. -/
theorem helperMoveOverVQuantity_lower_of_pointConsistencyAddInU_transfer
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    {T : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Z : 𝔓}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
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
    strategy.state.subMeasMass (Hhat.liftLeft strategy.state) ≤
      helperMoveOverVQuantity params strategy T.toSubMeas + addInUError params eps delta := by
  -- `E_v T_h A^v_{h(v)} = T_h A_h`.
  have hmul_avg : ∀ h : MIPStarRE.LDT.Polynomial params,
      averageOperatorOverDistribution (uniformDistribution (Point params))
          (fun v => T.toSubMeas.outcome h *
            pointConditionedOutcomeOperatorAtPolynomial params strategy h v) =
        T.toSubMeas.outcome h * averagedPointOperator params strategy h := fun h => by
    simp only [averagedPointOperator, averageOperatorOverDistribution, Finset.mul_sum,
      mul_smul_comm]
  -- Average over `v`, use slackness, and collapse the `T`-sum to `Z`.
  have hmove_eq :
      helperMoveOverVQuantity params strategy T.toSubMeas =
        avgOver (uniformDistribution (Point params)) (fun u =>
          ∑ h' : MIPStarRE.LDT.Polynomial params,
            strategy.state.ev (strategy.state.opTensor
              ((sandwichedPolynomialSubMeasAt params strategy T.toSubMeas u).outcome h') Z)) := by
    refine (avgOver_uniform_prod (α := Point params) (β := Point params) (fun u v =>
        ∑ h : MIPStarRE.LDT.Polynomial params, ∑ h' : MIPStarRE.LDT.Polynomial params,
          strategy.state.ev (strategy.state.opTensor
            ((sandwichedPolynomialSubMeasAt params strategy T.toSubMeas u).outcome h')
            (T.toSubMeas.outcome h *
              pointConditionedOutcomeOperatorAtPolynomial params strategy h v)))).trans
      (avgOver_congr _ _ _ fun u => ?_)
    rw [avgOver_sum]
    calc
      _ = ∑ h : MIPStarRE.LDT.Polynomial params, ∑ h' : MIPStarRE.LDT.Polynomial params,
            strategy.state.ev (strategy.state.opTensor
              ((sandwichedPolynomialSubMeasAt params strategy T.toSubMeas u).outcome h')
              (T.toSubMeas.outcome h * Z)) :=
          Finset.sum_congr rfl fun h _ => by
            rw [avgOver_sum]
            refine Finset.sum_congr rfl fun h' _ => ?_
            rw [← strategy.state.ev_opTensor_averageOperatorOverDistribution_right, hmul_avg h,
              hslack h]
      _ = ∑ h' : MIPStarRE.LDT.Polynomial params, ∑ h : MIPStarRE.LDT.Polynomial params,
            strategy.state.ev (strategy.state.opTensor
              ((sandwichedPolynomialSubMeasAt params strategy T.toSubMeas u).outcome h')
              (T.toSubMeas.outcome h * Z)) := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun h' _ => by
          rw [← strategy.state.ev_sum, ← strategy.state.opTensor_sum_right_univ,
            ← Finset.sum_mul, T.toSubMeas.sum_eq_total, T.total_eq_one, one_mul]
  -- The agreement average, computed per polynomial.
  have hagree_eq :
      strategy.state.ev (helperAgreementAverageOperator params strategy Hhat) =
        avgOver (uniformDistribution (Point params)) (fun u =>
          ∑ h : MIPStarRE.LDT.Polynomial params,
            strategy.state.ev (strategy.state.opTensor
              ((sandwichedPolynomialSubMeasAt params strategy T.toSubMeas u).outcome h)
              (averagedPointOperator params strategy h))) := by
    rw [hhelper.averagedConstruction, helper_agreement_average_ev_eq_polynomial_sum,
      avgOver_sum, avgOver_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    calc
      _ = strategy.state.ev (strategy.state.opTensor (averagedPointOperator params strategy h)
            ((averagedSandwichedPolynomialSubMeas params strategy T.toSubMeas).outcome h)) :=
          (strategy.state.ev_opTensor_averageOperatorOverDistribution_left _
            (pointConditionedOutcomeOperatorAtPolynomial params strategy h) _).symm
      _ = avgOver (uniformDistribution (Point params)) (fun u =>
            strategy.state.ev (strategy.state.opTensor (averagedPointOperator params strategy h)
              ((sandwichedPolynomialSubMeasAt params strategy T.toSubMeas u).outcome h))) :=
          strategy.state.ev_opTensor_averageOperatorOverDistribution_right _ _
            (fun u => (sandwichedPolynomialSubMeasAt params strategy T.toSubMeas u).outcome h)
      _ = _ := avgOver_congr _ _ _ fun u =>
          strategy.state.ev_opTensor_swap_of_density_fixed _ _
  -- Dual feasibility: `A_h ≤ Z`.
  have hmove_ge :
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : MIPStarRE.LDT.Polynomial params,
          strategy.state.ev (strategy.state.opTensor
            ((sandwichedPolynomialSubMeasAt params strategy T.toSubMeas u).outcome h)
            (averagedPointOperator params strategy h))) ≤
        helperMoveOverVQuantity params strategy T.toSubMeas := by
    rw [hmove_eq]
    refine avgOver_mono _ _ _ fun u => Finset.sum_le_sum fun h _ => ?_
    exact strategy.state.ev_mono _ _ <| strategy.state.opTensor_mono_right
      ((sandwichedPolynomialSubMeasAt params strategy T.toSubMeas u).outcome_pos h)
      (sub_nonneg.mp (hhelper.sdpWitness.dualFeasible h))
  have hoffdiag :=
    pointConsistencyAddInU_off_diagonal_avg_le_of_transfer
      params strategy eps delta T.toSubMeas Hhat htransfer
  have hdecomp := helper_boundedness_slack_average_ev_eq_off_diagonal_avg params strategy Hhat
  have hmass_eq :
      strategy.state.subMeasMass (Hhat.liftLeft strategy.state) =
        strategy.state.ev (strategy.state.R Hhat.total) :=
    strategy.state.ev_L_eq_ev_R Hhat.total
  rw [hmass_eq]
  linarith

/-- Assemble the paper's final residual-chain estimate from the displayed scalar
transport bounds.

The first two hypotheses are the two variance swaps used to pass from
`eq:added-indicator` to the Schwartz--Zippel endpoint.  The next two hypotheses
are the transports from `eq:delete-an-A` to `eq:move-over-v`.  The final
hypothesis is the lower bound on the `move-over-v` endpoint obtained after
substituting the averaged operator `Z` and using the explicit point-consistency
bound for the point measurement. -/
theorem helperOffDiagonalBareQuantity_le_paper_chain_of_scalar_transports
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    {T : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Z : 𝔓}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hleft :
      |helperOffDiagonalIndicatorQuantity params strategy T.toSubMeas -
        helperOffDiagonalOneSidedSwappedIndicatorQuantity params strategy T.toSubMeas| ≤
          Real.sqrt (selfImprovementVarianceError params eps delta))
    (hright :
      |helperOffDiagonalOneSidedSwappedIndicatorQuantity params strategy T.toSubMeas -
        helperOffDiagonalSwappedIndicatorQuantity params strategy T.toSubMeas| ≤
          Real.sqrt (selfImprovementVarianceError params eps delta))
    (hclone :
      |helperDeleteAQuantity params strategy T.toSubMeas -
        helperDeleteAClonedQuantity params strategy T.toSubMeas| ≤
          Real.sqrt (selfImprovementVarianceError params eps delta))
    (hmove :
      |helperDeleteAClonedQuantity params strategy T.toSubMeas -
        helperMoveOverVQuantity params strategy T.toSubMeas| ≤
          Real.sqrt (2 * delta))
    (hmoveLower :
      strategy.state.subMeasMass (Hhat.liftLeft strategy.state) ≤
        helperMoveOverVQuantity params strategy T.toSubMeas +
          4 * Real.sqrt (selfImprovementVarianceError params eps delta)) :
    helperOffDiagonalBareQuantity params strategy T.toSubMeas ≤
      7 * Real.sqrt (selfImprovementVarianceError params eps delta) +
        Real.sqrt (2 * delta) +
        ((params.m : ℝ) * (params.d : ℝ) / (params.q : ℝ)) := by
  have houter :=
    helperOffDiagonalOuterSandwichQuantity_le_two_sqrt_variance_add_mdq_of_abs_transports
      params strategy eps delta T.toSubMeas hleft hright
  have hmove_to_delete :=
    helperMoveOverVQuantity_le_deleteA_of_abs_transports
      params strategy eps delta T.toSubMeas hclone hmove
  have hfull_delete := helperFullOuterSandwichQuantity_eq_deleteAQuantity
    params strategy T.toSubMeas
  have hfull_split :=
    helperFullOuterSandwichQuantity_eq_release_add_offDiagonalOuterSandwichQuantity
      params strategy T.toSubMeas
  have hresidual := helper_mass_sub_release_eq_polynomial_off_diagonal params strategy T
  rw [← hhelper.averagedConstruction] at hresidual
  have hbare : helperOffDiagonalBareQuantity params strategy T.toSubMeas =
      strategy.state.subMeasMass (Hhat.liftLeft strategy.state) -
        addInURightQuantity params strategy
          (sandwichedPolynomialSubMeasAt params strategy T.toSubMeas)
          T.toSubMeas
          (selfConsistencyAddInUSelection params) := hresidual.symm
  rw [hbare]
  linarith

/-- Construct the helper-stage bounds from local variance and a named
off-diagonal residual estimate.

This produces the same named bounds as
`helper_strong_self_consistency_bounds_of_selfConsistency_localVariance`,
but its final input is the concrete off-diagonal polynomial-pair bound obtained
after expanding the released residual. -/
theorem helper_strong_self_consistency_bounds_of_selfConsistency_localVariance_offDiagonal
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    {T : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Z : 𝔓}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hssc : strategy.state.BipartiteSSCRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta)
    (hlocal :
      (∑ g : MIPStarRE.LDT.Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state T.toSubMeas g) ≤
        localVarianceOfPointsError params eps delta)
    (hoffdiag :
      helperOffDiagonalBareQuantity params strategy T.toSubMeas ≤
        (11 * Real.sqrt (selfImprovementVarianceError params eps delta) +
            Real.sqrt (2 * delta) +
            ((params.m : ℝ) * (params.d : ℝ) / (params.q : ℝ))) -
          addInUError params eps delta) :
    HelperStrongSelfConsistencyBounds params strategy T Hhat eps delta :=
  helper_strong_self_consistency_bounds_of_selfConsistency_localVariance
    params strategy eps delta hssc hlocal
    (helper_residualLowerBound_of_offDiagonal_bound
      params strategy eps delta hhelper hoffdiag)

/-- Construct the helper-stage bounds from the paper's final residual
chain estimate.

This variant lets downstream work target the paper's natural bound
`7√ζ_variance + √(2δ) + md/q` on the expanded off-diagonal residual.  The
conversion to the record's `11√ζ_variance + √(2δ) + md/q - addInUError`
form is performed internally. -/
theorem helper_strong_self_consistency_bounds_of_selfConsistency_localVariance_paperChain
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    {T : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Z : 𝔓}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hssc : strategy.state.BipartiteSSCRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta)
    (hlocal :
      (∑ g : MIPStarRE.LDT.Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state T.toSubMeas g) ≤
        localVarianceOfPointsError params eps delta)
    (hoffdiag :
      helperOffDiagonalBareQuantity params strategy T.toSubMeas ≤
        7 * Real.sqrt (selfImprovementVarianceError params eps delta) +
          Real.sqrt (2 * delta) +
          ((params.m : ℝ) * (params.d : ℝ) / (params.q : ℝ))) :
    HelperStrongSelfConsistencyBounds params strategy T Hhat eps delta :=
  helper_strong_self_consistency_bounds_of_selfConsistency_localVariance
    params strategy eps delta hssc hlocal
    (helper_residualLowerBound_of_paper_chain_bound
      params strategy eps delta hhelper hoffdiag)

/-- Construct the helper-stage bounds directly from the scalar
transport estimates appearing in the paper.

Compared with
`helper_strong_self_consistency_bounds_of_selfConsistency_localVariance_paperChain`,
this version does not ask for the already assembled residual-chain estimate.
It consumes the two off-diagonal variance swaps, the two post-`delete-an-A`
transports, and the final lower bound on the `move-over-v` endpoint, then
assembles the residual estimate internally. -/
theorem helper_strong_self_consistency_bounds_of_selfConsistency_localVariance_scalarTransports
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    {T : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Z : 𝔓}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hssc : strategy.state.BipartiteSSCRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta)
    (hlocal :
      (∑ g : MIPStarRE.LDT.Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state T.toSubMeas g) ≤
        localVarianceOfPointsError params eps delta)
    (hleft :
      |helperOffDiagonalIndicatorQuantity params strategy T.toSubMeas -
        helperOffDiagonalOneSidedSwappedIndicatorQuantity params strategy T.toSubMeas| ≤
          Real.sqrt (selfImprovementVarianceError params eps delta))
    (hright :
      |helperOffDiagonalOneSidedSwappedIndicatorQuantity params strategy T.toSubMeas -
        helperOffDiagonalSwappedIndicatorQuantity params strategy T.toSubMeas| ≤
          Real.sqrt (selfImprovementVarianceError params eps delta))
    (hclone :
      |helperDeleteAQuantity params strategy T.toSubMeas -
        helperDeleteAClonedQuantity params strategy T.toSubMeas| ≤
          Real.sqrt (selfImprovementVarianceError params eps delta))
    (hmove :
      |helperDeleteAClonedQuantity params strategy T.toSubMeas -
        helperMoveOverVQuantity params strategy T.toSubMeas| ≤
          Real.sqrt (2 * delta))
    (hmoveLower :
      strategy.state.subMeasMass (Hhat.liftLeft strategy.state) ≤
        helperMoveOverVQuantity params strategy T.toSubMeas +
          4 * Real.sqrt (selfImprovementVarianceError params eps delta)) :
    HelperStrongSelfConsistencyBounds params strategy T Hhat eps delta :=
  helper_strong_self_consistency_bounds_of_selfConsistency_localVariance_paperChain
    params strategy eps delta hhelper hssc hlocal
    (helperOffDiagonalBareQuantity_le_paper_chain_of_scalar_transports
      params strategy eps delta hhelper hleft hright hclone hmove hmoveLower)

/-- Construct the helper-stage bounds from the paper's scalar transports and
the point-consistency add-in-`u` transfer.

This is the same residual-chain constructor as
`helper_strong_self_consistency_bounds_of_selfConsistency_localVariance_scalarTransports`,
but it discharges the two off-diagonal variance swaps from local variance and
the final `move-over-v` lower-bound input from complementary slackness, dual
feasibility, and the point-consistency transfer. It packages the paper lines
after `eq:move-over-v` together with the two post-`delete-an-A` scalar
transports. -/
theorem helper_ssc_bounds_of_scalarTransports_pointTransfer
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    {T : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Z : 𝔓}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hssc : strategy.state.BipartiteSSCRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta)
    (hlocal :
      (∑ g : MIPStarRE.LDT.Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state T.toSubMeas g) ≤
        localVarianceOfPointsError params eps delta)
    (hclone :
      |helperDeleteAQuantity params strategy T.toSubMeas -
        helperDeleteAClonedQuantity params strategy T.toSubMeas| ≤
          Real.sqrt (selfImprovementVarianceError params eps delta))
    (hmove :
      |helperDeleteAClonedQuantity params strategy T.toSubMeas -
        helperMoveOverVQuantity params strategy T.toSubMeas| ≤
          Real.sqrt (2 * delta))
    (hslack :
      ∀ h : MIPStarRE.LDT.Polynomial params,
        T.toSubMeas.outcome h * averagedPointOperator params strategy h =
          T.toSubMeas.outcome h * Z)
    (hpointTransfer :
      |addInULeftQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          Hhat
          (pointConsistencyAddInUSelection params) -
        addInURightQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          T.toSubMeas
          (pointConsistencyAddInUSelection params)| ≤ addInUError params eps delta) :
    HelperStrongSelfConsistencyBounds params strategy T Hhat eps delta :=
  helper_strong_self_consistency_bounds_of_selfConsistency_localVariance_scalarTransports
    params strategy eps delta hhelper hssc hlocal
    (helperOffDiagonalIndicatorQuantity_abs_sub_oneSidedSwappedIndicator_le_sqrt
      params strategy eps delta T.toSubMeas hlocal)
    (helperOffDiagonalOneSidedSwappedIndicator_abs_sub_swappedIndicator_le_sqrt
      params strategy eps delta T.toSubMeas hlocal)
    hclone hmove
    ((helperMoveOverVQuantity_lower_of_pointConsistencyAddInU_transfer
      params strategy eps delta hhelper hslack hpointTransfer).trans_eq
      (congrArg (_ + 4 * ·) (Real.sqrt_eq_rpow _).symm))

/-- Produce the helper-stage strong self-consistency conclusion from the actual
helper construction together with the named add-in-`u`/variance transports.

The theorem consumes the reduced helper output
`SelfImprovementHelperConclusion params strategy T Hhat Z eps delta` and the
four named scalar chain bounds together with the final lower bound on the
released right-hand side. It then assembles the diagonal transfer
using `add_in_u_simplified_transfer_of_cs_chain_sqrt_form`, upgrades it to the
paper's released right-hand side via
`selfConsistencyDiagonalAddInU_of_simplifiedTransfer`, and applies the closing
arithmetic absorption
`helper_strong_self_consistency_error_le_selfImprovementHelperError`.

This is the complete route from the actual helper construction and the named
scalar bounds to helper-stage strong self-consistency. The analytic work is
therefore stated as named bounds, rather than left as an
unstructured `BipartiteSSCRel` assumption. -/
theorem helper_strong_self_consistency_of_helper_conclusion
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    (hd_le_q : (params.d : ℝ) ≤ (params.q : ℝ))
    {T : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Z : 𝔓}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hbounds : HelperStrongSelfConsistencyBounds
      params strategy T Hhat eps delta) :
    strategy.state.BipartiteSSCRel (uniformDistribution Unit)
      (constSubMeasFamily Hhat)
      (selfImprovementHelperError params eps delta) := by
  have htransfer_release :=
    selfConsistencyDiagonalAddInU_of_simplifiedTransfer
      params strategy eps delta T.toSubMeas
      (add_in_u_simplified_transfer_of_cs_chain_sqrt_form
        params strategy eps delta heps hdelta T.toSubMeas
        hbounds.step01Bound hbounds.step12Bound
        hbounds.step23Bound hbounds.step34Bound)
  rw [← addInURightQuantity_selfConsistencySelection_eq_release,
    ← hhelper.averagedConstruction] at htransfer_release
  have hhelperGap :
      strategy.state.subMeasMass (Hhat.liftLeft strategy.state) -
          strategy.state.qBipartiteMatchMass Hhat Hhat ≤
        selfImprovementHelperError params eps delta := by
    have habsorb :=
      helper_strong_self_consistency_error_le_selfImprovementHelperError
        params eps delta heps hdelta hd_le_q
    linarith [(abs_le.mp htransfer_release).1, hbounds.residualLowerBound]
  exact ⟨(avgOver_uniform_const (α := Unit) _).trans_le
    (max_le (selfImprovementHelperError_nonneg params eps delta) hhelperGap)⟩

end MIPRE.LIDT.Co.SelfImprovement

end

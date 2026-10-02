/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
SelfImprovement/Theorems/Results/SelfImprovementTop/FinalFields.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Results.BoundednessTransport.BoundednessGap
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Results.SelfImprovementTop.Completeness
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Results.SelfImprovementTop.SelfCloseness

@[expose] public section

/-!
# Final-fields assembly routes

The final-fields assembler of the projective self-improvement theorem: the completeness,
point-consistency, self-closeness and projective-residual constructions combined into
`SelfImprovementFinalFields`, with the total-difference route for the point-consistency field.
The counterpart of the vendored
`SelfImprovement/Theorems/Results/SelfImprovementTop/FinalFields.lean` (under
`MIPRE/Background/LIDT/MIPStarRE/LDT/`) in the port of `planning/c6b-plan.md` (milestone M10,
section "Port conventions").

## Contents

- `final_fields_of_helper_outputs_of_total_difference`: `SelfImprovementFinalFields` from the
  helper outputs, the orthonormalization SDD bound, the data-processing bound and a scalar bound
  on the difference of the right totals.

The theorem takes the orthonormalization SDD bound as a hypothesis and calls no
orthonormalization, so it carries no finite-pair, abelian-projection or `ζ > 0` hypothesis.

The translation is that of `BoundednessTransport/BoundednessGap.lean`: a strategy is a
`SymStrat params 𝔓 K`, `Z : MIPStarRE.Quantum.Op ι` is `Z : 𝔓`, `A.liftLeft` is
`A.liftLeft strategy.state`, `(F).liftLeft` on a family is `IdxSubMeas.liftLeft strategy.state F`,
`ev strategy.state (rightTensor (ι₁ := ι) X)` is `strategy.state.ev (strategy.state.R X)`, the
relations are read on `strategy.state`, and `Error` is `ℝ`. The hypothesis `hslack` (SDP
complementary slackness, `T_h A_h = T_h Z` for every `h`) is passed through, of unchanged shape.
No statement of the vendored file carries a swap, density or normalization hypothesis, so the
statement changed only by the translation, and the proof is the vendored one over the ported
pieces; the file sets no option, the vendored file-wide `respectTransparency false` not being
needed. The imports mirror the vendored ones.

## Not ported

Every declaration of the vendored file has a counterpart here.
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.SelfImprovement

open MIPStarRE.LDT (Parameters FieldModel Point uniformDistribution)
open MIPStarRE.LDT.SelfImprovement (addInUError selfImprovementHelperError
  selfImprovementOrthogonalizationError selfImprovementDataProcessingError selfImprovementError
  pointConsistencyAddInUSelection)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Final-fields construction using an explicit right-total-difference bound.

This is the submeasurement-total fallback for the point-consistency field. When the proof supplies
only a scalar bound on `|⟨ψ, I ⊗ H.total⟩ - ⟨ψ, I ⊗ Hhat.total⟩|`, rather than the monotonicity
`⟨ψ, I ⊗ H.total⟩ ≤ ⟨ψ, I ⊗ Hhat.total⟩`, the point-consistency field is assembled through
`final_fields_point_consistency_totalGap_of_total_difference`. The other fields are the
completeness, self-closeness and projective-residual constructions. -/
theorem final_fields_of_helper_outputs_of_total_difference
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta nu η : ℝ)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : ℝ) ≤ (params.q : ℝ))
    {T : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    {H : ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Z : 𝔓}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hhelperCompleteness :
      strategy.state.CompletenessAtLeast (Hhat.liftLeft strategy.state)
        ((1 - nu) - selfImprovementHelperError params eps delta))
    (hhelperSSC :
      strategy.state.BipartiteSSCRel (uniformDistribution Unit)
        (constSubMeasFamily Hhat)
        (selfImprovementHelperError params eps delta))
    (hpointSSC :
      strategy.state.BipartiteSSCRel (uniformDistribution (Point params))
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
    (horth :
      strategy.state.SDDRel (uniformDistribution Unit)
        (constSubMeasFamily (Hhat.liftLeft strategy.state))
        (constSubMeasFamily (H.toSubMeas.liftLeft strategy.state))
        (selfImprovementOrthogonalizationError params eps delta))
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
    SelfImprovementFinalFields params strategy H Z eps delta nu where
  completeness :=
    final_fields_completeness_of_helper_completeness_of_small_errors
      params strategy eps delta nu heps heps_le_one hdelta hdelta_le_one hd_le_q
      Hhat H hhelperCompleteness hhelperSSC horth
  pointConsistency :=
    final_fields_point_consistency_totalGap_of_total_difference
      params strategy eps delta η
      (helper_point_consistency_of_pointConsistencyAddInU_transfer
        params strategy eps delta heps hdelta htransfer)
      hdata hTotal habsorb
  selfCloseness :=
    final_fields_self_closeness_of_small_errors
      params strategy eps delta heps heps_le_one hdelta hdelta_le_one hd_le_q
      Hhat H hhelperSSC horth
  projectiveResidualBound :=
    final_fields_projective_residual_bound_of_helper_outputs
      params strategy eps delta heps heps_le_one hdelta hdelta_le_one hd_le_q
      hhelper hpointSSC hslack htransfer hdata

end MIPRE.LIDT.Co.SelfImprovement

end

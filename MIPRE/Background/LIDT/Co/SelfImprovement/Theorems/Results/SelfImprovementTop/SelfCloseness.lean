/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
SelfImprovement/Theorems/Results/SelfImprovementTop/SelfCloseness.lean, to the symmetric model
of `planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Basic.SubMeasurementFamilies
public import MIPRE.Background.LIDT.Co.MakingMeasurementsProjective.ProjectivizationChain.Basic
public import MIPRE.Background.LIDT.Co.Preliminaries.SelfConsistency.DataProcessing
public import MIPRE.Background.LIDT.MIPStarRE.LDT.SelfImprovement.Theorems.Thresholds.Final
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Statements

@[expose] public section

/-!
# Final-fields self-closeness construction

The self-closeness transport that fills the `selfCloseness` field of
`SelfImprovementFinalFields`: the triangle through helper self-consistency and the
orthonormalization SDD step. The counterpart of the vendored
`SelfImprovement/Theorems/Results/SelfImprovementTop/SelfCloseness.lean` (under
`MIPRE/Background/LIDT/MIPStarRE/LDT/`) in the port of `planning/c6b-plan.md` (milestone M10,
section "Port conventions").

## Contents

- `self_closeness_transport_through_orthonormalization`: the generic transport along
  `B.liftLeft → A.liftLeft → A.liftRight → B.liftRight`, with edges `ε`, `2δ`, `ε` and the
  triangle constant `3`.
- `final_fields_self_closeness` and `…_of_small_errors`: its specialization to the
  self-improvement errors, at the natural and at the literal threshold.

The theorems take the orthonormalization SDD bound as a hypothesis and call no orthonormalization,
so they carry no finite-pair, abelian-projection or `ζ > 0` hypothesis.

The translation is that of `BoundednessTransport/BoundednessGap.lean`: a strategy is a
`SymStrat params 𝔓 K`, `A.liftLeft` is `A.liftLeft strategy.state`, `IdxSubMeas.liftLeft F` and
`IdxSubMeas.liftRight F` are `IdxSubMeas.liftLeft strategy.state F` and
`IdxSubMeas.liftRight strategy.state F`, `leftPlacedSubMeas (ιB := ι)` and
`rightPlacedSubMeas (ιA := ι)` are `strategy.state.leftPlacedSubMeas` and
`strategy.state.rightPlacedSubMeas`, the relations are read on `strategy.state`, and `Error` is
`ℝ`. Swap symmetry is a theorem of the model, so the vendored
`MakingMeasurementsProjective.sddRel_liftRight_of_liftLeft_permInv strategy.permInvState …` is
M8's `MakingMeasurementsProjective.sddRel_liftRight_of_liftLeft_permInv strategy.state …`, and the
vendored hypothesis `⟨strategy.permInvState, hssc⟩` of `Preliminaries.twoNotionsOfSelfConsistency`
is `hssc` (M3). No statement of the vendored file carries a swap, density or normalization
hypothesis, so no statement changed beyond the translation; the file sets no option, the vendored
file-wide `respectTransparency false` not being needed.

The classical threshold lemma `final_fields_self_closeness_error_le_selfImprovementError`
(vendored `Thresholds/Final.lean`) is imported; the imports mirror the vendored ones.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/self_improvement.tex` lines 727--741
- `blueprint/src/chapter/ch07_self_improvement.tex`, the proof of
  `item:self-improvement-self-closeness`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.SelfImprovement

open MIPStarRE.LDT (Parameters FieldModel uniformDistribution)
open MIPStarRE.LDT.SelfImprovement (selfImprovementHelperError
  selfImprovementOrthogonalizationError selfImprovementError
  final_fields_self_closeness_error_le_selfImprovementError)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Generic self-closeness transport through helper-stage strong self-consistency and the
orthonormalization SDD step, for the `Unit`-indexed constant families of the self-improvement
pipeline.

From the bipartite strong self-consistency `hssc` of `A` at `δ` and the orthonormalization SDD
bound `horth` between the left lifts of `A` and `B` at `ε`, the left and right placements of `B`
are `3 (ε + 2δ + ε)`-close: `twoNotionsOfSelfConsistency` gives `A.liftLeft ≃_{2δ} A.liftRight`,
`sddRel_liftRight_of_liftLeft_permInv` reflects `horth` to the right lifts, and
`stateDependentDistanceRel_triangle_three` closes
`B.liftLeft → A.liftLeft → A.liftRight → B.liftRight`. -/
theorem self_closeness_transport_through_orthonormalization
    {α : Type*} [Fintype α]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (A B : SubMeas α 𝔓)
    (δ ε : ℝ)
    (hssc :
      strategy.state.BipartiteSSCRel (uniformDistribution Unit)
        (constSubMeasFamily A) δ)
    (horth :
      strategy.state.SDDRel (uniformDistribution Unit)
        (IdxSubMeas.liftLeft strategy.state (constSubMeasFamily A))
        (IdxSubMeas.liftLeft strategy.state (constSubMeasFamily B)) ε) :
    strategy.state.SDDRel (uniformDistribution Unit)
      (constSubMeasFamily (B.liftLeft strategy.state))
      (constSubMeasFamily (B.liftRight strategy.state))
      (3 * (ε + 2 * δ + ε)) :=
  Preliminaries.stateDependentDistanceRel_triangle_three strategy.state.toVecState
    (uniformDistribution Unit)
    (IdxSubMeas.liftLeft strategy.state (constSubMeasFamily B))
    (IdxSubMeas.liftLeft strategy.state (constSubMeasFamily A))
    (IdxSubMeas.liftRight strategy.state (constSubMeasFamily A))
    (IdxSubMeas.liftRight strategy.state (constSubMeasFamily B))
    ε (2 * δ) ε
    (Preliminaries.sddRel_symm strategy.state.toVecState (uniformDistribution Unit)
      (IdxSubMeas.liftLeft strategy.state (constSubMeasFamily A))
      (IdxSubMeas.liftLeft strategy.state (constSubMeasFamily B)) ε horth)
    (Preliminaries.twoNotionsOfSelfConsistency strategy.state (uniformDistribution Unit)
      (constSubMeasFamily A) δ hssc)
    (MakingMeasurementsProjective.sddRel_liftRight_of_liftLeft_permInv strategy.state
      (uniformDistribution Unit) (constSubMeasFamily A) (constSubMeasFamily B) ε horth)

/-- Final-fields self-closeness construction.

`self_closeness_transport_through_orthonormalization` at the self-improvement errors: from the
helper-stage bipartite SSC of `Hhat` and the orthonormalization SDD bound between `Hhat.liftLeft`
and `H.toSubMeas.liftLeft`, both produced inside `selfImprovement`, the `selfCloseness` field of
`SelfImprovementFinalFields` at the natural paper sum
`3 (selfImprovementOrthogonalizationError + 2 selfImprovementHelperError
  + selfImprovementOrthogonalizationError)`, with no new analytic hypothesis. -/
theorem final_fields_self_closeness
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    (Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (H : ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hssc :
      strategy.state.BipartiteSSCRel (uniformDistribution Unit)
        (constSubMeasFamily Hhat)
        (selfImprovementHelperError params eps delta))
    (horth :
      strategy.state.SDDRel (uniformDistribution Unit)
        (constSubMeasFamily (Hhat.liftLeft strategy.state))
        (constSubMeasFamily (H.toSubMeas.liftLeft strategy.state))
        (selfImprovementOrthogonalizationError params eps delta)) :
    strategy.state.SDDRel (uniformDistribution Unit)
      (constSubMeasFamily (strategy.state.leftPlacedSubMeas H.toSubMeas))
      (constSubMeasFamily (strategy.state.rightPlacedSubMeas H.toSubMeas))
      (3 * (selfImprovementOrthogonalizationError params eps delta
        + 2 * selfImprovementHelperError params eps delta
        + selfImprovementOrthogonalizationError params eps delta)) :=
  self_closeness_transport_through_orthonormalization params strategy Hhat H.toSubMeas
    (selfImprovementHelperError params eps delta)
    (selfImprovementOrthogonalizationError params eps delta) hssc horth

/-- Literal-threshold self-closeness construction under the standard unit-interval hypotheses:
`final_fields_self_closeness` with the numerical absorption
`final_fields_self_closeness_error_le_selfImprovementError`, giving exactly the `selfCloseness`
threshold of `SelfImprovementFinalFields`. -/
theorem final_fields_self_closeness_of_small_errors
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : ℝ) ≤ (params.q : ℝ))
    (Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (H : ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hssc :
      strategy.state.BipartiteSSCRel (uniformDistribution Unit)
        (constSubMeasFamily Hhat)
        (selfImprovementHelperError params eps delta))
    (horth :
      strategy.state.SDDRel (uniformDistribution Unit)
        (constSubMeasFamily (Hhat.liftLeft strategy.state))
        (constSubMeasFamily (H.toSubMeas.liftLeft strategy.state))
        (selfImprovementOrthogonalizationError params eps delta)) :
    strategy.state.SDDRel (uniformDistribution Unit)
      (constSubMeasFamily (strategy.state.leftPlacedSubMeas H.toSubMeas))
      (constSubMeasFamily (strategy.state.rightPlacedSubMeas H.toSubMeas))
      (selfImprovementError params eps delta) :=
  Preliminaries.stateDependentDistanceRel_mono strategy.state.toVecState
    (uniformDistribution Unit)
    (constSubMeasFamily (strategy.state.leftPlacedSubMeas H.toSubMeas))
    (constSubMeasFamily (strategy.state.rightPlacedSubMeas H.toSubMeas))
    (3 * (selfImprovementOrthogonalizationError params eps delta
      + 2 * selfImprovementHelperError params eps delta
      + selfImprovementOrthogonalizationError params eps delta))
    (selfImprovementError params eps delta)
    (final_fields_self_closeness_error_le_selfImprovementError params eps delta
      heps heps_le_one hdelta hdelta_le_one hd_le_q)
    (final_fields_self_closeness params strategy eps delta Hhat H hssc horth)

end MIPRE.LIDT.Co.SelfImprovement

end

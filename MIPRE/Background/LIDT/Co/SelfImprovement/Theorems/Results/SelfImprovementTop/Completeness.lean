/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
SelfImprovement/Theorems/Results/SelfImprovementTop/Completeness.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Basic.SubMeasurementFamilies
public import MIPRE.Background.LIDT.Co.Preliminaries.SelfConsistency.DataProcessing
public import MIPStarRE.LDT.SelfImprovement.Theorems.Thresholds.Final
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Statements

@[expose] public section

/-!
# Final-fields completeness construction

The completeness transport that fills the `completeness` field of `SelfImprovementFinalFields`:
from helper-stage completeness, through the orthonormalization SDD step, to the projective
final-field completeness estimate. The counterpart of the vendored
`SelfImprovement/Theorems/Results/SelfImprovementTop/Completeness.lean` (under
`MIPRE/Background/LIDT/MIPStarRE/LDT/`) in the port of `planning/c6b-plan.md` (milestone M10,
section "Port conventions").

## Contents

- `idx_sub_meas_mass_uniform_unit_const_sub_meas_family_lift_left`: the `Unit`-indexed mass of a
  constant family is the mass of its one submeasurement.
- `completeness_transport_through_orthonormalization`: the generic transport, by
  `Preliminaries.completenessTransferSelfConsistentA` at `Question = Unit`.
- `final_fields_completeness_of_helper_completeness` and `…_of_small_errors`: its
  specialization to the self-improvement errors, at the natural and at the literal threshold.

The theorems take the orthonormalization SDD bound as a hypothesis and call no orthonormalization,
so they carry no finite-pair, abelian-projection or `ζ > 0` hypothesis.

The translation is that of `BoundednessTransport/BoundednessGap.lean`: a strategy is a
`SymStrat params 𝔓 K`, `ψ : QuantumState (ι × ι)` is `S : SymModel 𝔓 K`, `A.liftLeft` is
`A.liftLeft S` (`SubMeas.liftLeft S A`), `IdxSubMeas.liftLeft F` is `IdxSubMeas.liftLeft S F`, the
relations `CompletenessAtLeast`, `BipartiteSSCRel`, `SDDRel` and the masses are read on
`strategy.state`, and `Error` is `ℝ`. The lemma
`idx_sub_meas_mass_uniform_unit_const_sub_meas_family_lift_left` places by `S.L`, so its vendored
state `ψ` is the model `S`, an explicit first argument. The vendored call
`completenessTransferSelfConsistentA strategy.state strategy.permInvState strategy.isNormalized …`
is the M3 form `completenessTransferSelfConsistentA strategy.state 𝒟 h𝒟 …`, swap symmetry and
normalization being theorems of the model. No statement of the vendored file carries a swap,
density or normalization hypothesis, so no statement changed beyond the translation; the file sets
no option, the vendored file-wide `respectTransparency false` not being needed.

The classical threshold lemma `final_fields_completeness_error_le_selfImprovementError` (vendored
`Thresholds/Final.lean`) is imported; the imports mirror the vendored ones.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/self_improvement.tex` lines 351--414 and 713--717
- `blueprint/src/chapter/ch07_self_improvement.tex` lines 101--142
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.SelfImprovement

open MIPStarRE.LDT (Parameters FieldModel avgOver uniformDistribution
  uniformDistribution_weight_sum_le_one)
open MIPStarRE.LDT.SelfImprovement (selfImprovementHelperError
  selfImprovementOrthogonalizationError selfImprovementError
  final_fields_completeness_error_le_selfImprovementError)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The `Unit`-indexed mass of the left lift of a constant family is the mass of the left lift of
its one submeasurement. -/
theorem idx_sub_meas_mass_uniform_unit_const_sub_meas_family_lift_left
    {α : Type*} [Fintype α]
    (S : SymModel 𝔓 K) (A : SubMeas α 𝔓) :
    S.idxSubMeasMass (uniformDistribution Unit)
        (IdxSubMeas.liftLeft S (constSubMeasFamily A)) =
      S.subMeasMass (A.liftLeft S) := by
  simp [VecState.idxSubMeasMass, avgOver, uniformDistribution, constSubMeasFamily,
    IdxSubMeas.liftLeft, SubMeas.liftLeft]

/-- Completeness transport through helper-stage strong self-consistency and the
orthonormalization SDD step, for the `Unit`-indexed constant families of the self-improvement
pipeline.

Given the completeness `hcomplete` of the helper-stage submeasurement `A` at level `m`, its
bipartite strong self-consistency `hssc` at `δ`, and the orthonormalization SDD bound `hsdd`
between the left lifts of `A` and `B` at `ε`, the left lift of `B` is complete at
`m - δ - 2 √ε`. The proof is `Preliminaries.completenessTransferSelfConsistentA` at
`Question = Unit`, after rewriting the `Unit`-indexed masses. -/
theorem completeness_transport_through_orthonormalization
    {α : Type*} [Fintype α]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (A B : SubMeas α 𝔓)
    (m δ ε : ℝ)
    (hcomplete : strategy.state.CompletenessAtLeast (A.liftLeft strategy.state) m)
    (hssc :
      strategy.state.BipartiteSSCRel (uniformDistribution Unit)
        (constSubMeasFamily A) δ)
    (hsdd :
      strategy.state.SDDRel (uniformDistribution Unit)
        (IdxSubMeas.liftLeft strategy.state (constSubMeasFamily A))
        (IdxSubMeas.liftLeft strategy.state (constSubMeasFamily B)) ε) :
    strategy.state.CompletenessAtLeast (B.liftLeft strategy.state)
      (m - δ - 2 * Real.sqrt ε) := by
  have htransfer :=
    Preliminaries.completenessTransferSelfConsistentA strategy.state
      (uniformDistribution Unit) (uniformDistribution_weight_sum_le_one Unit)
      (constSubMeasFamily A) (constSubMeasFamily B) δ ε hssc hsdd
  rw [idx_sub_meas_mass_uniform_unit_const_sub_meas_family_lift_left,
    idx_sub_meas_mass_uniform_unit_const_sub_meas_family_lift_left] at htransfer
  exact ⟨by linarith [hcomplete.lowerBound]⟩

/-- Final-fields completeness construction.

From the helper-stage completeness of `Hhat.liftLeft` at `(1 - nu) - selfImprovementHelperError`,
the helper-stage strong self-consistency of `Hhat` and the orthonormalization SDD bound between
`Hhat.liftLeft` and `H.toSubMeas.liftLeft`, the `completeness` field of
`SelfImprovementFinalFields` at the natural paper sum
`(1 - nu) - selfImprovementHelperError - selfImprovementHelperError
  - 2 √selfImprovementOrthogonalizationError`.
The comparison with `(1 - nu) - selfImprovementError` is the separate numerical step of
`final_fields_completeness_of_helper_completeness_of_small_errors`. -/
theorem final_fields_completeness_of_helper_completeness
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta nu : ℝ)
    (Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (H : ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hhelperCompleteness :
      strategy.state.CompletenessAtLeast (Hhat.liftLeft strategy.state)
        ((1 - nu) - selfImprovementHelperError params eps delta))
    (hssc :
      strategy.state.BipartiteSSCRel (uniformDistribution Unit)
        (constSubMeasFamily Hhat)
        (selfImprovementHelperError params eps delta))
    (horth :
      strategy.state.SDDRel (uniformDistribution Unit)
        (constSubMeasFamily (Hhat.liftLeft strategy.state))
        (constSubMeasFamily (H.toSubMeas.liftLeft strategy.state))
        (selfImprovementOrthogonalizationError params eps delta)) :
    strategy.state.CompletenessAtLeast (H.toSubMeas.liftLeft strategy.state)
      ((1 - nu) - selfImprovementHelperError params eps delta
        - selfImprovementHelperError params eps delta
        - 2 * Real.sqrt (selfImprovementOrthogonalizationError params eps delta)) :=
  completeness_transport_through_orthonormalization params strategy Hhat H.toSubMeas
    ((1 - nu) - selfImprovementHelperError params eps delta)
    (selfImprovementHelperError params eps delta)
    (selfImprovementOrthogonalizationError params eps delta)
    hhelperCompleteness hssc horth

/-- Literal-threshold completeness construction under the standard unit-interval hypotheses:
`final_fields_completeness_of_helper_completeness` with the numerical absorption
`final_fields_completeness_error_le_selfImprovementError`, giving exactly the `completeness`
threshold of `SelfImprovementFinalFields`. -/
theorem final_fields_completeness_of_helper_completeness_of_small_errors
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta nu : ℝ)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : ℝ) ≤ (params.q : ℝ))
    (Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (H : ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hhelperCompleteness :
      strategy.state.CompletenessAtLeast (Hhat.liftLeft strategy.state)
        ((1 - nu) - selfImprovementHelperError params eps delta))
    (hssc :
      strategy.state.BipartiteSSCRel (uniformDistribution Unit)
        (constSubMeasFamily Hhat)
        (selfImprovementHelperError params eps delta))
    (horth :
      strategy.state.SDDRel (uniformDistribution Unit)
        (constSubMeasFamily (Hhat.liftLeft strategy.state))
        (constSubMeasFamily (H.toSubMeas.liftLeft strategy.state))
        (selfImprovementOrthogonalizationError params eps delta)) :
    strategy.state.CompletenessAtLeast (H.toSubMeas.liftLeft strategy.state)
      ((1 - nu) - selfImprovementError params eps delta) :=
  have hnatural := (final_fields_completeness_of_helper_completeness params strategy eps delta nu
    Hhat H hhelperCompleteness hssc horth).lowerBound
  have herr := final_fields_completeness_error_le_selfImprovementError params eps delta
    heps heps_le_one hdelta hdelta_le_one hd_le_q
  ⟨by linarith⟩

end MIPRE.LIDT.Co.SelfImprovement

end

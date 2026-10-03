/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122),
MIPStarRE/LDT/Test/MainTheorem/SourceRoleRegister/Final.lean, to the models of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Test.MainTheorem.SourceRoleRegister.Core
public import MIPRE.Background.LIDT.Co.Test.MainTheorem.SourceRoleRegister.Completion

@[expose] public section

/-!
# Source-boundary role-register handoff: final point consistency

The final completed-measurement and point-consistency statements of the two-space route toward
`thm:main-formal`: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Test/MainTheorem/SourceRoleRegister/Final.lean` in the port
of `planning/c6b-plan.md` (milestone M13, section "Port conventions").

**The strategy is two-space**, as in Co `SourceRoleRegister/Core` and `Completion`:
`strategy : ProjStrat params 𝒞 𝒜 ℬ` has the bipartite model `strategy.state` with unit vector
`strategy.isNormalized`, and the translation is that of `Co/Test/MainTheorem/TwoSpace.lean`:
* the vendored `ConsRel strategy.state 𝒟 A B δ` is `bipartiteConsError strategy.state 𝒟 A B ≤ δ`;
* `SDDRel strategy.state 𝒟 (leftPlacedSubMeas G) …` is
  `(TwoSpace.vecState strategy.state strategy.isNormalized).SDDRel 𝒟
  (TwoSpace.leftPlacedSubMeas strategy.state G) …`, and the right forms likewise;
* the vendored `Preliminaries.{approxToSimeq, simeqToApprox, simeqTriangleInequality,
  triangleSub}_heterogeneous` on the two-space state are their `TwoSpace` forms, and the
  same-space `sddRel_symm`, `stateDependentDistanceRel_triangle` and `_mono` are applied to
  `TwoSpace.vecState strategy.state strategy.isNormalized` with both families explicit.
The measurements are `Measurement`, `ProjSubMeas` and `ProjMeas` of
`MIPStarRE.LDT.Polynomial params` in `𝒜` (Alice) and `ℬ` (Bob). The errors `σ`, `ζ₁`, `ζ₂`, `η`,
`ζ₃` are the vendored ones.

**Departure: new hypotheses.** Every theorem takes `(hM : strategy.state.IsDyadicPair)
(hd : 1 ≤ params.d)` right after `strategy`, as Co
`sourceRoleRegisterCompletePolynomialSelfConsistency` does: the main induction runs in the doubled model of a dyadic pair and needs `1 ≤ params.d`
(milestone M12's threaded `hS hA hd`), and the two-space orthonormalizations of Co `Core` need
`hM` and `ζ₁ > 0`. The latter is the only other use of `hd`: `σ ≥ 0`, being an upper bound of a
nonnegative defect, and `m d / q > 0` when `1 ≤ d` (`zeta₁_pos`); it replaces the vendored
derivation of `0 ≤ ζ₁` inside the orthonormalization lemma. The completion of Co `Completion`
takes `hM.isFinitePair`. No statement carries a swap, density or normalization hypothesis.

**Departure: imports.** The vendored file imports `SourceRoleRegister/Completion`, which imports
`Core`; Co `Completion` does not import Co `Core`, so this file imports both.

## Not ported

Every declaration of the vendored file has a counterpart here, with the new hypotheses `hM` and
`hd` above.
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.ProjStrat

open MIPStarRE.LDT (Parameters FieldModel Point uniformDistribution
  uniformDistribution_weight_sum_le_one)
open MIPStarRE.LDT.MainInductionStep (mainInductionError)
open MIPStarRE.LDT.MakingMeasurementsProjective (orthonormalizationError
  orthonormalizeAndCompleteError)
open MIPRE.LIDT.Co.TwoSpace (vecState leftPlacedSubMeas rightPlacedSubMeas placeLeft placeRight)

variable {𝒞 : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞]
  {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  {ℬ : Type*} [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]

/-- The error `ζ₁ = σ + 2√(3ε + σ) + md/q` of the source route is positive when `σ ≥ 0` and
`1 ≤ d`, as the two-space orthonormalizations require. -/
private theorem zeta₁_pos (params : Parameters) (hd : 1 ≤ params.d) {σ : ℝ} (hσ : 0 ≤ σ)
    (eps : ℝ) :
    0 < σ + 2 * Real.sqrt (3 * eps + σ) + (params.m * params.d : ℝ) / params.q := by
  have hmdq : 0 < (params.m * params.d : ℝ) / params.q :=
    div_pos (mul_pos (Nat.cast_pos.2 params.hm) (Nat.cast_pos.2 hd)) (Nat.cast_pos.2 params.hq)
  have := Real.sqrt_nonneg (3 * eps + σ)
  linarith

/-- Alice-side projective submeasurement from the source role-register route.

It combines the source role-register Step 5 theorem
(`sourceRoleRegisterCompletePolynomialSelfConsistency`) with the two-space orthonormalization
(`sourceRoleRegisterLeftProjectiveSubmeasurement_ofFullConsistency`), and constructs only the
Alice-side projective submeasurement with its left-factor state-dependent-distance estimate.

Departure: the hypotheses `hM : strategy.state.IsDyadicPair` and `hd : 1 ≤ params.d` are new. -/
theorem sourceRoleRegisterLeftProjectiveSubmeasurement
    (params : Parameters) [FieldModel params.q]
    (strategy : ProjStrat params 𝒞 𝒜 ℬ)
    (hM : strategy.state.IsDyadicPair)
    (hd : 1 ≤ params.d)
    (eps : ℝ)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ G_A : Measurement (MIPStarRE.LDT.Polynomial params) 𝒜,
      ∃ G_B : Measurement (MIPStarRE.LDT.Polynomial params) ℬ,
        ∃ P_A : ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝒜,
          bipartiteConsError strategy.state (uniformDistribution (Point params))
              (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
              (polynomialEvaluationFamily params G_B.toSubMeas) ≤
            2 * mainInductionError params k (3 * eps) (3 * eps) (3 * eps) ∧
          bipartiteConsError strategy.state (uniformDistribution (Point params))
              (polynomialEvaluationFamily params G_A.toSubMeas)
              (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB) ≤
            2 * mainInductionError params k (3 * eps) (3 * eps) (3 * eps) ∧
          bipartiteConsError strategy.state (uniformDistribution Unit)
              (constSubMeasFamily G_A.toSubMeas) (constSubMeasFamily G_B.toSubMeas) ≤
            2 * mainInductionError params k (3 * eps) (3 * eps) (3 * eps) +
              2 * Real.sqrt (3 * eps +
                2 * mainInductionError params k (3 * eps) (3 * eps) (3 * eps)) +
              (params.m * params.d : ℝ) / params.q ∧
          (vecState strategy.state strategy.isNormalized).SDDRel (uniformDistribution Unit)
            (constSubMeasFamily (leftPlacedSubMeas strategy.state G_A.toSubMeas))
            (constSubMeasFamily (leftPlacedSubMeas strategy.state P_A.toSubMeas))
            (orthonormalizationError
              (2 * mainInductionError params k (3 * eps) (3 * eps) (3 * eps) +
                2 * Real.sqrt (3 * eps +
                  2 * mainInductionError params k (3 * eps) (3 * eps) (3 * eps)) +
                (params.m * params.d : ℝ) / params.q)) := by
  obtain ⟨G_A, G_B, hpointAGB, hGApointB, hfull⟩ :=
    sourceRoleRegisterCompletePolynomialSelfConsistency params strategy hM hd eps hpass k hk
  obtain ⟨P_A, hP_A⟩ := sourceRoleRegisterLeftProjectiveSubmeasurement_ofFullConsistency params
    strategy hM G_A G_B _ (zeta₁_pos params hd
      ((MIPRE.LIDT.Co.bipartiteConsError_nonneg _ _ _ _).trans hpointAGB) eps) hfull
  exact ⟨G_A, G_B, P_A, hpointAGB, hGApointB, hfull, hP_A⟩

/-- Two-sided projective submeasurements from the source role-register route.

It combines the source role-register Step 5 theorem with the two-space orthonormalizations on
both factors, constructing the projective submeasurements `P_A`, `P_B` and the two
state-dependent-distance estimates; completion and the line-169 transport come after.

Departure: the hypotheses `hM : strategy.state.IsDyadicPair` and `hd : 1 ≤ params.d` are new. -/
theorem sourceRoleRegisterTwoSidedProjectiveSubmeasurements
    (params : Parameters) [FieldModel params.q]
    (strategy : ProjStrat params 𝒞 𝒜 ℬ)
    (hM : strategy.state.IsDyadicPair)
    (hd : 1 ≤ params.d)
    (eps : ℝ)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ G_A : Measurement (MIPStarRE.LDT.Polynomial params) 𝒜,
      ∃ G_B : Measurement (MIPStarRE.LDT.Polynomial params) ℬ,
        ∃ P_A : ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝒜,
          ∃ P_B : ProjSubMeas (MIPStarRE.LDT.Polynomial params) ℬ,
            bipartiteConsError strategy.state (uniformDistribution (Point params))
                (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
                (polynomialEvaluationFamily params G_B.toSubMeas) ≤
              2 * mainInductionError params k (3 * eps) (3 * eps) (3 * eps) ∧
            bipartiteConsError strategy.state (uniformDistribution (Point params))
                (polynomialEvaluationFamily params G_A.toSubMeas)
                (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB) ≤
              2 * mainInductionError params k (3 * eps) (3 * eps) (3 * eps) ∧
            bipartiteConsError strategy.state (uniformDistribution Unit)
                (constSubMeasFamily G_A.toSubMeas) (constSubMeasFamily G_B.toSubMeas) ≤
              2 * mainInductionError params k (3 * eps) (3 * eps) (3 * eps) +
                2 * Real.sqrt (3 * eps +
                  2 * mainInductionError params k (3 * eps) (3 * eps) (3 * eps)) +
                (params.m * params.d : ℝ) / params.q ∧
            (vecState strategy.state strategy.isNormalized).SDDRel (uniformDistribution Unit)
              (constSubMeasFamily (leftPlacedSubMeas strategy.state G_A.toSubMeas))
              (constSubMeasFamily (leftPlacedSubMeas strategy.state P_A.toSubMeas))
              (orthonormalizationError
                (2 * mainInductionError params k (3 * eps) (3 * eps) (3 * eps) +
                  2 * Real.sqrt (3 * eps +
                    2 * mainInductionError params k (3 * eps) (3 * eps) (3 * eps)) +
                  (params.m * params.d : ℝ) / params.q)) ∧
            (vecState strategy.state strategy.isNormalized).SDDRel (uniformDistribution Unit)
              (constSubMeasFamily (rightPlacedSubMeas strategy.state G_B.toSubMeas))
              (constSubMeasFamily (rightPlacedSubMeas strategy.state P_B.toSubMeas))
              (orthonormalizationError
                (2 * mainInductionError params k (3 * eps) (3 * eps) (3 * eps) +
                  2 * Real.sqrt (3 * eps +
                    2 * mainInductionError params k (3 * eps) (3 * eps) (3 * eps)) +
                  (params.m * params.d : ℝ) / params.q)) := by
  obtain ⟨G_A, G_B, hpointAGB, hGApointB, hfull⟩ :=
    sourceRoleRegisterCompletePolynomialSelfConsistency params strategy hM hd eps hpass k hk
  have hζ₁ := zeta₁_pos params hd
    ((MIPRE.LIDT.Co.bipartiteConsError_nonneg _ _ _ _).trans hpointAGB) eps
  obtain ⟨P_A, hP_A⟩ := sourceRoleRegisterLeftProjectiveSubmeasurement_ofFullConsistency params
    strategy hM G_A G_B _ hζ₁ hfull
  obtain ⟨P_B, hP_B⟩ := sourceRoleRegisterRightProjectiveSubmeasurement_ofFullConsistency params
    strategy hM G_A G_B _ hζ₁ hfull
  exact ⟨G_A, G_B, P_A, P_B, hpointAGB, hGApointB, hfull, hP_A, hP_B⟩

/-- Completed projective measurements from the source role-register route.

Paper origin: `references/ldt-paper/inductive_step.tex:143-149`. From the two-space strategy it
constructs the complete polynomial measurements `G_A`, `G_B`, the projective submeasurements
`P_A`, `P_B` and the completed projective measurements `Q_A`, `Q_B`
(`completedProjectiveMeasurementsAndLine169_ofTwoSidedSubmeasurements`), with the two
state-dependent-distance estimates at the orthonormalize-and-complete error and the repaired
line-169 polynomial consistencies.

Departure: the hypotheses `hM : strategy.state.IsDyadicPair` and `hd : 1 ≤ params.d` are new. -/
theorem sourceRoleRegisterCompletedProjectiveMeasurements
    (params : Parameters) [FieldModel params.q]
    (strategy : ProjStrat params 𝒞 𝒜 ℬ)
    (hM : strategy.state.IsDyadicPair)
    (hd : 1 ≤ params.d)
    (eps : ℝ)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    let σ : ℝ := 2 * mainInductionError params k (3 * eps) (3 * eps) (3 * eps)
    let ζ₁ : ℝ := σ + 2 * Real.sqrt (3 * eps + σ) + (params.m * params.d : ℝ) / params.q
    ∃ G_A : Measurement (MIPStarRE.LDT.Polynomial params) 𝒜,
      ∃ G_B : Measurement (MIPStarRE.LDT.Polynomial params) ℬ,
        ∃ P_A : ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝒜,
          ∃ P_B : ProjSubMeas (MIPStarRE.LDT.Polynomial params) ℬ,
            ∃ Q_A : ProjMeas (MIPStarRE.LDT.Polynomial params) 𝒜,
              ∃ Q_B : ProjMeas (MIPStarRE.LDT.Polynomial params) ℬ,
                bipartiteConsError strategy.state (uniformDistribution (Point params))
                    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
                    (polynomialEvaluationFamily params G_B.toSubMeas) ≤ σ ∧
                bipartiteConsError strategy.state (uniformDistribution (Point params))
                    (polynomialEvaluationFamily params G_A.toSubMeas)
                    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB) ≤ σ ∧
                bipartiteConsError strategy.state (uniformDistribution Unit)
                    (constSubMeasFamily G_A.toSubMeas)
                    (constSubMeasFamily G_B.toSubMeas) ≤ ζ₁ ∧
                (vecState strategy.state strategy.isNormalized).SDDRel
                    (uniformDistribution Unit)
                    (constSubMeasFamily (leftPlacedSubMeas strategy.state G_A.toSubMeas))
                    (constSubMeasFamily (leftPlacedSubMeas strategy.state P_A.toSubMeas))
                    (orthonormalizationError ζ₁) ∧
                (vecState strategy.state strategy.isNormalized).SDDRel
                    (uniformDistribution Unit)
                    (constSubMeasFamily (rightPlacedSubMeas strategy.state G_B.toSubMeas))
                    (constSubMeasFamily (rightPlacedSubMeas strategy.state P_B.toSubMeas))
                    (orthonormalizationError ζ₁) ∧
                (vecState strategy.state strategy.isNormalized).SDDRel
                    (uniformDistribution Unit)
                    (constSubMeasFamily (leftPlacedSubMeas strategy.state G_A.toSubMeas))
                    (constSubMeasFamily (leftPlacedSubMeas strategy.state Q_A.toSubMeas))
                    (orthonormalizeAndCompleteError ζ₁) ∧
                (vecState strategy.state strategy.isNormalized).SDDRel
                    (uniformDistribution Unit)
                    (constSubMeasFamily (rightPlacedSubMeas strategy.state G_B.toSubMeas))
                    (constSubMeasFamily (rightPlacedSubMeas strategy.state Q_B.toSubMeas))
                    (orthonormalizeAndCompleteError ζ₁) ∧
                bipartiteConsError strategy.state (uniformDistribution Unit)
                    (constSubMeasFamily Q_A.toSubMeas) (constSubMeasFamily G_B.toSubMeas) ≤
                  ζ₁ + Real.sqrt (orthonormalizationError ζ₁) ∧
                bipartiteConsError strategy.state (uniformDistribution Unit)
                    (constSubMeasFamily G_A.toSubMeas) (constSubMeasFamily Q_B.toSubMeas) ≤
                  ζ₁ + Real.sqrt (orthonormalizationError ζ₁) := by
  intro σ ζ₁
  obtain ⟨G_A, G_B, P_A, P_B, hpointAGB, hGApointB, hfull, hleft, hright⟩ :=
    sourceRoleRegisterTwoSidedProjectiveSubmeasurements params strategy hM hd eps hpass k hk
  obtain ⟨Q_A, Q_B, hleftComplete, hrightComplete, hleftLine169, hrightLine169⟩ :=
    completedProjectiveMeasurementsAndLine169_ofTwoSidedSubmeasurements params strategy
      hM.isFinitePair G_A G_B P_A P_B ζ₁ hfull hleft hright
  exact ⟨G_A, G_B, P_A, P_B, Q_A, Q_B, hpointAGB, hGApointB, hfull, hleft, hright,
    hleftComplete, hrightComplete, hleftLine169, hrightLine169⟩

/-- Final point-consistency estimates of the source role-register route, before scalar
absorption.

Paper origin: `references/ldt-paper/inductive_step.tex:158-185`. No point-consistency estimate is
assumed: the line-169 polynomial consistencies of `(Q_A, G_B)` and `(G_A, Q_B)` are evaluated at
the sampled point (`Test.consRel_constPolynomialEvaluation_heterogeneous`), the
`(Q_A, Q_B)` consistency comes from the line-156 distance `ζ₃`
(`completedProjectiveConsistency_ofFullConsistency`, then
`Test.projectiveEvaluationConsistency_ofFullPolynomialConsistency_heterogeneous` and
`TwoSpace.approxToSimeq_heterogeneous`), and the two point estimates are the two-space triangle
inequalities `TwoSpace.simeqTriangleInequality_heterogeneous` (Alice) and
`TwoSpace.triangleSub_heterogeneous` (Bob). The errors are the literal ones these produce.

Departure: the hypotheses `hM : strategy.state.IsDyadicPair` and `hd : 1 ≤ params.d` are new. -/
theorem sourceRoleRegisterFinalPointConsistency
    (params : Parameters) [FieldModel params.q]
    (strategy : ProjStrat params 𝒞 𝒜 ℬ)
    (hM : strategy.state.IsDyadicPair)
    (hd : 1 ≤ params.d)
    (eps : ℝ)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    let σ : ℝ := 2 * mainInductionError params k (3 * eps) (3 * eps) (3 * eps)
    let ζ₁ : ℝ := σ + 2 * Real.sqrt (3 * eps + σ) + (params.m * params.d : ℝ) / params.q
    let ζ₂ : ℝ := orthonormalizeAndCompleteError ζ₁
    let η : ℝ := ζ₁ + Real.sqrt (orthonormalizationError ζ₁)
    let ζ₃ : ℝ := 6 * ζ₁ + 6 * ζ₂
    ∃ Q_A : ProjMeas (MIPStarRE.LDT.Polynomial params) 𝒜,
      ∃ Q_B : ProjMeas (MIPStarRE.LDT.Polynomial params) ℬ,
        bipartiteConsError strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
            (polynomialEvaluationFamily params Q_B.toSubMeas) ≤
          σ + 2 * Real.sqrt (η + ζ₃ / 2) ∧
        bipartiteConsError strategy.state (uniformDistribution (Point params))
            (polynomialEvaluationFamily params Q_A.toSubMeas)
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB) ≤
          σ + 2 * Real.sqrt (η + ζ₃ / 2) ∧
        bipartiteConsError strategy.state (uniformDistribution (Point params))
            (polynomialEvaluationFamily params Q_A.toSubMeas)
            (polynomialEvaluationFamily params Q_B.toSubMeas) ≤ ζ₃ / 2 ∧
        bipartiteConsError strategy.state (uniformDistribution Unit)
            (constSubMeasFamily Q_A.toSubMeas) (constSubMeasFamily Q_B.toSubMeas) ≤
          ζ₃ / 2 := by
  intro σ ζ₁ ζ₂ η ζ₃
  obtain ⟨G_A, G_B, -, -, Q_A, Q_B, hpointAGB, hGApointB, hfull, -, -, hleftComplete,
      hrightComplete, hleftLine169, hrightLine169⟩ :=
    sourceRoleRegisterCompletedProjectiveMeasurements params strategy hM hd eps hpass k hk
  set V := vecState strategy.state strategy.isNormalized
  have h𝒟 := uniformDistribution_weight_sum_le_one (Point params)
  -- the line-156 distance of the completed measurements and its two consequences
  have hQQSDD : V.SDDRel (uniformDistribution Unit)
      (constSubMeasFamily (leftPlacedSubMeas strategy.state Q_A.toSubMeas))
      (constSubMeasFamily (rightPlacedSubMeas strategy.state Q_B.toSubMeas)) ζ₃ :=
    completedProjectiveConsistency_ofFullConsistency params strategy G_A G_B Q_A Q_B ζ₁ hfull
      hleftComplete hrightComplete
  have hQQEval : bipartiteConsError strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params Q_A.toSubMeas)
      (polynomialEvaluationFamily params Q_B.toSubMeas) ≤ ζ₃ / 2 :=
    Test.projectiveEvaluationConsistency_ofFullPolynomialConsistency_heterogeneous
      strategy.isNormalized Q_A Q_B hQQSDD
  have hQQUnit : bipartiteConsError strategy.state (uniformDistribution Unit)
      (constSubMeasFamily Q_A.toSubMeas) (constSubMeasFamily Q_B.toSubMeas) ≤ ζ₃ / 2 :=
    TwoSpace.approxToSimeq_heterogeneous strategy.state strategy.isNormalized
      (uniformDistribution Unit) (fun _ => Q_A) (fun _ => Q_B) (ζ₃ / 2)
      ⟨hQQSDD.squaredDistanceBound.trans_eq (by ring)⟩
  -- the evaluated line-169 consistencies
  have hleftLineEval : bipartiteConsError strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params Q_A.toSubMeas)
      (polynomialEvaluationFamily params G_B.toSubMeas) ≤ η :=
    Test.consRel_constPolynomialEvaluation_heterogeneous strategy.state Q_A.toMeasurement G_B
      hleftLine169
  have hrightLineEval : bipartiteConsError strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params G_A.toSubMeas)
      (polynomialEvaluationFamily params Q_B.toSubMeas) ≤ η :=
    Test.consRel_constPolynomialEvaluation_heterogeneous strategy.state G_A Q_B.toMeasurement
      hrightLine169
  let pointA := IdxProjMeas.toIdxMeas strategy.pointMeasurementA
  let pointB := IdxProjMeas.toIdxMeas strategy.pointMeasurementB
  let gAEval := Test.polynomialEvaluationMeasurementFamily params G_A
  let gBEval := Test.polynomialEvaluationMeasurementFamily params G_B
  let qAEval := Test.polynomialEvaluationMeasurementFamily params Q_A.toMeasurement
  let qBEval := Test.polynomialEvaluationMeasurementFamily params Q_B.toMeasurement
  -- Alice: `A^{A,u} ≃_σ G_B`, `Q_A ≃_η G_B`, `Q_A ≃_{ζ₃/2} Q_B`
  have hAliceFinal := TwoSpace.simeqTriangleInequality_heterogeneous strategy.state
    strategy.isNormalized (uniformDistribution (Point params)) h𝒟 pointA qAEval gBEval qBEval
    σ η (ζ₃ / 2) hpointAGB hleftLineEval hQQEval
  -- Bob: the placed distance of `G_A` and `Q_A` through `Q_B`, then `triangle-sub`
  have hrightLineSDD := TwoSpace.simeqToApprox_heterogeneous strategy.state
    strategy.isNormalized (uniformDistribution (Point params)) gAEval qBEval η hrightLineEval
  have hQQEvalSDD := TwoSpace.simeqToApprox_heterogeneous strategy.state
    strategy.isNormalized (uniformDistribution (Point params)) qAEval qBEval (ζ₃ / 2) hQQEval
  have hQGSDD := Preliminaries.sddRel_symm V (uniformDistribution (Point params))
    (placeLeft strategy.state (IdxMeas.toIdxSubMeas qAEval))
    (placeRight strategy.state (IdxMeas.toIdxSubMeas qBEval)) _ hQQEvalSDD
  have hgAqA : V.SDDRel (uniformDistribution (Point params))
      (placeLeft strategy.state (IdxMeas.toIdxSubMeas gAEval))
      (placeLeft strategy.state (IdxMeas.toIdxSubMeas qAEval)) (4 * (η + ζ₃ / 2)) :=
    Preliminaries.stateDependentDistanceRel_mono V _ _ _ _ _ (le_of_eq (by ring))
      (Preliminaries.stateDependentDistanceRel_triangle V (uniformDistribution (Point params))
        (placeLeft strategy.state (IdxMeas.toIdxSubMeas gAEval))
        (placeRight strategy.state (IdxMeas.toIdxSubMeas qBEval))
        (placeLeft strategy.state (IdxMeas.toIdxSubMeas qAEval)) _ _ hrightLineSDD hQGSDD)
  have hBobRaw := TwoSpace.triangleSub_heterogeneous strategy.state strategy.isNormalized
    (uniformDistribution (Point params)) h𝒟 gAEval qAEval (IdxMeas.toIdxSubMeas pointB) σ
    (4 * (η + ζ₃ / 2)) hGApointB hgAqA
  have hsqrt_four : Real.sqrt (4 * (η + ζ₃ / 2)) = 2 * Real.sqrt (η + ζ₃ / 2) := by
    rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  rw [hsqrt_four] at hBobRaw
  exact ⟨Q_A, Q_B, hAliceFinal, hBobRaw, hQQEval, hQQUnit⟩

end MIPRE.LIDT.Co.ProjStrat

end

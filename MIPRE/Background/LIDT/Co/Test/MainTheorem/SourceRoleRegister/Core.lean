/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122),
MIPStarRE/LDT/Test/MainTheorem/SourceRoleRegister/Core.lean, to the models of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.MainInductionStep.Theorems.MainTheorems.Successor
public import MIPRE.Background.LIDT.Co.MakingMeasurementsProjective.Orthonormalization
public import MIPRE.Background.LIDT.Co.Test.SchwartzZippelStep
public import MIPRE.Background.LIDT.Co.Test.MainTheorem.ProjectiveConsistency.Evaluation
public import MIPRE.Background.LIDT.Co.Doubling.Strategy
public import MIPRE.Background.LIDT.Co.Doubling.Unsymmetrization

@[expose] public section

/-!
# Source-boundary role-register handoff: core reductions

The main-induction handoff, the unsymmetrization and the first two-space projectivization outputs
of the source route toward `thm:main-formal`: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Test/MainTheorem/SourceRoleRegister/Core.lean` in the port of
`planning/c6b-plan.md` (milestone M13, section "Port conventions").

**The strategy is two-space.** `strategy : ProjStrat params 𝒞 𝒜 ℬ` is the Co two-space container:
its state is a bipartite model `strategy.state : MIPRE.BipartiteModel 𝒞 𝒜 ℬ` with a unit vector
(`strategy.isNormalized`), Alice's measurements in `𝒜` and Bob's in `ℬ`. The translation is that
of `Co/Test/MainTheorem/TwoSpace.lean`:
* the vendored `ConsRel strategy.state 𝒟 A B δ` is `bipartiteConsError strategy.state 𝒟 A B ≤ δ`
  (M2's two-space defect, `Co/Test/StrategyBiProj/Measurements.lean`);
* `SDDRel strategy.state 𝒟 (leftPlacedSubMeas G) …` is
  `(TwoSpace.vecState strategy.state strategy.isNormalized).SDDRel 𝒟
  (TwoSpace.leftPlacedSubMeas strategy.state G) …`;
* the role-register local space `RoleRegisterLocal ιA ιB` is the doubled local algebra
  `Doubling.Loc strategy.state`, and `strategy.roleRegisterSymmStrategy` is the symmetric strategy
  `Doubling.symmStrat strategy hM.isFinitePair` on the doubled model (Theorem D);
* `Measurement.extractRoleRegisterAlice`/`Bob` are `Doubling.measA`/`measB` (Theorem E,
  `Co/Doubling/Unsymmetrization.lean`).

**Departure: imports.** The vendored imports `Test/StrategyBiProjRoleAverage/Final` (the
role-register symmetrization) and `Test/StrategyBiProjUnsymmetrization` (the extractions and the
factor-two lemmas) are not ported; this file imports Co `Doubling/Strategy` and
`Doubling/Unsymmetrization`, which replace them.

**Departure: new hypotheses.** The doubling and the orthonormalization tier need the two-space
model to be a finite pair, and the main induction needs the doubled model to be a finite pair
without abelian projections and `1 ≤ params.d` (milestone M12's threaded `hS hA hd`). So:
* `roleRegisterSymmStrategy_sourceMainInduction`, `sourceRoleRegisterUnsymmetrizedPointConsistency`
  and `sourceRoleRegisterCompletePolynomialSelfConsistency` take
  `(hM : strategy.state.IsDyadicPair) (hd : 1 ≤ params.d)` right after `strategy`; the induction's
  `hS hA` are `Doubling.isFinitePair hM.isFinitePair strategy.isNormalized` and
  `Doubling.noAbelianProj_opsA_of_isDyadicPair hM strategy.isNormalized`, which type-check because
  the symmetric strategy is always built with `hM.isFinitePair`;
* `sourceRoleRegisterPointConsistency_ofSymConsistency` and
  `sourceRoleRegisterFullPolynomialSelfConsistency_ofPointConsistency` take
  `(hM : strategy.state.IsFinitePair)` right after `strategy`;
* `sourceRoleRegisterLeftProjectiveSubmeasurement_ofFullConsistency` and its right form take
  `(hM : strategy.state.IsDyadicPair)` right after `strategy` and `(hζ : 0 < ζ)` right after `ζ`:
  the orthonormalization tier T1 needs `ζ > 0` (`planning/c6b-plan.md`, "Departures in M4, M6,
  M7 and M8"), which replaces the vendored derivation of `0 ≤ ζ` from `hfull`.
No statement carries a swap, density or normalization hypothesis; the constants are the vendored
ones.

**Step 5 runs in the doubled model, losslessly.** The vendored
`sourceRoleRegisterFullPolynomialSelfConsistency_ofPointConsistency` applies the heterogeneous
Schwartz–Zippel step on the two-space state. Here the two polynomial measurements are paired,
`X = Doubling.pairMeasurement hM G_A G_B`, a measurement of `Doubling.Loc strategy.state`; the
diagonal identity `Doubling.bipartiteConsError_model_diag` turns the evaluated two-space
consistency of `(G_A, G_B)` into the doubled consistency of the evaluations of `X` with
themselves, Co `Test.mainFormalStep5_selfConsistency_ofExpansionBound` adds `md/q` in the doubled
model, and the diagonal identity reads the result back, with no loss of a factor two.

**Projective submeasurements.** M8's two-space orthonormalizations conclude with
`∑ₐ ‖π(πA(Aₐ − Pₐ)) ψ‖² ≤ orthonormalizationError ζ`; `Preliminaries.constFamily_sdd_unit` and
`TwoSpace.qSDD_leftPlaced_eq_sum_norm_sq` (and the `πB` form) turn it into the vendored `SDDRel`
shape over `TwoSpace.vecState`.

## Not ported

Every declaration of the vendored file has a counterpart here, with the statement changes listed
above: `hM` (and `hd` where the main induction is called, `hζ` for the two orthonormalizations).
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.ProjStrat

open MIPStarRE.LDT (Parameters FieldModel Point uniformDistribution
  uniformDistribution_weight_sum_le_one)
open MIPStarRE.LDT.MainInductionStep (mainInductionError)
open MIPStarRE.LDT.MakingMeasurementsProjective (orthonormalizationError)
open MIPRE.LIDT.Co.MakingMeasurementsProjective (
  orthonormalizationMeasurement_of_consistency_from_projectivizationRepair_heterogeneous
  orthonormalizationMeasurement_right_of_consistency_from_projectivizationRepair_heterogeneous)

variable {𝒞 : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞]
  {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  {ℬ : Type*} [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]

/-- Apply the source-shaped main-induction theorem to the symmetrization of a two-space strategy
in the doubled model.

Paper origin: `references/ldt-paper/inductive_step.tex:26-83`, where the general projective
strategy of `thm:main-formal` is symmetrized and `thm:main-induction` is applied to the resulting
symmetric strategy. Here the symmetrization is `Doubling.symmStrat`, which is
`(3ε, 3ε, 3ε)`-good (`Doubling.symmStrat_isGood_three_mul`), and the induction is Co
`MainInductionStep.mainInduction`, whose model hypotheses hold in the doubled model of a dyadic
pair (`Doubling.isFinitePair`, `Doubling.noAbelianProj_opsA_of_isDyadicPair`).

Departure: the hypotheses `hM : strategy.state.IsDyadicPair` and `hd : 1 ≤ params.d` are new. -/
theorem roleRegisterSymmStrategy_sourceMainInduction
    (params : Parameters) [FieldModel params.q]
    (strategy : ProjStrat params 𝒞 𝒜 ℬ)
    (hM : strategy.state.IsDyadicPair)
    (hd : 1 ≤ params.d)
    (eps : ℝ)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ G : Measurement (MIPStarRE.LDT.Polynomial params) (Doubling.Loc strategy.state),
      (Doubling.symmStrat strategy hM.isFinitePair).state.ConsRel
        (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas (Doubling.symmStrat strategy hM.isFinitePair).pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas)
        (mainInductionError params k (3 * eps) (3 * eps) (3 * eps)) :=
  MainInductionStep.mainInduction params (Doubling.symmStrat strategy hM.isFinitePair)
    (Doubling.isFinitePair hM.isFinitePair strategy.isNormalized)
    (Doubling.noAbelianProj_opsA_of_isDyadicPair hM strategy.isNormalized) hd
    (3 * eps) (3 * eps) (3 * eps) k
    (Doubling.symmStrat_isGood_three_mul strategy hM.isFinitePair hpass) hk

/-- Unsymmetrize the point consistency of a polynomial measurement of the doubled model.

Paper origin: `references/ldt-paper/inductive_step.tex:84-109`.

From the consistency `σ` of the symmetric strategy's point measurements with the evaluations of a
polynomial measurement `G` of the doubled local algebra, the first player's point measurements
are `2σ`-consistent with the evaluations of `G`'s second component `Doubling.measB hM G`, and the
evaluations of its first component `Doubling.measA hM G` with the second player's point
measurements. This is Theorem E, `Doubling.symmStrat_pointConsistency_unsymmetrize`.

Departure: the hypothesis `hM : strategy.state.IsFinitePair` is new. -/
theorem sourceRoleRegisterPointConsistency_ofSymConsistency
    (params : Parameters) [FieldModel params.q]
    (strategy : ProjStrat params 𝒞 𝒜 ℬ)
    (hM : strategy.state.IsFinitePair)
    (G : Measurement (MIPStarRE.LDT.Polynomial params) (Doubling.Loc strategy.state))
    (σ : ℝ)
    (hsym : (Doubling.symmStrat strategy hM).state.ConsRel
      (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas (Doubling.symmStrat strategy hM).pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas) σ) :
    bipartiteConsError strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
        (polynomialEvaluationFamily params (Doubling.measB hM G).toSubMeas) ≤ 2 * σ ∧
      bipartiteConsError strategy.state (uniformDistribution (Point params))
        (polynomialEvaluationFamily params (Doubling.measA hM G).toSubMeas)
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB) ≤ 2 * σ :=
  Doubling.symmStrat_pointConsistency_unsymmetrize strategy hM G hsym

/-- Passing the two-space low individual degree test bounds the point-agreement branch by `3ε`.

It follows because the point-agreement branch is one of the three nonnegative terms averaged in
`ProjStrat.lowIndividualDegreeFailureProbability`. -/
theorem pointAgreementFailureProbability_le_three_mul
    (params : Parameters) [FieldModel params.q]
    {strategy : ProjStrat params 𝒞 𝒜 ℬ} {eps : ℝ}
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    strategy.pointAgreementFailureProbability ≤ 3 * eps := by
  have haxis := strategy.axisParallelRoleAverage_nonneg
  have hdiag := strategy.diagonalRoleAverage_nonneg
  have hmain := hpass.soundnessHypothesis
  rw [lowIndividualDegreeFailureProbability_eq_role_averages] at hmain
  linarith

/-- The two-space Step 5 self-consistency calculation before projectivization.

Paper origin: `references/ldt-paper/inductive_step.tex:111-133`.

Starting from the two unsymmetrized estimates `G^A_[g(u)=a] ⊗ I ≃_σ I ⊗ A^{B,u}_a` and
`A^{A,u}_a ⊗ I ≃_σ I ⊗ G^B_[g(u)=a]`, the point-agreement branch of the test gives the evaluated
polynomial consistency at error `σ + 2√(3ε + σ)` (`TwoSpace.simeqTriangleInequality_heterogeneous`).
The Schwartz–Zippel Step 5 lemma then gives full-polynomial consistency with the additional `md/q`
loss; it is applied in the doubled model to the paired measurement
`Doubling.pairMeasurement hM G_A G_B`, through the lossless diagonal identity
`Doubling.bipartiteConsError_model_diag`.

Departure: the hypothesis `hM : strategy.state.IsFinitePair` is new. -/
theorem sourceRoleRegisterFullPolynomialSelfConsistency_ofPointConsistency
    (params : Parameters) [FieldModel params.q]
    (strategy : ProjStrat params 𝒞 𝒜 ℬ)
    (hM : strategy.state.IsFinitePair)
    (eps σ : ℝ)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (G_A : Measurement (MIPStarRE.LDT.Polynomial params) 𝒜)
    (G_B : Measurement (MIPStarRE.LDT.Polynomial params) ℬ)
    (hpointAGB : bipartiteConsError strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (polynomialEvaluationFamily params G_B.toSubMeas) ≤ σ)
    (hGApointB : bipartiteConsError strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params G_A.toSubMeas)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB) ≤ σ) :
    bipartiteConsError strategy.state (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas) (constSubMeasFamily G_B.toSubMeas) ≤
      σ + 2 * Real.sqrt (3 * eps + σ) + (params.m * params.d : ℝ) / params.q := by
  have hpoint : bipartiteConsError strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB) ≤ 3 * eps :=
    pointAgreementFailureProbability_le_three_mul params hpass
  have hevaluated : bipartiteConsError strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params G_A.toSubMeas)
      (polynomialEvaluationFamily params G_B.toSubMeas) ≤ σ + 2 * Real.sqrt (3 * eps + σ) :=
    TwoSpace.simeqTriangleInequality_heterogeneous strategy.state strategy.isNormalized
      (uniformDistribution (Point params)) (uniformDistribution_weight_sum_le_one (Point params))
      (Test.polynomialEvaluationMeasurementFamily params G_A)
      (IdxProjMeas.toIdxMeas strategy.pointMeasurementA)
      (IdxProjMeas.toIdxMeas strategy.pointMeasurementB)
      (Test.polynomialEvaluationMeasurementFamily params G_B)
      σ (3 * eps) σ hGApointB hpoint hpointAGB
  -- Step 5 in the doubled model, on the paired measurement
  let X := Doubling.pairMeasurement hM G_A G_B
  have hXA : (fun u => Doubling.subMeasA hM (polynomialEvaluationFamily params X.toSubMeas u)) =
      polynomialEvaluationFamily params G_A.toSubMeas := funext fun u => by
    rw [← Doubling.polynomialEvaluationFamily_subMeasA, Doubling.subMeasA_pairMeasurement]
  have hXB : (fun u => Doubling.subMeasB hM (polynomialEvaluationFamily params X.toSubMeas u)) =
      polynomialEvaluationFamily params G_B.toSubMeas := funext fun u => by
    rw [← Doubling.polynomialEvaluationFamily_subMeasB, Doubling.subMeasB_pairMeasurement]
  have hX : (Doubling.model hM strategy.isNormalized).ConsRel
      (uniformDistribution (Point params))
      (polynomialEvaluationFamily params X.toSubMeas)
      (polynomialEvaluationFamily params X.toSubMeas) (σ + 2 * Real.sqrt (3 * eps + σ)) := by
    refine ⟨?_⟩
    rw [Doubling.bipartiteConsError_model_diag, hXA, hXB]
    exact hevaluated
  have h5 := (Test.mainFormalStep5_selfConsistency_ofExpansionBound params
    (Doubling.model hM strategy.isNormalized) X.toSubMeas X.toSubMeas _ hX).offDiagonalBound
  rw [Doubling.bipartiteConsError_model_diag] at h5
  change bipartiteConsError strategy.state (uniformDistribution Unit)
    (constSubMeasFamily (Doubling.subMeasA hM X.toSubMeas))
    (constSubMeasFamily (Doubling.subMeasB hM X.toSubMeas)) ≤ _ at h5
  rwa [Doubling.subMeasA_pairMeasurement, Doubling.subMeasB_pairMeasurement] at h5

/-- The two unsymmetrized polynomial measurements obtained from the source-shaped main-induction
call on the doubled model.

Paper origin: `references/ldt-paper/inductive_step.tex:68-109`.

After applying source main induction to the symmetrization `Doubling.symmStrat`, the components
`Doubling.measA`, `Doubling.measB` of the resulting polynomial measurement are consistent with the
original two-space point measurements, with the factor-two loss. The outputs are complete
polynomial measurements, not projective measurements, and no self-consistency conclusion is
claimed.

Departure: the hypotheses `hM : strategy.state.IsDyadicPair` and `hd : 1 ≤ params.d` are new. -/
theorem sourceRoleRegisterUnsymmetrizedPointConsistency
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
        bipartiteConsError strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
            (polynomialEvaluationFamily params G_B.toSubMeas) ≤
          2 * mainInductionError params k (3 * eps) (3 * eps) (3 * eps) ∧
        bipartiteConsError strategy.state (uniformDistribution (Point params))
            (polynomialEvaluationFamily params G_A.toSubMeas)
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB) ≤
          2 * mainInductionError params k (3 * eps) (3 * eps) (3 * eps) := by
  obtain ⟨G, hG⟩ :=
    roleRegisterSymmStrategy_sourceMainInduction params strategy hM hd eps hpass k hk
  exact ⟨Doubling.measA hM.isFinitePair G, Doubling.measB hM.isFinitePair G,
    sourceRoleRegisterPointConsistency_ofSymConsistency params strategy hM.isFinitePair G _ hG⟩

/-- Complete polynomial measurements obtained from the two-space source route, including
full-polynomial self-consistency.

Paper origin: `references/ldt-paper/inductive_step.tex:68-133`.

This is the source-boundary route through the end of the paper's Schwartz–Zippel Step 5
calculation: source main induction on the doubled model, the components of its polynomial
measurement, the two factor-two point-consistency estimates, and the triangle and
Schwartz–Zippel calculation for full-polynomial consistency. The measurements are complete, not
projective, and the scalar cascade has not yet been absorbed into `mainFormalError`.

Departure: the hypotheses `hM : strategy.state.IsDyadicPair` and `hd : 1 ≤ params.d` are new. -/
theorem sourceRoleRegisterCompletePolynomialSelfConsistency
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
            (params.m * params.d : ℝ) / params.q := by
  obtain ⟨G_A, G_B, hpointAGB, hGApointB⟩ :=
    sourceRoleRegisterUnsymmetrizedPointConsistency params strategy hM hd eps hpass k hk
  exact ⟨G_A, G_B, hpointAGB, hGApointB,
    sourceRoleRegisterFullPolynomialSelfConsistency_ofPointConsistency params strategy
      hM.isFinitePair eps _ hpass G_A G_B hpointAGB hGApointB⟩

/-- Alice-side projective submeasurement obtained from a two-space complete-measurement Step 5
output.

Paper origin: `references/ldt-paper/inductive_step.tex:135-143`, applying
`lem:orthonormalization-main-lemma` to the complete polynomial measurements whose full-polynomial
consistency has just been proved. It constructs the Alice-side projective submeasurement from the
complete measurement `G_A` and its cross-consistency with `G_B`, through M8's two-space
`orthonormalizationMeasurement_of_consistency_from_projectivizationRepair_heterogeneous`,
without identifying the two players' algebras.

Departure: the hypotheses `hM : strategy.state.IsDyadicPair` and `hζ : 0 < ζ` are new. -/
theorem sourceRoleRegisterLeftProjectiveSubmeasurement_ofFullConsistency
    (params : Parameters) [FieldModel params.q]
    (strategy : ProjStrat params 𝒞 𝒜 ℬ)
    (hM : strategy.state.IsDyadicPair)
    (G_A : Measurement (MIPStarRE.LDT.Polynomial params) 𝒜)
    (G_B : Measurement (MIPStarRE.LDT.Polynomial params) ℬ)
    (ζ : ℝ) (hζ : 0 < ζ)
    (hfull : bipartiteConsError strategy.state (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas) (constSubMeasFamily G_B.toSubMeas) ≤ ζ) :
    ∃ P_A : ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝒜,
      (TwoSpace.vecState strategy.state strategy.isNormalized).SDDRel (uniformDistribution Unit)
        (constSubMeasFamily (TwoSpace.leftPlacedSubMeas strategy.state G_A.toSubMeas))
        (constSubMeasFamily (TwoSpace.leftPlacedSubMeas strategy.state P_A.toSubMeas))
        (orthonormalizationError ζ) := by
  obtain ⟨P, hP⟩ :=
    orthonormalizationMeasurement_of_consistency_from_projectivizationRepair_heterogeneous
      strategy.state strategy.isNormalized hM G_A G_B ζ hζ hfull
  refine ⟨P, ⟨?_⟩⟩
  rw [Preliminaries.constFamily_sdd_unit, TwoSpace.qSDD_leftPlaced_eq_sum_norm_sq]
  exact hP

/-- Bob-side projective submeasurement obtained from a two-space complete-measurement Step 5
output.

Paper origin: `references/ldt-paper/inductive_step.tex:135-143`. The right-register counterpart
of `sourceRoleRegisterLeftProjectiveSubmeasurement_ofFullConsistency`, through M8's
`orthonormalizationMeasurement_right_of_consistency_from_projectivizationRepair_heterogeneous`.

Departure: the hypotheses `hM : strategy.state.IsDyadicPair` and `hζ : 0 < ζ` are new. -/
theorem sourceRoleRegisterRightProjectiveSubmeasurement_ofFullConsistency
    (params : Parameters) [FieldModel params.q]
    (strategy : ProjStrat params 𝒞 𝒜 ℬ)
    (hM : strategy.state.IsDyadicPair)
    (G_A : Measurement (MIPStarRE.LDT.Polynomial params) 𝒜)
    (G_B : Measurement (MIPStarRE.LDT.Polynomial params) ℬ)
    (ζ : ℝ) (hζ : 0 < ζ)
    (hfull : bipartiteConsError strategy.state (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas) (constSubMeasFamily G_B.toSubMeas) ≤ ζ) :
    ∃ P_B : ProjSubMeas (MIPStarRE.LDT.Polynomial params) ℬ,
      (TwoSpace.vecState strategy.state strategy.isNormalized).SDDRel (uniformDistribution Unit)
        (constSubMeasFamily (TwoSpace.rightPlacedSubMeas strategy.state G_B.toSubMeas))
        (constSubMeasFamily (TwoSpace.rightPlacedSubMeas strategy.state P_B.toSubMeas))
        (orthonormalizationError ζ) := by
  obtain ⟨P, hP⟩ :=
    orthonormalizationMeasurement_right_of_consistency_from_projectivizationRepair_heterogeneous
      strategy.state strategy.isNormalized hM G_A G_B ζ hζ hfull
  refine ⟨P, ⟨?_⟩⟩
  rw [Preliminaries.constFamily_sdd_unit, TwoSpace.qSDD_rightPlaced_eq_sum_norm_sq]
  exact hP

end MIPRE.LIDT.Co.ProjStrat

end

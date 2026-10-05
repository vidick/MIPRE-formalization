/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122),
MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean, to the models of `planning/c6b-plan.md`; not a
vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Test.MainTheorem.SourceRoleRegister.Final
public import MIPRE.Background.LIDT.Co.Doubling.Strategy
public import MIPStarRE.LDT.Test.MainTheorem.SourceScalars

@[expose] public section

/-!
# Main-formal soundness theorem

The two-space final theorem `thm:main-formal` of the low individual degree test: the counterpart
of `MIPRE/Background/LIDT/MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean` in the port of
`planning/c6b-plan.md` (milestone M13, section "Port conventions"). It is the last theorem of the
port. A projective strategy `strategy : ProjStrat params 𝒞 𝒜 ℬ` whose bipartite model is a dyadic
pair and which passes the test with error `ε` has projective polynomial measurements `G_A` in `𝒜`
and `G_B` in `ℬ` consistent with the point measurements and with each other up to
`mainFormalError params k ε`. The statement is two-space, as the vendored one is: the symmetric
model appears only inside, as the doubled model `D(M)` in which the main induction runs
(Co `SourceRoleRegister/Core`).

**Translation.** That of Co `Test/MainTheorem/TwoSpace.lean`: the vendored
`ConsRel strategy.state 𝒟 A B δ` is `bipartiteConsError strategy.state 𝒟 A B ≤ δ`, the measurements
are `ProjMeas (MIPStarRE.LDT.Polynomial params)` in `𝒜` (Alice) and `ℬ` (Bob), and the saturated
branch bounds a defect by `1` through `TwoSpace.bipartiteConsError_uniform_le_one`. The small-error
branch is the vendored scalar absorption, verbatim, applied to
`ProjStrat.sourceRoleRegisterFinalPointConsistency`.

**Departure: new hypotheses.** `mainFormalConclusion_ofRoleRegisterScalarBoundary`,
`mainFormal_smallErrorConclusion`, `mainFormalConclusion` and `mainFormal` take
`(hM : strategy.state.IsDyadicPair) (hd : 1 ≤ params.d)` right after `strategy`, as Co
`SourceRoleRegister/Final` does: the main induction runs in the doubled model of a dyadic pair and
needs `1 ≤ params.d`, and the two-space orthonormalizations need `hM` and `ζ₁ > 0`.
`mainFormal_trivial_witness` uses neither and does not take them. No statement carries a swap,
density or normalization hypothesis (the strategy's state is a unit vector by
`strategy.isNormalized`).

**Departure: transparency.** The vendored file sets `backward.isDefEq.respectTransparency false`
for the whole file; this one does not set it.

**Classical, imported.** The scalar files of the vendored directory are wholly classical (the
error `mainFormalError`, the cascade scalars and their absorption bounds). They get no Co file:
this module imports the vendored `Test/MainTheorem/SourceScalars.lean`, which imports the others,
and names their declarations through explicit `open` lists. They are
- `Test/MainTheorem/ScalarBounds/Definitions.lean`,
- `Test/MainTheorem/ScalarBounds/EnvelopeBounds.lean`,
- `Test/MainTheorem/ScalarBounds/CascadeBounds/SigmaZeta1.lean`,
- `Test/MainTheorem/ScalarBounds/CascadeBounds/Zeta2Zeta3.lean`,
- `Test/MainTheorem/ScalarBounds/CascadeBounds/Zeta4.lean`,
- `Test/MainTheorem/ScalarBounds/CascadeBounds/Final.lean`,
- `Test/MainTheorem/SourceScalars.lean`,
all classical, imported.

## New here

- `mainFormal_isPVMIn`: the conclusion of `mainFormal`, with the two measurements projective
  measurements of the repository (`MIPRE.IsPVMIn`), through
  `MIPRE.LIDT.Co.ProjMeas.isPVMIn_of_isFinitePair` and its `B` form.
- `mainFormal_inconsistency`: the same, with the three consistency bounds stated as the
  inconsistency of the bipartite model (`MIPRE.BipartiteModel.inconsistency`), the form of
  `MIPRE.LIDT.Simul.SoundIn`, through `bipartiteConsError_eq_inconsistency`.

## Not ported

Every declaration of the vendored file has a counterpart here; all but
`mainFormal_trivial_witness` carry the new hypotheses `hM` and `hd`.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/test_definition.tex`, `thm:main-formal` at line 180;
- `references/ldt-paper/inductive_step.tex`, lines 26–236;
- `docs/paper-gaps/issue-906-main-formal-k-bound.tex` (`k ≥ 400 m d`) and
  `docs/paper-gaps/issue-422-main-formal-zero-k-boundary.tex` (`0 < k`).
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Test

open MIPStarRE.LDT (Parameters FieldModel Point uniformDistribution)
open MIPStarRE.LDT.MainInductionStep (mainInductionError)
open MIPStarRE.LDT.MakingMeasurementsProjective (orthonormalizationError
  orthonormalizeAndCompleteError)
open MIPStarRE.LDT.Test (mainFormalError MainFormalScalarBounds cascadeZeta1 cascadeZeta3
  cascadeLine169RepairError mainFormalScalarSigma_eq_mainInductionError)

variable {𝒞 : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞]
  {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  {ℬ : Type*} [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]

/-- **Saturated-error branch of `thm:main-formal`.** Whenever `mainFormalError params k ε ≥ 1`,
the three consistency conclusions hold for arbitrary projective polynomial measurements (here
the trivial ones), since each two-space consistency defect is at most `1` for a unit vector and a
uniform question distribution. Neither the test hypothesis nor `hM`, `hd` is used. -/
theorem mainFormal_trivial_witness
    (params : Parameters) [FieldModel params.q]
    (strategy : ProjStrat params 𝒞 𝒜 ℬ)
    (eps : ℝ) (k : ℕ)
    (herr : 1 ≤ mainFormalError params k eps) :
    ∃ G_A : ProjMeas (MIPStarRE.LDT.Polynomial params) 𝒜,
      ∃ G_B : ProjMeas (MIPStarRE.LDT.Polynomial params) ℬ,
        bipartiteConsError strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
            (polynomialEvaluationFamily params G_B.toSubMeas) ≤ mainFormalError params k eps ∧
        bipartiteConsError strategy.state (uniformDistribution (Point params))
            (polynomialEvaluationFamily params G_A.toSubMeas)
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB) ≤
          mainFormalError params k eps ∧
        bipartiteConsError strategy.state (uniformDistribution Unit)
            (constSubMeasFamily G_A.toSubMeas) (constSubMeasFamily G_B.toSubMeas) ≤
          mainFormalError params k eps := by
  classical
  let p₀ : MIPStarRE.LDT.Polynomial params := ⟨0, by intro i; simp [MvPolynomial.degreeOf_zero]⟩
  refine ⟨ProjMeas.trivialDistinguishedOutcome p₀, ProjMeas.trivialDistinguishedOutcome p₀,
    ?_, ?_, ?_⟩
  all_goals exact
    (TwoSpace.bipartiteConsError_uniform_le_one strategy.state strategy.isNormalized _ _).trans herr

/-- **The role-register conclusion with the scalar absorption**, once the scalar branch has
supplied `0 < k` and `mainFormalError params k ε < 1`: `sourceRoleRegisterFinalPointConsistency`
with its explicit errors weakened to `mainFormalError` by the vendored Step 8 cascade
(`MainFormalScalarBounds`).

Departure: the hypotheses `hM : strategy.state.IsDyadicPair` and `hd : 1 ≤ params.d` are new. -/
theorem mainFormalConclusion_ofRoleRegisterScalarBoundary
    (params : Parameters) [FieldModel params.q]
    (strategy : ProjStrat params 𝒞 𝒜 ℬ)
    (hM : strategy.state.IsDyadicPair) (hd : 1 ≤ params.d)
    (eps : ℝ) (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ) (hk : 400 * params.m * params.d ≤ k) (hk0 : 0 < k)
    (hsmall : ¬ 1 ≤ mainFormalError params k eps) :
    ∃ G_A : ProjMeas (MIPStarRE.LDT.Polynomial params) 𝒜,
      ∃ G_B : ProjMeas (MIPStarRE.LDT.Polynomial params) ℬ,
        bipartiteConsError strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
            (polynomialEvaluationFamily params G_B.toSubMeas) ≤ mainFormalError params k eps ∧
        bipartiteConsError strategy.state (uniformDistribution (Point params))
            (polynomialEvaluationFamily params G_A.toSubMeas)
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB) ≤
          mainFormalError params k eps ∧
        bipartiteConsError strategy.state (uniformDistribution Unit)
            (constSubMeasFamily G_A.toSubMeas) (constSubMeasFamily G_B.toSubMeas) ≤
          mainFormalError params k eps := by
  let scalars : MainFormalScalarBounds params eps k :=
    MainFormalScalarBounds.ofNontrivialMainFormal (ProjStrat.eps_nonneg_of_passes hpass) hk0
      hsmall
  let σ : ℝ := 2 * mainInductionError params k (3 * eps) (3 * eps) (3 * eps)
  let ζ₁ : ℝ := σ + 2 * Real.sqrt (3 * eps + σ) + (params.m * params.d : ℝ) / params.q
  let ζ₂ : ℝ := orthonormalizeAndCompleteError ζ₁
  let η : ℝ := ζ₁ + Real.sqrt (orthonormalizationError ζ₁)
  let ζ₃ : ℝ := 6 * ζ₁ + 6 * ζ₂
  have hσ : σ = 2 * scalars.sigma := by
    simp [σ, MainFormalScalarBounds.sigma, mainFormalScalarSigma_eq_mainInductionError]
  have hζ₁ : ζ₁ = scalars.zeta1 := by
    simp [ζ₁, σ, MainFormalScalarBounds.zeta1, cascadeZeta1, MainFormalScalarBounds.sigma,
      mainFormalScalarSigma_eq_mainInductionError]
  have hζ₂ : ζ₂ ≤ scalars.zeta2 := by
    change orthonormalizeAndCompleteError ζ₁ ≤ scalars.zeta2
    rw [hζ₁]
    exact MainFormalScalarBounds.orthonormalizeAndCompleteError_zeta1_le_zeta2 scalars hsmall
  have hη : η = scalars.line169Error := by
    have hsqrt := MIPStarRE.LDT.MakingMeasurementsProjective.sqrt_orthonormalizationError_eq
      (MainFormalScalarBounds.zeta1_nonneg scalars)
    simp [η, hζ₁, MainFormalScalarBounds.line169Error, cascadeLine169RepairError, hsqrt]
  have hζ₃ : ζ₃ ≤ scalars.zeta3 := by
    simp only [ζ₃, MainFormalScalarBounds.zeta3, cascadeZeta3]
    linarith [hζ₁.le]
  have hpoint : σ + 2 * Real.sqrt (η + ζ₃ / 2) ≤ mainFormalError params k eps := by
    have hsqrt : Real.sqrt (η + ζ₃ / 2) ≤
        Real.sqrt (scalars.line169Error + scalars.zeta3 / 2) :=
      Real.sqrt_le_sqrt (by linarith [hη.le])
    refine le_trans ?_ (MainFormalScalarBounds.zeta4Repaired_le_mainFormalError scalars)
    change _ ≤ 2 * scalars.sigma + 2 * Real.sqrt (scalars.line169Error + scalars.zeta3 / 2)
    linarith
  have hself : ζ₃ / 2 ≤ mainFormalError params k eps :=
    le_trans (by linarith) (MainFormalScalarBounds.zeta3_div_two_le_mainFormalError scalars)
  obtain ⟨Q_A, Q_B, hA, hB, -, hQQ⟩ :=
    ProjStrat.sourceRoleRegisterFinalPointConsistency params strategy hM hd eps hpass k hk
  exact ⟨Q_A, Q_B, hA.trans hpoint, hB.trans hpoint, hQQ.trans hself⟩

/-- **Small-error branch of `thm:main-formal`**: the role-register route with the scalar
absorption, once `0 < k` is supplied and `mainFormalError params k ε < 1`. It is not an
additional hypothesis of `thm:main-formal`: `mainFormalConclusion` calls it only after the
saturated branch has been discharged by `mainFormal_trivial_witness`.

Departure: the hypotheses `hM : strategy.state.IsDyadicPair` and `hd : 1 ≤ params.d` are new. -/
theorem mainFormal_smallErrorConclusion
    (params : Parameters) [FieldModel params.q]
    (strategy : ProjStrat params 𝒞 𝒜 ℬ)
    (hM : strategy.state.IsDyadicPair) (hd : 1 ≤ params.d)
    (eps : ℝ) (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ) (hk : 400 * params.m * params.d ≤ k) (hk0 : 0 < k)
    (hsmall : ¬ 1 ≤ mainFormalError params k eps) :
    ∃ G_A : ProjMeas (MIPStarRE.LDT.Polynomial params) 𝒜,
      ∃ G_B : ProjMeas (MIPStarRE.LDT.Polynomial params) ℬ,
        bipartiteConsError strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
            (polynomialEvaluationFamily params G_B.toSubMeas) ≤ mainFormalError params k eps ∧
        bipartiteConsError strategy.state (uniformDistribution (Point params))
            (polynomialEvaluationFamily params G_A.toSubMeas)
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB) ≤
          mainFormalError params k eps ∧
        bipartiteConsError strategy.state (uniformDistribution Unit)
            (constSubMeasFamily G_A.toSubMeas) (constSubMeasFamily G_B.toSubMeas) ≤
          mainFormalError params k eps :=
  mainFormalConclusion_ofRoleRegisterScalarBoundary params strategy hM hd eps hpass k hk hk0
    hsmall

/-- **Source-boundary reduction of `thm:main-formal`**: the saturated branch
(`mainFormal_trivial_witness`) when `mainFormalError params k ε ≥ 1`, the small-error branch
(`mainFormal_smallErrorConclusion`) otherwise.

Departure: the hypotheses `hM : strategy.state.IsDyadicPair` and `hd : 1 ≤ params.d` are new. -/
theorem mainFormalConclusion
    (params : Parameters) [FieldModel params.q]
    (strategy : ProjStrat params 𝒞 𝒜 ℬ)
    (hM : strategy.state.IsDyadicPair) (hd : 1 ≤ params.d)
    (eps : ℝ) (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ) (hk : 400 * params.m * params.d ≤ k) (hk0 : 0 < k) :
    ∃ G_A : ProjMeas (MIPStarRE.LDT.Polynomial params) 𝒜,
      ∃ G_B : ProjMeas (MIPStarRE.LDT.Polynomial params) ℬ,
        bipartiteConsError strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
            (polynomialEvaluationFamily params G_B.toSubMeas) ≤ mainFormalError params k eps ∧
        bipartiteConsError strategy.state (uniformDistribution (Point params))
            (polynomialEvaluationFamily params G_A.toSubMeas)
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB) ≤
          mainFormalError params k eps ∧
        bipartiteConsError strategy.state (uniformDistribution Unit)
            (constSubMeasFamily G_A.toSubMeas) (constSubMeasFamily G_B.toSubMeas) ≤
          mainFormalError params k eps := by
  by_cases hlarge : 1 ≤ mainFormalError params k eps
  · exact mainFormal_trivial_witness params strategy eps k hlarge
  · exact mainFormal_smallErrorConclusion params strategy hM hd eps hpass k hk hk0 hlarge

/-- **`thm:main-formal`, for a dyadic pair.** A projective strategy whose bipartite model is a
dyadic pair and whose failure probability in the low individual degree test is at most `ε` has
projective polynomial measurements `G_A` in `𝒜` and `G_B` in `ℬ` such that Alice's points are
consistent with Bob's evaluations of `G_B`, Alice's evaluations of `G_A` with Bob's points, and
`G_A` with `G_B`, each up to `mainFormalError params k ε`. As in the vendored theorem, the
paper's `k ≥ m d` is corrected to `k ≥ 400 m d`, and `0 < k` is assumed.

Departure: the hypotheses `hM : strategy.state.IsDyadicPair` and `hd : 1 ≤ params.d` are new. -/
theorem mainFormal
    (params : Parameters) [FieldModel params.q]
    (strategy : ProjStrat params 𝒞 𝒜 ℬ)
    (hM : strategy.state.IsDyadicPair) (hd : 1 ≤ params.d)
    (eps : ℝ) (hpass : strategy.lowIndividualDegreeFailureProbability ≤ eps)
    (k : ℕ) (hk : 400 * params.m * params.d ≤ k) (hk0 : 0 < k) :
    ∃ G_A : ProjMeas (MIPStarRE.LDT.Polynomial params) 𝒜,
      ∃ G_B : ProjMeas (MIPStarRE.LDT.Polynomial params) ℬ,
        bipartiteConsError strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
            (polynomialEvaluationFamily params G_B.toSubMeas) ≤ mainFormalError params k eps ∧
        bipartiteConsError strategy.state (uniformDistribution (Point params))
            (polynomialEvaluationFamily params G_A.toSubMeas)
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB) ≤
          mainFormalError params k eps ∧
        bipartiteConsError strategy.state (uniformDistribution Unit)
            (constSubMeasFamily G_A.toSubMeas) (constSubMeasFamily G_B.toSubMeas) ≤
          mainFormalError params k eps :=
  mainFormalConclusion params strategy hM hd eps ⟨hpass⟩ k hk hk0

/-! ### Readouts for the soundness adapters -/

/-- **`thm:main-formal` with projective measurements of the repository**: the measurements of
`mainFormal` are `MIPRE.IsPVMIn` in `𝒜` and `ℬ`, as every projective measurement of a player's
algebra of a finite pair is (`MIPRE.LIDT.Co.ProjMeas.isPVMIn_of_isFinitePair`). -/
theorem mainFormal_isPVMIn
    (params : Parameters) [FieldModel params.q]
    (strategy : ProjStrat params 𝒞 𝒜 ℬ)
    (hM : strategy.state.IsDyadicPair) (hd : 1 ≤ params.d)
    (eps : ℝ) (hpass : strategy.lowIndividualDegreeFailureProbability ≤ eps)
    (k : ℕ) (hk : 400 * params.m * params.d ≤ k) (hk0 : 0 < k) :
    ∃ G_A : ProjMeas (MIPStarRE.LDT.Polynomial params) 𝒜,
      ∃ G_B : ProjMeas (MIPStarRE.LDT.Polynomial params) ℬ,
        IsPVMIn G_A.outcome ∧ IsPVMIn G_B.outcome ∧
        bipartiteConsError strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
            (polynomialEvaluationFamily params G_B.toSubMeas) ≤ mainFormalError params k eps ∧
        bipartiteConsError strategy.state (uniformDistribution (Point params))
            (polynomialEvaluationFamily params G_A.toSubMeas)
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB) ≤
          mainFormalError params k eps ∧
        bipartiteConsError strategy.state (uniformDistribution Unit)
            (constSubMeasFamily G_A.toSubMeas) (constSubMeasFamily G_B.toSubMeas) ≤
          mainFormalError params k eps := by
  obtain ⟨G_A, G_B, h⟩ := mainFormal params strategy hM hd eps hpass k hk hk0
  exact ⟨G_A, G_B, ProjMeas.isPVMIn_of_isFinitePair hM.isFinitePair G_A,
    ProjMeas.isPVMIn_of_isFinitePairB hM.isFinitePair G_B, h⟩

/-- **`thm:main-formal` as inconsistencies of the bipartite model**: the three consistency
bounds of `mainFormal_isPVMIn`, stated as `MIPRE.BipartiteModel.inconsistency` of measurement
families weighted by the uniform question distribution, the form of the consistency conclusions of
`MIPRE.LIDT.Simul.SoundIn` (through `bipartiteConsError_eq_inconsistency`). -/
theorem mainFormal_inconsistency
    (params : Parameters) [FieldModel params.q]
    (strategy : ProjStrat params 𝒞 𝒜 ℬ)
    (hM : strategy.state.IsDyadicPair) (hd : 1 ≤ params.d)
    (eps : ℝ) (hpass : strategy.lowIndividualDegreeFailureProbability ≤ eps)
    (k : ℕ) (hk : 400 * params.m * params.d ≤ k) (hk0 : 0 < k) :
    ∃ G_A : ProjMeas (MIPStarRE.LDT.Polynomial params) 𝒜,
      ∃ G_B : ProjMeas (MIPStarRE.LDT.Polynomial params) ℬ,
        IsPVMIn G_A.outcome ∧ IsPVMIn G_B.outcome ∧
        strategy.state.inconsistency (uniformDistribution (Point params)).weight
            (fun u => (strategy.pointMeasurementA u).toPOVMIn)
            (fun u => (polynomialEvaluationMeasurementFamily params G_B.toMeasurement u).toPOVMIn)
          ≤ mainFormalError params k eps ∧
        strategy.state.inconsistency (uniformDistribution (Point params)).weight
            (fun u => (polynomialEvaluationMeasurementFamily params G_A.toMeasurement u).toPOVMIn)
            (fun u => (strategy.pointMeasurementB u).toPOVMIn)
          ≤ mainFormalError params k eps ∧
        strategy.state.inconsistency (uniformDistribution Unit).weight
            (fun _ => G_A.toPOVMIn) (fun _ => G_B.toPOVMIn) ≤ mainFormalError params k eps := by
  classical
  obtain ⟨G_A, G_B, hA, hB, h1, h2, h3⟩ :=
    mainFormal_isPVMIn params strategy hM hd eps hpass k hk hk0
  refine ⟨G_A, G_B, hA, hB, ?_, ?_, ?_⟩
  · exact (bipartiteConsError_eq_inconsistency _ (IdxProjMeas.toIdxMeas strategy.pointMeasurementA)
      (polynomialEvaluationMeasurementFamily params G_B.toMeasurement)).symm.le.trans h1
  · exact (bipartiteConsError_eq_inconsistency _
      (polynomialEvaluationMeasurementFamily params G_A.toMeasurement)
      (IdxProjMeas.toIdxMeas strategy.pointMeasurementB)).symm.le.trans h2
  · exact (bipartiteConsError_eq_inconsistency _ (fun _ : Unit => G_A.toMeasurement)
      (fun _ : Unit => G_B.toMeasurement)).symm.le.trans h3

end MIPRE.LIDT.Co.Test

end

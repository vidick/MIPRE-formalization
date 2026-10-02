/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Test/
StrategyBiProj/Measurements.lean, to the models of `planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Test.StrategyFailures

@[expose] public section

/-!
# Two-space projective strategies: the failure surrogate

The failure surrogate of a two-space projective strategy (`ProjStrat`, `Co/Test/StrategyCore.lean`)
for the low-individual-degree test: the counterpart of the surrogate half of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Test/StrategyBiProj/Measurements.lean` in the port of
`planning/c6b-plan.md` (milestone M2; `reports/c6b-paper-proofs.md`, §4, Theorem D, the
surrogate `fail_M`). The doubling (`Co/Doubling/Strategy.lean`) consumes it: a strategy whose
surrogate is at most `ε` doubles to a `(3ε, 3ε, 3ε)`-good symmetric strategy.

**The two-space defect.** The vendored surrogate is built from `bipartiteConsError ψ`, for a state
`ψ` on `ιA × ιB`: the bipartite defect of a submeasurement `A` of the first factor and `B` of the
second is inherently a two-space quantity. The port's `SymModel.bipartiteConsError`
(`Co/Test/Defs.lean`) is its symmetric-model form, with both families in one local algebra. This
file adds the two-space form over a bipartite model `M : MIPRE.BipartiteModel 𝒞 𝒜 ℬ` of the
repository, with `ev (A ⊗ B)` read as the Born probability `M.bornProb A B`: `qBipartiteMatchMass`,
`qBipartiteConsDefect` and `bipartiteConsError`, in the root namespace `MIPRE.LIDT.Co` and with the
state an explicit argument, as in the vendored file, so that the vendored text
`bipartiteConsError strategy.state 𝒟 A B` ports unchanged. On the bipartite model of a symmetric
model they are the symmetric-model quantities (`SymModel.bipartiteConsError_toBipartite`, by
`rfl`). This departs from the port convention that bipartite defects are `SymModel` declarations
(`planning/c6b-plan.md`, "Port conventions"): the departure is needed because the two-space
`ProjStrat` keeps its two algebras, and only its failure surrogate is stated with it; its
consistency conclusions remain `MIPRE.BipartiteModel.inconsistency`.

**The surrogate** (`lowIndividualDegreeFailureProbability`) is the vendored expression verbatim,
with the vendored answer families and branch probabilities, and the decomposition into its three
branch averages (`lowIndividualDegreeFailureProbability_eq_role_averages`, by `rfl`). The
nonnegativity lemmas of the branches, which the vendored development keeps in
`Test/StrategyBiProjRoleAverage/Final.lean`, are here, beside the definitions; the goodness bound
of that file is `Doubling.symmStrat_isGood_three_mul` (`Co/Doubling/Strategy.lean`).

## Not ported

- `localDirectSumMeasurement`: the role-register direct sum `ιA ⊕ ιB` of the vendored
  symmetrization; replaced by the doubling `Co/Doubling/`.
- `localDirectSumMeasurement_outcome`: as `localDirectSumMeasurement`.
- `localDirectSumMeasurement_total`: as `localDirectSumMeasurement`.
- `localDirectSumProjMeas`: as `localDirectSumMeasurement`.
- `localDirectSumProjMeas_outcome`: as `localDirectSumMeasurement`.
- `roleBlockMeasurement`: the role-register block; replaced by the doubling.
- `roleBlockMeasurement_outcome`: as `roleBlockMeasurement`.
- `roleBlockMeasurement_total`: as `roleBlockMeasurement`.
- `roleBlockProjMeas`: as `roleBlockMeasurement`.
- `roleBlockProjMeas_outcome`: as `roleBlockMeasurement`.
- `roleRegisterProjMeas`: the role-register measurement; replaced by the componentwise pairing
  `Doubling.pairProjMeas` (`Co/Doubling/Strategy.lean`).
- `roleRegisterProjMeas_A_inl_inl`: as `roleRegisterProjMeas`.
- `roleRegisterProjMeas_B_inr_inr`: as `roleRegisterProjMeas`.
- `roleRegisterProjMeas_A_B`: as `roleRegisterProjMeas`.
- `roleRegisterProjMeas_B_A`: as `roleRegisterProjMeas`.
- `roleRegisterPointMeasurement`: replaced by `Doubling.symmStrat`'s point measurement.
- `roleRegisterAxisParallelMeasurement`: replaced by `Doubling.symmStrat`'s axis-parallel
  measurement.
- `roleRegisterDiagonalMeasurement`: replaced by `Doubling.symmStrat`'s diagonal measurement.
- `roleRegisterAxisParallelTransportInvariant`: replaced by
  `Doubling.pairAxisParallel_reparamInvariant`.
- `roleRegisterDiagonalTransportInvariant`: replaced by `Doubling.pairDiagonal_reparamInvariant`.
- `roleRegisterSymmStrategy`: replaced by the doubled strategy `Doubling.symmStrat`.
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co

open MIPStarRE.LDT (Parameters FieldModel Point Fq zeroCoord Distribution avgOver
  avgOver_nonneg uniformDistribution AxisParallelLine DiagonalLine AxisParallelTestSample
  RestrictedDiagonalSample extendRestrictedDirection)

/-! ### The two-space bipartite defect -/

section TwoSpace

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [PartialOrder 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder ℬ]
  (M : MIPRE.BipartiteModel 𝒞 𝒜 ℬ)

/-- Two-space bipartite matching mass `∑_a ⟨ψ, (A_a ⊗ B_a) ψ⟩ = ∑_a bornProb (A_a, B_a)`, with
`A` in the first player's algebra and `B` in the second's (the vendored `qBipartiteMatchMass` on
`ιA × ιB`). -/
noncomputable def qBipartiteMatchMass {Outcome : Type*} [Fintype Outcome]
    (A : SubMeas Outcome 𝒜) (B : SubMeas Outcome ℬ) : ℝ :=
  ∑ a, M.bornProb (A.outcome a) (B.outcome a)

/-- Two-space bipartite questionwise consistency defect
`max 0 (⟨ψ, (A_total ⊗ B_total) ψ⟩ − ∑_a ⟨ψ, (A_a ⊗ B_a) ψ⟩)` (the vendored
`qBipartiteConsDefect` on `ιA × ιB`). -/
noncomputable def qBipartiteConsDefect {Outcome : Type*} [Fintype Outcome]
    (A : SubMeas Outcome 𝒜) (B : SubMeas Outcome ℬ) : ℝ :=
  max 0 (M.bornProb A.total B.total - qBipartiteMatchMass M A B)

/-- Two-space averaged bipartite consistency defect (the vendored `bipartiteConsError` on
`ιA × ιB`). -/
noncomputable def bipartiteConsError {Question Outcome : Type*} [Fintype Outcome]
    (𝒟 : Distribution Question) (A : IdxSubMeas Question Outcome 𝒜)
    (B : IdxSubMeas Question Outcome ℬ) : ℝ :=
  avgOver 𝒟 (fun q => qBipartiteConsDefect M (A q) (B q))

/-- The two-space bipartite consistency defect is nonnegative. -/
theorem qBipartiteConsDefect_nonneg {Outcome : Type*} [Fintype Outcome]
    (A : SubMeas Outcome 𝒜) (B : SubMeas Outcome ℬ) :
    0 ≤ qBipartiteConsDefect M A B :=
  le_max_left 0 _

/-- The two-space averaged bipartite consistency defect is nonnegative. -/
theorem bipartiteConsError_nonneg {Question Outcome : Type*} [Fintype Outcome]
    (𝒟 : Distribution Question) (A : IdxSubMeas Question Outcome 𝒜)
    (B : IdxSubMeas Question Outcome ℬ) :
    0 ≤ bipartiteConsError M 𝒟 A B :=
  avgOver_nonneg 𝒟 _ fun _ => qBipartiteConsDefect_nonneg M _ _

end TwoSpace

/-- **The two-space defect generalizes the symmetric one**: on the bipartite model of a symmetric
model, the two-space averaged defect is `SymModel.bipartiteConsError`. -/
theorem SymModel.bipartiteConsError_toBipartite {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓]
    [StarOrderedRing 𝔓] {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (S : SymModel 𝔓 K) {Question Outcome : Type*} [Fintype Outcome]
    (𝒟 : Distribution Question) (A B : IdxSubMeas Question Outcome 𝔓) :
    MIPRE.LIDT.Co.bipartiteConsError S.toBipartite 𝒟 A B = S.bipartiteConsError 𝒟 A B :=
  rfl

namespace ProjStrat

variable {params : Parameters} [FieldModel params.q]
  {𝒞 : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞]
  {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  {ℬ : Type*} [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]

/-! ### Answer families -/

/-- Alice's point answers in the axis-parallel branch: Alice receives `u`,
the base point of the sampled line, and answers with `A^{A,u}`. -/
noncomputable def axisParallelPointAnswerFamilyA
    (strategy : ProjStrat params 𝒞 𝒜 ℬ) :
    IdxSubMeas (AxisParallelTestSample params) (Fq params) 𝒜 :=
  fun s => (strategy.pointMeasurementA s.1).toSubMeas

/-- Bob's point answers in the axis-parallel branch: Bob receives `u`,
the base point of the sampled line, and answers with `A^{B,u}`. -/
noncomputable def axisParallelPointAnswerFamilyB
    (strategy : ProjStrat params 𝒞 𝒜 ℬ) :
    IdxSubMeas (AxisParallelTestSample params) (Fq params) ℬ :=
  fun s => (strategy.pointMeasurementB s.1).toSubMeas

/-- Alice's axis-parallel-line answers: Alice receives `ℓ`, answers with
`B^{A,ℓ}`, and the verifier postprocesses to the value at the sampled base
point. -/
noncomputable def axisParallelLineAnswerFamilyA
    (strategy : ProjStrat params 𝒞 𝒜 ℬ) :
    IdxSubMeas (AxisParallelTestSample params) (Fq params) 𝒜 :=
  fun s =>
    let ℓ : AxisParallelLine params :=
      { base := s.1, direction := s.2 }
    postprocess
      ((strategy.axisParallelMeasurementA ℓ).toSubMeas)
      (· zeroCoord)

/-- Bob's axis-parallel-line answers: Bob receives `ℓ`, answers with
`B^{B,ℓ}`, and the verifier postprocesses to the value at the sampled base
point. -/
noncomputable def axisParallelLineAnswerFamilyB
    (strategy : ProjStrat params 𝒞 𝒜 ℬ) :
    IdxSubMeas (AxisParallelTestSample params) (Fq params) ℬ :=
  fun s =>
    let ℓ : AxisParallelLine params :=
      { base := s.1, direction := s.2 }
    postprocess
      ((strategy.axisParallelMeasurementB ℓ).toSubMeas)
      (· zeroCoord)

/-- Alice's point answers in the restricted diagonal branch: Alice receives the
sampled base point `u` and answers with `A^{A,u}`. -/
noncomputable def diagonalPointAnswerFamilyA
    (strategy : ProjStrat params 𝒞 𝒜 ℬ) (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j) (Fq params) 𝒜 :=
  fun s => (strategy.pointMeasurementA s.1).toSubMeas

/-- Bob's point answers in the restricted diagonal branch: Bob receives the
sampled base point `u` and answers with `A^{B,u}`. -/
noncomputable def diagonalPointAnswerFamilyB
    (strategy : ProjStrat params 𝒞 𝒜 ℬ) (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j) (Fq params) ℬ :=
  fun s => (strategy.pointMeasurementB s.1).toSubMeas

/-- Alice's restricted diagonal-line answers: Alice receives `ℓ`, answers with
`L^{A,ℓ}`, and the verifier postprocesses to the value at the sampled base
point. -/
noncomputable def diagonalLineAnswerFamilyA
    (strategy : ProjStrat params 𝒞 𝒜 ℬ) (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j) (Fq params) 𝒜 :=
  fun s =>
    let v := extendRestrictedDirection j s.2
    let ℓ : DiagonalLine params :=
      { base := s.1, direction := v }
    postprocess
      ((strategy.diagonalMeasurementA ℓ).toSubMeas)
      (· zeroCoord)

/-- Bob's restricted diagonal-line answers: Bob receives `ℓ`, answers with
`L^{B,ℓ}`, and the verifier postprocesses to the value at the sampled base
point. -/
noncomputable def diagonalLineAnswerFamilyB
    (strategy : ProjStrat params 𝒞 𝒜 ℬ) (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j) (Fq params) ℬ :=
  fun s =>
    let v := extendRestrictedDirection j s.2
    let ℓ : DiagonalLine params :=
      { base := s.1, direction := v }
    postprocess
      ((strategy.diagonalMeasurementB ℓ).toSubMeas)
      (· zeroCoord)

/-! ### Branch failure probabilities -/

/-- Axis-parallel branch component where Alice receives the sampled line and Bob
receives its base point. -/
noncomputable def axisParallelLineLeftPointRightFailureProbability
    (strategy : ProjStrat params 𝒞 𝒜 ℬ) : ℝ :=
  bipartiteConsError strategy.state
    (uniformDistribution (AxisParallelTestSample params))
    (axisParallelLineAnswerFamilyA strategy)
    (axisParallelPointAnswerFamilyB strategy)

/-- Axis-parallel branch component where Alice receives the sampled base point
and Bob receives the sampled line. -/
noncomputable def axisParallelPointLeftLineRightFailureProbability
    (strategy : ProjStrat params 𝒞 𝒜 ℬ) : ℝ :=
  bipartiteConsError strategy.state
    (uniformDistribution (AxisParallelTestSample params))
    (axisParallelPointAnswerFamilyA strategy)
    (axisParallelLineAnswerFamilyB strategy)

/-- The paper's axis-parallel branch for a two-space general strategy, averaged
over the two role choices. -/
noncomputable def axisParallelRoleAverage
    (strategy : ProjStrat params 𝒞 𝒜 ℬ) : ℝ :=
  (axisParallelLineLeftPointRightFailureProbability strategy +
    axisParallelPointLeftLineRightFailureProbability strategy) / 2

/-- Point-agreement branch: both provers receive the same point and the verifier
checks equality of their field answers. -/
noncomputable def pointAgreementFailureProbability
    (strategy : ProjStrat params 𝒞 𝒜 ℬ) : ℝ :=
  bipartiteConsError strategy.state
    (uniformDistribution (Point params))
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)

/-- Diagonal branch component where Alice receives the sampled diagonal line and
Bob receives its base point. -/
noncomputable def diagonalLineLeftPointRightFailureProbability
    (strategy : ProjStrat params 𝒞 𝒜 ℬ) : ℝ :=
  (1 / (params.m : ℝ)) *
    ∑ j : Fin params.m,
      bipartiteConsError strategy.state
        (uniformDistribution (RestrictedDiagonalSample params j))
        (diagonalLineAnswerFamilyA strategy j)
        (diagonalPointAnswerFamilyB strategy j)

/-- Diagonal branch component where Alice receives the sampled base point and
Bob receives the sampled diagonal line. -/
noncomputable def diagonalPointLeftLineRightFailureProbability
    (strategy : ProjStrat params 𝒞 𝒜 ℬ) : ℝ :=
  (1 / (params.m : ℝ)) *
    ∑ j : Fin params.m,
      bipartiteConsError strategy.state
        (uniformDistribution (RestrictedDiagonalSample params j))
        (diagonalPointAnswerFamilyA strategy j)
        (diagonalLineAnswerFamilyB strategy j)

/-- The paper's diagonal branch for a two-space general strategy, averaged over
the two role choices and the restricted diagonal samples. -/
noncomputable def diagonalRoleAverage
    (strategy : ProjStrat params 𝒞 𝒜 ℬ) : ℝ :=
  (diagonalLineLeftPointRightFailureProbability strategy +
    diagonalPointLeftLineRightFailureProbability strategy) / 2

/-! ### The surrogate -/

/-- Failure surrogate for the full low-individual-degree test for a
paper-faithful two-space projective strategy (the vendored expression verbatim).

The three outer summands are respectively axis-parallel consistency, point
agreement, and restricted-diagonal consistency, with outer weight `1 / 3`.
Each line branch averages the two prover-role orderings with weight `1 / 2`, and
the restricted-diagonal branch also averages its restriction index with weight
`1 / m`.  Line answers are evaluated at `zeroCoord`, the parameter value of the
sampled base point. -/
noncomputable def lowIndividualDegreeFailureProbability
    (strategy : ProjStrat params 𝒞 𝒜 ℬ) : ℝ :=
  let axisPointA : IdxSubMeas (Point params × Fin params.m) (Fq params) 𝒜 :=
    fun s => (strategy.pointMeasurementA s.1).toSubMeas
  let axisPointB : IdxSubMeas (Point params × Fin params.m) (Fq params) ℬ :=
    fun s => (strategy.pointMeasurementB s.1).toSubMeas
  let axisLineA : IdxSubMeas (Point params × Fin params.m) (Fq params) 𝒜 :=
    fun s =>
      let ℓ : AxisParallelLine params := { base := s.1, direction := s.2 }
      postprocess ((strategy.axisParallelMeasurementA ℓ).toSubMeas) (· zeroCoord)
  let axisLineB : IdxSubMeas (Point params × Fin params.m) (Fq params) ℬ :=
    fun s =>
      let ℓ : AxisParallelLine params := { base := s.1, direction := s.2 }
      postprocess ((strategy.axisParallelMeasurementB ℓ).toSubMeas) (· zeroCoord)
  let extendDirection (j : Fin params.m)
      (freeCoords : Fin (j.val + 1) → Fq params) : Point params :=
    fun k =>
      if h : k.val ≤ j.val then
        freeCoords ⟨k.val, Nat.lt_succ_of_le h⟩
      else zeroCoord
  let diagonalPointA (j : Fin params.m) :
      IdxSubMeas (Point params × (Fin (j.val + 1) → Fq params)) (Fq params) 𝒜 :=
    fun s => (strategy.pointMeasurementA s.1).toSubMeas
  let diagonalPointB (j : Fin params.m) :
      IdxSubMeas (Point params × (Fin (j.val + 1) → Fq params)) (Fq params) ℬ :=
    fun s => (strategy.pointMeasurementB s.1).toSubMeas
  let diagonalLineA (j : Fin params.m) :
      IdxSubMeas (Point params × (Fin (j.val + 1) → Fq params)) (Fq params) 𝒜 :=
    fun s =>
      let ℓ : DiagonalLine params := { base := s.1, direction := extendDirection j s.2 }
      postprocess ((strategy.diagonalMeasurementA ℓ).toSubMeas) (· zeroCoord)
  let diagonalLineB (j : Fin params.m) :
      IdxSubMeas (Point params × (Fin (j.val + 1) → Fq params)) (Fq params) ℬ :=
    fun s =>
      let ℓ : DiagonalLine params := { base := s.1, direction := extendDirection j s.2 }
      postprocess ((strategy.diagonalMeasurementB ℓ).toSubMeas) (· zeroCoord)
  ((bipartiteConsError strategy.state
        (@uniformDistribution (Point params × Fin params.m) _ _
          ⟨(fun _ => zeroCoord, default)⟩) axisLineA axisPointB +
      bipartiteConsError strategy.state
        (@uniformDistribution (Point params × Fin params.m) _ _
          ⟨(fun _ => zeroCoord, default)⟩) axisPointA axisLineB) / ((2 : ℕ) : ℝ) +
    bipartiteConsError strategy.state
      (@uniformDistribution (Point params) _ _ ⟨fun _ => zeroCoord⟩)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB) +
    ((1 / (params.m : ℝ)) * ∑ j : Fin params.m,
        bipartiteConsError strategy.state
          (@uniformDistribution (Point params × (Fin (j.val + 1) → Fq params)) _ _
            ⟨(fun _ => zeroCoord, fun _ => zeroCoord)⟩)
          (diagonalLineA j) (diagonalPointB j) +
      (1 / (params.m : ℝ)) * ∑ j : Fin params.m,
        bipartiteConsError strategy.state
          (@uniformDistribution (Point params × (Fin (j.val + 1) → Fq params)) _ _
            ⟨(fun _ => zeroCoord, fun _ => zeroCoord)⟩)
          (diagonalPointA j) (diagonalLineB j)) / ((2 : ℕ) : ℝ)) / 3

/-- The direct low-individual-degree score agrees with its decomposition into
axis-parallel, point-agreement, and restricted-diagonal role averages. -/
theorem lowIndividualDegreeFailureProbability_eq_role_averages
    (strategy : ProjStrat params 𝒞 𝒜 ℬ) :
    strategy.lowIndividualDegreeFailureProbability =
      (strategy.axisParallelRoleAverage + strategy.pointAgreementFailureProbability +
        strategy.diagonalRoleAverage) / 3 := by
  rfl

/-- Passing the full low-individual-degree test with error `ε`, for the
paper-faithful two-space strategy container. -/
structure PassesLowIndividualDegreeTest
    (strategy : ProjStrat params 𝒞 𝒜 ℬ) (eps : ℝ) : Prop where
  /-- The failure surrogate is at most `ε`. -/
  soundnessHypothesis : strategy.lowIndividualDegreeFailureProbability ≤ eps

/-! ### Nonnegativity (the vendored `Test/StrategyBiProjRoleAverage/Final.lean`) -/

/-- The axis-parallel role-average branch of a two-space projective strategy is
nonnegative. -/
theorem axisParallelRoleAverage_nonneg (strategy : ProjStrat params 𝒞 𝒜 ℬ) :
    0 ≤ strategy.axisParallelRoleAverage :=
  div_nonneg (add_nonneg (bipartiteConsError_nonneg _ _ _ _)
    (bipartiteConsError_nonneg _ _ _ _)) zero_le_two

/-- The point-agreement branch of a two-space projective strategy is
nonnegative. -/
theorem pointAgreementFailureProbability_nonneg (strategy : ProjStrat params 𝒞 𝒜 ℬ) :
    0 ≤ strategy.pointAgreementFailureProbability :=
  bipartiteConsError_nonneg _ _ _ _

/-- The diagonal role-average branch of a two-space projective strategy is
nonnegative. -/
theorem diagonalRoleAverage_nonneg (strategy : ProjStrat params 𝒞 𝒜 ℬ) :
    0 ≤ strategy.diagonalRoleAverage :=
  div_nonneg (add_nonneg
    (mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => bipartiteConsError_nonneg _ _ _ _))
    (mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => bipartiteConsError_nonneg _ _ _ _)))
    zero_le_two

/-- The full low-individual-degree failure probability of a two-space projective
strategy is nonnegative. -/
theorem lowIndividualDegreeFailureProbability_nonneg (strategy : ProjStrat params 𝒞 𝒜 ℬ) :
    0 ≤ strategy.lowIndividualDegreeFailureProbability := by
  rw [lowIndividualDegreeFailureProbability_eq_role_averages]
  have := strategy.axisParallelRoleAverage_nonneg
  have := strategy.pointAgreementFailureProbability_nonneg
  have := strategy.diagonalRoleAverage_nonneg
  positivity

/-- Any passing two-space projective strategy has a nonnegative error
parameter. -/
theorem eps_nonneg_of_passes {strategy : ProjStrat params 𝒞 𝒜 ℬ} {eps : ℝ}
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    0 ≤ eps :=
  strategy.lowIndividualDegreeFailureProbability_nonneg.trans hpass.soundnessHypothesis

end ProjStrat

end MIPRE.LIDT.Co

end

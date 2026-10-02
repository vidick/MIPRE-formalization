/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
MainInductionStep/Defs.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored
file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Test.StrategyCore
public import MIPRE.Background.LIDT.MIPStarRE.LDT.MainInductionStep.Defs

@[expose] public section

/-!
# Section 6 — Definitions

Restriction maps, the restricted strategy, its failure surrogates and the tensor-failure
expectation of the induction step: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/MainInductionStep/Defs.lean` in the port of
`planning/c6b-plan.md` (milestone M4, section "Port conventions").

A strategy here is a `SymStrat params.next 𝔓 K` (`Co/Test/StrategyCore.lean`): the local
operators live in the C*-algebra `𝔓`, the state is a symmetric model `strategy.state :
SymModel 𝔓 K`. Restricting a strategy to the slice at height `x` reindexes its measurement
families and keeps its state, as in the vendored file. The restricted strategy
`RestrictedSymStrat` keeps the vendored fields except `isNormalized`, which is a theorem of the
model (`RestrictedSymStrat.isNormalized`); the vendored `AnswerSymStrat` fields `permInvState`
and `densityFixed`, set by `xRestrictedAnswerSymStrat`, are not fields of the ported
`AnswerSymStrat` (`Co/Test/StrategyCore.lean`).

The vendored `tensorFailureExpectation` is stated for a state on a product `ιA × ιB` of two
carriers. Its vendored uses (`MainInductionStep/Theorems/{PastingAssembly,
SelfImprovementAssembly}`) apply it to the state of a symmetric strategy, so here it is narrowed
to one local algebra in a symmetric model, `S.ev (S.L Z * S.R (1 - H.total))`, as M3 narrowed the
heterogeneous triangle lemmas (`planning/c6b-plan.md`, "Departures in M3 and M5").

The classical half of the vendored file (the answer lift and its equivalence, the canonical
diagonal representative, the error constants and the slice weights) is not ported: this file
imports the vendored file and names those declarations through an explicit
`open MIPStarRE.LDT.MainInductionStep (…)` list.

## Not ported

- `liftAxisAnswer`: classical, imported.
- `axisLinePolynomialEquiv`: classical, imported.
- `diagonalValueRepresentative`: classical, imported.
- `mainInductionNu`: classical, imported.
- `mainInductionError`: classical, imported.
- `selfImprovementInInductionError`: classical, imported.
- `ldPastingInInductionNu`: classical, imported.
- `ldPastingInInductionError`: classical, imported.
- `sliceTransverseDirectionWeight`: classical, imported.
- `sliceConditioningLoss`: classical, imported.

## Ported elsewhere

The field `isNormalized` of `RestrictedSymStrat` is the theorem `RestrictedSymStrat.isNormalized`
below.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/inductive_step.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.MainInductionStep

open MIPStarRE.LDT (Parameters FieldModel Point Fq zeroCoord appendPoint uniformDistribution
  AxisParallelLine AxisLinePolynomial DiagonalLine DiagonalLinePolynomial DiagonalLineAnswer
  AxisParallelTestSample RestrictedDiagonalSample)
open MIPStarRE.LDT.MainInductionStep (liftAxisAnswer axisLinePolynomialEquiv
  diagonalValueRepresentative)
open MIPRE.LIDT.Co (SymStrat AnswerSymStrat AxisParallelCovariantMeasurement
  DiagonalAnswerMeasurementTransportInvariant)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Restricted slice data keeps the point and axis-parallel measurements
complete, and packages a genuine projective measurement on the slice's diagonal
answer space.

The paper's outcome-level formula would send a slice polynomial `f` to the
ambient outcome `append_x(f)`. With the current ambient diagonal answer
encoding, that map is not total on all ambient outcomes, so here we preserve the
verifier-visible base-point readout used in Chapter 10 instead: first
postprocess the ambient slice-preserving diagonal measurement to its value at
`zeroCoord` in `F_q`, then re-embed that `F_q`-valued projective measurement
into the honest slice answer space `DiagonalLinePolynomial params` using
canonical representatives.

The vendored field `isNormalized` is a theorem of the symmetric model `state`
(`RestrictedSymStrat.isNormalized`). -/
structure RestrictedSymStrat (params : Parameters) [FieldModel params.q]
    (𝔓 : Type*) [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
    (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] where
  /-- The bipartite state carried by the restricted strategy. -/
  state : SymModel 𝔓 K
  /-- The restricted point measurement. -/
  pointMeasurement : IdxProjMeas (Point params) (Fq params) 𝔓
  /-- The restricted axis-parallel line measurement, packaged with transport covariance. -/
  axisParallelMeasurement : AxisParallelCovariantMeasurement params 𝔓
  /-- The restricted diagonal-line measurement on the honest slice answer space. -/
  diagonalMeasurement :
    IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) 𝔓

namespace RestrictedSymStrat

/-- The state of a restricted strategy is normalized (the vendored field
`RestrictedSymStrat.isNormalized`, a theorem of the model). -/
theorem isNormalized {params : Parameters} [FieldModel params.q]
    (strategy : RestrictedSymStrat params 𝔓 K) : strategy.state.IsNormalized :=
  strategy.state.isNormalized

/-- Sampled point answers in the axis-parallel lines test.
Point player receives `u` (base point) and answers at `u`. -/
noncomputable def axisParallelPointAnswerFamily
    {params : Parameters} [FieldModel params.q]
    (strategy : RestrictedSymStrat params 𝔓 K) :
    IdxSubMeas (AxisParallelTestSample params) (Fq params) 𝔓 :=
  axisParallelPointAnswerFamilyOf strategy.pointMeasurement

/-- Sampled line answers in the axis-parallel lines test,
evaluated at the base point `u` (parameter `zeroCoord`). -/
noncomputable def axisParallelLineAnswerFamily
    {params : Parameters} [FieldModel params.q]
    (strategy : RestrictedSymStrat params 𝔓 K) :
    IdxSubMeas (AxisParallelTestSample params) (Fq params) 𝔓 :=
  axisParallelLineAnswerFamilyOf strategy.axisParallelMeasurement

/-- Sampled point answers in the `j`-restricted diagonal test.
Point player receives `u` and answers at `u`. -/
noncomputable def restrictedDiagonalPointAnswerFamily
    {params : Parameters} [FieldModel params.q]
    (strategy : RestrictedSymStrat params 𝔓 K) (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j) (Fq params) 𝔓 :=
  diagonalPointAnswerFamilyOf strategy.pointMeasurement j

/-- Sampled diagonal-line answers in the `j`-restricted diagonal
test, evaluated at the base point (parameter `zeroCoord`). -/
noncomputable def restrictedDiagonalLineAnswerFamily
    {params : Parameters} [FieldModel params.q]
    (strategy : RestrictedSymStrat params 𝔓 K) (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j) (Fq params) 𝔓 :=
  diagonalLineAnswerFamilyOf strategy.diagonalMeasurement (· zeroCoord) j

/-- Failure surrogate for the axis-parallel lines test. -/
noncomputable def axisParallelFailureProbability
    {params : Parameters} [FieldModel params.q]
    (strategy : RestrictedSymStrat params 𝔓 K) : ℝ :=
  strategy.state.bipartiteConsError
    (uniformDistribution (AxisParallelTestSample params))
    (axisParallelPointAnswerFamily strategy)
    (axisParallelLineAnswerFamily strategy)

/-- Failure surrogate for the self-consistency test. -/
noncomputable def selfConsistencyFailureProbability
    {params : Parameters} [FieldModel params.q]
    (strategy : RestrictedSymStrat params 𝔓 K) : ℝ :=
  strategy.state.bipartiteSSCError
    (uniformDistribution (Point params))
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)

/-- Failure surrogate for the diagonal lines test.
Averages over restriction index `j`, then the
`j`-restricted diagonal test. -/
noncomputable def diagonalFailureProbability
    {params : Parameters} [FieldModel params.q]
    (strategy : RestrictedSymStrat params 𝔓 K) : ℝ :=
  (1 / (params.m : ℝ)) *
    ∑ j : Fin params.m,
      strategy.state.bipartiteConsError
        (uniformDistribution (RestrictedDiagonalSample params j))
        (restrictedDiagonalPointAnswerFamily strategy j)
        (restrictedDiagonalLineAnswerFamily strategy j)

/-- Goodness data for a restricted strategy. -/
structure IsGood {params : Parameters} [FieldModel params.q]
    (strategy : RestrictedSymStrat params 𝔓 K)
    (eps delta gamma : ℝ) : Prop where
  /-- The restricted axis-parallel test fails with probability at most `eps`. -/
  axisParallelTest :
    strategy.axisParallelFailureProbability ≤ eps
  /-- The restricted self-consistency test fails with probability at most `delta`. -/
  selfConsistencyTest :
    strategy.selfConsistencyFailureProbability ≤ delta
  /-- The restricted diagonal-line test fails with probability at most `gamma`. -/
  diagonalLineTest :
    strategy.diagonalFailureProbability ≤ gamma

end RestrictedSymStrat

/-- Restrict an axis-parallel line measurement to the slice at height `x`. -/
noncomputable def restrictAxisParallelMeasurement (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (x : Fq params) :
    IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) 𝔓 :=
  fun ℓ =>
    let lifted := strategy.axisParallelMeasurement (AxisParallelLine.appendAtHeight params ℓ x)
    { toMeasurement := {
        toSubMeas := {
          outcome := fun f => lifted.outcome (liftAxisAnswer params x f)
          total := 1
          outcome_pos := fun f => lifted.outcome_pos (liftAxisAnswer params x f)
          sum_eq_total :=
            ((axisLinePolynomialEquiv params x).sum_comp lifted.outcome).trans
              (lifted.sum_eq_total.trans lifted.total_eq_one)
          total_le_one := le_rfl }
        total_eq_one := rfl }
      proj := fun f => lifted.proj (liftAxisAnswer params x f) }

/-- Restricting an axis-parallel measurement reindexes outcomes by slice extension. -/
@[simp] theorem restrictAxisParallelMeasurement_outcome (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (x : Fq params)
    (ℓ : AxisParallelLine params) (f : AxisLinePolynomial params) :
    (restrictAxisParallelMeasurement params strategy x ℓ).toSubMeas.outcome f =
      (strategy.axisParallelMeasurement
        (AxisParallelLine.appendAtHeight params ℓ x)).toSubMeas.outcome
        (liftAxisAnswer params x f) :=
  rfl

/-- The restricted axis-parallel measurement is transport-covariant. -/
theorem restrictAxisParallelMeasurement_transportInvariant
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (x : Fq params) :
    AxisParallelMeasurementTransportInvariant params
      (restrictAxisParallelMeasurement params strategy x) := by
  intro ℓ t
  have htransport := strategy.axisParallelMeasurement.transportInvariant
    (AxisParallelLine.appendAtHeight params ℓ x) t
  refine ProjMeas.ext fun a => ?_
  calc
    (restrictAxisParallelMeasurement params strategy x
        (MIPStarRE.LDT.AxisParallelLine.rebaseAt ℓ t)).outcome a
      = (strategy.axisParallelMeasurement
          (MIPStarRE.LDT.AxisParallelLine.rebaseAt
            (AxisParallelLine.appendAtHeight params ℓ x) t)).outcome
          (liftAxisAnswer params x a) := by
            simp [restrictAxisParallelMeasurement]
    _ = (strategy.axisParallelMeasurement (AxisParallelLine.appendAtHeight params ℓ x)).outcome
          (liftAxisAnswer params x
            (((AxisLinePolynomial.reparamAtEquiv (params := params) t).symm) a)) := by
            rw [htransport]
            simp [AxisParallelLine.transportMeasurement, ProjMeas.transport,
              Measurement.transport, SubMeas.transport, liftAxisAnswer]
    _ = (AxisParallelLine.transportMeasurement (params := params)
          (restrictAxisParallelMeasurement params strategy x ℓ) t).outcome a := by
            simp [AxisParallelLine.transportMeasurement, ProjMeas.transport,
              Measurement.transport, SubMeas.transport, restrictAxisParallelMeasurement]

/-- Restrict a diagonal-line measurement to the slice at height `x`.

This is not literally the paper's outcome reindexing
`f ↦ DiagonalLinePolynomial.appendAtHeight params f x`; that map only covers the
degree-`params.m * params.d` ambient outcomes. Instead we preserve the only
statistic used by the restricted diagonal test formalized here, namely the
base-point answer at `zeroCoord`: restrict the ambient line question to the slice-preserving
line, postprocess the ambient projective measurement to its `zeroCoord` value in `F_q`, and
re-embed that `F_q`-valued projective measurement into the honest slice answer space via
`diagonalValueRepresentative`. -/
noncomputable def restrictDiagonalMeasurement (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (x : Fq params) :
    IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) 𝔓 :=
  fun ℓ =>
    ProjMeas.postprocess
      (ProjMeas.postprocess
        (strategy.diagonalMeasurement (DiagonalLine.appendAtHeight params ℓ x))
        (fun f : DiagonalLinePolynomial params.next => f zeroCoord))
      (diagonalValueRepresentative params)

/-- Restrict a diagonal-line measurement to the slice at height `x`, using the
paper-level function-answer alphabet.

Unlike `restrictDiagonalMeasurement`, this keeps the whole line answer function
rather than only the value at `zeroCoord`.  The map is total because
`DiagonalLineAnswer` has no degree-bound subtype proof to preserve. -/
noncomputable def restrictDiagonalAnswerMeasurement (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (x : Fq params) :
    IdxProjMeas (DiagonalLine params) (DiagonalLineAnswer params) 𝔓 :=
  fun ℓ =>
    ProjMeas.postprocess
      (strategy.diagonalMeasurement (DiagonalLine.appendAtHeight params ℓ x))
      (fun f : DiagonalLinePolynomial params.next =>
        DiagonalLineAnswer.restrictAtHeight params f.toAnswer x)

/-- Transport covariance for the function-valued restricted diagonal-line
measurement. -/
theorem restrictDiagonalAnswerMeasurement_transportInvariant (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (x : Fq params) :
    DiagonalAnswerMeasurementTransportInvariant params
      (restrictDiagonalAnswerMeasurement params strategy x) := by
  intro ℓ t
  refine ProjMeas.ext fun a => ?_
  have htransport := strategy.diagonalMeasurement.transportInvariant
    (DiagonalLine.appendAtHeight params ℓ x) t
  let A := (strategy.diagonalMeasurement (DiagonalLine.appendAtHeight params ℓ x)).toSubMeas
  let ePoly := DiagonalLinePolynomial.reparamAtEquiv (params := params.next) t
  let eAns := DiagonalLineAnswer.reparamAtEquiv (params := params) t
  let f : DiagonalLinePolynomial params.next → DiagonalLineAnswer params :=
    fun g => DiagonalLineAnswer.restrictAtHeight params g.toAnswer x
  have hcomm : ∀ g, f (ePoly g) = eAns (f g) := by
    intro g
    funext s
    dsimp [f, ePoly, eAns, DiagonalLinePolynomial.reparamAtEquiv,
      DiagonalLineAnswer.reparamAtEquiv, DiagonalLinePolynomial.toAnswer,
      DiagonalLineAnswer.restrictAtHeight, DiagonalLineAnswer.reparamAt]
    exact DiagonalLinePolynomial.reparamAt_apply g t s
  have hpost : postprocess (SubMeas.transport ePoly A) f =
      SubMeas.transport eAns (postprocess A f) :=
    SubMeas.postprocess_transport_equiv ePoly eAns A f f hcomm
  exact congrArg (fun M : SubMeas (DiagonalLineAnswer params) 𝔓 => M.outcome a) <| by
    simpa [restrictDiagonalAnswerMeasurement, DiagonalLine.transportMeasurement,
      ProjMeas.transport, Measurement.transport, A, ePoly, eAns, f,
      DiagonalLine.appendAtHeight_rebaseAt, htransport] using hpost

/-- The `x`-restricted strategy with function-valued diagonal-line
answers.

This matches the slice-restriction interface in `inductive_step.tex`, lines
436--455. It is kept parallel to `xRestrictedStrategy`, whose diagonal field uses the
degree-bounded answer alphabet and therefore only preserves the sampled
base-point readout. -/
noncomputable def xRestrictedAnswerSymStrat (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (x : Fq params) : AnswerSymStrat params 𝔓 K where
  state := strategy.state
  pointMeasurement := fun u => strategy.pointMeasurement (appendPoint params u x)
  axisParallelMeasurement :=
    { toIdxProjMeas := restrictAxisParallelMeasurement params strategy x
      transportInvariant :=
        restrictAxisParallelMeasurement_transportInvariant params strategy x }
  diagonalMeasurement :=
    { toIdxProjMeas := restrictDiagonalAnswerMeasurement params strategy x
      transportInvariant :=
        restrictDiagonalAnswerMeasurement_transportInvariant params strategy x }

/-- The function-answer restricted strategy reuses the ambient bipartite state. -/
@[simp] theorem xRestrictedAnswerSymStrat_state (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (x : Fq params) :
    (xRestrictedAnswerSymStrat params strategy x).state = strategy.state :=
  rfl

/-- The function-answer restricted strategy reindexes point questions by appending
the slice height. -/
@[simp] theorem xRestrictedAnswerSymStrat_pointMeasurement_apply (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (x : Fq params) (u : Point params) :
    (xRestrictedAnswerSymStrat params strategy x).pointMeasurement u =
      strategy.pointMeasurement (appendPoint params u x) :=
  rfl

/-- The function-answer restricted strategy has the parent's normalization (the vendored
statement equates the two normalization witnesses; here both are the model's). -/
theorem xRestrictedAnswerSymStrat_isNormalized (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (x : Fq params) :
    (xRestrictedAnswerSymStrat params strategy x).isNormalized = strategy.isNormalized :=
  rfl

/-- The function-answer restricted diagonal measurement is the answer-valued
restriction of the ambient diagonal measurement. -/
@[simp] theorem xRestrictedAnswerSymStrat_diagonalMeasurement_apply (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (x : Fq params) (ℓ : DiagonalLine params) :
    (xRestrictedAnswerSymStrat params strategy x).diagonalMeasurement ℓ =
      restrictDiagonalAnswerMeasurement params strategy x ℓ :=
  rfl

/-- Evaluating the answer-valued restricted diagonal measurement at the base point
recovers the ambient slice-preserving diagonal readout. -/
@[simp] theorem restrictDiagonalAnswerMeasurement_postprocess_zero (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (x : Fq params)
    (ℓ : DiagonalLine params) :
    postprocess ((restrictDiagonalAnswerMeasurement params strategy x ℓ).toSubMeas)
        (fun f : DiagonalLineAnswer params => f zeroCoord) =
      postprocess
        ((strategy.diagonalMeasurement
          (DiagonalLine.appendAtHeight params ℓ x)).toSubMeas)
        (fun f : DiagonalLinePolynomial params.next => f zeroCoord) := by
  simp [restrictDiagonalAnswerMeasurement, ProjMeas.postprocess_toSubMeas,
    SubMeas.postprocess_comp, DiagonalLinePolynomial.toAnswer,
    DiagonalLineAnswer.restrictAtHeight]
  rfl

/-- The `x`-restricted strategy from the proof of the main induction theorem. -/
noncomputable def xRestrictedStrategy (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (x : Fq params) :
    RestrictedSymStrat params 𝔓 K where
  state := strategy.state
  pointMeasurement := fun u => strategy.pointMeasurement (appendPoint params u x)
  axisParallelMeasurement :=
    { toIdxProjMeas := restrictAxisParallelMeasurement params strategy x
      transportInvariant :=
        restrictAxisParallelMeasurement_transportInvariant params strategy x }
  diagonalMeasurement := restrictDiagonalMeasurement params strategy x

/-- Restricting a strategy does not change its bipartite state. -/
@[simp] theorem xRestrictedStrategy_state (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (x : Fq params) :
    (xRestrictedStrategy params strategy x).state = strategy.state :=
  rfl

/-- Restricting a strategy keeps the parent's normalization (the vendored statement equates
the two normalization witnesses; here both are the model's). -/
theorem xRestrictedStrategy_isNormalized (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (x : Fq params) :
    (xRestrictedStrategy params strategy x).isNormalized = strategy.isNormalized :=
  rfl

/-- Restricting a strategy reindexes point questions by appending the slice height. -/
@[simp] theorem xRestrictedStrategy_pointMeasurement_apply (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (x : Fq params) (u : Point params) :
    (xRestrictedStrategy params strategy x).pointMeasurement u =
      strategy.pointMeasurement (appendPoint params u x) :=
  rfl

/-- Postprocessing the restricted diagonal measurement at the base point recovers
exactly the ambient slice-preserving diagonal answer distribution at the base
point. -/
@[simp] theorem restrictDiagonalMeasurement_postprocess_zero (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (x : Fq params)
    (ℓ : DiagonalLine params) :
    postprocess ((restrictDiagonalMeasurement params strategy x ℓ).toSubMeas)
        (fun f : DiagonalLinePolynomial params => f zeroCoord) =
      postprocess
        ((strategy.diagonalMeasurement
          (DiagonalLine.appendAtHeight params ℓ x)).toSubMeas)
        (fun f : DiagonalLinePolynomial params.next => f zeroCoord) := by
  refine (SubMeas.postprocess_comp _ _ _).trans ((SubMeas.postprocess_comp _ _ _).trans ?_)
  congr 1
  funext f
  simp only [diagonalValueRepresentative, DiagonalLinePolynomial.toFun,
    MIPStarRE.LDT.evalLinePolynomialModel, Polynomial.eval_C]
  exact MIPStarRE.LDT.encode_decodeScalar _

/-- Tensor-failure expectation in a symmetric model:
`⟨Ψ| (Z ⊗ I)(I ⊗ (I - Σ H_a)) |Ψ⟩`, with `Z` on the first factor and `H` on the second.

The vendored definition allows a state on two different carriers; its uses are all on the state
of a symmetric strategy, so it is stated with one local algebra (module docstring). -/
noncomputable def tensorFailureExpectation {Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (Z : 𝔓) (H : SubMeas Outcome 𝔓) : ℝ :=
  S.ev (S.L Z * S.R (1 - H.total))

end MIPRE.LIDT.Co.MainInductionStep

end

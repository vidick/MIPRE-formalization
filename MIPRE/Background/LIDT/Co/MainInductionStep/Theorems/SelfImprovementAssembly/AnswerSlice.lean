/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
MainInductionStep/Theorems/SelfImprovementAssembly/AnswerSlice.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.MainInductionStep.Theorems.SelfImprovementAssembly.Core

@[expose] public section

/-!
# Section 6 — Answer-Valued Self-Improvement Slice Transport

The answer-valued analogues of the Section 6 slice-transport constructors. The ordinary
construction, including `selfImprovementInInductionSection`, lives in
`SelfImprovementAssembly.Core` and is imported here so that the answer-valued construction can
reuse the same Section 9 self-improvement theorem. This is the counterpart of the vendored
`MainInductionStep/Theorems/SelfImprovementAssembly/AnswerSlice.lean` (under
`MIPRE/Background/LIDT/MIPStarRE/LDT/`) in the port of `planning/c6b-plan.md` (milestone M12,
section "Port conventions").

## Translation

A strategy is a `SymStrat params 𝔓 K`, `SymStrat params.next 𝔓 K` or `AnswerSymStrat params 𝔓 K`,
whose state is the symmetric model `strategy.state : SymModel 𝔓 K`; `Polynomial params` is
`MIPStarRE.LDT.Polynomial params`, `Z : MIPStarRE.Quantum.Op ι` is `Z : 𝔓`, `Error` is `ℝ`,
`H.toSubMeas.liftLeft` is `H.toSubMeas.liftLeft strategy.state`, `leftPlacedSubMeas (ιB := ι)` is
`strategy.state.leftPlacedSubMeas` (and `rightPlacedSubMeas`), and the relations are read on
`strategy.state`. The state-free `dummyDiagonalCovariantMeasurement` is generic over an ordered
`⋆`-ring `R` in the position of the vendored carrier `ι`. The vendored `AnswerSymStrat` and
`SymStrat` fields `permInvState`, `densityFixed` and `isNormalized`, which
`answerSelfImprovementCarrier` and `xRestrictedAnswerSymStratOfAnswer` copy from their argument,
are theorems of the model here, so those two constructors set no such field, and
`xRestrictedAnswerSymStratOfAnswer_isNormalized`, an equality of two proofs, loses `@[simp]`, as
`xRestrictedAnswerSymStrat_isNormalized` did (milestone M4). The vendored file-wide
`respectTransparency false` is not needed: the file sets no option.

## Three threaded hypotheses

As in `SelfImprovementAssembly.Core`, the four declarations that reach the ported
`SelfImprovement.selfImprovement` take, right after `strategy`,
`hS : strategy.state.toBipartite.IsFinitePair`, `hA : NoAbelianProj strategy.state.toBipartite.opsA`
and `hd : 1 ≤ params.d`: `AnswerSelfImprovementData.slice_outputs_ofSliceStrategyTransport`,
`AnswerSelfImprovementData.slice_outputs_ofAnswerCarrier`,
`AnswerSelfImprovementData.ofSliceStrategyTransport` and `AnswerSelfImprovementData.ofAnswerCarrier`.
They are stated for the ambient strategy. A concrete slice strategy of `SliceStrategyTransport` has
the ambient state (`state_eq`), so `hS` and `hA` pass to it as `hstate ▸ hS`; the answer carrier
has the ambient state by definition, so they pass to it unchanged; and `hd` is a hypothesis on
`params`. The vendored statements, on finite carriers, need none of the three.
`AnswerSelfImprovementData.SliceStrategyTransport` keeps its five vendored fields.

## Proofs that differ from the vendored ones

- `AnswerSelfImprovementData.slice_outputs_ofSliceStrategyTransport` rewrites with `state_eq` in
  the goal rather than in each of the six hypotheses, as the ordinary one in `Core` does.
- `AnswerSelfImprovementData.slice_outputs_ofAnswerCarrier` closes the six fields by definitional
  equality: the carrier's state, point measurement and averaged point operator are those of the
  answer slice by `rfl`, and `answerSliceSelfImprovementError` unfolds to the error of the
  conclusion.
- `AnswerSelfImprovementData.ofSelfImprovementInInductionSection` builds the record from
  `Classical.choose` directly, as `SelfImprovementData.ofSelfImprovementInInductionSection` does.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/inductive_step.tex`
- `references/ldt-paper/self_improvement.tex`
- `blueprint/src/chapter/ch10_induction.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.MainInductionStep

open MIPStarRE.LDT (Parameters FieldModel Point Fq zeroCoord appendPoint uniformDistribution
  DiagonalLine DiagonalLinePolynomial DiagonalLineAnswer extendRestrictedDirection)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A covariant diagonal measurement with a fixed zero polynomial outcome.

This measurement is used only as an inert diagonal component when applying the
axis-parallel/self-consistency form of self-improvement to an answer-valued
slice. The Section 9 conclusion obtained in this way is independent of the
diagonal-line failure probability. It is state-free, so it is stated over any ordered
`⋆`-ring `R`, in the position of the vendored carrier. -/
noncomputable def dummyDiagonalCovariantMeasurement
    (params : Parameters)
    [FieldModel params.q]
    (R : Type*) [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R] :
    DiagonalCovariantMeasurement params R where
  toIdxProjMeas := fun _ =>
    ProjMeas.trivialDistinguishedOutcome (default : DiagonalLinePolynomial params)
  transportInvariant := fun _ t =>
    ((ProjMeas.transport_trivialDistinguishedOutcome
      (DiagonalLinePolynomial.reparamAtEquiv (params := params) t)
      (default : DiagonalLinePolynomial params)).trans
        (congrArg (ProjMeas.trivialDistinguishedOutcome (R := R))
          (DiagonalLinePolynomial.reparamAt_default t))).symm

/-- Forget the answer-valued diagonal alphabet of a restricted slice, replacing
it by an inert ordinary diagonal measurement.

The point, axis-parallel and state data are unchanged. This is
therefore sufficient for the self-improvement theorem variant whose hypotheses
are exactly the axis-parallel and point self-consistency bounds. The vendored fields
`permInvState`, `densityFixed` and `isNormalized` are theorems of the model. -/
noncomputable def answerSelfImprovementCarrier
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params 𝔓 K) :
    SymStrat params 𝔓 K where
  state := strategy.state
  pointMeasurement := strategy.pointMeasurement
  axisParallelMeasurement := strategy.axisParallelMeasurement
  diagonalMeasurement := dummyDiagonalCovariantMeasurement params 𝔓

/-- Restrict an answer-valued diagonal-line measurement to the slice at height
`x`.

This is the answer-valued analogue of `restrictDiagonalAnswerMeasurement`.
Because the diagonal answer alphabet is the full function space on the line,
restriction is the total map
`DiagonalLineAnswer.restrictAtHeight`; no low-degree support theorem is needed
to define this slice. -/
noncomputable def restrictAnswerDiagonalAnswerMeasurement
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next 𝔓 K)
    (x : Fq params) :
    IdxProjMeas (DiagonalLine params) (DiagonalLineAnswer params) 𝔓 :=
  fun ℓ =>
    ProjMeas.postprocess
      (strategy.diagonalMeasurement (DiagonalLine.appendAtHeight params ℓ x))
      (fun f : DiagonalLineAnswer params.next =>
        DiagonalLineAnswer.restrictAtHeight params f x)

/-- Transport covariance for the answer-valued restricted diagonal-line
measurement. -/
theorem restrictAnswerDiagonalAnswerMeasurement_transportInvariant
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next 𝔓 K)
    (x : Fq params) :
    DiagonalAnswerMeasurementTransportInvariant params
      (restrictAnswerDiagonalAnswerMeasurement params strategy x) := by
  intro ℓ t
  refine ProjMeas.ext fun a => ?_
  have htransport := strategy.diagonalMeasurement.transportInvariant
    (DiagonalLine.appendAtHeight params ℓ x) t
  let A := (strategy.diagonalMeasurement (DiagonalLine.appendAtHeight params ℓ x)).toSubMeas
  let eNext := DiagonalLineAnswer.reparamAtEquiv (params := params.next) t
  let eSlice := DiagonalLineAnswer.reparamAtEquiv (params := params) t
  let f : DiagonalLineAnswer params.next → DiagonalLineAnswer params :=
    fun g => DiagonalLineAnswer.restrictAtHeight params g x
  have hcomm : ∀ g, f (eNext g) = eSlice (f g) := fun _ => rfl
  have hpost : postprocess (SubMeas.transport eNext A) f =
      SubMeas.transport eSlice (postprocess A f) :=
    SubMeas.postprocess_transport_equiv eNext eSlice A f f hcomm
  exact congrArg (fun M : SubMeas (DiagonalLineAnswer params) 𝔓 => M.outcome a) <| by
    simpa [restrictAnswerDiagonalAnswerMeasurement, ProjMeas.transport, Measurement.transport,
      A, eNext, eSlice, f, DiagonalLine.appendAtHeight_rebaseAt, htransport] using hpost

/-- Evaluating the answer-valued restricted diagonal measurement at the base point
recovers the ambient answer-valued diagonal readout. -/
@[simp] theorem restrictAnswerDiagonalAnswerMeasurement_postprocess_zero
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next 𝔓 K)
    (x : Fq params)
    (ℓ : DiagonalLine params) :
    postprocess ((restrictAnswerDiagonalAnswerMeasurement params strategy x ℓ).toSubMeas)
        (fun f : DiagonalLineAnswer params => f zeroCoord) =
      postprocess
        ((strategy.diagonalMeasurement
          (DiagonalLine.appendAtHeight params ℓ x)).toSubMeas)
        (fun f : DiagonalLineAnswer params.next => f zeroCoord) := by
  simp [restrictAnswerDiagonalAnswerMeasurement, ProjMeas.postprocess_toSubMeas,
    SubMeas.postprocess_comp, DiagonalLineAnswer.restrictAtHeight]
  rfl

/-- The `x`-restricted strategy of an answer-valued successor strategy.

Paper origin: `references/ldt-paper/inductive_step.tex:436-455`, in the
answer-valued strategy interface used for the recursive slice call.

This is the recursive restriction map needed for a simultaneous answer-valued
form of the main induction theorem. It preserves the state, point
measurement, axis-parallel measurement, and full answer-valued diagonal
measurement on the slice. The vendored fields `permInvState`, `densityFixed` and
`isNormalized` are theorems of the model. -/
noncomputable def xRestrictedAnswerSymStratOfAnswer
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next 𝔓 K)
    (x : Fq params) : AnswerSymStrat params 𝔓 K where
  state := strategy.state
  pointMeasurement := fun u => strategy.pointMeasurement (appendPoint params u x)
  axisParallelMeasurement :=
    (xRestrictedAnswerSymStrat params
      (answerSelfImprovementCarrier params.next strategy) x).axisParallelMeasurement
  diagonalMeasurement :=
    { toIdxProjMeas := restrictAnswerDiagonalAnswerMeasurement params strategy x
      transportInvariant :=
        restrictAnswerDiagonalAnswerMeasurement_transportInvariant params strategy x }

/-- Answer-valued slice restriction does not change the bipartite state. -/
@[simp] theorem xRestrictedAnswerSymStratOfAnswer_state
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next 𝔓 K)
    (x : Fq params) :
    (xRestrictedAnswerSymStratOfAnswer params strategy x).state = strategy.state :=
  rfl

/-- Answer-valued slice restriction reindexes point questions by appending the
slice height. -/
@[simp] theorem xRestrictedAnswerSymStratOfAnswer_pointMeasurement_apply
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next 𝔓 K)
    (x : Fq params)
    (u : Point params) :
    (xRestrictedAnswerSymStratOfAnswer params strategy x).pointMeasurement u =
      strategy.pointMeasurement (appendPoint params u x) :=
  rfl

/-- Answer-valued slice restriction keeps the parent's normalization (the vendored statement
equates the two normalization witnesses; here both are the model's). -/
theorem xRestrictedAnswerSymStratOfAnswer_isNormalized
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next 𝔓 K)
    (x : Fq params) :
    (xRestrictedAnswerSymStratOfAnswer params strategy x).isNormalized =
      strategy.isNormalized :=
  rfl

/-- The diagonal measurement of an answer-valued slice is the full answer-valued
restriction of the ambient diagonal measurement. -/
@[simp] theorem xRestrictedAnswerSymStratOfAnswer_diagonalMeasurement_apply
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next 𝔓 K)
    (x : Fq params)
    (ℓ : DiagonalLine params) :
    (xRestrictedAnswerSymStratOfAnswer params strategy x).diagonalMeasurement ℓ =
      restrictAnswerDiagonalAnswerMeasurement params strategy x ℓ :=
  rfl

/-- Transport data for producing the answer-valued self-improvement data from
concrete per-slice symmetric strategies.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551` and
`references/ldt-paper/self_improvement.tex:631-811`; this is the answer-valued
restricted-slice interface for the same self-improvement step.

The answer-valued restriction `xRestrictedAnswerSymStrat` has the paper-faithful
answer-valued diagonal interface, while the Section 9 self-improvement
theorem is stated for ordinary `SymStrat`s. This structure records the
route through concrete ordinary slice strategies, together with the
state and point-measurement transports needed to move the resulting conclusions
back to the answer-valued restricted bookkeeping. The concrete slice strategies are
`SymStrat params 𝔓 K` on the algebra and Hilbert space of the ambient strategy, so `state_eq`
is an equality of symmetric models.

The legacy restricted strategy `xRestrictedStrategy` is not such an ordinary
slice strategy. It is a `RestrictedSymStrat`, and its diagonal measurement is
only the degree-bounded re-embedding of the sampled base-point value. Thus it
does not by itself supply the transport-covariant diagonal measurement required
by `SymStrat`.

An ordinary covariant realization is not a formal relabelling of the
answer-valued strategy. Diagonal covariance after rebasing a line would force
the ordinary polynomial outcome to reproduce all values of the function answer,
not only the value at `zeroCoord` used by the diagonal test. Thus this route
requires a genuine low-degree support/interpolation theorem for the
answer-valued diagonal measurement; `AnswerSelfImprovementData.ofAnswerCarrier` avoids it.

The Section 9 analytic proof debt is not stored in this record. The data-record
constructor below calls the paper-facing theorem
`selfImprovementInInductionSection`; its proof applies the Section 9 theorem and
then transports the output estimates to the answer-valued induction notation. -/
structure AnswerSelfImprovementData.SliceStrategyTransport
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (inductionPkg :
      AnswerPerSliceInductionData params strategy eps delta gamma restrictionPkg k) where
  /-- Concrete symmetric strategies realizing the answer-restricted slice interfaces. -/
  sliceStrategy : Fq params → SymStrat params 𝔓 K
  /-- Each concrete slice strategy uses the ambient state. -/
  state_eq : ∀ x, (sliceStrategy x).state = strategy.state
  /-- Its point measurement agrees with the answer-valued restricted-slice point interface. -/
  pointMeasurement_eq :
    ∀ x,
      (sliceStrategy x).pointMeasurement =
        (xRestrictedAnswerSymStrat params strategy x).pointMeasurement
  /-- Its averaged point operator is the averaged slice point operator used by
  Section 6. -/
  averagedPoint_eq :
    ∀ x h,
      IdxPolyFamily.averagedPointEvaluationOperator (sliceStrategy x) h =
        IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x h
  /-- The concrete slice strategy is good with the answer-restricted failure profile. -/
  good :
    ∀ x,
      (sliceStrategy x).IsGood
        (restrictionPkg.profile.axisParallel x)
        (restrictionPkg.profile.selfConsistency x)
        (restrictionPkg.profile.diagonal x)

/-- The averaged point-operator compatibility for answer-valued slices follows
from point-measurement transport.

Both sides unfold to the same average over `strategy.pointMeasurement
(appendPoint params u x)` once the concrete slice point measurement is identified
with `xRestrictedAnswerSymStrat`. -/
theorem AnswerSelfImprovementData.SliceStrategyTransport.averagedPoint_eq_of_pointMeasurement_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (sliceStrategy : Fq params → SymStrat params 𝔓 K)
    (hpoint :
      ∀ x,
        (sliceStrategy x).pointMeasurement =
          (xRestrictedAnswerSymStrat params strategy x).pointMeasurement) :
    ∀ x h,
      IdxPolyFamily.averagedPointEvaluationOperator (sliceStrategy x) h =
        IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x h := by
  intro x h
  unfold IdxPolyFamily.averagedPointEvaluationOperator
    IdxPolyFamily.averagedSlicePointEvaluationOperator
  rw [hpoint x]
  rfl

/-- Build answer-valued `SliceStrategyTransport` without separately assuming averaged
point-operator compatibility.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551`; the averaged
point-operator compatibility is a formal transport between the answer-valued
restricted slice interface and the Section 9 interface.

The structural averaged-point field is derived from `pointMeasurement_eq`; the
remaining inputs are the concrete slice strategies, their state transport, and
their restricted-profile goodness. -/
noncomputable def AnswerSelfImprovementData.SliceStrategyTransport.ofPointMeasurementEq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (inductionPkg :
      AnswerPerSliceInductionData params strategy eps delta gamma restrictionPkg k)
    (sliceStrategy : Fq params → SymStrat params 𝔓 K)
    (state_eq : ∀ x, (sliceStrategy x).state = strategy.state)
    (pointMeasurement_eq :
      ∀ x,
        (sliceStrategy x).pointMeasurement =
          (xRestrictedAnswerSymStrat params strategy x).pointMeasurement)
    (good :
      ∀ x,
        (sliceStrategy x).IsGood
          (restrictionPkg.profile.axisParallel x)
          (restrictionPkg.profile.selfConsistency x)
          (restrictionPkg.profile.diagonal x)) :
    AnswerSelfImprovementData.SliceStrategyTransport params strategy eps delta gamma k
      restrictionPkg inductionPkg where
  sliceStrategy := sliceStrategy
  state_eq := state_eq
  pointMeasurement_eq := pointMeasurement_eq
  averagedPoint_eq :=
    AnswerSelfImprovementData.SliceStrategyTransport.averagedPoint_eq_of_pointMeasurement_eq
      params strategy sliceStrategy pointMeasurement_eq
  good := good

/-- Transport answer-restricted goodness to a concrete slice strategy once the
state and verifier-visible measurements agree with `xRestrictedAnswerSymStrat`.

The diagonal compatibility is stated only after postprocessing both diagonal
answer alphabets to their `zeroCoord` value; this is the comparison used by the
LDT diagonal subtest and avoids claiming a false equality between
`DiagonalLinePolynomial` and `DiagonalLineAnswer` families. -/
theorem AnswerSelfImprovementData.SliceStrategyTransport.good_of_restrictedGood
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (sliceStrategy : Fq params → SymStrat params 𝔓 K)
    (state_eq : ∀ x, (sliceStrategy x).state = strategy.state)
    (pointMeasurement_eq :
      ∀ x,
        (sliceStrategy x).pointMeasurement =
          (xRestrictedAnswerSymStrat params strategy x).pointMeasurement)
    (axisParallelMeasurement_eq :
      ∀ x,
        (sliceStrategy x).axisParallelMeasurement.toIdxProjMeas =
          (xRestrictedAnswerSymStrat params strategy x).axisParallelMeasurement.toIdxProjMeas)
    (diagonalZeroCoord_eq :
      ∀ x ℓ,
        postprocess
            (((sliceStrategy x).diagonalMeasurement.toIdxProjMeas ℓ).toSubMeas)
            (fun f : DiagonalLinePolynomial params => f zeroCoord) =
          postprocess
            (((xRestrictedAnswerSymStrat params strategy x).diagonalMeasurement.toIdxProjMeas
              ℓ).toSubMeas)
            (fun f : DiagonalLineAnswer params => f zeroCoord)) :
    ∀ x,
      (sliceStrategy x).IsGood
        (restrictionPkg.profile.axisParallel x)
        (restrictionPkg.profile.selfConsistency x)
        (restrictionPkg.profile.diagonal x) := by
  intro x
  have hgood := restrictionPkg.profile.restrictedGood x
  refine ⟨?_, ?_, ?_⟩
  · have hfail : (sliceStrategy x).axisParallelFailureProbability =
        (xRestrictedAnswerSymStrat params strategy x).axisParallelFailureProbability := by
      unfold SymStrat.axisParallelFailureProbability
        AnswerSymStrat.axisParallelFailureProbability
        axisParallelPointAnswerFamily AnswerSymStrat.axisParallelPointAnswerFamily
        axisParallelLineAnswerFamily AnswerSymStrat.axisParallelLineAnswerFamily
      rw [state_eq x, pointMeasurement_eq x]
      unfold axisParallelLineAnswerFamilyOf
      simp only [axisParallelMeasurement_eq x]
      rfl
    exact hfail ▸ hgood.axisParallelTest
  · have hfail : (sliceStrategy x).selfConsistencyFailureProbability =
        (xRestrictedAnswerSymStrat params strategy x).selfConsistencyFailureProbability := by
      unfold SymStrat.selfConsistencyFailureProbability
        AnswerSymStrat.selfConsistencyFailureProbability
      rw [state_eq x, pointMeasurement_eq x]
      rfl
    exact hfail ▸ hgood.selfConsistencyTest
  · have hfail : (sliceStrategy x).diagonalFailureProbability =
        (xRestrictedAnswerSymStrat params strategy x).diagonalFailureProbability := by
      unfold SymStrat.diagonalFailureProbability
        AnswerSymStrat.diagonalFailureProbability
        diagonalPointAnswerFamily AnswerSymStrat.diagonalPointAnswerFamily
        diagonalLineAnswerFamily AnswerSymStrat.diagonalLineAnswerFamily
      rw [state_eq x, pointMeasurement_eq x]
      refine congrArg (fun s => (1 / (params.m : ℝ)) * s) (Finset.sum_congr rfl fun j _ => ?_)
      have hB :
          diagonalLineAnswerFamilyOf (sliceStrategy x).diagonalMeasurement.toIdxProjMeas
              (fun f : DiagonalLinePolynomial params => f.toFun zeroCoord) j =
            diagonalLineAnswerFamilyOf
              (xRestrictedAnswerSymStrat params strategy x).diagonalMeasurement.toIdxProjMeas
              (fun f : DiagonalLineAnswer params => f zeroCoord) j := by
        funext s
        exact diagonalZeroCoord_eq x
          { base := s.1, direction := extendRestrictedDirection j s.2 }
      exact congrArg (fun B => strategy.state.bipartiteConsError _ _ B) hB
    exact hfail ▸ hgood.diagonalLineTest

/-- Build answer-valued `SliceStrategyTransport` from concrete slice strategies and
verifier-visible measurement transport.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551` and
`references/ldt-paper/self_improvement.tex:631-811`.

This constructor fills both structural fields forced by the answer-restricted
interface: averaged point compatibility follows from point-measurement transport,
and goodness follows from the answer-restricted failure profile plus state,
axis-parallel, and diagonal zero-coordinate transport. -/
noncomputable def AnswerSelfImprovementData.SliceStrategyTransport.ofMeasurementEq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (inductionPkg :
      AnswerPerSliceInductionData params strategy eps delta gamma restrictionPkg k)
    (sliceStrategy : Fq params → SymStrat params 𝔓 K)
    (state_eq : ∀ x, (sliceStrategy x).state = strategy.state)
    (pointMeasurement_eq :
      ∀ x,
        (sliceStrategy x).pointMeasurement =
          (xRestrictedAnswerSymStrat params strategy x).pointMeasurement)
    (axisParallelMeasurement_eq :
      ∀ x,
        (sliceStrategy x).axisParallelMeasurement.toIdxProjMeas =
          (xRestrictedAnswerSymStrat params strategy x).axisParallelMeasurement.toIdxProjMeas)
    (diagonalZeroCoord_eq :
      ∀ x ℓ,
        postprocess
            (((sliceStrategy x).diagonalMeasurement.toIdxProjMeas ℓ).toSubMeas)
            (fun f : DiagonalLinePolynomial params => f zeroCoord) =
          postprocess
            (((xRestrictedAnswerSymStrat params strategy x).diagonalMeasurement.toIdxProjMeas
              ℓ).toSubMeas)
            (fun f : DiagonalLineAnswer params => f zeroCoord)) :
    AnswerSelfImprovementData.SliceStrategyTransport params strategy eps delta gamma k
      restrictionPkg inductionPkg :=
  AnswerSelfImprovementData.SliceStrategyTransport.ofPointMeasurementEq
    params strategy eps delta gamma k restrictionPkg inductionPkg sliceStrategy state_eq
    pointMeasurement_eq
    (AnswerSelfImprovementData.SliceStrategyTransport.good_of_restrictedGood
      params strategy eps delta gamma restrictionPkg sliceStrategy state_eq
      pointMeasurement_eq axisParallelMeasurement_eq diagonalZeroCoord_eq)

/-- Convert the slice-wise outputs feeding the answer-valued restricted-strategy
self-improvement stage into the bookkeeping object expected by the answer-valued
successor-step construction.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551` and
`references/ldt-paper/self_improvement.tex:631-811`. -/
noncomputable def AnswerSelfImprovementData.ofSelfImprovementInInductionSection
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (inductionPkg :
      AnswerPerSliceInductionData params strategy eps delta gamma restrictionPkg k)
    (hslice :
      ∀ x,
        ∃ H : ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝔓, ∃ Z : 𝔓,
          strategy.state.CompletenessAtLeast (H.toSubMeas.liftLeft strategy.state)
            ((1 - inductionPkg.sliceError x) -
              answerSliceSelfImprovementError params restrictionPkg x) ∧
          strategy.state.ConsRel (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas
              (xRestrictedAnswerSymStrat params strategy x).pointMeasurement)
            (polynomialEvaluationFamily params H.toSubMeas)
            (answerSliceSelfImprovementError params restrictionPkg x) ∧
          strategy.state.BipartiteSSCRel (uniformDistribution Unit)
            (constSubMeasFamily H.toSubMeas)
            (answerSliceSelfImprovementError params restrictionPkg x) ∧
          strategy.state.SDDRel (uniformDistribution Unit)
            (constSubMeasFamily (strategy.state.leftPlacedSubMeas H.toSubMeas))
            (constSubMeasFamily (strategy.state.rightPlacedSubMeas H.toSubMeas))
            (answerSliceSelfImprovementError params restrictionPkg x) ∧
          tensorFailureExpectation strategy.state Z H.toSubMeas ≤
            answerSliceSelfImprovementError params restrictionPkg x ∧
          (∀ h : MIPStarRE.LDT.Polynomial params,
            IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x h ≤ Z)) :
    AnswerSelfImprovementData params strategy eps delta gamma k restrictionPkg inductionPkg :=
  { sliceProj := fun x => Classical.choose (hslice x)
    sliceWitness := fun x => Classical.choose (Classical.choose_spec (hslice x))
    completeness := fun x => (Classical.choose_spec (Classical.choose_spec (hslice x))).1
    pointConsistency := fun x =>
      (Classical.choose_spec (Classical.choose_spec (hslice x))).2.1
    strongSelfConsistency := fun x =>
      (Classical.choose_spec (Classical.choose_spec (hslice x))).2.2.1
    selfCloseness := fun x =>
      (Classical.choose_spec (Classical.choose_spec (hslice x))).2.2.2.1
    bounded := fun x =>
      (Classical.choose_spec (Classical.choose_spec (hslice x))).2.2.2.2.1
    dominatesAveragePointOperator := fun x h =>
      (Classical.choose_spec (Classical.choose_spec (hslice x))).2.2.2.2.2 h }

/-- Concrete answer-valued slice strategies give the slice-wise Section 9
outputs used by the answer-valued self-improvement data.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551` and
`references/ldt-paper/self_improvement.tex:631-811`.

This is an internal transport theorem. It applies
`selfImprovementInInductionSection` to each ordinary slice strategy supplied by
`SliceStrategyTransport`, and then rewrites the state, point-measurement, and
averaged-point conclusions back into the answer-restricted notation of the
successor step. The hypotheses `hS` and `hA` are stated for the ambient strategy and pass to
each slice strategy through `state_eq`; `hd` is a hypothesis on `params`. -/
theorem AnswerSelfImprovementData.slice_outputs_ofSliceStrategyTransport
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (hS : strategy.state.toBipartite.IsFinitePair)
    (hA : NoAbelianProj strategy.state.toBipartite.opsA)
    (hd : 1 ≤ params.d)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (inductionPkg :
      AnswerPerSliceInductionData params strategy eps delta gamma restrictionPkg k)
    (sliceTransport :
      AnswerSelfImprovementData.SliceStrategyTransport params strategy eps delta gamma k
        restrictionPkg inductionPkg) :
    ∀ x,
      ∃ H : ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝔓, ∃ Z : 𝔓,
        strategy.state.CompletenessAtLeast (H.toSubMeas.liftLeft strategy.state)
          ((1 - inductionPkg.sliceError x) -
            answerSliceSelfImprovementError params restrictionPkg x) ∧
        strategy.state.ConsRel (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas
            (xRestrictedAnswerSymStrat params strategy x).pointMeasurement)
          (polynomialEvaluationFamily params H.toSubMeas)
          (answerSliceSelfImprovementError params restrictionPkg x) ∧
        strategy.state.BipartiteSSCRel (uniformDistribution Unit)
          (constSubMeasFamily H.toSubMeas)
          (answerSliceSelfImprovementError params restrictionPkg x) ∧
        strategy.state.SDDRel (uniformDistribution Unit)
          (constSubMeasFamily (strategy.state.leftPlacedSubMeas H.toSubMeas))
          (constSubMeasFamily (strategy.state.rightPlacedSubMeas H.toSubMeas))
          (answerSliceSelfImprovementError params restrictionPkg x) ∧
        tensorFailureExpectation strategy.state Z H.toSubMeas ≤
          answerSliceSelfImprovementError params restrictionPkg x ∧
        (∀ h : MIPStarRE.LDT.Polynomial params,
          IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x h ≤ Z) := by
  intro x
  have hstate := sliceTransport.state_eq x
  have hconsSlice :
      (sliceTransport.sliceStrategy x).state.ConsRel (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas (sliceTransport.sliceStrategy x).pointMeasurement)
        (polynomialEvaluationFamily params (inductionPkg.sliceMeasurement x).toSubMeas)
        (inductionPkg.sliceError x) := by
    rw [hstate, sliceTransport.pointMeasurement_eq x]
    exact inductionPkg.pointConsistency x
  obtain ⟨H, Z, hH⟩ := selfImprovementInInductionSection params
      (sliceTransport.sliceStrategy x) (hstate ▸ hS) (hstate ▸ hA) hd
      (restrictionPkg.profile.axisParallel x)
      (restrictionPkg.profile.selfConsistency x)
      (restrictionPkg.profile.diagonal x)
      (inductionPkg.sliceError x)
      (sliceTransport.good x)
      (inductionPkg.sliceMeasurement x)
      hconsSlice
  have hpoint := hH.pointConsistency
  rw [sliceTransport.pointMeasurement_eq x] at hpoint
  refine ⟨H, Z, ?_⟩
  rw [← hstate]
  exact ⟨hH.completeness, hpoint, hH.strongSelfConsistency, hH.selfCloseness, hH.bounded,
    fun h => sliceTransport.averagedPoint_eq x h ▸ hH.dominatesAveragePointOperator h⟩

/-- The answer-valued restricted slices directly give the slice-wise Section 9
outputs once self-improvement is applied in its axis-parallel/self-consistency
form.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551` and
`references/ldt-paper/self_improvement.tex:631-811`.

The ordinary carrier used in the proof keeps the slice state, point
measurement, and axis-parallel measurement, and replaces only the diagonal
measurement by an inert covariant measurement. This is sufficient because the
called self-improvement theorem consumes only the axis-parallel and point
self-consistency bounds. The carrier has the ambient state by definition, so the hypotheses
`hS` and `hA` on the ambient strategy are its own; `hd` is a hypothesis on `params`. -/
theorem AnswerSelfImprovementData.slice_outputs_ofAnswerCarrier
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (hS : strategy.state.toBipartite.IsFinitePair)
    (hA : NoAbelianProj strategy.state.toBipartite.opsA)
    (hd : 1 ≤ params.d)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (inductionPkg :
      AnswerPerSliceInductionData params strategy eps delta gamma restrictionPkg k) :
    ∀ x,
      ∃ H : ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝔓, ∃ Z : 𝔓,
        strategy.state.CompletenessAtLeast (H.toSubMeas.liftLeft strategy.state)
          ((1 - inductionPkg.sliceError x) -
            answerSliceSelfImprovementError params restrictionPkg x) ∧
        strategy.state.ConsRel (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas
            (xRestrictedAnswerSymStrat params strategy x).pointMeasurement)
          (polynomialEvaluationFamily params H.toSubMeas)
          (answerSliceSelfImprovementError params restrictionPkg x) ∧
        strategy.state.BipartiteSSCRel (uniformDistribution Unit)
          (constSubMeasFamily H.toSubMeas)
          (answerSliceSelfImprovementError params restrictionPkg x) ∧
        strategy.state.SDDRel (uniformDistribution Unit)
          (constSubMeasFamily (strategy.state.leftPlacedSubMeas H.toSubMeas))
          (constSubMeasFamily (strategy.state.rightPlacedSubMeas H.toSubMeas))
          (answerSliceSelfImprovementError params restrictionPkg x) ∧
        tensorFailureExpectation strategy.state Z H.toSubMeas ≤
          answerSliceSelfImprovementError params restrictionPkg x ∧
        (∀ h : MIPStarRE.LDT.Polynomial params,
          IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x h ≤ Z) := by
  intro x
  let carrier := answerSelfImprovementCarrier params (xRestrictedAnswerSymStrat params strategy x)
  have hgood := restrictionPkg.profile.restrictedGood x
  obtain ⟨H, Z, hH⟩ :=
    selfImprovementInInductionSection_of_axisParallel_selfConsistency
      params carrier hS hA hd
      (restrictionPkg.profile.axisParallel x)
      (restrictionPkg.profile.selfConsistency x)
      (restrictionPkg.profile.diagonal x)
      (inductionPkg.sliceError x)
      hgood.axisParallelTest hgood.selfConsistencyTest
      (inductionPkg.sliceMeasurement x)
      (inductionPkg.pointConsistency x)
  exact ⟨H, Z, hH.completeness, hH.pointConsistency, hH.strongSelfConsistency,
    hH.selfCloseness, hH.bounded, hH.dominatesAveragePointOperator⟩

/-- Convert concrete per-slice structural data into the answer-valued Section 6
self-improvement data.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551` and
`references/ldt-paper/self_improvement.tex:631-811`.

The construction assumes ordinary slice strategies and their structural
measurement transports. It applies the theorem
`selfImprovementInInductionSection` slice-by-slice and transports its fields
back to the answer-valued restricted-slice interface via the recorded state and
point-measurement equalities. It takes the hypotheses `hS`, `hA` and `hd` of
`slice_outputs_ofSliceStrategyTransport`. -/
noncomputable def AnswerSelfImprovementData.ofSliceStrategyTransport
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (hS : strategy.state.toBipartite.IsFinitePair)
    (hA : NoAbelianProj strategy.state.toBipartite.opsA)
    (hd : 1 ≤ params.d)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (inductionPkg :
      AnswerPerSliceInductionData params strategy eps delta gamma restrictionPkg k)
    (sliceTransport :
      AnswerSelfImprovementData.SliceStrategyTransport params strategy eps delta gamma k
        restrictionPkg inductionPkg) :
    AnswerSelfImprovementData params strategy eps delta gamma k restrictionPkg inductionPkg :=
  AnswerSelfImprovementData.ofSelfImprovementInInductionSection
    params strategy eps delta gamma k restrictionPkg inductionPkg
    (AnswerSelfImprovementData.slice_outputs_ofSliceStrategyTransport
      params strategy hS hA hd eps delta gamma k restrictionPkg inductionPkg sliceTransport)

/-- Construct the answer-valued Section 6 self-improvement data directly from
the answer-valued restricted slices.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551` and
`references/ldt-paper/self_improvement.tex:631-811`.

This removes the ordinary slice-realization assumption from the
self-improvement stage. The construction uses the ordinary carrier only as a
device for invoking the Section 9 theorem in the form whose hypotheses are the
axis-parallel and point self-consistency estimates. It takes the hypotheses `hS`, `hA` and
`hd` of `slice_outputs_ofAnswerCarrier`. -/
noncomputable def AnswerSelfImprovementData.ofAnswerCarrier
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (hS : strategy.state.toBipartite.IsFinitePair)
    (hA : NoAbelianProj strategy.state.toBipartite.opsA)
    (hd : 1 ≤ params.d)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (inductionPkg :
      AnswerPerSliceInductionData params strategy eps delta gamma restrictionPkg k) :
    AnswerSelfImprovementData params strategy eps delta gamma k restrictionPkg inductionPkg :=
  AnswerSelfImprovementData.ofSelfImprovementInInductionSection
    params strategy eps delta gamma k restrictionPkg inductionPkg
    (AnswerSelfImprovementData.slice_outputs_ofAnswerCarrier
      params strategy hS hA hd eps delta gamma k restrictionPkg inductionPkg)

end MIPRE.LIDT.Co.MainInductionStep

end

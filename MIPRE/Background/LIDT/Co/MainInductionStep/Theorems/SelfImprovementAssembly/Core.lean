/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
MainInductionStep/Theorems/SelfImprovementAssembly/Core.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.MainInductionStep.Statements
public import MIPRE.Background.LIDT.Co.Preliminaries.Defs
public import MIPRE.Background.LIDT.Co.Test.StrategyFailures
public import MIPRE.Background.LIDT.Co.Commutativity.ScalarApproximation.Core
public import MIPRE.Background.LIDT.Co.Pasting.Bernoulli.Final
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Statements
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Results.SelfImprovementTop.Core

@[expose] public section

/-!
# Section 6 — Ordinary Self-Improvement Data

Core public API for the ordinary self-improvement data: constructors for
`SelfImprovementData`, the induction-section theorem `selfImprovementInInductionSection`, the
monotone-witness cleanup `mainInductionOfWitness`, and the source-facing pasting theorem
`ldPastingInInductionSection`. This is the counterpart of the vendored
`MainInductionStep/Theorems/SelfImprovementAssembly/Core.lean` (under
`MIPRE/Background/LIDT/MIPStarRE/LDT/`) in the port of `planning/c6b-plan.md` (milestone M12,
section "Port conventions").

The answer-valued slice-transport constructors are separated into
`SelfImprovementAssembly.AnswerSlice`.

## Translation

A strategy is a `SymStrat params 𝔓 K` (or `SymStrat params.next 𝔓 K`), whose state is the
symmetric model `strategy.state : SymModel 𝔓 K`; `Polynomial params` is
`MIPStarRE.LDT.Polynomial params`, `Z : MIPStarRE.Quantum.Op ι` is `Z : 𝔓`, `Error` is `ℝ`,
`H.toSubMeas.liftLeft` is `H.toSubMeas.liftLeft strategy.state` (and `liftRight`),
`leftPlacedSubMeas (ιB := ι)` is `strategy.state.leftPlacedSubMeas` (and `rightPlacedSubMeas`),
and the relations (`ConsRel`, `BipartiteSSCRel`, `SDDRel`, `CompletenessAtLeast`) are read on
`strategy.state`. The concrete slice strategies of `SelfImprovementData.SliceStrategyTransport`
are `SymStrat params 𝔓 K` on the same algebra and Hilbert space as the ambient strategy, so
`state_eq` is an equality of symmetric models. The vendored `strategy.permInvState` passed to
`Commutativity.qBipartiteSSCDefect_eq_half_qSDD_of_proj` is gone (M7's lemma takes the model
`S` first and no swap hypothesis), and the vendored file-wide `respectTransparency false` is not
needed: the file sets no option.

## Three threaded hypotheses

The ported `SelfImprovement.selfImprovement` (milestone M10) takes, right after `strategy`,

- `hS : strategy.state.toBipartite.IsFinitePair` and
  `hA : NoAbelianProj strategy.state.toBipartite.opsA`, the model hypotheses of the ported
  orthonormalization (T1, through M2's Theorem G) and of the summed semidefinite form (M9), and
- `hd : 1 ≤ params.d`, which makes the in-core orthonormalization error positive.

So `selfImprovementInInductionSection` and
`selfImprovementInInductionSection_of_axisParallel_selfConsistency` take `hS hA hd` right after
`strategy`, and so do `SelfImprovementData.slice_outputs_ofSliceStrategyTransport` and
`SelfImprovementData.ofSliceStrategyTransport`, for the ambient strategy: a concrete slice
strategy has the ambient state (`SliceStrategyTransport.state_eq`), so the model hypotheses pass
to it by rewriting, and `hd` is a hypothesis on `params`, unchanged on the slices. The vendored
statements, on finite carriers, need none of the three. Milestone M13 discharges `hS hA` for the
doubled model `D(M)` and M14 supplies `hd` from `SoundIn`. `ldPastingInInductionSection` takes no
new hypothesis, pasting neither orthonormalizing nor solving a semidefinite program (M11).

## Proofs that differ from the vendored ones

- `strongSelfConsistency_of_sddRel` identifies the two averages over `uniformDistribution Unit`
  by `avgOver_const_mul` and `avgOver_congr`, as M7's `Commutativity/ScalarApproximation/Pointwise`
  does, in place of the vendored `simpa` unfolding them, and closes the error comparison by
  `rfl` (`selfImprovementError params eps delta` is `selfImprovementInInductionError params eps
  delta 0`, whose last argument is unused).
- `selfImprovementInInductionSectionConclusion_ofSelfImprovementConclusion` takes its
  `strongSelfConsistency` field from `strongSelfConsistency_of_sddRel` at the conclusion's
  `selfCloseness`, whose placements `strategy.state.leftPlacedSubMeas H.toSubMeas` and
  `H.toSubMeas.liftLeft strategy.state` agree by definitional equality, as in the vendored file.
- `SelfImprovementData.slice_outputs_ofSliceStrategyTransport` rewrites with `state_eq` in the
  goal rather than in each of the six hypotheses.

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

open MIPStarRE.LDT (Parameters FieldModel Point Fq avgOver avgOver_congr avgOver_const_mul
  uniformDistribution)
open MIPStarRE.LDT.MainInductionStep (mainInductionError selfImprovementInInductionError
  ldPastingInInductionError)
open MIPStarRE.LDT.SelfImprovement (selfImprovementError)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Monotone postprocessing of an explicit witness for the main-induction conclusion.

This helper is the final `error ≤ mainInductionError` cleanup step only; the
actual Section 6 construction is carried by `mainInductionBaseCase`,
`mainInduction`, and their predecessor, self-improvement, and pasting
construction lemmas. -/
theorem mainInductionOfWitness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (hwitness :
      ∃ error : ℝ, ∃ G : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓,
        strategy.state.ConsRel (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          (polynomialEvaluationFamily params G.toSubMeas)
          error ∧
        error ≤ mainInductionError params k eps delta gamma) :
    ∃ G : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓,
      strategy.state.ConsRel (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas)
        (mainInductionError params k eps delta gamma) :=
  let ⟨_, G, hG, herror⟩ := hwitness
  ⟨G, ⟨hG.offDiagonalBound.trans herror⟩⟩

/-- Convert same-register closeness of a projective submeasurement into bipartite strong
self-consistency. The vendored lemma passes `strategy.permInvState` to the half-`qSDD` identity;
here that identity is M7's `Commutativity.qBipartiteSSCDefect_eq_half_qSDD_of_proj`, which needs
no swap hypothesis. -/
theorem strongSelfConsistency_of_sddRel
    (params : Parameters) [FieldModel params.q] (strategy : SymStrat params 𝔓 K)
    (eps delta gamma : ℝ) (H : ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hclose : strategy.state.SDDRel (uniformDistribution Unit)
        (constSubMeasFamily (H.toSubMeas.liftLeft strategy.state))
        (constSubMeasFamily (H.toSubMeas.liftRight strategy.state))
        (selfImprovementError params eps delta)) :
    strategy.state.BipartiteSSCRel (uniformDistribution Unit)
      (constSubMeasFamily H.toSubMeas)
      (selfImprovementInInductionError params eps delta gamma) := by
  have hssc_eq :
      strategy.state.bipartiteSSCError (uniformDistribution Unit)
          (constSubMeasFamily H.toSubMeas) =
        (1 / 2 : ℝ) * strategy.state.toVecState.sddError (uniformDistribution Unit)
          (constSubMeasFamily (H.toSubMeas.liftLeft strategy.state))
          (constSubMeasFamily (H.toSubMeas.liftRight strategy.state)) := by
    unfold SymModel.bipartiteSSCError VecState.sddError
    rw [← avgOver_const_mul]
    exact avgOver_congr _ _ _ fun _ =>
      Commutativity.qBipartiteSSCDefect_eq_half_qSDD_of_proj strategy.state H
  have hsdd_nonneg := strategy.state.toVecState.sddError_nonneg (uniformDistribution Unit)
    (constSubMeasFamily (H.toSubMeas.liftLeft strategy.state))
    (constSubMeasFamily (H.toSubMeas.liftRight strategy.state))
  have hbound := hclose.squaredDistanceBound
  refine ⟨hssc_eq ▸ ?_⟩
  change _ ≤ selfImprovementError params eps delta
  linarith

/-- Convert the Section 9 self-improvement conclusion into the Section 6
induction-level self-improvement conclusion.

The Section 6 conclusion records the original input submeasurement only as a
parameter; its six mathematical fields concern the output projective
submeasurement and the dual witness.  This lemma isolates that transport, so
the induction-section self-improvement target is not confused with measurement-completion
bookkeeping. -/
theorem selfImprovementInInductionSectionConclusion_ofSelfImprovementConclusion
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta gamma nu : ℝ)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (Gmeas : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓)
    (H : ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (Z : 𝔓)
    (hfinal :
      SelfImprovement.SelfImprovementConclusion params strategy Gmeas H Z
        eps delta gamma nu) :
    SelfImprovementInInductionSectionConclusion params strategy G H Z
      eps delta gamma nu :=
  { completeness := hfinal.completeness
    pointConsistency := hfinal.pointConsistency
    strongSelfConsistency :=
      strongSelfConsistency_of_sddRel params strategy eps delta gamma H hfinal.selfCloseness
    selfCloseness := hfinal.selfCloseness
    bounded := hfinal.projectiveResidualBound
    dominatesAveragePointOperator := fun h =>
      sub_nonneg.mp (hfinal.dualDominatesAveragedPoint h) }

/-- `thm:self-improvement-in-induction-section`.

Paper origin: `references/ldt-paper/self_improvement.tex:631-811`
(`\label{thm:self-improvement}`), used in the induction section at
`references/ldt-paper/inductive_step.tex:461-485`.  The labelled induction
statement at `references/ldt-paper/inductive_step.tex:249-286` states the input
as a submeasurement, while the proved form at
`references/ldt-paper/self_improvement.tex:635-671` uses a measurement.  This
Lean statement follows the proved measurement-valued form needed in the
induction proof.

The input \(G\) is a complete polynomial measurement, as in the paper's
restated self-improvement theorem.  The conclusion is phrased in the Section 6
record `SelfImprovementInInductionSectionConclusion`, whose fields are exactly
the projective output estimates used in the inductive step.  The proof applies
`SelfImprovement.selfImprovement` and transports the resulting fields into the
Section 6 record.

The hypotheses `hS`, `hA` and `hd` are those of the ported `SelfImprovement.selfImprovement`
(module docstring); the vendored statement has none of them. -/
theorem selfImprovementInInductionSection
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (hS : strategy.state.toBipartite.IsFinitePair)
    (hA : NoAbelianProj strategy.state.toBipartite.opsA)
    (hd : 1 ≤ params.d)
    (eps delta gamma nu : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (G : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hcons : strategy.state.ConsRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas) nu) :
    ∃ H : ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝔓, ∃ Z : 𝔓,
      SelfImprovementInInductionSectionConclusion params strategy G.toSubMeas H Z
        eps delta gamma nu :=
  let ⟨H, Z, hfinal⟩ :=
    SelfImprovement.selfImprovement params strategy hS hA hd eps delta gamma nu hgood G hcons
  ⟨H, Z,
    selfImprovementInInductionSectionConclusion_ofSelfImprovementConclusion
      params strategy eps delta gamma nu G.toSubMeas G H Z hfinal⟩

/-- Induction-section self-improvement using only the two strategy bounds
consumed by Section 9.

Paper origin: `references/ldt-paper/self_improvement.tex:631-811`.

This is a formalization-only strengthening of
`selfImprovementInInductionSection`.  The paper states the theorem in the
standing context of an `(eps, delta, gamma)`-good strategy, but the displayed
self-improvement construction uses the axis-parallel and point
self-consistency bounds and its conclusion is independent of the diagonal-line
error parameter. It takes the hypotheses `hS`, `hA` and `hd` of
`selfImprovementInInductionSection`. -/
theorem selfImprovementInInductionSection_of_axisParallel_selfConsistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (hS : strategy.state.toBipartite.IsFinitePair)
    (hA : NoAbelianProj strategy.state.toBipartite.opsA)
    (hd : 1 ≤ params.d)
    (eps delta gamma nu : ℝ)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself : strategy.selfConsistencyFailureProbability ≤ delta)
    (G : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hcons : strategy.state.ConsRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas) nu) :
    ∃ H : ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝔓, ∃ Z : 𝔓,
      SelfImprovementInInductionSectionConclusion params strategy G.toSubMeas H Z
        eps delta gamma nu :=
  let ⟨H, Z, hfinal⟩ :=
    SelfImprovement.selfImprovement_of_axisParallel_selfConsistency
      params strategy hS hA hd eps delta gamma nu haxis hself G hcons
  ⟨H, Z,
    selfImprovementInInductionSectionConclusion_ofSelfImprovementConclusion
      params strategy eps delta gamma nu G.toSubMeas G H Z hfinal⟩

/-- Convert the slice-wise outputs feeding `selfImprovementInInductionSection`
into the bookkeeping object expected by the later inductive step.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551`, using the
self-improvement theorem restated in
`references/ldt-paper/self_improvement.tex:631-811`.

Because `xRestrictedStrategy params strategy x` is only a
`RestrictedSymStrat params 𝔓 K` rather than a full `SymStrat params 𝔓 K`, the
restricted-strategy outputs are supplied directly as the six paper-faithful
fields recorded by `SelfImprovementData`. -/
noncomputable def SelfImprovementData.ofSelfImprovementInInductionSection
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (restrictionPkg : SliceRestrictionData params strategy eps delta gamma)
    (inductionPkg : PerSliceInductionData params strategy eps delta gamma restrictionPkg k)
    (hslice :
      ∀ x,
        ∃ H : ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝔓, ∃ Z : 𝔓,
          strategy.state.CompletenessAtLeast (H.toSubMeas.liftLeft strategy.state)
            ((1 - inductionPkg.sliceError x) -
              sliceSelfImprovementError params restrictionPkg x) ∧
          strategy.state.ConsRel (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas (xRestrictedStrategy params strategy x).pointMeasurement)
            (polynomialEvaluationFamily params H.toSubMeas)
            (sliceSelfImprovementError params restrictionPkg x) ∧
          strategy.state.BipartiteSSCRel (uniformDistribution Unit)
            (constSubMeasFamily H.toSubMeas)
            (sliceSelfImprovementError params restrictionPkg x) ∧
          strategy.state.SDDRel (uniformDistribution Unit)
            (constSubMeasFamily (strategy.state.leftPlacedSubMeas H.toSubMeas))
            (constSubMeasFamily (strategy.state.rightPlacedSubMeas H.toSubMeas))
            (sliceSelfImprovementError params restrictionPkg x) ∧
          tensorFailureExpectation strategy.state Z H.toSubMeas ≤
            sliceSelfImprovementError params restrictionPkg x ∧
          (∀ h : MIPStarRE.LDT.Polynomial params,
            IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x h ≤ Z)) :
    SelfImprovementData params strategy eps delta gamma k restrictionPkg inductionPkg :=
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

/-- Narrow transport record for running the Section 9 self-improvement theorem
on each concrete Section 6 slice strategy.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551` and
`references/ldt-paper/self_improvement.tex:631-811`; this records the
formalization boundary needed to run the Section 9 theorem on concrete slice
strategies.

For every slice the record asks for a concrete `SymStrat params 𝔓 K` whose state,
point-measurement interface, and averaged point operator agree with the
restricted-slice bookkeeping used by Section 6. The vendored record notes that the extra
`SymStrat` fields (`permInvState`, `densityFixed`, `isNormalized`) are not derived from the
restricted strategy; here they are not fields at all, each being a theorem of the model.

The Section 9 analytic proof debt is not stored in this record.  The data-record
constructor below calls the paper-facing theorem
`selfImprovementInInductionSection`; its proof applies the Section 9 theorem and
then transports the output estimates to the induction notation. -/
structure SelfImprovementData.SliceStrategyTransport
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (restrictionPkg : SliceRestrictionData params strategy eps delta gamma)
    (inductionPkg : PerSliceInductionData params strategy eps delta gamma restrictionPkg k)
    where
  /-- Concrete symmetric strategies realizing the slice interfaces. -/
  sliceStrategy : Fq params → SymStrat params 𝔓 K
  /-- Each concrete slice strategy uses the ambient state. -/
  state_eq : ∀ x, (sliceStrategy x).state = strategy.state
  /-- Its point measurement agrees with the restricted-slice point interface. -/
  pointMeasurement_eq :
    ∀ x,
      (sliceStrategy x).pointMeasurement =
        (xRestrictedStrategy params strategy x).pointMeasurement
  /-- Its averaged point operator is the averaged slice point operator used by
  Section 6. -/
  averagedPoint_eq :
    ∀ x h,
      IdxPolyFamily.averagedPointEvaluationOperator (sliceStrategy x) h =
        IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x h
  /-- The concrete slice strategy is good with the restricted failure profile. -/
  good :
    ∀ x,
      (sliceStrategy x).IsGood
        (restrictionPkg.profile.axisParallel x)
        (restrictionPkg.profile.selfConsistency x)
        (restrictionPkg.profile.diagonal x)

/-- The averaged slice point-operator compatibility is structural: once a
concrete slice strategy's point measurement agrees with the restricted-slice point
measurement, the averaged point operators agree by unfolding the two averages. -/
theorem SelfImprovementData.SliceStrategyTransport.averagedPoint_eq_of_pointMeasurement_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (sliceStrategy : Fq params → SymStrat params 𝔓 K)
    (hpoint :
      ∀ x,
        (sliceStrategy x).pointMeasurement =
          (xRestrictedStrategy params strategy x).pointMeasurement) :
    ∀ x h,
      IdxPolyFamily.averagedPointEvaluationOperator (sliceStrategy x) h =
        IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x h := by
  intro x h
  unfold IdxPolyFamily.averagedPointEvaluationOperator
    IdxPolyFamily.averagedSlicePointEvaluationOperator
  rw [hpoint x]
  rfl

/-- Build `SliceStrategyTransport` without separately assuming averaged point-operator
compatibility.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551`; the averaged
point-operator compatibility is a formal transport between the restricted slice
interface and the Section 9 interface.

The only structural equality needed for that field is `pointMeasurement_eq`.
The remaining inputs are the concrete slice strategies, their state transport, and
their restricted-profile goodness. -/
noncomputable def SelfImprovementData.SliceStrategyTransport.ofPointMeasurementEq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (restrictionPkg : SliceRestrictionData params strategy eps delta gamma)
    (inductionPkg : PerSliceInductionData params strategy eps delta gamma restrictionPkg k)
    (sliceStrategy : Fq params → SymStrat params 𝔓 K)
    (state_eq : ∀ x, (sliceStrategy x).state = strategy.state)
    (pointMeasurement_eq :
      ∀ x,
        (sliceStrategy x).pointMeasurement =
          (xRestrictedStrategy params strategy x).pointMeasurement)
    (good :
      ∀ x,
        (sliceStrategy x).IsGood
          (restrictionPkg.profile.axisParallel x)
          (restrictionPkg.profile.selfConsistency x)
          (restrictionPkg.profile.diagonal x)) :
    SelfImprovementData.SliceStrategyTransport params strategy eps delta gamma k
      restrictionPkg inductionPkg where
  sliceStrategy := sliceStrategy
  state_eq := state_eq
  pointMeasurement_eq := pointMeasurement_eq
  averagedPoint_eq :=
    SelfImprovementData.SliceStrategyTransport.averagedPoint_eq_of_pointMeasurement_eq
      params strategy sliceStrategy pointMeasurement_eq
  good := good

/-- Transport restricted-slice goodness to a concrete slice strategy once the
state and the measurements used by the three LDT subtests agree with
`xRestrictedStrategy`.

This is a structural helper for the successor route: it uses the
`restrictedGood` field already stored in `SliceRestrictionData.profile` and
does not introduce additional Section 9 analytic assumptions. -/
theorem SelfImprovementData.SliceStrategyTransport.good_of_restrictedGood
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (restrictionPkg : SliceRestrictionData params strategy eps delta gamma)
    (sliceStrategy : Fq params → SymStrat params 𝔓 K)
    (state_eq : ∀ x, (sliceStrategy x).state = strategy.state)
    (pointMeasurement_eq :
      ∀ x,
        (sliceStrategy x).pointMeasurement =
          (xRestrictedStrategy params strategy x).pointMeasurement)
    (axisParallelMeasurement_eq :
      ∀ x,
        (sliceStrategy x).axisParallelMeasurement.toIdxProjMeas =
          (xRestrictedStrategy params strategy x).axisParallelMeasurement.toIdxProjMeas)
    (diagonalMeasurement_eq :
      ∀ x,
        (sliceStrategy x).diagonalMeasurement.toIdxProjMeas =
          (xRestrictedStrategy params strategy x).diagonalMeasurement) :
    ∀ x,
      (sliceStrategy x).IsGood
        (restrictionPkg.profile.axisParallel x)
        (restrictionPkg.profile.selfConsistency x)
        (restrictionPkg.profile.diagonal x) := by
  intro x
  have hgood := restrictionPkg.profile.restrictedGood x
  refine ⟨?_, ?_, ?_⟩
  · have hfail : (sliceStrategy x).axisParallelFailureProbability =
        (xRestrictedStrategy params strategy x).axisParallelFailureProbability := by
      unfold SymStrat.axisParallelFailureProbability
        RestrictedSymStrat.axisParallelFailureProbability
        axisParallelPointAnswerFamily RestrictedSymStrat.axisParallelPointAnswerFamily
        axisParallelLineAnswerFamily RestrictedSymStrat.axisParallelLineAnswerFamily
      simp [state_eq x, pointMeasurement_eq x, axisParallelMeasurement_eq x]
    exact hfail ▸ hgood.axisParallelTest
  · have hfail : (sliceStrategy x).selfConsistencyFailureProbability =
        (xRestrictedStrategy params strategy x).selfConsistencyFailureProbability := by
      unfold SymStrat.selfConsistencyFailureProbability
        RestrictedSymStrat.selfConsistencyFailureProbability
      rw [state_eq x, pointMeasurement_eq x]
      rfl
    exact hfail ▸ hgood.selfConsistencyTest
  · have hfail : (sliceStrategy x).diagonalFailureProbability =
        (xRestrictedStrategy params strategy x).diagonalFailureProbability := by
      unfold SymStrat.diagonalFailureProbability
        RestrictedSymStrat.diagonalFailureProbability
        diagonalPointAnswerFamily RestrictedSymStrat.restrictedDiagonalPointAnswerFamily
        diagonalLineAnswerFamily RestrictedSymStrat.restrictedDiagonalLineAnswerFamily
      simp [state_eq x, pointMeasurement_eq x, diagonalMeasurement_eq x]
    exact hfail ▸ hgood.diagonalLineTest

/-- Build `SliceStrategyTransport` from concrete slice strategies and measurement
transport.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551` and
`references/ldt-paper/self_improvement.tex:631-811`.

This constructor fills both structural fields that are forced by the restricted
slice interface: `averagedPoint_eq` follows from point-measurement transport and
`good` follows from the restricted failure profile plus state/axis/diagonal
measurement transport.  The remaining non-structural inputs are the concrete
slice strategies themselves. -/
noncomputable def SelfImprovementData.SliceStrategyTransport.ofMeasurementEq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (restrictionPkg : SliceRestrictionData params strategy eps delta gamma)
    (inductionPkg : PerSliceInductionData params strategy eps delta gamma restrictionPkg k)
    (sliceStrategy : Fq params → SymStrat params 𝔓 K)
    (state_eq : ∀ x, (sliceStrategy x).state = strategy.state)
    (pointMeasurement_eq :
      ∀ x,
        (sliceStrategy x).pointMeasurement =
          (xRestrictedStrategy params strategy x).pointMeasurement)
    (axisParallelMeasurement_eq :
      ∀ x,
        (sliceStrategy x).axisParallelMeasurement.toIdxProjMeas =
          (xRestrictedStrategy params strategy x).axisParallelMeasurement.toIdxProjMeas)
    (diagonalMeasurement_eq :
      ∀ x,
        (sliceStrategy x).diagonalMeasurement.toIdxProjMeas =
          (xRestrictedStrategy params strategy x).diagonalMeasurement) :
    SelfImprovementData.SliceStrategyTransport params strategy eps delta gamma k
      restrictionPkg inductionPkg :=
  SelfImprovementData.SliceStrategyTransport.ofPointMeasurementEq
    params strategy eps delta gamma k restrictionPkg inductionPkg sliceStrategy state_eq
    pointMeasurement_eq
    (SelfImprovementData.SliceStrategyTransport.good_of_restrictedGood
      params strategy eps delta gamma restrictionPkg sliceStrategy state_eq
      pointMeasurement_eq axisParallelMeasurement_eq diagonalMeasurement_eq)

/-- Concrete slice strategies give the slice-wise Section 9 outputs used by the
ordinary self-improvement data in the successor step.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551` and
`references/ldt-paper/self_improvement.tex:631-811`.

This is an internal transport theorem.  It applies
`selfImprovementInInductionSection` to each ordinary slice strategy supplied by
`SliceStrategyTransport`, and then rewrites the state, point-measurement, and
averaged-point conclusions back into the restricted-slice notation used in the
successor step. The hypotheses `hS` and `hA` are stated for the ambient strategy and pass to
each slice strategy through `state_eq`; `hd` is a hypothesis on `params`. -/
theorem SelfImprovementData.slice_outputs_ofSliceStrategyTransport
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (hS : strategy.state.toBipartite.IsFinitePair)
    (hA : NoAbelianProj strategy.state.toBipartite.opsA)
    (hd : 1 ≤ params.d)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (restrictionPkg : SliceRestrictionData params strategy eps delta gamma)
    (inductionPkg : PerSliceInductionData params strategy eps delta gamma restrictionPkg k)
    (sliceTransport :
      SelfImprovementData.SliceStrategyTransport params strategy eps delta gamma k
        restrictionPkg inductionPkg) :
    ∀ x,
      ∃ H : ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝔓, ∃ Z : 𝔓,
        strategy.state.CompletenessAtLeast (H.toSubMeas.liftLeft strategy.state)
          ((1 - inductionPkg.sliceError x) -
            sliceSelfImprovementError params restrictionPkg x) ∧
        strategy.state.ConsRel (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas (xRestrictedStrategy params strategy x).pointMeasurement)
          (polynomialEvaluationFamily params H.toSubMeas)
          (sliceSelfImprovementError params restrictionPkg x) ∧
        strategy.state.BipartiteSSCRel (uniformDistribution Unit)
          (constSubMeasFamily H.toSubMeas)
          (sliceSelfImprovementError params restrictionPkg x) ∧
        strategy.state.SDDRel (uniformDistribution Unit)
          (constSubMeasFamily (strategy.state.leftPlacedSubMeas H.toSubMeas))
          (constSubMeasFamily (strategy.state.rightPlacedSubMeas H.toSubMeas))
          (sliceSelfImprovementError params restrictionPkg x) ∧
        tensorFailureExpectation strategy.state Z H.toSubMeas ≤
          sliceSelfImprovementError params restrictionPkg x ∧
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

/-- Convert per-slice structural slice data into the Section 6
self-improvement data.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551` and
`references/ldt-paper/self_improvement.tex:631-811`.

The construction assumes the concrete slice strategies and their structural
measurement transports. It applies the theorem
`selfImprovementInInductionSection` slice-by-slice and transports its fields
across the recorded equalities to the restricted-slice interface. It takes the hypotheses
`hS`, `hA` and `hd` of `slice_outputs_ofSliceStrategyTransport`. -/
noncomputable def SelfImprovementData.ofSliceStrategyTransport
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (hS : strategy.state.toBipartite.IsFinitePair)
    (hA : NoAbelianProj strategy.state.toBipartite.opsA)
    (hd : 1 ≤ params.d)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (restrictionPkg : SliceRestrictionData params strategy eps delta gamma)
    (inductionPkg : PerSliceInductionData params strategy eps delta gamma restrictionPkg k)
    (sliceTransport :
      SelfImprovementData.SliceStrategyTransport params strategy eps delta gamma k
        restrictionPkg inductionPkg) :
    SelfImprovementData params strategy eps delta gamma k restrictionPkg inductionPkg :=
  SelfImprovementData.ofSelfImprovementInInductionSection
    params strategy eps delta gamma k restrictionPkg inductionPkg
    (SelfImprovementData.slice_outputs_ofSliceStrategyTransport
      params strategy hS hA hd eps delta gamma k restrictionPkg inductionPkg sliceTransport)

/-- Source-facing Lean statement for `thm:ld-pasting-in-induction-section`.

Paper origin: `references/ldt-paper/inductive_step.tex:299-338`
(`\label{thm:ld-pasting-in-induction-section}`).  The statement is the
Chapter 6 restatement of `thm:ld-pasting`, with the error parameters named as
they are used in the main-induction proof.

**Source-faithful transport:** This theorem invokes the unrestricted formal
theorem `Pasting.ldPasting` and projects its point-consistency field into the
induction-section conclusion record.  It carries no additional assumption beyond
the already formalized pasting theorem. -/
theorem ldPastingInInductionSection
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma kappa zeta : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params 𝔓)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : Measurement (MIPStarRE.LDT.Polynomial params.next) 𝔓,
      LdPastingInInductionSectionConclusion params strategy family H
        eps delta gamma kappa zeta k :=
  let ⟨H, hH⟩ := Pasting.ldPasting params strategy eps delta gamma kappa zeta
    hgood family hcomplete hcons hself hbound k hk
  ⟨H, ⟨hH.pointConsistency⟩⟩

end MIPRE.LIDT.Co.MainInductionStep

end

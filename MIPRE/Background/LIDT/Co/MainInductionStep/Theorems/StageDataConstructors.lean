/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
MainInductionStep/Theorems/StageDataConstructors.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.MainInductionStep.Theorems.SelfImprovementAssembly.AnswerSlice
public import MIPRE.Background.LIDT.Co.MainInductionStep.Theorems.RestrictedProbabilities.AnswerValued

@[expose] public section

/-!
# Section 6 — Stage-Data Constructors

Constructors for the slice restriction, per-slice induction, self-improvement,
and averaged pasting stage records: `SliceRestrictionData.ofRestrictedProbabilities`,
`AnswerSliceRestrictionData.ofRestrictedProbabilities`,
`SliceRestrictionData.ofAnswer`, `PerSliceInductionData.ofRecursion`,
`AnswerPerSliceInductionData.*`, `SelfImprovementData.ofAnswerForPerSliceInductionData`,
`SelfImprovementData.ofAnswer`, `AnswerSelfImprovementData.ofSelfImprovementData`,
`AveragedPastingData.invokeLdPasting`, and `mainInductionFromStageData`. This is the counterpart
of `MIPRE/Background/LIDT/MIPStarRE/LDT/MainInductionStep/Theorems/StageDataConstructors.lean` in
the port of `planning/c6b-plan.md` (milestone M12, section "Port conventions").

## Translation

A strategy is a `SymStrat params.next 𝔓 K` (`Co/Test/StrategyCore.lean`), whose state is the
symmetric model `strategy.state : SymModel 𝔓 K`; `Polynomial params` is
`MIPStarRE.LDT.Polynomial params`, measurements and slice witnesses live in the local algebra `𝔓`
(the vendored `Op ι`), errors are real numbers (the vendored `Error := ℝ`), and every relation is
read on `strategy.state`. The vendored explicit universe instantiations of the stage records
(`SliceRestrictionData.{uι', uF}` and its siblings) and the separate carrier `ι' : Type uι'` of
`AveragedPastingData.invokeLdPasting_general` and `mainInductionFromStageData` are not needed: the
file declares `universe uP uK` with `𝔓 : Type uP` and `K : Type uK`, and those two declarations
keep only the binder `.{uF}` and take `[FieldModel.{uF} params.q]`, so that they hold for a field
model in any universe, while
`AveragedPastingData.invokeLdPasting` takes `FieldModel.{0}` as the vendored one does. No vendored
statement here has a swap, density or normalization hypothesis, so none is dropped. The vendored
file-wide `respectTransparency false` is not needed: the file sets no option.

## Two threaded hypotheses

`AnswerPerSliceInductionData.ofMainInductionHypothesis` applies the predecessor
`AnswerMainInductionHypothesis` (Co `MainInductionStep/Statements.lean`), which quantifies only over
strategies whose model is a finite pair without abelian projections in its first player's
operators. So it takes, right after `strategy`, `hS : strategy.state.toBipartite.IsFinitePair` and
`hA : NoAbelianProj strategy.state.toBipartite.opsA`, and passes them unchanged to each slice
`xRestrictedAnswerSymStrat params strategy x`, whose state is `strategy.state` by definition
(`xRestrictedAnswerSymStrat_state`). It does not take `1 ≤ params.d`: the hypothesis is applied,
not proved, here. The universes of the hypothesis are left to unification, as in the vendored
statement: `hinduction 𝔓 K` fixes them to those of `𝔓` and `K`. Every other declaration holds for
any symmetric model.

## Proofs that differ from the vendored ones

- The two `ofRestrictedProbabilities` constructors and the two `ofRecursion` constructors read the
  witnesses off `Classical.choose_spec` by projection, in place of the vendored `classical`,
  `let`, `rcases` and `simpa`.
- `restrictedPointSubMeasurement_eq_answer` is `rfl` (the vendored `funext` and `try rfl`): the two
  restricted point measurements are the same function.
- The answer-forgetting conversions `AnswerPerSliceInductionData.ofPerSliceInductionData`,
  `PerSliceInductionData.ofAnswer`, `SelfImprovementData.ofAnswerForPerSliceInductionData`,
  `SelfImprovementData.ofAnswer` and `AnswerSelfImprovementData.ofSelfImprovementData` copy every
  field unchanged, by definitional equality, in place of the vendored `rw` with
  `restrictedPointSubMeasurement_eq_answer` and `simpa` unfolding the error functions: the point
  measurements, the slice errors and the profiles of the two interfaces agree by `rfl`.
- `SliceRestrictionData.ofAnswer` copies the axis-parallel and self-consistency bounds by
  definitional equality and transports only the diagonal one, along
  `answerRestricted_diagonalFailureProbability_eq`.
- `mainInductionFromStageData` passes the pasted point consistency and `hpaste.error_le` to
  `mainInductionOfWitness` directly, in place of the vendored `simpa` with local `let`s.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/inductive_step.tex`
- `blueprint/src/chapter/ch10_induction.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.MainInductionStep

open MIPStarRE.LDT (Parameters FieldModel Point Fq uniformDistribution)
open MIPStarRE.LDT.MainInductionStep (mainInductionError ldPastingInInductionError)
open MIPRE.LIDT.Co (SymStrat AnswerSymStrat)

universe uP uK

variable {𝔓 : Type uP} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type uK} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ## Stage-data constructors and theorem composition -/

/-- Extract a concrete slice-restriction data record from
`lem:restricted-probabilities`.

Paper origin: `references/ldt-paper/inductive_step.tex:374-412`
(`\label{lem:restricted-probabilities}`). -/
noncomputable def SliceRestrictionData.ofRestrictedProbabilities
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (hrestricted : RestrictedProbabilitiesStatement params strategy eps delta gamma) :
    SliceRestrictionData params strategy eps delta gamma where
  profile := Classical.choose hrestricted.profileExists
  axisAverageBound := (Classical.choose_spec hrestricted.profileExists).1
  selfAverageBound := (Classical.choose_spec hrestricted.profileExists).2.1
  diagonalAverageBound := (Classical.choose_spec hrestricted.profileExists).2.2

/-- Extract a concrete answer-valued slice-restriction data record from the
answer-valued restricted-probabilities bookkeeping statement.

Paper origin: `references/ldt-paper/inductive_step.tex:374-412`
(`\label{lem:restricted-probabilities}`), with the answer-valued restriction
interface used for the recursive slice call. -/
noncomputable def AnswerSliceRestrictionData.ofRestrictedProbabilities
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (hrestricted : AnswerRestrictedProbabilitiesStatement params strategy eps delta gamma) :
    AnswerSliceRestrictionData params strategy eps delta gamma where
  profile := Classical.choose hrestricted.profileExists
  axisAverageBound := (Classical.choose_spec hrestricted.profileExists).1
  selfAverageBound := (Classical.choose_spec hrestricted.profileExists).2.1
  diagonalAverageBound := (Classical.choose_spec hrestricted.profileExists).2.2

/-- Forget the answer-valued diagonal alphabet after recording the verifier-visible
failure probabilities.  The three tests agree with the ordinary restricted
strategy at the sampled answer level.

Paper origin: `references/ldt-paper/inductive_step.tex:441-454`; this is a
formalization-only transport between two encodings of the same restricted slice
call. -/
noncomputable def SliceRestrictionData.ofAnswer
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (answerPkg : AnswerSliceRestrictionData params strategy eps delta gamma) :
    SliceRestrictionData params strategy eps delta gamma where
  profile :=
    { axisParallel := answerPkg.profile.axisParallel
      selfConsistency := answerPkg.profile.selfConsistency
      diagonal := answerPkg.profile.diagonal
      restrictedGood := fun x =>
        { axisParallelTest := (answerPkg.profile.restrictedGood x).axisParallelTest
          selfConsistencyTest := (answerPkg.profile.restrictedGood x).selfConsistencyTest
          diagonalLineTest :=
            answerRestricted_diagonalFailureProbability_eq params strategy x ▸
              (answerPkg.profile.restrictedGood x).diagonalLineTest } }
  axisAverageBound := answerPkg.axisAverageBound
  selfAverageBound := answerPkg.selfAverageBound
  diagonalAverageBound := answerPkg.diagonalAverageBound

/-- Turn the recursive family of slice-wise induction witnesses into explicit
slice data `x ↦ (σ_x, G^x)`.

Paper origin: `references/ldt-paper/inductive_step.tex:441-454`. -/
noncomputable def PerSliceInductionData.ofRecursion
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (restrictionPkg : SliceRestrictionData params strategy eps delta gamma)
    (hrec :
      ∀ x,
        ∃ error : ℝ, ∃ G : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓,
          strategy.state.ConsRel (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas (xRestrictedStrategy params strategy x).pointMeasurement)
            (polynomialEvaluationFamily params G.toSubMeas)
            error ∧
          error ≤
            mainInductionError params k
              (restrictionPkg.profile.axisParallel x)
              (restrictionPkg.profile.selfConsistency x)
              (restrictionPkg.profile.diagonal x)) :
    PerSliceInductionData params strategy eps delta gamma restrictionPkg k where
  sliceError := fun x => Classical.choose (hrec x)
  sliceMeasurement := fun x => Classical.choose (Classical.choose_spec (hrec x))
  pointConsistency := fun x => (Classical.choose_spec (Classical.choose_spec (hrec x))).1
  error_le := fun x => (Classical.choose_spec (Classical.choose_spec (hrec x))).2

/-- Turn answer-valued recursive slice-wise induction witnesses into explicit
slice data `x ↦ (σ_x, G^x)`.

Paper origin: `references/ldt-paper/inductive_step.tex:441-454`. -/
noncomputable def AnswerPerSliceInductionData.ofRecursion
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (hrec :
      ∀ x,
        ∃ error : ℝ, ∃ G : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓,
          strategy.state.ConsRel (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas
              (xRestrictedAnswerSymStrat params strategy x).pointMeasurement)
            (polynomialEvaluationFamily params G.toSubMeas)
            error ∧
          error ≤
            mainInductionError params k
              (restrictionPkg.profile.axisParallel x)
              (restrictionPkg.profile.selfConsistency x)
              (restrictionPkg.profile.diagonal x)) :
    AnswerPerSliceInductionData params strategy eps delta gamma restrictionPkg k where
  sliceError := fun x => Classical.choose (hrec x)
  sliceMeasurement := fun x => Classical.choose (Classical.choose_spec (hrec x))
  pointConsistency := fun x => (Classical.choose_spec (Classical.choose_spec (hrec x))).1
  error_le := fun x => (Classical.choose_spec (Classical.choose_spec (hrec x))).2

/-- Build an answer-valued per-slice induction data record from exact
main-induction conclusions for the answer-restricted slices.

Paper origin: `references/ldt-paper/inductive_step.tex:441-454`.

This is the data record form of the paper's invocation of the induction hypothesis in
`inductive_step.tex`, lines 441--454.  The hypotheses already have the exact
restricted-profile `mainInductionError` bound, so the proof only records those
witnesses in the `AnswerPerSliceInductionData` structure. -/
noncomputable def AnswerPerSliceInductionData.ofMainInductionConclusions
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (hinduction :
      ∀ x,
        AnswerMainInductionConclusion params
          (xRestrictedAnswerSymStrat params strategy x)
          (restrictionPkg.profile.axisParallel x)
          (restrictionPkg.profile.selfConsistency x)
          (restrictionPkg.profile.diagonal x)
          k) :
    AnswerPerSliceInductionData params strategy eps delta gamma restrictionPkg k :=
  AnswerPerSliceInductionData.ofRecursion params strategy eps delta gamma k
    restrictionPkg fun x =>
      let ⟨G, hG⟩ := hinduction x
      ⟨_, G, hG, le_rfl⟩

/-- Build an answer-valued per-slice induction data record from a predecessor
answer-valued main-induction hypothesis.

Paper origin: `references/ldt-paper/inductive_step.tex:441-454`.

The restriction data record already records that every `xRestrictedAnswerSymStrat`
is good with the slice profile.  The large-`k` side condition is the predecessor
side condition `400 * params.m * params.d ≤ k`, matching the application of the
induction hypothesis in `inductive_step.tex`, lines 441--442.  The condition
`1 ≤ k` is supplied by the surrounding nontrivial branch; in the successor proof
it follows from `mainInductionError < 1`, not from an artificial assumption
`0 < params.d`.

The hypothesis quantifies only over finite pairs without abelian projections, so `hS` and `hA`
are taken for the ambient model and pass unchanged to each slice, whose state is
`strategy.state` by definition; the vendored statement has neither. -/
noncomputable def AnswerPerSliceInductionData.ofMainInductionHypothesis
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (hS : strategy.state.toBipartite.IsFinitePair)
    (hA : NoAbelianProj strategy.state.toBipartite.opsA)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (hinduction : AnswerMainInductionHypothesis params)
    (hk_pos : 1 ≤ k)
    (hk : 400 * params.m * params.d ≤ k) :
    AnswerPerSliceInductionData params strategy eps delta gamma restrictionPkg k :=
  AnswerPerSliceInductionData.ofMainInductionConclusions params strategy eps delta gamma k
    restrictionPkg fun x =>
      hinduction 𝔓 K (xRestrictedAnswerSymStrat params strategy x)
        (restrictionPkg.profile.axisParallel x)
        (restrictionPkg.profile.selfConsistency x)
        (restrictionPkg.profile.diagonal x)
        k hS hA (restrictionPkg.profile.restrictedGood x) hk_pos hk

/-- Forgetting outcomes identifies the point measurements of the two restricted strategies. -/
theorem restrictedPointSubMeasurement_eq_answer
    (params : Parameters) [FieldModel params.q] (strategy : SymStrat params.next 𝔓 K)
    (x : Fq params) :
    IdxProjMeas.toIdxSubMeas (xRestrictedStrategy params strategy x).pointMeasurement =
      IdxProjMeas.toIdxSubMeas
        (xRestrictedAnswerSymStrat params strategy x).pointMeasurement :=
  rfl

/-- View a per-slice induction data record over an answer-forgotten restriction
data record as an answer-valued data record.

Paper origin: `references/ldt-paper/inductive_step.tex:441-454`; this is a
formalization-only conversion between answer-valued and ordinary restricted-slice
interfaces for the same recursive induction call. -/
noncomputable def AnswerPerSliceInductionData.ofPerSliceInductionData
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (perSliceInduction :
      PerSliceInductionData params strategy eps delta gamma
        (SliceRestrictionData.ofAnswer params strategy eps delta gamma restrictionPkg) k) :
    AnswerPerSliceInductionData params strategy eps delta gamma restrictionPkg k where
  sliceError := perSliceInduction.sliceError
  sliceMeasurement := perSliceInduction.sliceMeasurement
  pointConsistency := perSliceInduction.pointConsistency
  error_le := perSliceInduction.error_le

/-- View answer-valued recursive slice-wise induction witnesses as ordinary
per-slice induction data after forgetting the answer-valued diagonal alphabet.

Paper origin: `references/ldt-paper/inductive_step.tex:441-454`.  The point
measurements of `xRestrictedAnswerSymStrat` and `xRestrictedStrategy` are
definitionally the same slice of the ambient point measurement, so the
consistency witnesses and error bounds transport without changing the
mathematical content. -/
noncomputable def PerSliceInductionData.ofAnswer
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (answerInduction :
      AnswerPerSliceInductionData params strategy eps delta gamma restrictionPkg k) :
    PerSliceInductionData params strategy eps delta gamma
      (SliceRestrictionData.ofAnswer params strategy eps delta gamma restrictionPkg) k where
  sliceError := answerInduction.sliceError
  sliceMeasurement := answerInduction.sliceMeasurement
  pointConsistency := answerInduction.pointConsistency
  error_le := answerInduction.error_le

/-- Forget an answer-valued self-improvement data record when the target
per-slice induction data record is the one used by the ordinary assembly.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551`; this is a
formalization-only conversion between answer-valued and ordinary restricted-slice
self-improvement collects. -/
noncomputable def SelfImprovementData.ofAnswerForPerSliceInductionData
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (perSliceInduction :
      PerSliceInductionData params strategy eps delta gamma
        (SliceRestrictionData.ofAnswer params strategy eps delta gamma restrictionPkg) k)
    (answerSelf :
      AnswerSelfImprovementData params strategy eps delta gamma k restrictionPkg
        (AnswerPerSliceInductionData.ofPerSliceInductionData params strategy eps delta gamma k
          restrictionPkg perSliceInduction)) :
    SelfImprovementData params strategy eps delta gamma k
      (SliceRestrictionData.ofAnswer params strategy eps delta gamma restrictionPkg)
      perSliceInduction where
  sliceProj := answerSelf.sliceProj
  sliceWitness := answerSelf.sliceWitness
  completeness := answerSelf.completeness
  pointConsistency := answerSelf.pointConsistency
  strongSelfConsistency := answerSelf.strongSelfConsistency
  selfCloseness := answerSelf.selfCloseness
  bounded := answerSelf.bounded
  dominatesAveragePointOperator := answerSelf.dominatesAveragePointOperator

/-- View answer-valued self-improvement data as the self-improvement data
over the answer-forgotten per-slice induction record.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551`.  This is the
direct conversion needed by the source proof of `thm:main-induction`: the
recursive induction hypothesis naturally produces answer-valued restricted
slices, while the existing pasting assembly consumes the ordinary slice family.
The conversion changes only the formal restricted-strategy interface, not the
slice projective measurements, witnesses, or inequalities. -/
noncomputable def SelfImprovementData.ofAnswer
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (answerInduction :
      AnswerPerSliceInductionData params strategy eps delta gamma restrictionPkg k)
    (answerSelf :
      AnswerSelfImprovementData params strategy eps delta gamma k restrictionPkg
        answerInduction) :
    SelfImprovementData params strategy eps delta gamma k
      (SliceRestrictionData.ofAnswer params strategy eps delta gamma restrictionPkg)
      (PerSliceInductionData.ofAnswer params strategy eps delta gamma k
        restrictionPkg answerInduction) where
  sliceProj := answerSelf.sliceProj
  sliceWitness := answerSelf.sliceWitness
  completeness := answerSelf.completeness
  pointConsistency := answerSelf.pointConsistency
  strongSelfConsistency := answerSelf.strongSelfConsistency
  selfCloseness := answerSelf.selfCloseness
  bounded := answerSelf.bounded
  dominatesAveragePointOperator := answerSelf.dominatesAveragePointOperator

/-- View self-improvement data over the answer-forgotten slice interface
as answer-valued self-improvement data.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551`.  This is the
reverse bookkeeping conversion to `SelfImprovementData.ofAnswer`: the
answer-valued and ordinary restricted-slice interfaces have the same point
measurement, scalar error profile, projective slice measurements, and witness
operators after applying `SliceRestrictionData.ofAnswer` and
`PerSliceInductionData.ofAnswer`.  Thus a self-improvement record over
that answer-forgotten data can be read as the corresponding answer-valued record
without changing the mathematical estimates. -/
noncomputable def AnswerSelfImprovementData.ofSelfImprovementData
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (answerInduction :
      AnswerPerSliceInductionData params strategy eps delta gamma restrictionPkg k)
    (selfImprovement :
      SelfImprovementData params strategy eps delta gamma k
        (SliceRestrictionData.ofAnswer params strategy eps delta gamma restrictionPkg)
        (PerSliceInductionData.ofAnswer params strategy eps delta gamma k
          restrictionPkg answerInduction)) :
    AnswerSelfImprovementData params strategy eps delta gamma k restrictionPkg
      answerInduction where
  sliceProj := selfImprovement.sliceProj
  sliceWitness := selfImprovement.sliceWitness
  completeness := selfImprovement.completeness
  pointConsistency := selfImprovement.pointConsistency
  strongSelfConsistency := selfImprovement.strongSelfConsistency
  selfCloseness := selfImprovement.selfCloseness
  bounded := selfImprovement.bounded
  dominatesAveragePointOperator := selfImprovement.dominatesAveragePointOperator

/-- Lean-only universe-polymorphic form of
`AveragedPastingData.invokeLdPasting`.

This is the same mathematical invocation as the source-facing theorem below,
but with the universe used by the field model exposed for downstream role-register
constructions (the vendored form also exposes the universe of its carrier, which here is the
universe of `𝔓` and `K`, already arbitrary). -/
theorem AveragedPastingData.invokeLdPasting_general.{uF}
    (params : Parameters)
    [FieldModel.{uF} params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (k : ℕ)
    {restrictionPkg : SliceRestrictionData params strategy eps delta gamma}
    {inductionPkg :
      PerSliceInductionData params strategy eps delta gamma restrictionPkg k}
    {selfPkg :
      SelfImprovementData params strategy eps delta gamma k restrictionPkg inductionPkg}
    (pkg : AveragedPastingData params strategy eps delta gamma k selfPkg)
    (hgood : strategy.IsGood eps delta gamma)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : Measurement (MIPStarRE.LDT.Polynomial params.next) 𝔓,
      LdPastingInInductionSectionConclusion params strategy selfPkg.family H
        eps delta gamma pkg.kappa pkg.zeta k :=
  ldPastingInInductionSection params strategy eps delta gamma pkg.kappa pkg.zeta
    hgood selfPkg.family pkg.complete pkg.consistent pkg.selfConsistent pkg.bounded k hk

/-- Apply the unrestricted induction-section pasting theorem to averaged
pasting input.

Paper origin: `references/ldt-paper/inductive_step.tex:528-551`, where the
averaged slice family is passed directly to
`\label{thm:ld-pasting-in-induction-section}`.

This uses the source-facing theorem `ldPastingInInductionSection`, not the
restricted nontrivial-regime theorem.  Consequently the successor construction does
not require the auxiliary proof-reduction hypotheses `0 < d` or `1 ≤ k`. -/
theorem AveragedPastingData.invokeLdPasting
    (params : Parameters)
    [FieldModel.{0} params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (k : ℕ)
    {restrictionPkg : SliceRestrictionData params strategy eps delta gamma}
    {inductionPkg :
      PerSliceInductionData params strategy eps delta gamma restrictionPkg k}
    {selfPkg :
      SelfImprovementData params strategy eps delta gamma k restrictionPkg inductionPkg}
    (pkg : AveragedPastingData params strategy eps delta gamma k selfPkg)
    (hgood : strategy.IsGood eps delta gamma)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : Measurement (MIPStarRE.LDT.Polynomial params.next) 𝔓,
      LdPastingInInductionSectionConclusion params strategy selfPkg.family H
        eps delta gamma pkg.kappa pkg.zeta k :=
  AveragedPastingData.invokeLdPasting_general params strategy eps delta gamma k pkg hgood hk

/-- Compose the four paper-faithful induction-step inputs
`restrict → induct → self-improve → paste` into the main-induction conclusion in
one higher dimension.

The construction applies the unrestricted induction-section pasting theorem
through `AveragedPastingData.invokeLdPasting_general`, so its stated hypotheses are
only the paper stage data and the large-`k` condition. The point `_fieldPoint` of a type in the
universe `uF` is the vendored device that fixes the universe of the field model. -/
theorem mainInductionFromStageData.{uF}
    {_fieldUniverse : Type uF}
    (_fieldPoint : _fieldUniverse)
    (params : Parameters)
    [FieldModel.{uF} params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hrestrict : SliceRestrictionData params strategy eps delta gamma)
    (hinduction : PerSliceInductionData params strategy eps delta gamma hrestrict k)
    (hself : SelfImprovementData params strategy eps delta gamma k hrestrict hinduction)
    (hpaste : AveragedPastingData params strategy eps delta gamma k hself)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : Measurement (MIPStarRE.LDT.Polynomial params.next) 𝔓,
      strategy.state.ConsRel (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next H.toSubMeas)
        (mainInductionError params.next k eps delta gamma) :=
  let ⟨H, hH⟩ :=
    AveragedPastingData.invokeLdPasting_general params strategy eps delta gamma k hpaste hgood hk
  mainInductionOfWitness params.next strategy eps delta gamma k
    ⟨ldPastingInInductionError params k eps delta gamma hpaste.kappa hpaste.zeta, H,
      hH.pointConsistency, hpaste.error_le⟩

end MIPRE.LIDT.Co.MainInductionStep

end

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
MainInductionStep/Theorems/AvgSliceErrors/Successor.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.MainInductionStep.Theorems.AvgSliceErrors.Core
public import MIPRE.Background.LIDT.Co.MainInductionStep.Theorems.SelfImprovementAssembly.AnswerSlice

@[expose] public section

/-!
# Section 6 — Averaged Slice Error Bounds: Successor Outputs

The recursive answer-valued slice measurements of the successor step, the self-improvement
outputs on those slices, and the comparison of the self-improvement error `ζ` with the
next-stage induction parameter `ν`. This is the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/MainInductionStep/Theorems/AvgSliceErrors/Successor.lean`
in the port of `planning/c6b-plan.md` (milestone M12, section "Port conventions").

## Translation

A strategy is a `SymStrat params.next 𝔓 K` or an `AnswerSymStrat params.next 𝔓 K`
(`Co/Test/StrategyCore.lean`), whose state is the symmetric model `strategy.state : SymModel 𝔓 K`;
`Polynomial params` is `MIPStarRE.LDT.Polynomial params`, `MIPStarRE.Quantum.Op ι` is `𝔓`,
`Error` is `ℝ`, `H.toSubMeas.liftLeft` is `H.toSubMeas.liftLeft strategy.state`,
`leftPlacedSubMeas (ιB := ι)` is `strategy.state.leftPlacedSubMeas` (and `rightPlacedSubMeas`),
and the relations (`ConsRel`, `BipartiteSSCRel`, `SDDRel`, `CompletenessAtLeast`) are read on
`strategy.state`. The error functions (`mainInductionError`, `mainInductionNu`,
`selfImprovementInInductionError`, `sliceConditioningLoss`) and `dq_ratio_le_one` are the
vendored classical declarations, reached through explicit `open` lists. No vendored statement
here has a swap, density or normalization hypothesis, so none is dropped. The vendored file-wide
`respectTransparency false` is not needed: the file sets no option.

## Threaded hypotheses

`answerSuccessorRecursiveSliceMeasurements_ofMainInductionHypothesis` applies Co
`answerSuccessorRestrictedSliceConclusions`, which takes the model hypotheses
`hS : strategy.state.toBipartite.IsFinitePair` and
`hA : NoAbelianProj strategy.state.toBipartite.opsA` of the predecessor
`AnswerMainInductionHypothesis`; so it takes `hS hA` right after `strategy`.
`answerSuccessorSelfImprovementOutputs_ofMainInductionHypothesis` also runs
`selfImprovementInInductionSection_of_axisParallel_selfConsistency` (Co
`SelfImprovementAssembly/Core`) on each slice carrier, so it takes `hS hA` and
`hd : 1 ≤ params.d` right after `strategy`. The slice carrier
`answerSelfImprovementCarrier params (xRestrictedAnswerSymStratOfAnswer params strategy x)` has the
ambient state by definition, so `hS` and `hA` pass to it unchanged; `hd` is a hypothesis on
`params`. The universe binder of the induction hypothesis is
`AnswerMainInductionHypothesis.{uF, uP, uK}`, with `𝔓 : Type uP` and `K : Type uK`, where the
vendored one is `.{uF, uι}`. The two `ζ ≤ ν` lemmas take no new hypothesis.

## Proofs that differ from the vendored ones

- In `answerSuccessorSelfImprovementOutputs_ofMainInductionHypothesis` the slice carrier's
  state, point measurement, failure probabilities and averaged point operator are those of the
  answer slice and of the ambient carrier by definitional equality, so the six output fields, the
  carrier's goodness (`restrictedGood`'s `axisParallelTest` and `selfConsistencyTest`) and its
  point consistency (`hpoint x`) are passed directly, with no `simpa` and no
  `averagedPoint_eq_of_pointMeasurement_eq` detour, and the slice outputs are chosen with
  `choose` rather than through `Classical.choose_spec`.
- The two `ζ ≤ ν` lemmas, which the vendored file proves twice by the same `calc`, share the
  private theorem `selfImprovementInInductionError_le_mainInductionNu_of_nonneg`, which takes the
  nonnegativity of `eps`, `delta`, `gamma` and `3 ≤ k² · m_next` in place of the strategy, and
  proves the comparison by `mul_le_mul_of_nonneg_left`/`_right` steps and one `linarith` for the
  coefficient, given the product `m_next · 3 ≤ m_next · (k² · m_next)`.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/inductive_step.tex`
- `blueprint/src/chapter/ch10_induction.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.MainInductionStep

open MIPStarRE.LDT (Parameters FieldModel Point Fq uniformDistribution avgOver)
open MIPStarRE.LDT.MainInductionStep (mainInductionError mainInductionNu
  selfImprovementInInductionError sliceConditioningLoss dq_ratio_le_one)
open MIPRE.LIDT.Co (SymStrat AnswerSymStrat)

universe uF uP uK

variable {𝔓 : Type uP} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type uK} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Extract the recursive answer-valued slice measurements and their averaged
main-induction error bound.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`.  After the
restricted-probabilities theorem and the predecessor answer-valued induction
hypothesis are applied to the restricted slices, this theorem packages the
resulting measurements `G^x` and proves the displayed bound
`\mathbb E_x \sigma_x \leq \sigma`.

**Lean-only:** This is an internal construction theorem for the simultaneous
answer-valued successor route tracked in issue #1507; it does not add a
predecessor conclusion as an assumption to any source-facing theorem.
Discharge: proved here from the restricted-probabilities theorem and the
answer-valued predecessor induction hypothesis. The model hypotheses `hS hA` are those the
predecessor hypothesis requires of each slice (module docstring). -/
theorem answerSuccessorRecursiveSliceMeasurements_ofMainInductionHypothesis
    (params : Parameters)
    [FieldModel.{uF} params.q]
    (strategy : AnswerSymStrat params.next 𝔓 K)
    (hS : strategy.state.toBipartite.IsFinitePair)
    (hA : NoAbelianProj strategy.state.toBipartite.opsA)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hinduction : AnswerMainInductionHypothesis.{uF, uP, uK} params)
    (hk_next : 400 * params.next.m * params.next.d ≤ k)
    (hsmall : mainInductionError params.next k eps delta gamma < 1) :
    ∃ profile : AnswerSuccessorRestrictedFailureProfile params strategy,
      ∃ sliceError : Fq params → ℝ,
        ∃ sliceMeasurement : Fq params → Measurement (MIPStarRE.LDT.Polynomial params) 𝔓,
          averageAnswerSuccessorRestrictedAxisParallelError params profile ≤
              sliceConditioningLoss params * eps ∧
            averageAnswerSuccessorRestrictedSelfConsistencyError params profile ≤ delta ∧
            averageAnswerSuccessorRestrictedDiagonalError params profile ≤
              sliceConditioningLoss params * gamma ∧
            (∀ x,
              strategy.state.ConsRel (uniformDistribution (Point params))
                (IdxProjMeas.toIdxSubMeas
                  (xRestrictedAnswerSymStratOfAnswer params strategy x).pointMeasurement)
                (polynomialEvaluationFamily params (sliceMeasurement x).toSubMeas)
                (sliceError x)) ∧
            (∀ x,
              sliceError x ≤
                mainInductionError params k
                  (profile.axisParallel x)
                  (profile.selfConsistency x)
                  (profile.diagonal x)) ∧
            avgOver (uniformDistribution (Fq params)) sliceError ≤
              ((params.m : ℝ) ^ (2 : ℕ)) *
                (mainInductionNu params.next k eps delta gamma +
                  Real.exp (-((k : ℝ) / (80000 * ((params.m : ℝ) ^ (2 : ℕ)))))) := by
  obtain ⟨profile, haxis, hself, hdiag, hconclusion⟩ :=
    answerSuccessorRestrictedSliceConclusions
      params strategy hS hA eps delta gamma k hgood hinduction hk_next hsmall
  choose sliceMeasurement hpoint using hconclusion
  exact ⟨profile, fun x => mainInductionError params k (profile.axisParallel x)
      (profile.selfConsistency x) (profile.diagonal x), sliceMeasurement,
    haxis, hself, hdiag, hpoint, fun _ => le_rfl,
    average_answerSuccessorSliceMainInductionError_le
      params strategy eps delta gamma k hgood profile haxis hself hdiag⟩

/-- Apply self-improvement to the recursive answer-valued successor slices.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551`.  Starting from
the recursive answer-valued slice measurements supplied by the predecessor
induction hypothesis, this theorem constructs the projective slice
submeasurements `\widehat G^x` and witnesses `Z^x`, proves their four
self-improvement outputs, and keeps the averaged `\zeta_x` and `\sigma_x`
bounds available.

**Lean-only:** The ordinary carrier appears only in the domination field, where
its point measurement is the same last-coordinate restriction of the ambient
answer-valued point measurement.  The proof invokes only the
axis-parallel/self-consistency form of self-improvement, and therefore does not
claim that the carrier's dummy diagonal measurement is a good diagonal
realization of the answer-valued strategy.  This internal construction is
tracked in issue #1507.  Discharge: proved here from the recursive slice
measurements and the formal self-improvement theorem. The hypotheses `hS hA hd` are those of
the predecessor hypothesis and of the ported self-improvement theorem (module docstring). -/
theorem answerSuccessorSelfImprovementOutputs_ofMainInductionHypothesis
    (params : Parameters)
    [FieldModel.{uF} params.q]
    (strategy : AnswerSymStrat params.next 𝔓 K)
    (hS : strategy.state.toBipartite.IsFinitePair)
    (hA : NoAbelianProj strategy.state.toBipartite.opsA)
    (hd : 1 ≤ params.d)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hinduction : AnswerMainInductionHypothesis.{uF, uP, uK} params)
    (hk_next : 400 * params.next.m * params.next.d ≤ k)
    (hsmall : mainInductionError params.next k eps delta gamma < 1) :
    ∃ profile : AnswerSuccessorRestrictedFailureProfile params strategy,
      ∃ sliceError : Fq params → ℝ,
        ∃ sliceMeasurement : Fq params → Measurement (MIPStarRE.LDT.Polynomial params) 𝔓,
          ∃ sliceProj : Fq params → ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝔓,
            ∃ sliceWitness : Fq params → 𝔓,
              averageAnswerSuccessorRestrictedAxisParallelError params profile ≤
                  sliceConditioningLoss params * eps ∧
                averageAnswerSuccessorRestrictedSelfConsistencyError params profile ≤ delta ∧
                averageAnswerSuccessorRestrictedDiagonalError params profile ≤
                  sliceConditioningLoss params * gamma ∧
                (∀ x,
                  strategy.state.ConsRel (uniformDistribution (Point params))
                    (IdxProjMeas.toIdxSubMeas
                      (xRestrictedAnswerSymStratOfAnswer params strategy x).pointMeasurement)
                    (polynomialEvaluationFamily params (sliceMeasurement x).toSubMeas)
                    (sliceError x)) ∧
                (∀ x,
                  sliceError x ≤
                    mainInductionError params k
                      (profile.axisParallel x)
                      (profile.selfConsistency x)
                      (profile.diagonal x)) ∧
                avgOver (uniformDistribution (Fq params)) sliceError ≤
                  ((params.m : ℝ) ^ (2 : ℕ)) *
                    (mainInductionNu params.next k eps delta gamma +
                      Real.exp (-((k : ℝ) / (80000 * ((params.m : ℝ) ^ (2 : ℕ)))))) ∧
                avgOver (uniformDistribution (Fq params))
                    (fun x =>
                      selfImprovementInInductionError params
                        (profile.axisParallel x)
                        (profile.selfConsistency x)
                        (profile.diagonal x)) ≤
                  selfImprovementInInductionError params.next eps delta gamma ∧
                (∀ x,
                  strategy.state.CompletenessAtLeast
                    ((sliceProj x).toSubMeas.liftLeft strategy.state)
                    ((1 - sliceError x) -
                      selfImprovementInInductionError params
                        (profile.axisParallel x)
                        (profile.selfConsistency x)
                        (profile.diagonal x))) ∧
                (∀ x,
                  strategy.state.ConsRel (uniformDistribution (Point params))
                    (IdxProjMeas.toIdxSubMeas
                      (xRestrictedAnswerSymStratOfAnswer params strategy x).pointMeasurement)
                    (polynomialEvaluationFamily params (sliceProj x).toSubMeas)
                    (selfImprovementInInductionError params
                      (profile.axisParallel x)
                      (profile.selfConsistency x)
                      (profile.diagonal x))) ∧
                (∀ x,
                  strategy.state.BipartiteSSCRel (uniformDistribution Unit)
                    (constSubMeasFamily (sliceProj x).toSubMeas)
                    (selfImprovementInInductionError params
                      (profile.axisParallel x)
                      (profile.selfConsistency x)
                      (profile.diagonal x))) ∧
                (∀ x,
                  strategy.state.SDDRel (uniformDistribution Unit)
                    (constSubMeasFamily (strategy.state.leftPlacedSubMeas (sliceProj x).toSubMeas))
                    (constSubMeasFamily
                      (strategy.state.rightPlacedSubMeas (sliceProj x).toSubMeas))
                    (selfImprovementInInductionError params
                      (profile.axisParallel x)
                      (profile.selfConsistency x)
                      (profile.diagonal x))) ∧
                (∀ x,
                  tensorFailureExpectation strategy.state (sliceWitness x) (sliceProj x).toSubMeas
                    ≤ selfImprovementInInductionError params
                      (profile.axisParallel x)
                      (profile.selfConsistency x)
                      (profile.diagonal x)) ∧
                (∀ x, ∀ h : MIPStarRE.LDT.Polynomial params,
                  IdxPolyFamily.averagedSlicePointEvaluationOperator
                    (answerSelfImprovementCarrier params.next strategy) x h ≤ sliceWitness x) := by
  obtain ⟨profile, sliceError, sliceMeasurement, haxis, hself, hdiag, hpoint, herror,
      havgSigma⟩ :=
    answerSuccessorRecursiveSliceMeasurements_ofMainInductionHypothesis
      params strategy hS hA eps delta gamma k hgood hinduction hk_next hsmall
  have hslice := fun x =>
    selfImprovementInInductionSection_of_axisParallel_selfConsistency params
      (answerSelfImprovementCarrier params (xRestrictedAnswerSymStratOfAnswer params strategy x))
      hS hA hd
      (profile.axisParallel x) (profile.selfConsistency x) (profile.diagonal x) (sliceError x)
      (profile.restrictedGood x).axisParallelTest (profile.restrictedGood x).selfConsistencyTest
      (sliceMeasurement x) (hpoint x)
  choose sliceProj sliceWitness hH using hslice
  exact ⟨profile, sliceError, sliceMeasurement, sliceProj, sliceWitness,
    haxis, hself, hdiag, hpoint, herror, havgSigma,
    average_answerSuccessorSliceSelfImprovementError_le
      params strategy eps delta gamma hgood profile haxis hself,
    fun x => (hH x).completeness, fun x => (hH x).pointConsistency,
    fun x => (hH x).strongSelfConsistency, fun x => (hH x).selfCloseness,
    fun x => (hH x).bounded, fun x => (hH x).dominatesAveragePointOperator⟩

/-- The scalar core of the two `ζ ≤ ν` comparisons: with `eps`, `delta`, `gamma` nonnegative,
`eps, delta ≤ 1`, `d ≤ q` and `3 ≤ k² · m_next`, the self-improvement error of the next stage is
at most its induction parameter `ν`. -/
private theorem selfImprovementInInductionError_le_mainInductionNu_of_nonneg
    (params : Parameters) {eps delta gamma : ℝ} {k : ℕ}
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta) (hgamma : 0 ≤ gamma)
    (heps_le_one : eps ≤ 1) (hdelta_le_one : delta ≤ 1)
    (hdq_le_q : params.d ≤ params.q)
    (hthree : (3 : ℝ) ≤ ((k : ℝ) ^ (2 : ℕ)) * (params.next.m : ℝ)) :
    selfImprovementInInductionError params.next eps delta gamma ≤
      mainInductionNu params.next k eps delta gamma := by
  have hratio : (0 : ℝ) ≤ (params.d : ℝ) / (params.q : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hexp : (1 / (1024 : ℝ)) ≤ 1 / (32 : ℝ) := by norm_num
  have hexp0 : (0 : ℝ) ≤ 1 / (1024 : ℝ) := by norm_num
  have ha : Real.rpow eps (1 / (32 : ℝ)) ≤ Real.rpow eps (1 / (1024 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge' heps heps_le_one hexp0 hexp
  have hb : Real.rpow delta (1 / (32 : ℝ)) ≤ Real.rpow delta (1 / (1024 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge' hdelta hdelta_le_one hexp0 hexp
  have hr : Real.rpow ((params.d : ℝ) / (params.q : ℝ)) (1 / (32 : ℝ)) ≤
      Real.rpow ((params.d : ℝ) / (params.q : ℝ)) (1 / (1024 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge' hratio (dq_ratio_le_one params hdq_le_q) hexp0 hexp
  have ha0 : 0 ≤ Real.rpow eps (1 / (1024 : ℝ)) := Real.rpow_nonneg heps _
  have hb0 : 0 ≤ Real.rpow delta (1 / (1024 : ℝ)) := Real.rpow_nonneg hdelta _
  have hc0 : 0 ≤ Real.rpow gamma (1 / (1024 : ℝ)) := Real.rpow_nonneg hgamma _
  have hr0 : 0 ≤ Real.rpow ((params.d : ℝ) / (params.q : ℝ)) (1 / (1024 : ℝ)) :=
    Real.rpow_nonneg hratio _
  have hm : (0 : ℝ) ≤ (params.next.m : ℝ) := Nat.cast_nonneg _
  have hcoef : 3000 * (params.next.m : ℝ) ≤
      1000 * ((k : ℝ) ^ (2 : ℕ)) * ((params.next.m : ℝ) ^ (2 : ℕ)) := by
    linarith [mul_le_mul_of_nonneg_left hthree hm]
  change 3000 * (params.next.m : ℝ) *
      (Real.rpow eps (1 / (32 : ℝ)) + Real.rpow delta (1 / (32 : ℝ)) +
        Real.rpow ((params.d : ℝ) / (params.q : ℝ)) (1 / (32 : ℝ))) ≤
    1000 * ((k : ℝ) ^ (2 : ℕ)) * ((params.next.m : ℝ) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : ℝ)) + Real.rpow delta (1 / (1024 : ℝ)) +
        Real.rpow gamma (1 / (1024 : ℝ)) +
        Real.rpow ((params.d : ℝ) / (params.q : ℝ)) (1 / (1024 : ℝ)))
  calc 3000 * (params.next.m : ℝ) *
        (Real.rpow eps (1 / (32 : ℝ)) + Real.rpow delta (1 / (32 : ℝ)) +
          Real.rpow ((params.d : ℝ) / (params.q : ℝ)) (1 / (32 : ℝ)))
      ≤ 3000 * (params.next.m : ℝ) *
        (Real.rpow eps (1 / (1024 : ℝ)) + Real.rpow delta (1 / (1024 : ℝ)) +
          Real.rpow ((params.d : ℝ) / (params.q : ℝ)) (1 / (1024 : ℝ))) :=
        mul_le_mul_of_nonneg_left (add_le_add (add_le_add ha hb) hr) (by positivity)
    _ ≤ 1000 * ((k : ℝ) ^ (2 : ℕ)) * ((params.next.m : ℝ) ^ (2 : ℕ)) *
        (Real.rpow eps (1 / (1024 : ℝ)) + Real.rpow delta (1 / (1024 : ℝ)) +
          Real.rpow ((params.d : ℝ) / (params.q : ℝ)) (1 / (1024 : ℝ))) :=
        mul_le_mul_of_nonneg_right hcoef (add_nonneg (add_nonneg ha0 hb0) hr0)
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- Paper's `\eqref{eq:zeta-smaller-than-nu}`: under the small-parameter
hypotheses, the averaged self-improvement interface error `\zeta` is bounded by
the next-stage induction parameter `\nu`. -/
lemma selfImprovementInInductionError_le_mainInductionNu
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1)
    (heps_le_one : eps ≤ 1) (hdelta_le_one : delta ≤ 1)
    (hdq_le_q : params.d ≤ params.q) :
    selfImprovementInInductionError params.next eps delta gamma ≤
      mainInductionNu params.next k eps delta gamma :=
  selfImprovementInInductionError_le_mainInductionNu_of_nonneg params
    (eps_nonneg_of_isGood params.next strategy hgood)
    (delta_nonneg_of_isGood params.next strategy hgood)
    (gamma_nonneg_of_isGood params.next strategy hgood)
    heps_le_one hdelta_le_one hdq_le_q
    (three_le_k_sq_mul_next_m_of_hsmall params strategy hgood hsmall)

/-- Answer-valued analogue of
`selfImprovementInInductionError_le_mainInductionNu`.

This is the scalar part of the successor proof for an ambient answer-valued
strategy.  It uses only the answer-valued goodness bounds and does not replace
the answer-valued diagonal measurement by an ordinary one. -/
lemma answer_selfImprovementInInductionError_le_mainInductionNu
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1)
    (heps_le_one : eps ≤ 1) (hdelta_le_one : delta ≤ 1)
    (hdq_le_q : params.d ≤ params.q) :
    selfImprovementInInductionError params.next eps delta gamma ≤
      mainInductionNu params.next k eps delta gamma :=
  selfImprovementInInductionError_le_mainInductionNu_of_nonneg params
    (answer_eps_nonneg_of_isGood params.next strategy hgood)
    (answer_delta_nonneg_of_isGood params.next strategy hgood)
    (answer_gamma_nonneg_of_isGood params.next strategy hgood)
    heps_le_one hdelta_le_one hdq_le_q
    (answer_three_le_k_sq_mul_next_m_of_hsmall params strategy hgood hsmall)

end MIPRE.LIDT.Co.MainInductionStep

end

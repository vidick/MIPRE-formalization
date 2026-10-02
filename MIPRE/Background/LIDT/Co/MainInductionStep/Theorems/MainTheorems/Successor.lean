/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
MainInductionStep/Theorems/MainTheorems/Successor.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.MainInductionStep.Theorems.MainTheorems.Base

@[expose] public section

/-!
# Section 6 — Main Induction Theorems: Successor and Public Interfaces

The answer-valued induction theorem, the successor reductions, and the corrected large-`k`
main-induction interface `mainInduction`. This is the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/MainInductionStep/Theorems/MainTheorems/Successor.lean` in
the port of `planning/c6b-plan.md` (milestone M12, section "Port conventions").

## Translation

A strategy is a `SymStrat params 𝔓 K` (or `SymStrat params.next 𝔓 K`, or an
`AnswerSymStrat`; `Co/Test/StrategyCore.lean`), whose state is the symmetric model
`strategy.state : SymModel 𝔓 K`; `Polynomial params` is `MIPStarRE.LDT.Polynomial params`,
measurements live in the local algebra `𝔓` (the vendored `Op ι`), errors are real numbers (the
vendored `Error := ℝ`), and `ConsRel` is read on `strategy.state`. The error function
`mainInductionError` and the scalar lemmas `one_le_k_of_mainInductionError_lt_one` and
`mainInductionSuccessorBound_pred` are the vendored classical declarations, reached through
explicit `open` lists. The vendored explicit universe instantiations of the stage records
(`AnswerSliceRestrictionData.{uι, uF}` and its siblings) are left to unification, as in Co
`StageDataConstructors`; the file declares `universe uP uK` with `𝔓 : Type uP` and `K : Type uK`,
and the induction hypotheses are `AnswerMainInductionHypothesis.{uF, uP, uK}` where the vendored
ones are `.{uF, uι}`. `answerMainInduction.{uF, vP, vK}` proves the hypothesis in any universes
`vP`, `vK` of the local algebra and the Hilbert space, as the vendored `.{uF, vι}` does in any
universe of the carrier. The vendored file-wide `respectTransparency false` is not needed: the
file sets no option.

## Threaded hypotheses

The successor step runs Co `answerMainInductionSuccessorNext_ofRecursiveHypothesisAndAnswerPasting`
and Co `AnswerSelfImprovementData.ofAnswerCarrier`, which take the model hypotheses
`hS : strategy.state.toBipartite.IsFinitePair` and
`hA : NoAbelianProj strategy.state.toBipartite.opsA` of the ported orthonormalization and
`hd : 1 ≤ params.d` of the ported self-improvement theorem, and Co
`AnswerPerSliceInductionData.ofMainInductionHypothesis`, which takes `hS hA`. So:
- `answerMainInduction` takes `hd : 1 ≤ params.d` after the field model. Its conclusion,
  `AnswerMainInductionHypothesis` (Co `MainInductionStep/Statements.lean`), already quantifies only
  over finite pairs without abelian projections, so `hS hA` come from it; `hd` is a hypothesis on
  `params`, constant along the induction, which changes only `m` (`Parameters.next` keeps `d`), so
  the strong induction carries it to the predecessor.
- `mainInductionSuccessorNext_ofAnswerCarrier`,
  `mainInductionSuccessorNext_ofAnswerCarrierFromSuccessorBound`,
  `mainInductionSuccessorNext_ofSmallErrorConstruction`, `mainInductionSuccessorNext`,
  `mainInductionSuccessor` and `mainInduction` take `hS hA hd` right after `strategy`, as Co
  `SelfImprovement.selfImprovement` and Co `PastingAssembly/Successor` place them.
The base case and the large-error branches (`MainTheorems/Base.lean`) take none of them, so
`mainInduction` does not use them when `m = 1`. No vendored statement here has a swap, density or
normalization hypothesis, so none is dropped.

## Proofs that differ from the vendored ones

- `answerMainInduction` runs the strong induction with `Nat.strong_induction_on` over a
  predicate that also assumes `1 ≤ params.d`; the predecessor's field model is transported along
  `pred.next.q = pred.q`, as in the vendored proof.
- `mainInductionSuccessorNext_ofAnswerCarrier` is a term, the vendored `let`s with their explicit
  universe instantiations being inlined.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/inductive_step.tex`
- `docs/paper-gaps/issue-906-main-formal-k-bound.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.MainInductionStep

open MIPStarRE.LDT (Parameters FieldModel Point Fq uniformDistribution)
open MIPStarRE.LDT.MainInductionStep (mainInductionError one_le_k_of_mainInductionError_lt_one
  mainInductionSuccessorBound_pred)
open MIPRE.LIDT.Co (SymStrat AnswerSymStrat Measurement IdxProjMeas polynomialEvaluationFamily)

universe uP uK

variable {𝔓 : Type uP} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type uK} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Answer-valued corrected large-`k` induction theorem.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`, as an internal
simultaneous-induction strengthening used to prove the ordinary main induction.

This theorem is not advertised as `thm:main-induction`.  It records the
answer-valued induction statement needed for the recursive restricted slices.
The proof is a genuine strong induction on the dimension.  In the successor
branch the predecessor hypothesis is applied to the restricted answer-valued
slices, and the checked successor reduction then carries the result through
the slice restriction, self-improvement, averaging, and scalar estimates.

The degree hypothesis `hd : 1 ≤ params.d` is the one of the ported
self-improvement theorem; it does not change along the induction, which
changes only the dimension. -/
theorem answerMainInduction.{uF, vP, vK}
    (params : Parameters)
    [FieldModel.{uF} params.q]
    (hd : 1 ≤ params.d) :
    AnswerMainInductionHypothesis.{uF, vP, vK} params := by
  let P : ℕ → Prop := fun n =>
    ∀ (params : Parameters), params.m = n → 1 ≤ params.d →
      ∀ instField : FieldModel.{uF} params.q,
        @AnswerMainInductionHypothesis.{uF, vP, vK} params instField
  have hAll : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih params hm hd instField 𝔓 _ _ _ K _ _ _ strategy eps delta gamma k hS hA hgood
      _hk_pos hk
    by_cases hm1 : params.m = 1
    · exact answerMainInductionBaseCase params strategy eps delta gamma k hm1 hgood
    · by_cases hsmall : mainInductionError params k eps delta gamma < 1
      · rcases params.successorDecompositionOfNeOne hm1 with ⟨pred, hnext⟩
        have hq : pred.q = params.q := (congrArg Parameters.q hnext :)
        let : FieldModel.{uF} pred.q := hq.symm ▸ instField
        have hpred_lt : pred.m < n := by
          rw [← hm, ← hnext]
          exact Nat.lt_succ_self _
        have hd_pred : 1 ≤ pred.d := by
          rw [← hnext] at hd
          exact hd
        have hinduction : AnswerMainInductionHypothesis.{uF, vP, vK} pred :=
          ih pred.m hpred_lt pred rfl hd_pred inferInstance
        cases hnext
        exact
          answerMainInductionSuccessorNext_ofRecursiveHypothesisAndAnswerPasting
            pred strategy hS hA hd_pred eps delta gamma k hgood hinduction hk hsmall
      · exact answerMainInductionOfOneLeError params strategy eps delta gamma k
          (le_of_not_gt hsmall)
  exact hAll params.m params rfl hd inferInstance

/-- Internal successor assembly from the predecessor induction hypothesis,
using the answer-valued slice self-improvement construction.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`.

The self-improvement data are obtained directly from the answer-valued
restricted slices via `AnswerSelfImprovementData.ofAnswerCarrier`.  This is an
internal reduction for the successor proof of `thm:main-induction`, not a paper
theorem.  Its only recursive input is the predecessor answer-valued induction
hypothesis, which is supplied by the strong-induction theorem
`answerMainInduction`. -/
theorem mainInductionSuccessorNext_ofAnswerCarrier.{uF}
    (params : Parameters)
    [FieldModel.{uF} params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (hS : strategy.state.toBipartite.IsFinitePair)
    (hA : NoAbelianProj strategy.state.toBipartite.opsA)
    (hd : 1 ≤ params.d)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1)
    (hinduction : AnswerMainInductionHypothesis.{uF, uP, uK} params)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ G : Measurement (MIPStarRE.LDT.Polynomial params.next) 𝔓,
      strategy.state.ConsRel (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
        (mainInductionError params.next k eps delta gamma) :=
  let answerRestrict :=
    AnswerSliceRestrictionData.ofRestrictedProbabilities params strategy eps delta gamma
      (answerRestrictedProbabilities params strategy eps delta gamma hgood)
  let answerInduction :=
    AnswerPerSliceInductionData.ofMainInductionHypothesis params strategy hS hA eps delta gamma k
      answerRestrict hinduction
      (one_le_k_of_mainInductionError_lt_one params.next k eps delta gamma hsmall) hk
  let answerSelf :=
    AnswerSelfImprovementData.ofAnswerCarrier params strategy hS hA hd eps delta gamma k
      answerRestrict answerInduction
  let hrestrict := SliceRestrictionData.ofAnswer params strategy eps delta gamma answerRestrict
  let hinduction :=
    PerSliceInductionData.ofAnswer params strategy eps delta gamma k answerRestrict
      answerInduction
  let hself :=
    SelfImprovementData.ofAnswer params strategy eps delta gamma k answerRestrict
      answerInduction answerSelf
  mainInductionFromStageData (_fieldUniverse := ULift.{uF} PUnit) (ULift.up PUnit.unit)
    params strategy eps delta gamma k hgood hrestrict hinduction hself
    (assembleAveragedPastingDataOfSmallError params strategy eps delta gamma k hgood hsmall
      hrestrict hinduction hself hk) hk

/-- Internal successor assembly from the successor large-`k` hypothesis, using
the answer-valued slice self-improvement construction.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`.

This is an internal reduction for the successor proof of `thm:main-induction`,
not a paper theorem.  It replaces the predecessor large-`k` hypothesis in
`mainInductionSuccessorNext_ofAnswerCarrier` by the successor large-`k`
hypothesis through the elementary successor-to-predecessor bound. -/
theorem mainInductionSuccessorNext_ofAnswerCarrierFromSuccessorBound.{uF}
    (params : Parameters)
    [FieldModel.{uF} params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (hS : strategy.state.toBipartite.IsFinitePair)
    (hA : NoAbelianProj strategy.state.toBipartite.opsA)
    (hd : 1 ≤ params.d)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1)
    (hinduction : AnswerMainInductionHypothesis.{uF, uP, uK} params)
    (hk_next : 400 * params.next.m * params.next.d ≤ k) :
    ∃ G : Measurement (MIPStarRE.LDT.Polynomial params.next) 𝔓,
      strategy.state.ConsRel (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
        (mainInductionError params.next k eps delta gamma) :=
  mainInductionSuccessorNext_ofAnswerCarrier
    params strategy hS hA hd eps delta gamma k hgood hsmall hinduction
    (mainInductionSuccessorBound_pred params hk_next)

/-- Small-error construction for the native successor step of
`thm:main-induction`.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`, restricted to
the nontrivial regime
`mainInductionError params.next k eps delta gamma < 1`.

This theorem is the named construction for the nontrivial branch of the
successor proof.  Its public parameters are the successor strategy hypotheses,
the model and degree hypotheses `hS hA hd`, and the branch condition
`mainInductionError < 1`, so downstream users do not acquire
restricted-probability records, slice-induction data, self-improvement data,
pasting data, residual packages, or arbitrary implication hypotheses as
assumptions of the theorem.

The proof constructs the answer-valued restricted slice profile,
applies the recursive predecessor induction conclusion for each slice, assembles
the pasting input, and proves the scalar absorption estimates.  The
predecessor induction argument is the genuine strong-induction theorem
`answerMainInduction`; it is not a hypothesis of the ordinary successor theorem. -/
theorem mainInductionSuccessorNext_ofSmallErrorConstruction
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (hS : strategy.state.toBipartite.IsFinitePair)
    (hA : NoAbelianProj strategy.state.toBipartite.opsA)
    (hd : 1 ≤ params.d)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hk : 400 * params.next.m * params.next.d ≤ k)
    (hsmall : mainInductionError params.next k eps delta gamma < 1) :
    ∃ G : Measurement (MIPStarRE.LDT.Polynomial params.next) 𝔓,
      strategy.state.ConsRel (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
        (mainInductionError params.next k eps delta gamma) :=
  mainInductionSuccessorNext_ofAnswerCarrierFromSuccessorBound
    params strategy hS hA hd eps delta gamma k hgood hsmall
    (answerMainInduction params hd) hk

/-- Native successor step for `thm:main-induction`.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`, where the proof
passes from dimension `m` to dimension `m + 1`.

This is the native successor step for the corrected large-`k` Lean interface:
the ambient strategy already lives in dimension `params.next`, so no predecessor
compatibility record is introduced.  In the small-error regime it calls
`mainInductionSuccessorNext_ofSmallErrorConstruction`, whose recursive
predecessor conclusion is supplied by `answerMainInduction`; otherwise the
trivial large-error branch `mainInductionOfOneLeError` applies. -/
theorem mainInductionSuccessorNext
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (hS : strategy.state.toBipartite.IsFinitePair)
    (hA : NoAbelianProj strategy.state.toBipartite.opsA)
    (hd : 1 ≤ params.d)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hk : 400 * params.next.m * params.next.d ≤ k) :
    ∃ G : Measurement (MIPStarRE.LDT.Polynomial params.next) 𝔓,
      strategy.state.ConsRel (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
        (mainInductionError params.next k eps delta gamma) := by
  by_cases hsmall : mainInductionError params.next k eps delta gamma < 1
  · exact mainInductionSuccessorNext_ofSmallErrorConstruction
      params strategy hS hA hd eps delta gamma k hgood hk hsmall
  · exact mainInductionOfOneLeError params.next strategy eps delta gamma k
      (le_of_not_gt hsmall)

/-- Successor branch of `thm:main-induction`.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`, the induction
step after the restricted-probability estimates and the slice-wise recursive
calls have been set up.

This theorem is the parameter-decomposition form used by `mainInduction`.
Its assumptions are the corrected large-`k` hypotheses for
`thm:main-induction`, the model and degree hypotheses `hS hA hd`, and the branch
condition `params.m ≠ 1`.  The proof decomposes the non-base parameter bundle as
`pred.next` and then invokes the native successor-step theorem
`mainInductionSuccessorNext`. -/
theorem mainInductionSuccessor
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (hS : strategy.state.toBipartite.IsFinitePair)
    (hA : NoAbelianProj strategy.state.toBipartite.opsA)
    (hd : 1 ≤ params.d)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hk : 400 * params.m * params.d ≤ k)
    (hm1 : params.m ≠ 1) :
    ∃ G : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓,
      strategy.state.ConsRel (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas)
        (mainInductionError params k eps delta gamma) := by
  rcases params.successorDecompositionOfNeOne hm1 with ⟨pred, hnext⟩
  have hq : pred.q = params.q := (congrArg Parameters.q hnext :)
  let : FieldModel pred.q := hq.symm ▸ (inferInstance : FieldModel params.q)
  cases hnext
  exact mainInductionSuccessorNext pred strategy hS hA hd eps delta gamma k hgood hk

/-- Corrected large-`k` interface for `thm:main-induction`.

A good symmetric strategy whose model is a finite pair without abelian
projections in its first player's operators, with `1 ≤ d`, and an integer
`k ≥ 400 m d` produce a polynomial measurement consistent with the point
measurement at error `mainInductionError`.  The strengthening from the printed
`k ≥ m d` hypothesis in `references/ldt-paper/inductive_step.tex` is the
vendored statement correction (`docs/paper-gaps/issue-906-main-formal-k-bound.tex`
upstream).

The proof uses the base case `mainInductionBaseCase` and the corrected
large-`k` successor theorem `mainInductionSuccessor`.  In the small-error
successor branch the recursive predecessor calls are supplied by the genuine
strong-induction theorem `answerMainInduction`. -/
theorem mainInduction
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (hS : strategy.state.toBipartite.IsFinitePair)
    (hA : NoAbelianProj strategy.state.toBipartite.opsA)
    (hd : 1 ≤ params.d)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ G : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓,
      strategy.state.ConsRel (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas)
        (mainInductionError params k eps delta gamma) := by
  by_cases hm1 : params.m = 1
  · exact mainInductionBaseCase params strategy eps delta gamma k hm1 hgood
  · exact mainInductionSuccessor params strategy hS hA hd eps delta gamma k hgood hk hm1

end MIPRE.LIDT.Co.MainInductionStep

end

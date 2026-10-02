/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
GlobalVariance/Theorems/SelfConsistencyTransportSum.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.GlobalVariance.Theorems.SelfConsistencyTransport.PointLine

@[expose] public section

/-!
# Sum-form (cardinality-free) `2ε` axis-parallel consistency endpoints

The counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/GlobalVariance/Theorems/SelfConsistencyTransportSum.lean`
in the port of `planning/c6b-plan.md` (milestone M6, section "Port conventions"): the
polynomial-sum (unnormalized `∑_g`) analogues of the per-`g` `2ε` endpoints of
`SelfConsistencyTransport/PointLine.lean`. They keep the answer space at `Fq params` rather than
postprocessing to the per-`g` `Option Unit` event, and group polynomials by the common value
`g(u)` through the `cabApproxDelta` multiplier `if a = g s.1 then S.R ((G_g)^{1/2}) else 0`
(`cabApproxDelta_sum_from_sdd`). With the contraction `∑_{g : g(u) = a} G_g ≤ I` this gives `2ε`
for the whole polynomial sum, with no polynomial-cardinality loss: the steps 2 and 5 sum-level
inputs to `eq:equivalent-local-variance` (`references/ldt-paper/expansion.tex:317--321`).

The vendored swap of the two prover roles, `consRel_symm_of_density_fixed` applied to
`strategy.densityFixed`, is the model's theorem `SymModel.consRel_symm_of_density_fixed`, so no
swap hypothesis appears; the axis-parallel consistency hypothesis is the `axisParallelTest` field
of `IsGood` itself. The base-sample sum bound is a single application of
`cabApproxDelta_sum_from_sdd`, its two bridges being `S.rightTensor_mul_leftTensor_eq_opTensor`
after `liftLeft_lineAnswerMeasurement_outcome_at_g`, and `S.rightTensor_mul_rightTensor`.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/expansion.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.GlobalVariance

open MIPStarRE.LDT (Parameters FieldModel Fq AxisParallelTestSample avgOver uniformDistribution
  avgOver_congr avgOver_congr_on_support)
open MIPStarRE.LDT.GlobalVariance (AxisParallelLineQuestion axisParallelLineQuestionDistribution
  pointOnLine avgOver_axisParallelLineQuestionDistribution_to_axisParallelTestSample)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The point answers of the axis-parallel test, `s ↦ A^{s.1}`, as an indexed measurement. -/
noncomputable def axisParallelPointAnswerMeasurement
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K) :
    IdxMeas (AxisParallelTestSample params) (Fq params) 𝔓 :=
  fun s => (axisParallelPointAnswerFamily strategy s).toMeasurement
    (strategy.pointMeasurement s.1).total_eq_one

/-- The line answers of the axis-parallel test, evaluated at the base point, as an indexed
measurement. -/
noncomputable def axisParallelLineAnswerMeasurement
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K) :
    IdxMeas (AxisParallelTestSample params) (Fq params) 𝔓 :=
  fun s => (axisParallelLineAnswerFamily strategy s).toMeasurement
    (strategy.axisParallelMeasurement { base := s.1, direction := s.2 }).total_eq_one

/-- The lifted line-answer family outcome at value `a = g(s.1)` is the left placement of the
`lem:generalize-b` left operator at the incident question `(ℓ, s.1)` with
`ℓ = {base := s.1, direction := s.2}`.

This is the operator identity bridging the un-postprocessed `Fq params`-valued
line answer family to the per-`g` line operator used in
`weightedGeneralizeBLeftOperatorAtPolynomial`; it is `generalizeBLeftOutcome_base` after
collapsing the postprocessing to the event `a = g(s.1)`. -/
theorem liftLeft_lineAnswerMeasurement_outcome_at_g
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (g : MIPStarRE.LDT.Polynomial params)
    (s : AxisParallelTestSample params) :
    ((IdxSubMeas.liftLeft strategy.state
        (IdxMeas.toIdxSubMeas (axisParallelLineAnswerMeasurement params strategy))) s).outcome
        (g s.1) =
      strategy.state.L
        (generalizeBLeftOperatorAtPolynomial params strategy g
          ({ base := s.1, direction := s.2 }, s.1)) := by
  classical
  show strategy.state.L ((axisParallelLineAnswerFamily strategy s).outcome (g s.1)) = _
  rw [← generalizeBLeftOutcome_base params strategy g s]
  simp only [SubMeas.postprocess_outcome, ite_eq_left_iff, reduceCtorEq, imp_false, not_not,
    Finset.filter_eq', Finset.mem_univ, ite_true, Finset.sum_singleton]

/-- The lifted point-answer family outcome at value `a = g(s.1)` is the right placement of the
point-conditioned operator at the base point `s.1`. -/
theorem liftRight_pointAnswerMeasurement_outcome_at_g
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (g : MIPStarRE.LDT.Polynomial params)
    (s : AxisParallelTestSample params) :
    ((IdxSubMeas.liftRight strategy.state
        (IdxMeas.toIdxSubMeas (axisParallelPointAnswerMeasurement params strategy))) s).outcome
        (g s.1) =
      strategy.state.R (pointConditionedOutcomeOperatorAtPolynomial params strategy g s.1) :=
  rfl

/-- Sum-level base-sample form of the `2ε` axis-parallel consistency move,
oriented with the line event on the left register and the point event on the
right register.

This is the polynomial-sum version of
`axisParallelBaseEventApproximation_weighted_sample`: instead of fixing `g`
and postprocessing both sides to the `Option Unit` event `a = g(u)`, we keep
the full `Fq params` answer space and use the multiplier
`C s a g := if a = g s.1 then S.R ((G_g)^{1/2}) else 0` inside
`prop:cab-approx-delta`. The contraction `∀ s a, ∑_g (C s a g)† * (C s a g) ≤ I` is
`rightPolynomialWeightSqrt_grouped_contraction`, from the submeasurement
inequality `∑_{g : g(s.1) = a} G_g ≤ I`. Consequently the bound is `2ε` for
the polynomial sum, with no polynomial-cardinality loss. -/
theorem axisParallelBaseEventApproximation_weighted_sample_sum
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    (∑ g : MIPStarRE.LDT.Polynomial params,
      avgOver (uniformDistribution (AxisParallelTestSample params))
        (fun s =>
          let qu : AxisParallelLineQuestion params :=
            ({ base := s.1, direction := s.2 }, s.1)
          let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
            weightedPointConditionedRightOperatorAtPolynomial params strategy G g s.1
          strategy.state.ev (star D * D))) ≤
      2 * eps :=
  cabApproxDelta_sum_from_sdd params strategy.state
    (uniformDistribution (AxisParallelTestSample params)) (fun s => s.1)
    (fun s a => ((IdxSubMeas.liftLeft strategy.state
      (IdxMeas.toIdxSubMeas (axisParallelLineAnswerMeasurement params strategy))) s).outcome a)
    (fun s a => ((IdxSubMeas.liftRight strategy.state
      (IdxMeas.toIdxSubMeas (axisParallelPointAnswerMeasurement params strategy))) s).outcome a)
    (fun s g => weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g
      ({ base := s.1, direction := s.2 }, s.1))
    (fun s g => weightedPointConditionedRightOperatorAtPolynomial params strategy G g s.1)
    G (2 * eps)
    (Preliminaries.simeqToApprox strategy.state
      (uniformDistribution (AxisParallelTestSample params))
      (axisParallelLineAnswerMeasurement params strategy)
      (axisParallelPointAnswerMeasurement params strategy) eps
      (strategy.state.consRel_symm_of_density_fixed _ _ _ eps ⟨hgood.axisParallelTest⟩)
    ).leftRightSquaredDistanceBound
    (fun s g => by
      rw [liftLeft_lineAnswerMeasurement_outcome_at_g]
      exact strategy.state.rightTensor_mul_leftTensor_eq_opTensor _ _)
    (fun _ _ => strategy.state.rightTensor_mul_rightTensor _ _)

/-- Sum-level form of the weighted line-to-point approximation
(`expansion.tex:309--310`, paper step 5) on the
`axisParallelLineQuestionDistribution` distribution.

This is the polynomial-sum analogue of
`axisParallelPointLineConsistency_weighted_leftToRightLineQuestion`. After
reindexing the line-question sampling along its incident-pair structure (using
the rebasing covariance of the line operator), it reduces to the
sum-level base-sample bound `axisParallelBaseEventApproximation_weighted_sample_sum`. -/
theorem axisParallelPointLineConsistency_weighted_leftToRightLineQuestion_sum
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    (∑ g : MIPStarRE.LDT.Polynomial params,
      avgOver (axisParallelLineQuestionDistribution params)
        (fun qu =>
          let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
            weightedPointConditionedRightOperatorAtPolynomial params strategy G g qu.2
          strategy.state.ev (star D * D))) ≤
      2 * eps := by
  let F : MIPStarRE.LDT.Polynomial params → AxisParallelTestSample params → ℝ := fun g s =>
    let qu : AxisParallelLineQuestion params := ({ base := s.1, direction := s.2 }, s.1)
    let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
      weightedPointConditionedRightOperatorAtPolynomial params strategy G g s.1
    strategy.state.ev (star D * D)
  have hstep : ∀ g, avgOver (axisParallelLineQuestionDistribution params)
      (fun qu =>
        let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
          weightedPointConditionedRightOperatorAtPolynomial params strategy G g qu.2
        strategy.state.ev (star D * D)) =
      avgOver (axisParallelLineQuestionDistribution params)
        (fun qu => F g (qu.2, qu.1.direction)) := fun g => by
    apply avgOver_congr_on_support
    intro qu hqu
    have hline : pointOnLine (params := params) qu := by
      simpa [axisParallelLineQuestionDistribution] using hqu
    rcases qu with ⟨ℓ, u⟩
    rcases hline with ⟨t, ht⟩
    change ℓ.pointAt t = u at ht
    subst u
    dsimp only [F]
    rw [weightedGeneralizeBLeftOperatorAtPolynomial_rebaseAt_pointAt]
    rfl
  calc
    _ = ∑ g : MIPStarRE.LDT.Polynomial params,
          avgOver (uniformDistribution (AxisParallelTestSample params)) (F g) :=
        Finset.sum_congr rfl fun g _ => (hstep g).trans
          (avgOver_axisParallelLineQuestionDistribution_to_axisParallelTestSample params (F g))
    _ ≤ 2 * eps :=
        axisParallelBaseEventApproximation_weighted_sample_sum
          params strategy eps delta gamma hgood G

/-- Sum-level form of the reverse weighted point-to-line approximation
(`expansion.tex:306--307`, paper step 2) on the
`axisParallelLineQuestionDistribution` distribution.

This is the polynomial-sum analogue of
`axisParallelPointLineConsistency_weighted_rightToLeftLineQuestion`. Each
summand is unchanged after swapping the two endpoint operators, so this reduces
to `axisParallelPointLineConsistency_weighted_leftToRightLineQuestion_sum`. -/
theorem axisParallelPointLineConsistency_weighted_rightToLeftLineQuestion_sum
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    (∑ g : MIPStarRE.LDT.Polynomial params,
      avgOver (axisParallelLineQuestionDistribution params)
        (fun qu =>
          let D := weightedPointConditionedRightOperatorAtPolynomial params strategy G g qu.2 -
            weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
          strategy.state.ev (star D * D))) ≤
      2 * eps :=
  (Finset.sum_congr rfl fun g _ => avgOver_congr _ _ _ fun qu =>
      ev_adjoint_sub_swap strategy.state.toVecState
        (weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu)
        (weightedPointConditionedRightOperatorAtPolynomial params strategy G g qu.2)).trans_le
    (axisParallelPointLineConsistency_weighted_leftToRightLineQuestion_sum
      params strategy eps delta gamma hgood G)

end MIPRE.LIDT.Co.GlobalVariance

end

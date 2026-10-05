/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
MainInductionStep/Theorems/MainTheorems/Base.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPStarRE.LDT.Basic.LinePolynomialEmbedding
public import MIPRE.Background.LIDT.Co.MainInductionStep.Theorems.SelfImprovementAssembly.Core
public import MIPRE.Background.LIDT.Co.MainInductionStep.Theorems.InductionParameterBounds.Preliminaries
public import MIPRE.Background.LIDT.Co.MainInductionStep.Theorems.PastingAssembly.Successor
public import MIPRE.Background.LIDT.Co.MainInductionStep.Theorems.StageDataConstructors
public import MIPRE.Background.LIDT.Co.Pasting.Bernoulli.DegreeZero

@[expose] public section

/-!
# Section 6 — Main Induction Theorems: Base and Large-Error Branches

The base cases (`m = 1`) and the trivial large-error branches of the ordinary and answer-valued
main induction statements. This is the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/MainInductionStep/Theorems/MainTheorems/Base.lean` in the
port of `planning/c6b-plan.md` (milestone M12, section "Port conventions").

## Translation

A strategy is a `SymStrat params 𝔓 K` or an `AnswerSymStrat params 𝔓 K`
(`Co/Test/StrategyCore.lean`), whose state is the symmetric model `strategy.state : SymModel 𝔓 K`;
`Polynomial params` is `MIPStarRE.LDT.Polynomial params`, measurements live in the local algebra
`𝔓` (the vendored `Op ι`), errors are real numbers (the vendored `Error := ℝ`), and `ConsRel` is
read on `strategy.state`. The geometry of axis-parallel lines, `zeroPoint`,
`axisLinePolynomialToPolynomial` (the vendored `Basic/LinePolynomialEmbedding.lean`, classical
and imported, as it has no Co counterpart) and the scalar lemmas
`throughPoint_eq_zeroPoint_of_m_eq_one` and `min_eps_one_le_mainInductionError_of_m_eq_one` are
the vendored classical declarations, reached through explicit `open` lists. The vendored
file-wide `respectTransparency false` is not needed: the file sets no option.

## Dropped hypotheses

The vendored bounds of the axis-parallel failure probability and of the trivial witness's
consistency defect by `1` pass `strategy.isNormalized` to `bipartiteConsError_uniform_le_one`; here
that is the keystone's `strategy.state.bipartiteConsError_uniform_le_one`, with no normalization
argument (the vector state of a model is a unit vector). No statement takes a new hypothesis:
neither the base case nor the large-error branch orthonormalizes.

## Proofs that differ from the vendored ones

- The one-dimensional argument, which the vendored file writes out twice (for `SymStrat` and for
  `AnswerSymStrat`), is the private theorem `exists_polynomialMeasurement_consRel_of_m_eq_one`,
  stated for a point measurement and an axis-parallel measurement: the polynomial measurement is
  the canonical line's measurement read as a global polynomial, and its evaluation family is the
  sampled line family by covariance (`AxisParallelCovariantMeasurement.reparamInvariant`) and
  `throughPoint_eq_zeroPoint_of_m_eq_one`. Both base cases apply it.
- The nonnegativity of `ε`, `δ` and `γ` is `eps_nonneg_of_isGood` and its siblings
  (`Co/Test/StrategyFailures.lean`), which the vendored file proves inline.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/inductive_step.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.MainInductionStep

open MIPStarRE.LDT (Parameters FieldModel Point Fq uniformDistribution AxisParallelTestSample
  AxisParallelLine zeroPoint zeroCoord axisLinePolynomialToPolynomial
  axisLinePolynomialToPolynomial_apply)
open MIPStarRE.LDT.MainInductionStep (mainInductionError throughPoint_eq_zeroPoint_of_m_eq_one
  min_eps_one_le_mainInductionError_of_m_eq_one)
open MIPRE.LIDT.Co (SymStrat AnswerSymStrat SymModel SubMeas Measurement IdxProjMeas
  AxisParallelCovariantMeasurement axisParallelPointAnswerFamilyOf axisParallelLineAnswerFamilyOf
  postprocess evaluateAt polynomialEvaluationFamily eps_nonneg_of_isGood delta_nonneg_of_isGood
  gamma_nonneg_of_isGood answer_eps_nonneg_of_isGood answer_delta_nonneg_of_isGood
  answer_gamma_nonneg_of_isGood)

universe uP uK

variable {𝔓 : Type uP} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type uK} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The one-dimensional argument shared by the two base cases: when `m = 1`, an axis-parallel
consistency bound between a point measurement and an axis-parallel measurement gives a global
polynomial measurement, the canonical line's measurement read as a polynomial in the ambient
coordinate, consistent with the point measurement at the same error. -/
private theorem exists_polynomialMeasurement_consRel_of_m_eq_one
    (params : Parameters) [FieldModel params.q]
    (hm1 : params.m = 1)
    (S : SymModel 𝔓 K)
    (P : IdxProjMeas (Point params) (Fq params) 𝔓)
    (M : AxisParallelCovariantMeasurement params 𝔓)
    {e : ℝ}
    (h : S.ConsRel (uniformDistribution (AxisParallelTestSample params))
      (axisParallelPointAnswerFamilyOf P) (axisParallelLineAnswerFamilyOf M) e) :
    ∃ G : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓,
      S.ConsRel (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas P)
        (polynomialEvaluationFamily params G.toSubMeas)
        e := by
  classical
  have : Subsingleton (Fin params.m) := hm1 ▸ inferInstance
  let i0 : Fin params.m := ⟨0, by omega⟩
  let eSample : AxisParallelTestSample params ≃ Point params :=
    { toFun := fun s => s.1
      invFun := fun u => (u, i0)
      left_inv := fun s => Prod.ext rfl (Subsingleton.elim _ _)
      right_inv := fun _ => rfl }
  let c : AxisParallelLine params := AxisParallelLine.throughPoint (params := params) zeroPoint i0
  refine ⟨⟨postprocess (M c).toSubMeas (axisLinePolynomialToPolynomial params i0),
    (M c).total_eq_one⟩, ?_⟩
  convert (Preliminaries.consRel_uniform_equiv eSample S _ _ e).mp h using 2 with u u
  · rfl
  refine SubMeas.ext (fun a => ?_)
    ((M c).total_eq_one.trans (M { base := u, direction := i0 }).total_eq_one.symm)
  have hrep := M.reparamInvariant (AxisParallelLine.throughPoint (params := params) u i0)
    (AxisParallelLine.sampleParameter (params := params) u i0) a
  rw [AxisParallelLine.rebaseAt_throughPoint_sampleParameter,
    throughPoint_eq_zeroPoint_of_m_eq_one params hm1 u i0] at hrep
  refine Eq.trans ?_ hrep.symm
  simp only [polynomialEvaluationFamily, evaluateAt, SubMeas.postprocess_comp,
    axisLinePolynomialToPolynomial_apply]
  rfl

/-- Direct base case of `thm:main-induction` when `m = 1`.

The paper uses the unique axis-parallel line measurement as the global
polynomial measurement in this case. -/
theorem mainInductionBaseCase
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (hm1 : params.m = 1)
    (hgood : strategy.IsGood eps delta gamma) :
    ∃ G : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓,
      strategy.state.ConsRel (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas)
        (mainInductionError params k eps delta gamma) :=
  let ⟨G, hG⟩ := exists_polynomialMeasurement_consRel_of_m_eq_one params hm1 strategy.state
    strategy.pointMeasurement strategy.axisParallelMeasurement
    (e := strategy.axisParallelFailureProbability) ⟨le_rfl⟩
  mainInductionOfWitness params strategy eps delta gamma k
    ⟨_, G, hG, (le_min hgood.axisParallelTest
      (strategy.state.bipartiteConsError_uniform_le_one _ _)).trans
      (min_eps_one_le_mainInductionError_of_m_eq_one params k eps delta gamma hm1
        (eps_nonneg_of_isGood params strategy hgood)
        (delta_nonneg_of_isGood params strategy hgood)
        (gamma_nonneg_of_isGood params strategy hgood))⟩

/-- Answer-valued base case of the main induction when `m = 1`.

Paper origin: `references/ldt-paper/inductive_step.tex:441-454`, specialized
to the base dimension.

The proof is the same one-dimensional argument as `mainInductionBaseCase`.
Only the axis-parallel line measurement is used to construct the global
polynomial measurement, so the function-valued diagonal answer interface plays
no role in this case. -/
theorem answerMainInductionBaseCase
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (hm1 : params.m = 1)
    (hgood : strategy.IsGood eps delta gamma) :
    AnswerMainInductionConclusion params strategy eps delta gamma k :=
  let ⟨G, hG⟩ := exists_polynomialMeasurement_consRel_of_m_eq_one params hm1 strategy.state
    strategy.pointMeasurement strategy.axisParallelMeasurement
    (e := strategy.axisParallelFailureProbability) ⟨le_rfl⟩
  ⟨G, hG.mono <| (le_min hgood.axisParallelTest
    (strategy.state.bipartiteConsError_uniform_le_one _ _)).trans
    (min_eps_one_le_mainInductionError_of_m_eq_one params k eps delta gamma hm1
      (answer_eps_nonneg_of_isGood params strategy hgood)
      (answer_delta_nonneg_of_isGood params strategy hgood)
      (answer_gamma_nonneg_of_isGood params strategy hgood))⟩

/-- Trivial branch of `thm:main-induction` when the target error is at least
`1`.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`, where the
successor proof reduces to the nontrivial small-error regime before invoking the
pasting argument.  In the complementary branch the normalized consistency defect
is bounded by `1`, so a distinguished trivial polynomial measurement suffices.
-/
theorem mainInductionOfOneLeError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (herror : 1 ≤ mainInductionError params k eps delta gamma) :
    ∃ G : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓,
      strategy.state.ConsRel (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas)
        (mainInductionError params k eps delta gamma) :=
  ⟨Measurement.trivialDistinguishedOutcome
      (Classical.choice (inferInstance : Nonempty (MIPStarRE.LDT.Polynomial params))),
    ⟨(strategy.state.bipartiteConsError_uniform_le_one _ _).trans herror⟩⟩

/-- Trivial branch of the answer-valued main induction when the target error is
at least `1`.

This is the answer-valued analogue of `mainInductionOfOneLeError`.  It supplies
the large-error branch needed by a simultaneous answer-valued induction proof:
the diagonal answer interface is irrelevant because the consistency defect
between the point measurement and a distinguished trivial polynomial measurement
is bounded by `1`. -/
theorem answerMainInductionOfOneLeError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (herror : 1 ≤ mainInductionError params k eps delta gamma) :
    AnswerMainInductionConclusion params strategy eps delta gamma k :=
  ⟨Measurement.trivialDistinguishedOutcome
      (Classical.choice (inferInstance : Nonempty (MIPStarRE.LDT.Polynomial params))),
    ⟨(strategy.state.bipartiteConsError_uniform_le_one _ _).trans herror⟩⟩

end MIPRE.LIDT.Co.MainInductionStep

end

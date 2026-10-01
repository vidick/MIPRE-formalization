/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Test/
StrategyFailures.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Test.StrategyCore

@[expose] public section

/-!
# Symmetrized-strategy failure probabilities and test bounds

Failure-probability surrogates and basic low-individual-degree test bounds for
the split strategy interface: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Test/StrategyFailures.lean` in the port of
`planning/c6b-plan.md` (milestone M0, section "Port conventions").

The vendored file imports the role register `Test/StrategyRole/Algebra.lean` (the two-role
symmetrization of a two-space strategy, which the port replaces by the doubling of milestone M2),
but none of its declarations mentions it: the failure probabilities and `IsGood` are stated over
`SymStrat` alone. So this file imports only `Co/Test/StrategyCore.lean`, and the failure
probabilities are stated over the ported `SymStrat params 𝔓 K`, whose state is a symmetric model
`strategy.state : SymModel 𝔓 K`; the defects are the bipartite ones of `Co/Test/Defs.lean`, with
the point answers placed by `S.L` and the line answers by `S.R`.

The arithmetic lemma `three_summand_bounds_of_average_le` is classical; it is restated here
(with `ℝ` for the vendored `Error := ℝ`) rather than imported, since importing the vendored file
would bring in the role register.

## Not ported

Every declaration of the vendored file has a counterpart here. The vendored file declares nothing
about the role register, so no role-register-only declaration is dropped.
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co

open MIPStarRE.LDT (Parameters FieldModel Point uniformDistribution AxisParallelTestSample
  RestrictedDiagonalSample)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ### Symmetrized strategies and tested-branch bounds -/

namespace SymStrat

/-- Failure surrogate for the axis-parallel lines test.
Point answers on the left factor (`S.L`), line answers (evaluated at the
base point) on the right factor (`S.R`) of the symmetric model. -/
noncomputable def axisParallelFailureProbability
    {params : Parameters} [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K) : ℝ :=
  strategy.state.bipartiteConsError
    (uniformDistribution (AxisParallelTestSample params))
    (axisParallelPointAnswerFamily strategy)
    (axisParallelLineAnswerFamily strategy)

/-- Failure surrogate for the self-consistency test.
Uses the bipartite SSC defect (cross-factor overlap).
For projective measurements this equals `bipartiteConsError`
between the same measurement on both factors. -/
noncomputable def selfConsistencyFailureProbability
    {params : Parameters} [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K) : ℝ :=
  strategy.state.bipartiteSSCError
    (uniformDistribution (Point params))
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)

/-- Failure surrogate for the diagonal lines test.
Averages over the restriction index `j ∈ {0, …, m − 1}`, then
over the `j`-restricted diagonal test. For each `j`, direction
vectors have the last `m − j − 1` coordinates equal to zero. -/
noncomputable def diagonalFailureProbability
    {params : Parameters} [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K) : ℝ :=
  -- `params.hm : 0 < params.m` ensures the averaging denominator is nonzero.
  (1 / (params.m : ℝ)) *
    ∑ j : Fin params.m,
      strategy.state.bipartiteConsError
        (uniformDistribution
          (RestrictedDiagonalSample params j))
        (diagonalPointAnswerFamily strategy j)
        (diagonalLineAnswerFamily strategy j)

/-- The paper's notion of an `(ε,δ,γ)`-good symmetric strategy.

Matches the paper's Definition 3.1: three test-passing bounds with no
extra hypotheses.  The reparametrization covariance that was formerly
listed here is now a structural property of `SymStrat`, where it
belongs (the paper treats diagonal measurements as geometrically
covariant by construction). -/
structure IsGood {params : Parameters} [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta gamma : ℝ) : Prop where
  /-- The axis-parallel test fails with probability at most `eps`. -/
  axisParallelTest : strategy.axisParallelFailureProbability ≤ eps
  /-- The self-consistency test fails with probability at most `delta`. -/
  selfConsistencyTest : strategy.selfConsistencyFailureProbability ≤ delta
  /-- The diagonal-line test fails with probability at most `gamma`. -/
  diagonalLineTest : strategy.diagonalFailureProbability ≤ gamma

end SymStrat

/-- The diagonal-line failure surrogate is nonnegative. -/
theorem diagonalFailureProbability_nonneg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K) :
    0 ≤ strategy.diagonalFailureProbability :=
  mul_nonneg (by positivity) <| Finset.sum_nonneg fun j _ =>
    strategy.state.bipartiteConsError_nonneg
      (uniformDistribution (RestrictedDiagonalSample params j))
      (diagonalPointAnswerFamily strategy j)
      (diagonalLineAnswerFamily strategy j)

/-- A good symmetric strategy has a nonnegative axis-parallel error parameter
`ε`. -/
theorem eps_nonneg_of_isGood
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    {eps delta gamma : ℝ}
    (hgood : strategy.IsGood eps delta gamma) :
    0 ≤ eps :=
  le_trans
    (strategy.state.bipartiteConsError_nonneg
      (uniformDistribution (AxisParallelTestSample params))
      (axisParallelPointAnswerFamily strategy)
      (axisParallelLineAnswerFamily strategy))
    hgood.axisParallelTest

/-- A good symmetric strategy has a nonnegative self-consistency error
parameter `δ`. -/
theorem delta_nonneg_of_isGood
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    {eps delta gamma : ℝ}
    (hgood : strategy.IsGood eps delta gamma) :
    0 ≤ delta :=
  le_trans
    (strategy.state.bipartiteSSCError_nonneg
      (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
    hgood.selfConsistencyTest

/-- A good symmetric strategy has a nonnegative diagonal-lines error parameter
`γ`. -/
theorem gamma_nonneg_of_isGood
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    {eps delta gamma : ℝ}
    (hgood : strategy.IsGood eps delta gamma) :
    0 ≤ gamma :=
  le_trans (diagonalFailureProbability_nonneg params strategy)
    hgood.diagonalLineTest

/-! ### Answer-valued symmetric strategies -/

/-- The answer-valued diagonal-line failure surrogate is nonnegative. -/
theorem answer_diagonalFailureProbability_nonneg
    (params : Parameters) [FieldModel params.q]
    (strategy : AnswerSymStrat params 𝔓 K) :
    0 ≤ strategy.diagonalFailureProbability :=
  mul_nonneg (by positivity) <| Finset.sum_nonneg fun j _ =>
    strategy.state.bipartiteConsError_nonneg
      (uniformDistribution (RestrictedDiagonalSample params j))
      (AnswerSymStrat.diagonalPointAnswerFamily strategy j)
      (AnswerSymStrat.diagonalLineAnswerFamily strategy j)

/-- A good answer-valued symmetric strategy has a nonnegative axis-parallel
error parameter `ε`. -/
theorem answer_eps_nonneg_of_isGood
    (params : Parameters) [FieldModel params.q]
    (strategy : AnswerSymStrat params 𝔓 K)
    {eps delta gamma : ℝ}
    (hgood : strategy.IsGood eps delta gamma) :
    0 ≤ eps :=
  le_trans
    (strategy.state.bipartiteConsError_nonneg
      (uniformDistribution (AxisParallelTestSample params))
      (AnswerSymStrat.axisParallelPointAnswerFamily strategy)
      (AnswerSymStrat.axisParallelLineAnswerFamily strategy))
    hgood.axisParallelTest

/-- A good answer-valued symmetric strategy has a nonnegative self-consistency
error parameter `δ`. -/
theorem answer_delta_nonneg_of_isGood
    (params : Parameters) [FieldModel params.q]
    (strategy : AnswerSymStrat params 𝔓 K)
    {eps delta gamma : ℝ}
    (hgood : strategy.IsGood eps delta gamma) :
    0 ≤ delta :=
  le_trans
    (strategy.state.bipartiteSSCError_nonneg
      (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
    hgood.selfConsistencyTest

/-- A good answer-valued symmetric strategy has a nonnegative diagonal-lines
error parameter `γ`. -/
theorem answer_gamma_nonneg_of_isGood
    (params : Parameters) [FieldModel params.q]
    (strategy : AnswerSymStrat params 𝔓 K)
    {eps delta gamma : ℝ}
    (hgood : strategy.IsGood eps delta gamma) :
    0 ≤ gamma :=
  le_trans (answer_diagonalFailureProbability_nonneg params strategy)
    hgood.diagonalLineTest

/-- If three nonnegative summands have average at most `eps`, each summand is at
most `3 * eps`. -/
lemma three_summand_bounds_of_average_le
    {axis point diagonal eps : ℝ}
    (haxis : 0 ≤ axis) (hpoint : 0 ≤ point) (hdiagonal : 0 ≤ diagonal)
    (hmain : (axis + point + diagonal) / 3 ≤ eps) :
    axis ≤ 3 * eps ∧ point ≤ 3 * eps ∧ diagonal ≤ 3 * eps :=
  ⟨by linarith, by linarith, by linarith⟩

end MIPRE.LIDT.Co

end

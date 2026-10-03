/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
MainInductionStep/Theorems/PastingAssembly/ErrorBounds.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.MainInductionStep.Theorems.PastingAssembly.AnswerFields
public import MIPRE.Background.LIDT.MIPStarRE.LDT.MainInductionStep.Theorems.PastingAssembly.ErrorBounds

@[expose] public section

/-!
# Section 6 — Pasting Assembly: Error Bounds

The scalar absorption of the answer-valued pasting route and the degree-zero answer-valued
pasting construction of the small-error branch. This is the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/MainInductionStep/Theorems/PastingAssembly/ErrorBounds.lean`
in the port of `planning/c6b-plan.md` (milestone M12, section "Port conventions").

## Translation

A strategy is an `AnswerSymStrat params.next 𝔓 K` (`Co/Test/StrategyCore.lean`), whose state is
the symmetric model `strategy.state : SymModel 𝔓 K`; its point-equivalent ordinary carrier is Co
`answerSelfImprovementCarrier`, with the same state. `IdxPolyFamily params ι` is
`IdxPolyFamily params 𝔓`, `Error` is `ℝ`, and `ConsRel` is read on `strategy.state`. The error
functions (`mainInductionError`, `mainInductionNu`, `selfImprovementInInductionError`,
`ldPastingInInductionError`, `ldPastingInInductionNu`) and the scalar lemmas
`ldPastingInInductionNu_le_fifth_mainInductionNu` (vendored `PastingAssembly/Basic`) and
`ldPastingInInductionError_le_mainInductionError_of_bounds` (the vendored file) are the vendored
classical declarations, reached through explicit `open` lists; the vendored file is imported for
the second. No vendored statement here has a swap, density or normalization hypothesis, and no
statement takes a new hypothesis: the degree-zero pasting construction neither orthonormalizes
nor solves a semidefinite program. The vendored file-wide `respectTransparency false` is not
needed: the file sets no option.

## Proofs that differ from the vendored ones

- The carrier's axis-parallel and self-consistency failure probabilities, its completeness and
  its consistency with the points are those of `strategy` by definitional equality, as in Co
  `PastingAssembly/AnswerFields`: the vendored `unfold … ; simp` identities and `simpa [carrier,
  answerSelfImprovementCarrier]` transfers are dropped, and the hypotheses are passed directly.
- `answerLdPastingInInductionError_le_mainInductionError_of_smallError` is one term.

## Not ported

- `ldPastingInInductionError_le_mainInductionError_of_bounds`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/inductive_step.tex`
- `blueprint/src/chapter/ch10_induction.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.MainInductionStep

open MIPStarRE.LDT (Parameters FieldModel Point uniformDistribution)
open MIPStarRE.LDT.MainInductionStep (mainInductionError mainInductionNu
  selfImprovementInInductionError ldPastingInInductionError ldPastingInInductionNu
  ldPastingInInductionNu_le_fifth_mainInductionNu
  ldPastingInInductionError_le_mainInductionError_of_bounds)
open MIPRE.LIDT.Co (AnswerSymStrat)

universe uP uK

variable {𝔓 : Type uP} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type uK} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Scalar absorption for the answer-valued pasting route.

This is the answer-valued counterpart of
`ldPastingInInductionError_le_mainInductionError_of_bounds`.  Its proof uses
only the answer-valued scalar consequences of the small-error hypothesis; it
does not pass through the ordinary carrier strategy. -/
theorem answerLdPastingInInductionError_le_mainInductionError_of_smallError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next 𝔓 K)
    (eps delta gamma kappa : ℝ)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1)
    (hkappa_le :
      kappa ≤
        ((params.m : ℝ) ^ (2 : ℕ)) *
            (mainInductionNu params.next k eps delta gamma +
              Real.exp (-((k : ℝ) / (80000 * ((params.m : ℝ) ^ (2 : ℕ))))))
          + selfImprovementInInductionError params.next eps delta gamma)
    (hzeta_le_nu :
      selfImprovementInInductionError params.next eps delta gamma ≤
        mainInductionNu params.next k eps delta gamma) :
    ldPastingInInductionError params k eps delta gamma kappa
        (selfImprovementInInductionError params.next eps delta gamma) ≤
      mainInductionError params.next k eps delta gamma :=
  have heps_nonneg := answer_eps_nonneg_of_isGood params.next strategy hgood
  have hdelta_nonneg := answer_delta_nonneg_of_isGood params.next strategy hgood
  have hgamma_nonneg := answer_gamma_nonneg_of_isGood params.next strategy hgood
  ldPastingInInductionError_le_mainInductionError_of_bounds
    params eps delta gamma k kappa
    (selfImprovementInInductionError params.next eps delta gamma)
    heps_nonneg hdelta_nonneg hgamma_nonneg hkappa_le hzeta_le_nu
    (ldPastingInInductionNu_le_fifth_mainInductionNu
      params eps delta gamma k heps_nonneg hdelta_nonneg hgamma_nonneg
      (answer_eps_le_one_of_mainInductionError_lt_one params strategy hgood hsmall)
      (answer_delta_le_one_of_mainInductionError_lt_one params strategy hgood hsmall)
      (answer_gamma_le_one_of_mainInductionError_lt_one params strategy hgood hsmall)
      (answer_dq_le_q_of_mainInductionError_lt_one params strategy hgood hsmall))

/-- Degree-zero answer-valued pasting construction for the small-error successor
branch.

This is the complementary case to the positive-degree branch handled by
`answerLdPastingInInductionSectionOfComMainAndErrorBound`.  The proof applies
the axis/self-consistency form of the degree-zero pasting construction to the
point-equivalent carrier and then uses the answer-valued scalar absorption
estimate.  It does not use the carrier's dummy ordinary diagonal measurement.

Paper location: the pasting invocation in
`references/ldt-paper/inductive_step.tex:541-551`; this is the `d = 0`
complementary branch of the low-degree pasting theorem. -/
theorem answerLdPastingInInductionSectionDegreeZeroOfSmallError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1)
    (family : IdxPolyFamily params 𝔓)
    (kappa : ℝ)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons :
      strategy.state.ConsRel (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (IdxPolyFamily.evaluatedAtNextPoint family)
        (selfImprovementInInductionError params.next eps delta gamma))
    (_hself :
      family.StronglySelfConsistent strategy.state
        (selfImprovementInInductionError params.next eps delta gamma))
    (_hbound :
      IdxPolyFamily.SliceBoundednessInput
        (answerSelfImprovementCarrier params.next strategy)
        family
        (selfImprovementInInductionError params.next eps delta gamma))
    (hkappa_le :
      kappa ≤
        ((params.m : ℝ) ^ (2 : ℕ)) *
            (mainInductionNu params.next k eps delta gamma +
              Real.exp (-((k : ℝ) / (80000 * ((params.m : ℝ) ^ (2 : ℕ))))))
          + selfImprovementInInductionError params.next eps delta gamma)
    (hzeta_le_nu :
      selfImprovementInInductionError params.next eps delta gamma ≤
        mainInductionNu params.next k eps delta gamma)
    (_hk : 400 * params.m * params.d ≤ k)
    (hd_zero : params.d = 0) :
    AnswerMainInductionConclusion params.next strategy eps delta gamma k := by
  obtain ⟨H, -, hpasted⟩ :=
    Pasting.degreeZeroPastedPointConsistency_of_axis_self params
      (answerSelfImprovementCarrier params.next strategy)
      eps delta gamma kappa (selfImprovementInInductionError params.next eps delta gamma)
      hgood.axisParallelTest hgood.selfConsistencyTest
      (answer_eps_nonneg_of_isGood params.next strategy hgood)
      (answer_delta_nonneg_of_isGood params.next strategy hgood)
      (answer_gamma_nonneg_of_isGood params.next strategy hgood)
      family hcomplete ⟨hcons⟩ hd_zero k
  exact ⟨H, ⟨hpasted.offDiagonalBound.trans
    (answerLdPastingInInductionError_le_mainInductionError_of_smallError
      params strategy eps delta gamma kappa k hgood hsmall hkappa_le hzeta_le_nu)⟩⟩

end MIPRE.LIDT.Co.MainInductionStep

end

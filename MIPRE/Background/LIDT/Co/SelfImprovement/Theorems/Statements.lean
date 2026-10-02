/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
SelfImprovement/Theorems/Statements.lean, to the symmetric model of `planning/c6b-plan.md`; not a
vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.SelfImprovement.Defs
public import MIPRE.Foundations.SummedSdp

@[expose] public section

/-!
# Section 9 self-improvement statements

The SDP, `addInU` and orthonormalization interfaces of the self-improvement theorem: the
counterpart of `MIPRE/Background/LIDT/MIPStarRE/LDT/SelfImprovement/Theorems/Statements.lean` in
the port of `planning/c6b-plan.md` (milestone M10, section "Port conventions").

A strategy is a `SymStrat params 𝔓 K`. The SDP witnesses `T : SubMeas (Polynomial params) 𝔓` and
`Z : 𝔓` are local, and every structure keeps the vendored fields verbatim. The `addInU` and
helper-agreement operators are joint operators `K →L[ℂ] K`, built with
`strategy.state.opTensor`, so the strategy argument of `addInULeftOperatorAtPoint`, unused in the
vendored file (`_strategy`), is used here. The two operators that place without a strategy,
`helperUpperOperator` and `projectiveResidualOperator`, take the model `(S : SymModel 𝔓 K)` as an
explicit first argument, as M6's and M7's placement helpers do; `helperBoundednessOperator`,
`helperBoundednessGap` and `projectiveBoundednessGap` pass `strategy.state`. The vendored
placements `leftPlacedSubMeas (ιB := ι)` and `rightPlacedSubMeas (ιA := ι)` are
`strategy.state.leftPlacedSubMeas` and `strategy.state.rightPlacedSubMeas`.

## The summed semidefinite form

The vendored `SdpStatementWithSlackness` is supplied by the matrix SDP bridge
(`SelfImprovement/Theorems/Results/SdpMatrixBridge.lean`, through the canonical block SDP of
`SelfImprovement/MatrixRealization`), which the port does not have: there is no dimension. It is
replaced by the summed form of M9, `MIPRE.SummedSdp.IsSummedSdp`, whose fields are those of
`SdpOptimalPairWithSlackness`. `SdpStatementWithSlackness.of_isSummedSdp` is the interface half
of that adapter: a summed form for the averaged point operators `A_g = averagedPointOperator`
gives the SDP statement. `SdpOptimalPairWithSlackness.isSummedSdp` is its converse, with the
self-adjointness of `Z` from `dual_positive`. The other half, the existence of a summed form in a
finite pair, is `sdp_statement_with_slackness` in the ported `HelperCompleteness/Bracketed.lean`.

## Not ported

Every declaration of the vendored file has a counterpart here.

## New here

- `SdpStatementWithSlackness.of_isSummedSdp`: the summed form of M9 gives the SDP statement.
- `SdpOptimalPairWithSlackness.isSummedSdp`: its converse.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `blueprint/src/chapter/ch07_self_improvement.tex`
- `references/ldt-paper/self_improvement.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.SelfImprovement

open MIPStarRE.LDT (Parameters FieldModel Point Fq avgOver uniformDistribution)
open MIPStarRE.LDT.SelfImprovement (AddInUSelection addInUSelectionPairs
  selfImprovementVarianceError selfImprovementHelperError selfImprovementError)
open MIPRE.LIDT.Co.GlobalVariance (pointConditionedOutcomeOperatorAtPolynomial
  pointConditionedGlobalVariance)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ## Operators and conclusions -/

/-- Lean-only reduced SDP data for the currently formalized fragment of the
self-improvement argument.

Paper-gap note (upstream): `docs/paper-gaps/issue-1230-self-improvement-sdp-usage.tex`.

The paper's `lem:sdp` eventually supplies strong duality, complementary
slackness, and an optimal witness. The development only consumes the weaker facts recorded
here: the primal witness is a full measurement (`T.total = 1`), and the dual witness dominates
every averaged point operator. Positivity of the dual witness is derivable from dual
feasibility and positivity of the averaged point operators. Despite the
historical name, this reduced record does not assert SDP optimality. -/
structure SdpOptimalPair (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) (Z : 𝔓) : Prop where
  /-- The primal witness is complete. -/
  primalTotalOperator :
    T.total = 1
  /-- The dual witness dominates every averaged point operator. -/
  dualFeasible :
    ∀ g : MIPStarRE.LDT.Polynomial params,
      0 ≤ sdpDualSlackOperator params strategy Z g

namespace SdpOptimalPair

/-- The dual operator in an SDP witness is positive. -/
theorem dualPositive {params : Parameters} [FieldModel params.q]
    {strategy : SymStrat params 𝔓 K}
    {T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓} {Z : 𝔓}
    (h : SdpOptimalPair params strategy T Z) :
    0 ≤ Z :=
  sdpDualPositive_of_dualFeasible params strategy Z h.dualFeasible

end SdpOptimalPair

/-- SDP optimal-pair data strengthened by complementary slackness.

Paper origin: `references/ldt-paper/self_improvement.tex:82-181`
(`\label{lem:sdp}`); paper-gap note (upstream):
`docs/paper-gaps/issue-1230-self-improvement-sdp-usage.tex`.

The reduced `SdpOptimalPair` interface above contains only the feasibility and
normalization facts. The paper's strong-duality argument also gives complementary slackness,
which this successor interface records. -/
structure SdpOptimalPairWithSlackness (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) (Z : 𝔓) : Prop where
  /-- The reduced SDP data. -/
  toSdpOptimalPair :
    SdpOptimalPair params strategy T Z
  /-- Complementary slackness, `T_g Z = T_g A_g` for every `g`. -/
  complementarySlackness :
    ∀ g : MIPStarRE.LDT.Polynomial params,
      sdpComplementarySlacknessEquation params strategy T Z g

/-- Paper origin: `references/ldt-paper/self_improvement.tex:82-181`
(`\label{lem:sdp}`); the complementary-slackness equation `T_g · Z = T_g · A_g`
is `eq:complementary-slackness` at line 179.

SDP conclusion strengthened by complementary slackness.

Paper origin: `references/ldt-paper/self_improvement.tex` lines 62--88
introduce the Section 9 primal/dual SDP pair and state `\label{lem:sdp}`:
there is an optimal pair `{T_g}`, `Z` with `∑ g, T_g = I` and
`T_g Z = T_g A_g` for every polynomial `g`.

This is the statement shape expected from that paper argument: it records the
complete primal measurement, the dual-feasible operator, and the
complementary-slackness equations. In the port it comes from the summed form of M9
(`SdpStatementWithSlackness.of_isSummedSdp`). -/
structure SdpStatementWithSlackness (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K) : Prop where
  /-- A complete primal measurement and a dual witness with slackness. -/
  witness :
    ∃ T : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓, ∃ Z : 𝔓,
      SdpOptimalPairWithSlackness params strategy T.toSubMeas Z

namespace SdpOptimalPairWithSlackness

/-- The primal total of a slackness-carrying SDP pair is the identity. -/
theorem primal_total_operator {params : Parameters} [FieldModel params.q]
    {strategy : SymStrat params 𝔓 K}
    {T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓} {Z : 𝔓}
    (h : SdpOptimalPairWithSlackness params strategy T Z) :
    T.total = 1 :=
  h.toSdpOptimalPair.primalTotalOperator

/-- The dual operator in a slackness-carrying SDP pair is positive. -/
theorem dual_positive {params : Parameters} [FieldModel params.q]
    {strategy : SymStrat params 𝔓 K}
    {T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓} {Z : 𝔓}
    (h : SdpOptimalPairWithSlackness params strategy T Z) :
    0 ≤ Z :=
  h.toSdpOptimalPair.dualPositive

/-- The dual slack operators in a slackness-carrying SDP pair are positive. -/
theorem dual_feasible {params : Parameters} [FieldModel params.q]
    {strategy : SymStrat params 𝔓 K}
    {T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓} {Z : 𝔓}
    (h : SdpOptimalPairWithSlackness params strategy T Z) :
    ∀ g : MIPStarRE.LDT.Polynomial params,
      0 ≤ sdpDualSlackOperator params strategy Z g :=
  h.toSdpOptimalPair.dualFeasible

/-- The primal submeasurement in a slackness-carrying SDP pair is a
measurement. -/
def primalMeasurement {params : Parameters} [FieldModel params.q]
    {strategy : SymStrat params 𝔓 K}
    {T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓} {Z : 𝔓}
    (h : SdpOptimalPairWithSlackness params strategy T Z) :
    Measurement (MIPStarRE.LDT.Polynomial params) 𝔓 where
  toSubMeas := T
  total_eq_one := h.toSdpOptimalPair.primalTotalOperator

/-- The primal measurement of a slackness-carrying SDP pair has the pair's submeasurement. -/
@[simp] theorem primalMeasurement_toSubMeas {params : Parameters} [FieldModel params.q]
    {strategy : SymStrat params 𝔓 K}
    {T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓} {Z : 𝔓}
    (h : SdpOptimalPairWithSlackness params strategy T Z) :
    h.primalMeasurement.toSubMeas = T :=
  rfl

/-- **New here.** A slackness-carrying SDP pair is the summed form of M9
(`MIPRE.SummedSdp.IsSummedSdp`) for the averaged point operators, the self-adjointness of `Z`
coming from its positivity. -/
theorem isSummedSdp {params : Parameters} [FieldModel params.q]
    {strategy : SymStrat params 𝔓 K}
    {T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓} {Z : 𝔓}
    (h : SdpOptimalPairWithSlackness params strategy T Z) :
    MIPRE.SummedSdp.IsSummedSdp (averagedPointOperator params strategy) T.outcome Z where
  nonneg := T.outcome_pos
  total := T.sum_eq_total.trans h.primal_total_operator
  isSelfAdjoint := IsSelfAdjoint.of_nonneg h.dual_positive
  dualFeasible g := sub_nonneg.1 (h.dual_feasible g)
  complementarySlackness := h.complementarySlackness

end SdpOptimalPairWithSlackness

namespace SdpStatementWithSlackness

/-- A slackness-carrying SDP statement gives the displayed paper-form
measurement and dual witness: a complete primal measurement, a positive
dual operator dominating every averaged point operator, and the
complementary-slackness equations. -/
theorem exists_measurement_witness {params : Parameters} [FieldModel params.q]
    {strategy : SymStrat params 𝔓 K}
    (h : SdpStatementWithSlackness params strategy) :
    ∃ T : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓,
      ∃ Z : 𝔓,
        0 ≤ Z ∧
        (∀ g : MIPStarRE.LDT.Polynomial params, 0 ≤ sdpDualSlackOperator params strategy Z g) ∧
        ∀ g : MIPStarRE.LDT.Polynomial params,
          sdpComplementarySlacknessEquation params strategy T.toSubMeas Z g := by
  obtain ⟨T, Z, hpair⟩ := h.witness
  exact ⟨T, Z, hpair.dual_positive, hpair.dual_feasible, hpair.complementarySlackness⟩

/-- **New here.** The interface half of the adapter from M9's summed semidefinite form: a
summed form `IsSummedSdp A T Z` for the averaged point operators `A_g = averagedPointOperator`
gives the SDP statement, with the measurement `T` and the dual witness `Z`. -/
theorem of_isSummedSdp {params : Parameters} [FieldModel params.q]
    {strategy : SymStrat params 𝔓 K}
    {T : MIPStarRE.LDT.Polynomial params → 𝔓} {Z : 𝔓}
    (h : MIPRE.SummedSdp.IsSummedSdp (averagedPointOperator params strategy) T Z) :
    SdpStatementWithSlackness params strategy :=
  ⟨⟨{ outcome := T, total := 1, outcome_pos := h.nonneg, sum_eq_total := h.total,
      total_le_one := le_rfl, total_eq_one := rfl }, Z,
    ⟨⟨rfl, fun g => sub_nonneg.2 (h.dualFeasible g)⟩, h.complementarySlackness⟩⟩⟩

end SdpStatementWithSlackness

/-- The operator inside the left-hand side of `lem:add-in-u` at a fixed point `u`:
the joint operator `Σ_{(o, h) ∈ S u} (M u)_o ⊗ H_h`. -/
noncomputable def addInULeftOperatorAtPoint {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (M : IdxSubMeas (Point params) Outcome 𝔓)
    (H : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (S : AddInUSelection params Outcome)
    (u : Point params) : K →L[ℂ] K :=
  ∑ ah ∈ addInUSelectionPairs params S u,
    strategy.state.opTensor ((M u).outcome ah.1) (H.outcome ah.2)

/-- The operator inside the right-hand side of `lem:add-in-u` at a fixed point `u`:
the joint operator `Σ_{(o, h) ∈ S u} (A^u_{h(u)} (M u)_o A^u_{h(u)}) ⊗ T_h`. -/
noncomputable def addInURightOperatorAtPoint {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (M : IdxSubMeas (Point params) Outcome 𝔓)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (S : AddInUSelection params Outcome)
    (u : Point params) : K →L[ℂ] K :=
  ∑ ah ∈ addInUSelectionPairs params S u,
    let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 u
    strategy.state.opTensor (Au * (M u).outcome ah.1 * Au) (T.outcome ah.2)

/-- The uniform point average `E_u ⟨ψ, f(u) ψ⟩` of a point-indexed joint operator. -/
noncomputable def addInUPointAverage (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (f : Point params → K →L[ℂ] K) : ℝ :=
  avgOver (uniformDistribution (Point params)) (fun u => strategy.state.ev (f u))

/-- The left-hand expectation in `lem:add-in-u`. -/
noncomputable def addInULeftQuantity {Outcome : Type*} [Fintype Outcome] (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (M : IdxSubMeas (Point params) Outcome 𝔓)
    (H : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (S : AddInUSelection params Outcome) : ℝ :=
  addInUPointAverage params strategy (addInULeftOperatorAtPoint params strategy M H S)

/-- The right-hand expectation in `lem:add-in-u`. -/
noncomputable def addInURightQuantity {Outcome : Type*} [Fintype Outcome] (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (M : IdxSubMeas (Point params) Outcome 𝔓)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (S : AddInUSelection params Outcome) : ℝ :=
  addInUPointAverage params strategy (addInURightOperatorAtPoint params strategy M T S)

/-- The pointwise matched operator `Σ_a A^u_a ⊗ H_[h(u)=a]`, a joint operator. -/
noncomputable def helperAgreementOperatorAtPoint (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (H : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (u : Point params) : K →L[ℂ] K :=
  let Hu := evaluateAt params u H
  ∑ a : Fq params,
    strategy.state.opTensor ((strategy.pointMeasurement u).outcome a) (Hu.outcome a)

/-- The average operator `E_u Σ_a A^u_a ⊗ H_[h(u)=a]`, a joint operator. -/
noncomputable def helperAgreementAverageOperator (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (H : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) : K →L[ℂ] K :=
  averageOperatorOverDistribution (uniformDistribution (Point params))
    (helperAgreementOperatorAtPoint params strategy H)

/-- The helper-stage upper operator `Z ⊗ I`, the left placement of `Z` in the model `S`. -/
noncomputable def helperUpperOperator (S : SymModel 𝔓 K) (_params : Parameters) (Z : 𝔓) :
    K →L[ℂ] K :=
  S.L Z

/-- The operator measuring the helper-stage boundedness defect, a joint operator. -/
noncomputable def helperBoundednessOperator (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (H : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) (Z : 𝔓) : K →L[ℂ] K :=
  helperUpperOperator strategy.state params Z -
    helperAgreementAverageOperator params strategy H

/-- The helper-stage boundedness defect. -/
noncomputable def helperBoundednessGap (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (H : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) (Z : 𝔓) : ℝ :=
  strategy.state.ev (helperBoundednessOperator params strategy H Z)

/-- The projective-stage residual operator `Z ⊗ (I - H)`, placed in the model `S`. -/
noncomputable def projectiveResidualOperator (S : SymModel 𝔓 K) (params : Parameters)
    [FieldModel params.q]
    (H : ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) (Z : 𝔓) : K →L[ℂ] K :=
  S.L Z * S.R (1 - H.toSubMeas.total)

/-- The projective-stage boundedness defect. -/
noncomputable def projectiveBoundednessGap (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (H : ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) (Z : 𝔓) : ℝ :=
  strategy.state.ev (projectiveResidualOperator strategy.state params H Z)

/-- Paper origin: `references/ldt-paper/self_improvement.tex:238-455`
(`\label{lem:add-in-u}`).

Reduced conclusion for the currently formalized fragment of `lem:add-in-u`.

The paper statement quantifies over an auxiliary submeasurement `M`, the
averaged family `H`, and a selection rule `S`, and proves a transfer inequality
between two expectations. The development only uses the downstream
global-variance corollary, which depends only on the SDP measurement `T` and
the error parameters, so those unused inputs are omitted here. -/
structure AddInUStatement (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓)
    (eps delta : ℝ) : Prop where
  /-- The point-conditioned global variance of `T` is small. -/
  varianceBound :
    pointConditionedGlobalVariance params strategy T.toSubMeas ≤
      selfImprovementVarianceError params eps delta

/-- Paper origin: `references/ldt-paper/self_improvement.tex:24-60`
(`\label{lem:self-improvement-helper}`); upstream
`docs/paper-gaps/issue-1230-self-improvement-sdp-usage.tex` (SDP gap).

Reduced conclusion for the SDP and `addInU` stage of
`lem:self-improvement-helper`: the SDP witness, the averaged construction of `H`, and the
reduced `addInU` variance bound. Positivity and pointwise dual feasibility of `Z` are read from
the bundled SDP witness rather than repeated as helper fields.

The paper and blueprint state four additional helper-lemma guarantees
(`completeness`, `pointConsistency`, strong self-consistency, and boundedness).
They are not fields here; they are proved as separate estimates that consume this SDP-witness
conclusion together with the paper hypotheses. -/
structure SelfImprovementHelperConclusion (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓)
    (H : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (Z : 𝔓) (eps delta : ℝ) : Prop where
  /-- The SDP witness. -/
  sdpWitness : SdpOptimalPair params strategy T.toSubMeas Z
  /-- `H` is the averaged sandwiched submeasurement of `T`. -/
  averagedConstruction :
    H = averagedSandwichedPolynomialSubMeas params strategy T.toSubMeas
  /-- The reduced `addInU` variance bound. -/
  addInUVarianceBound :
    AddInUStatement params strategy T eps delta

/-- Paper origin: `references/ldt-paper/self_improvement.tex:24-60`
(`\label{lem:self-improvement-helper}`).

Output of the self-improvement helper lemma before rounding to projectors. The
submeasurement `H` satisfies the four conclusions stated in the paper:
completeness, consistency with the point measurement, strong self-consistency,
and boundedness by a positive dual witness `Z`. The boundedness
conclusion is represented by the positivity of `Z`, the pointwise domination
inequality `Z ≥ E_u A^u_{g(u)}`, and the corresponding state-dependent gap
estimate. -/
structure SelfImprovementHelperStatement (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (H : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (Z : 𝔓) (eps delta nu : ℝ) : Prop where
  /-- `H` is almost complete. -/
  completeness :
    strategy.state.CompletenessAtLeast (H.liftLeft strategy.state)
      ((1 - nu) - selfImprovementHelperError params eps delta)
  /-- `H` is consistent with the point measurement. -/
  pointConsistency :
    strategy.state.ConsRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params H)
      (selfImprovementHelperError params eps delta)
  /-- `H` is strongly self-consistent. -/
  strongSelfConsistency :
    strategy.state.BipartiteSSCRel (uniformDistribution Unit)
      (constSubMeasFamily H)
      (selfImprovementHelperError params eps delta)
  /-- The dual witness is positive. -/
  positiveSemidefiniteWitness :
    0 ≤ Z
  /-- The dual witness dominates every averaged point operator. -/
  dualDominatesAveragedPoint :
    ∀ g : MIPStarRE.LDT.Polynomial params,
      0 ≤ sdpDualSlackOperator params strategy Z g
  /-- The helper-stage boundedness defect is small. -/
  boundednessGap :
    helperBoundednessGap params strategy H Z ≤
      selfImprovementHelperError params eps delta

/-- Internal helper conclusion strengthened by the SDP complementary-slackness
equation.

Paper origin: `references/ldt-paper/self_improvement.tex:82-181`
(`\label{lem:sdp}`) and `references/ldt-paper/self_improvement.tex:635-671`
(`\label{thm:self-improvement}`); upstream paper-gap note:
`docs/paper-gaps/issue-1230-self-improvement-sdp-usage.tex`.

This is not an additional source-theorem hypothesis. It is the internal
helper-output record produced after the SDP theorem
`sdp_statement_with_slackness` supplies the slackness. It keeps all fields of
the reduced helper conclusion and additionally records the consequence
`T_g Z = T_g A_g`. -/
structure SelfImprovementHelperConclusionWithSlackness (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓)
    (H : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (Z : 𝔓) (eps delta : ℝ) : Prop where
  /-- The reduced helper conclusion. -/
  toHelperConclusion :
    SelfImprovementHelperConclusion params strategy T H Z eps delta
  /-- Complementary slackness, `T_g Z = T_g A_g` for every `g`. -/
  complementarySlackness :
    ∀ g : MIPStarRE.LDT.Polynomial params,
      sdpComplementarySlacknessEquation params strategy T.toSubMeas Z g

/-- Paper origin: `references/ldt-paper/self_improvement.tex:635-671`
(`\label{thm:self-improvement}`).

Conclusion of `thm:self-improvement`.

The paper's boundedness output is the projective residual estimate
`⟨ψ, Z ⊗ (I - H)⟩ ≤ ζ`, recorded here as `projectiveResidualBound`. This
structure is the conjunction of the paper's displayed conclusions for the
already-quantified witnesses `H` and `Z`; it does not store an internal helper
form or an SDP connection input. -/
structure SelfImprovementConclusion (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓)
    (H : ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (Z : 𝔓) (eps delta gamma nu : ℝ) : Prop where
  /-- `H` is almost complete. -/
  completeness :
    strategy.state.CompletenessAtLeast (H.toSubMeas.liftLeft strategy.state)
      ((1 - nu) - selfImprovementError params eps delta)
  /-- `H` is consistent with the point measurement. -/
  pointConsistency :
    strategy.state.ConsRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params H.toSubMeas)
      (selfImprovementError params eps delta)
  /-- The left and right placements of `H` are close. -/
  selfCloseness :
    strategy.state.SDDRel (uniformDistribution Unit)
      (constSubMeasFamily (strategy.state.leftPlacedSubMeas H.toSubMeas))
      (constSubMeasFamily (strategy.state.rightPlacedSubMeas H.toSubMeas))
      (selfImprovementError params eps delta)
  /-- The dual witness is positive. -/
  positiveSemidefiniteWitness :
    0 ≤ Z
  /-- The dual witness dominates every averaged point operator. -/
  dualDominatesAveragedPoint :
    ∀ g : MIPStarRE.LDT.Polynomial params,
      0 ≤ sdpDualSlackOperator params strategy Z g
  /-- The projective residual `⟨ψ, Z ⊗ (I - H)⟩` is small. -/
  projectiveResidualBound :
    projectiveBoundednessGap params strategy H Z ≤
      selfImprovementError params eps delta

/-- Final fields for the Section 9 transport stage.

The final fields are the Section 9 outputs that remain after combining
`SelfImprovementHelper`, orthonormalization, data processing, and the
monotone-total transport used in the projective-output step: completeness, point consistency,
self-closeness, and the projective-residual estimate, the paper-facing boundedness quantity
carried into `SelfImprovementConclusion`. -/
structure SelfImprovementFinalFields (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (H : ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (Z : 𝔓) (eps delta nu : ℝ) : Prop where
  /-- `H` is almost complete. -/
  completeness :
    strategy.state.CompletenessAtLeast (H.toSubMeas.liftLeft strategy.state)
      ((1 - nu) - selfImprovementError params eps delta)
  /-- `H` is consistent with the point measurement. -/
  pointConsistency :
    strategy.state.ConsRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params H.toSubMeas)
      (selfImprovementError params eps delta)
  /-- The left and right placements of `H` are close. -/
  selfCloseness :
    strategy.state.SDDRel (uniformDistribution Unit)
      (constSubMeasFamily (strategy.state.leftPlacedSubMeas H.toSubMeas))
      (constSubMeasFamily (strategy.state.rightPlacedSubMeas H.toSubMeas))
      (selfImprovementError params eps delta)
  /-- The projective residual `⟨ψ, Z ⊗ (I - H)⟩` is small. -/
  projectiveResidualBound :
    projectiveBoundednessGap params strategy H Z ≤
      selfImprovementError params eps delta

end MIPRE.LIDT.Co.SelfImprovement

end

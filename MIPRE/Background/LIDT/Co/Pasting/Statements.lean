/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/
Statements.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Commutativity.Scaffold.Core
public import MIPRE.Background.LIDT.Co.MainInductionStep.Defs
public import MIPRE.Background.LIDT.Co.Pasting.Sandwich.PastedFamilies
public import MIPRE.Background.LIDT.MIPStarRE.LDT.Pasting.Statements

@[expose] public section

/-!
# Section 12 — Statements

The Section 12 pasting conclusions as reusable proposition-valued structures: the statement
structures for the switcheroo, completed-family, half-sandwich, recurrence, Chernoff, and final
pasting steps, and the scalar masses they compare. This is the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Statements.lean` in the port of
`planning/c6b-plan.md` (milestone M11, section "Port conventions").

A strategy is a `SymStrat params.next 𝔓 K` and a slice family an `IdxPolyFamily params 𝔓`, with
local operators in `𝔓` (the vendored `Op ι`). The vendored second bipartite state
`ψbi : QuantumState (ι × ι)` (passed as `strategy.state` by every vendored caller) both places
the families and evaluates them here, so it is the symmetric model `S : SymModel 𝔓 K`, in the
vendored argument position; the placed families of `Co/Pasting/Defs/Families.lean`,
`Co/Pasting/Sandwich/Switcheroo.lean` and `Co/Pasting/Sandwich/GHatSandwich.lean` take it as their
first explicit argument. The one-space state of `ChernoffBernoulliMatrixStatement`, which
evaluates an operator `X` on its own space, is a vector state `V : VecState K` with
`X : K →L[ℂ] K`. Errors are in `ℝ` (the vendored `Error`).

The displayed error terms are classical (they mention no state, operator or measurement), so
they are not ported: this file imports the vendored file and names them through an explicit
`open MIPStarRE.LDT.Pasting (…)` list.

## Not ported

- `ldPastingCompletenessLowerBound`: classical, imported.
- `commutativitySwitcherooError`: classical, imported.
- `commutingWithGCompleteError`: classical, imported.
- `commutingWithGIncompleteError`: classical, imported.
- `pairwiseCompletePartCommutationError`: classical, imported.
- `gHatSelfConsistencyError`: classical, imported.
- `gHatCommutationError`: classical, imported.
- `commuteGHalfSandwichError`: classical, imported.
- `ldSandwichLineOnePointError`: classical, imported.
- `hBConsistencyError`: classical, imported.
- `overAllOutcomesError`: classical, imported.
- `fromHToGError`: classical, imported.
- `fromHToGRecurrenceError`: classical, imported.
- `fromHToGPaperTotalError`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel Fq Point PointTuple uniformDistribution)
open MIPStarRE.LDT.MainInductionStep (ldPastingInInductionError ldPastingInInductionNu)
open MIPStarRE.LDT.Pasting (GHatType SliceQuestion SlicePairQuestion SandwichedLineQuestion
  VerticalLineQuestion ldPastingCompletenessLowerBound commutativitySwitcherooError
  commutingWithGCompleteError commutingWithGIncompleteError pairwiseCompletePartCommutationError
  gHatSelfConsistencyError gHatCommutationError commuteGHalfSandwichError
  ldSandwichLineOnePointError hBConsistencyError overAllOutcomesError fromHToGError)
open MIPRE.LIDT.Co (SymModel VecState SymStrat SubMeas Measurement IdxSubMeas IdxProjSubMeas
  IdxProjMeas OpFamily IdxPolyFamily polynomialEvaluationFamily)
open MIPRE.LIDT.Co.CommutativityPoints (orderedProductOpFamily reversedProductOpFamily)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Paper origin: `references/ldt-paper/ld-pasting.tex:12-50`
(`\label{thm:ld-pasting}`), conclusion in `\label{item:ld-pasting-N-consistency}`
(lines 45-49).

Analytic conclusion for `thm:ld-pasting` once a witness `H` has been fixed.

The theorem `ldPastingNontrivial` separately records that the chosen witness is the
canonical construction `constructedPastedMeasurement params family k`, so this
structure stores only the quantitative conclusion from the paper. -/
structure LdPastingConclusion (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (H : Measurement (MIPStarRE.LDT.Polynomial params.next) 𝔓)
    (eps delta gamma kappa zeta : ℝ) (k : ℕ) : Prop where
  -- Naming note: this is not a `ν` field from the paper. The point-consistency
  -- bound here continues to use the induction-section error term, while `ν`
  -- tracks the completeness loss below.
  /-- The pasted measurement is point-consistent with the strategy. -/
  pointConsistency :
    strategy.state.ConsRel (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params.next H.toSubMeas)
      (ldPastingInInductionError params k eps delta gamma kappa zeta)

/-- Paper origin: `references/ldt-paper/ld-pasting.tex:118-131`
(`\label{lem:ld-pasting-sub-measurement}`).

Analytic conclusion for `lem:ld-pasting-sub-measurement` once a witness `H`
has been fixed.

The theorem `ldPastingSubMeas` separately records that the chosen witness is the
canonical construction `constructedPastedSubMeas params family k`, so this
structure stores only the quantitative properties proved about that witness. -/
structure LdPastingSubMeasConclusion (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (H : SubMeas (MIPStarRE.LDT.Polynomial params.next) 𝔓)
    (eps delta gamma kappa zeta : ℝ) (k : ℕ) : Prop where
  -- Naming note: this is not a `ν` field from the paper. The point-consistency
  -- bound here is the paper's intermediate `ν`, while the completeness field
  -- carries the missing-mass term needed for the final `σ` after completion.
  /-- The pasted submeasurement is point-consistent with the strategy. -/
  pointConsistency :
    strategy.state.ConsRel (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params.next H)
      (ldPastingInInductionNu params k eps delta gamma zeta)
  /-- The pasted submeasurement is almost complete. -/
  completeness :
    strategy.state.CompletenessAtLeast (H.liftLeft strategy.state)
      (ldPastingCompletenessLowerBound params kappa
        (ldPastingInInductionNu params k eps delta gamma zeta) k)

/-- Paper origin: `references/ldt-paper/ld-pasting.tex:514-536`
(`\label{lem:g-complete-self-consistency}`); the `\widehat G` rewrite at
`eq:gselfconall` (`references/ldt-paper/ld-pasting.tex:821`) is the family of
self-consistency bounds compared against here.

Lean statement for `lem:g-complete-self-consistency`.
`S` is the vendored bipartite state `ψbi` (passed as `strategy.state` by callers). -/
structure GCompleteSelfConsistencyStatement (params : Parameters)
    [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (zeta : ℝ) : Prop where
  /--
  Stores self-consistency of the full slice family `family.meas` because the
  `cor:G-hat-facts` decomposition expands `\widehat G` self-consistency into the
  original slice-family term plus the incomplete part, not the postprocessed
  complete-part family.
  -/
  completePartSelfConsistency :
    S.SDDRel
      (uniformDistribution (SliceQuestion params))
      (IdxSubMeas.liftLeft S (IdxProjSubMeas.toIdxSubMeas family.meas))
      (IdxSubMeas.liftRight S (IdxProjSubMeas.toIdxSubMeas family.meas))
      zeta

/-- Paper origin: `references/ldt-paper/ld-pasting.tex:537-558`
(`\label{cor:g-bot-self-consistency}`); incomplete-part complement of
`\label{lem:g-complete-self-consistency}` and the
`eq:gselfconall` self-consistency family at line 821.

Lean statement for `cor:g-bot-self-consistency`. -/
structure GBotSelfConsistencyStatement (params : Parameters)
    [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (zeta : ℝ) : Prop where
  /-- The incomplete parts `G^x_⊥` are self-consistent. -/
  incompletePartSelfConsistency :
    S.SDDRel
      (uniformDistribution (SliceQuestion params))
      (incompletePartLeftFamily S params family)
      (incompletePartRightFamily S params family)
      zeta

/-- Paper origin: `references/ldt-paper/ld-pasting.tex:560-720`
(`\label{lem:commutativity-switcheroo}`).

Lean statement for `lem:commutativity-switcheroo`. -/
structure CommutativitySwitcherooStatement {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓)
    (zeta omega chi : ℝ) : Prop where
  /-- The aggregate `G^x M^y` and `M^y G^x` families are close. -/
  aggregateCommutation :
    S.SDDOpRel
      (uniformDistribution (SlicePairQuestion params))
      (switcherooAggregateLeft S params family M)
      (switcherooAggregateRight S params family M)
      (commutativitySwitcherooError zeta omega chi)

/-- Paper origin: `references/ldt-paper/ld-pasting.tex:721-774`
(`\label{cor:commuting-with-G-complete}`).

Lean statement for `cor:commuting-with-G-complete`. -/
structure CommutingWithGCompleteStatement (params : Parameters)
    [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (gamma zeta : ℝ) : Prop where
  /-- The slice measurements `G^x`, `G^y` approximately commute. -/
  pairwiseCompletePartCommutation :
    S.SDDOpRel
      (uniformDistribution (SlicePairQuestion params))
      (fun q =>
        OpFamily.leftPlacedOpFamily S <|
          orderedProductOpFamily
            ((family.meas q.1).toSubMeas)
            ((family.meas q.2).toSubMeas))
      (fun q =>
        OpFamily.leftPlacedOpFamily S <|
          reversedProductOpFamily
            ((family.meas q.1).toSubMeas)
            ((family.meas q.2).toSubMeas))
      (pairwiseCompletePartCommutationError params gamma zeta)
  /-- The slice outcomes `G^x_g` approximately commute with the complete parts `G^y`. -/
  pointWithCompletePartCommutation :
    S.SDDOpRel
      (uniformDistribution (SlicePairQuestion params))
      (completePartPointProductLeft S params family)
      (completePartPointProductRight S params family)
      (commutingWithGCompleteError params gamma zeta)
  /-- The complete parts `G^x`, `G^y` approximately commute. -/
  completePartCommutation :
    S.SDDOpRel
      (uniformDistribution (SlicePairQuestion params))
      (completePartTotalProductLeft S params family)
      (completePartTotalProductRight S params family)
      (commutingWithGCompleteError params gamma zeta)

/-- Paper origin: `references/ldt-paper/ld-pasting.tex:775-816`
(`\label{cor:commuting-with-G-incomplete}`).

Lean statement for `cor:commuting-with-G-incomplete`. -/
structure CommutingWithGIncompleteStatement (params : Parameters)
    [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (gamma zeta : ℝ) : Prop where
  /-- The slice outcomes `G^x_g` approximately commute with the incomplete parts `G^y_⊥`. -/
  pointWithIncompletePartCommutation :
    S.SDDOpRel
      (uniformDistribution (SlicePairQuestion params))
      (incompletePartPointProductLeft S params family)
      (incompletePartPointProductRight S params family)
      (commutingWithGIncompleteError params gamma zeta)
  /-- The incomplete parts `G^x_⊥`, `G^y_⊥` approximately commute. -/
  incompletePartCommutation :
    S.SDDOpRel
      (uniformDistribution (SlicePairQuestion params))
      (incompletePartTotalProductLeft S params family)
      (incompletePartTotalProductRight S params family)
      (commutingWithGIncompleteError params gamma zeta)

/-- Paper origin: `references/ldt-paper/ld-pasting.tex:817-862`
(`\label{cor:G-hat-facts}`); the displayed `\widehat G` self-consistency and
commutation lines `eq:gselfconall` and `eq:gcomall` are at lines 821 and 823.

Lean statement for `cor:G-hat-facts`. -/
structure GHatFactsStatement (params : Parameters)
    [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (gamma zeta : ℝ) : Prop where
  /-- The completed slice measurements `\widehat G^x` are self-consistent. -/
  completedSelfConsistency :
    S.SDDRel
      (uniformDistribution (SliceQuestion params))
      (gHatSelfConsistencyLeftFamily S params family)
      (gHatSelfConsistencyRightFamily S params family)
      (gHatSelfConsistencyError zeta)
  /-- The completed slice measurements `\widehat G^x`, `\widehat G^y` approximately commute. -/
  completedCommutation :
    S.SDDOpRel
      (uniformDistribution (SlicePairQuestion params))
      (gHatPairProductLeft S params family)
      (gHatPairProductRight S params family)
      (gHatCommutationError params gamma zeta)

/-- Paper origin: `references/ldt-paper/ld-pasting.tex:872-917`
(`\label{lem:commute-g-half-sandwich}`).

Lean statement for `lem:commute-g-half-sandwich`. -/
structure CommuteGHalfSandwichStatement (params : Parameters)
    [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (gamma zeta : ℝ) (k : ℕ) : Prop where
  /-- The half-sandwich product and its cyclic rotation are close. -/
  repeatedCommutation :
    S.SDDOpRel
      (uniformDistribution (PointTuple params k))
      (gHatHalfSandwichLeft S params family k)
      (gHatHalfSandwichRight S params family k)
      (commuteGHalfSandwichError params gamma zeta k)

/-- Paper origin: `references/ldt-paper/ld-pasting.tex:918-1040`
(`\label{lem:ld-sandwich-line-one-point}`).

Lean statement for `lem:ld-sandwich-line-one-point`. -/
structure LdSandwichLineOnePointStatement (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (eps delta gamma zeta : ℝ)
    (k i : ℕ) : Prop where
  /-- The `i`-th sandwiched slice value agrees with the vertical line measurement. -/
  linePointComparison :
    strategy.state.ConsRel
      (uniformDistribution (SandwichedLineQuestion params k))
      (ldSandwichLineOnePointLeftFamily params strategy family k i)
      (ldSandwichLineOnePointRightFamily params strategy family k i)
      (ldSandwichLineOnePointError params eps delta gamma zeta k)

/-- Paper origin: `references/ldt-paper/ld-pasting.tex:1041-1140`
(`\label{lem:h-b-consistency}`).

Lean statement for `lem:h-b-consistency`. -/
structure HBConsistencyStatement (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (eps delta gamma zeta : ℝ) (k : ℕ) : Prop where
  /-- The pasted submeasurement restricted to vertical lines agrees with the line
  measurement. -/
  lineConsistency :
    strategy.state.ConsRel
      (uniformDistribution (VerticalLineQuestion params))
      (hRestrictionToVerticalLine params
        (constructedPastedSubMeas params family k))
      (verticalLineMeasurementFamily params strategy)
      (hBConsistencyError params eps delta gamma zeta k)

/-- Scalar expectation of the pasted submeasurement mass appearing on the
left-hand side of `lem:over-all-outcomes`. -/
noncomputable def overAllOutcomesPastedMass (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (k : ℕ) : ℝ :=
  strategy.state.subMeasMass ((constructedPastedSubMeas params family k).liftLeft strategy.state)

/-- Scalar expectation of the all-outcomes expansion on the right-hand side of
`lem:over-all-outcomes`. -/
noncomputable def overAllOutcomesExpansionMass (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (k : ℕ) : ℝ :=
  strategy.state.subMeasMass ((IdxSubMeas.liftLeft strategy.state
    (allOutcomesExpansionFamily params strategy family k)) ())

/-- Paper origin: `references/ldt-paper/ld-pasting.tex:1141-1294`
(`\label{lem:over-all-outcomes}`).

Lean statement for `lem:over-all-outcomes`.

The paper's displayed statement is a scalar approximation of expectation values,
not a stronger `≈_δ` relation between already-collapsed `Unit`-indexed
submeasurements.  Accordingly, this structure stores only the absolute-value bound
between the pasted mass and the all-outcomes expansion mass. -/
structure OverAllOutcomesStatement (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (eps delta gamma zeta : ℝ) (k : ℕ) : Prop where
  /-- The pasted mass is close to the all-outcomes expansion mass. -/
  totalOutcomeExpansion :
    |overAllOutcomesPastedMass params strategy family k -
        overAllOutcomesExpansionMass params strategy family k| ≤
      overAllOutcomesError params eps delta gamma zeta k

/-- Scalar expectation of one per-tail contribution in `lem:from-H-to-G`.

This is the single-`τ_{≥ℓ}` term appearing inside the aggregate stage mass from
`references/ldt-paper/ld-pasting.tex`, equation
`eq:i-think-this-is-what-i'm-supposed-to-prove-2` (lines 1386–1391).
The parameter `prefixLen` is the Lean 0-based stage index. In the ambient
`k`-step recurrence, the remaining tail length is `tailLen = k - prefixLen`. -/
noncomputable def fromHToGTailStageMass (params : Parameters)
    [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (prefixLen : ℕ) {tailLen : ℕ} (τtail : GHatType tailLen) : ℝ :=
  S.ev (((fromHToGTailStageFamily S params family prefixLen τtail) ()).total)

/-- Scalar expectation of the full Lean stage-`ℓ` quantity from `lem:from-H-to-G`.

This is the aggregate quantity displayed in
`references/ldt-paper/ld-pasting.tex`, equation
`eq:i-think-this-is-what-i'm-supposed-to-prove-2` (lines 1386–1391).
Lean uses 0-based indexing: stage `ℓ` here corresponds to the paper's stage
`ℓ + 1`, so the remaining tail has length `k - ℓ`. Accordingly, this sums over
all remaining tail types `τ_{≥ℓ} ∈ {0,1}^{k-ℓ}`, while the next Lean stage
`ℓ + 1` sums over the shorter tails `τ_{>ℓ}`. -/
noncomputable def fromHToGStageMass (params : Parameters)
    [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (k ℓ : ℕ) : ℝ :=
  ∑ τtail : GHatType (k - ℓ),
    fromHToGTailStageMass params S family ℓ τtail

/-- Scalar expectation of the left-hand side of `lem:from-H-to-G`, i.e. the
uniform average of the eligible pasted-sandwich total mass. -/
noncomputable def fromHToGAllOutcomesMass (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (k : ℕ) : ℝ :=
  S.subMeasMass ((IdxSubMeas.liftLeft S
    (allOutcomesExpansionFamily params strategy family k)) ())

/-- Scalar expectation of the Bernoulli-tail polynomial `F(G)` on the bipartite
state from `lem:from-H-to-G`. -/
noncomputable def fromHToGBernoulliTailMass (params : Parameters)
    [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (k : ℕ) : ℝ :=
  S.subMeasMass ((IdxSubMeas.liftRight S
    (bernoulliTailFromFamily params family k)) ())

/-- Paper origin: `references/ldt-paper/ld-pasting.tex:1295-1670`
(`\label{lem:from-H-to-G}`).

Lean statement for `lem:from-H-to-G`.

The paper's displayed statement is a scalar approximation of expectation values,
not a new `≈_δ` relation between submeasurements.  Accordingly, this statement
stores only the final all-outcomes vs. Bernoulli-tail comparison; the
adjacent-stage estimates are recorded by the internal construction lemmas. -/
structure FromHToGStatement (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (gamma zeta : ℝ) (k : ℕ) : Prop where
  /-- The all-outcomes mass is close to the Bernoulli-tail mass. -/
  bernoulliPolynomialRewrite :
    |fromHToGAllOutcomesMass params strategy S family k -
        fromHToGBernoulliTailMass params S family k| ≤
      fromHToGError params gamma zeta k

/-- Paper origin: `references/ldt-paper/ld-pasting.tex:1671-1798`
(`\label{lem:chernoff-bernoulli-matrix}`); the operator-Chernoff inequality is
proved by applying continuous functional calculus to the scalar tail polynomial
and the scalar Chernoff bound `eq:by-chernoff` at line 1739.

Lean statement for `lem:chernoff-bernoulli-matrix`. The vendored one-space state
`ψ : QuantumState ι` and operator `X : Op ι` are a vector state `V : VecState K` and an
operator `X : K →L[ℂ] K`. -/
structure ChernoffBernoulliMatrixStatement
    (V : VecState K)
    (theta : ℝ) (k degree : ℕ) (X : K →L[ℂ] K) (kappa : ℝ)
    (hXpsd : 0 ≤ X)
    (hXleOne : X ≤ 1) : Prop where
  /-- The Bernoulli-tail submeasurement of `X` is almost complete. -/
  matrixTailBound :
    V.CompletenessAtLeast
      (bernoulliTailSubMeas k degree X hXpsd hXleOne)
      (1 - kappa / (1 - theta) - Real.exp (-((theta ^ (2 : ℕ)) * (k : ℝ)) / 2))

/-- Paper origin: `references/ldt-paper/ld-pasting.tex:1799-1849`
(`\label{cor:ld-pasting-N-completeness}`).

Lean statement for `cor:ld-pasting-N-completeness`. -/
structure LdPastingNCompletenessStatement (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (kappa nu : ℝ) (k : ℕ) : Prop where
  /-- The constructed pasted submeasurement is almost complete. -/
  completenessBound :
    strategy.state.CompletenessAtLeast
      ((constructedPastedSubMeas params family k).liftLeft strategy.state)
      (ldPastingCompletenessLowerBound params kappa nu k)

end MIPRE.LIDT.Co.Pasting

end

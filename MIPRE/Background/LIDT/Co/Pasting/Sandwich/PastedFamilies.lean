/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/Sandwich/
PastedFamilies.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Basic.SubMeasurementFamilies
public import MIPRE.Background.LIDT.Co.CommutativityPoints.Approximation
public import MIPRE.Background.LIDT.Co.Pasting.Sandwich.GHatSandwich
public import MIPRE.Background.LIDT.Co.Preliminaries.Defs
public import MIPRE.Background.LIDT.Co.Test.StrategyCore
public import MIPRE.Background.LIDT.MIPStarRE.LDT.Pasting.Sandwich.PastedFamilies

@[expose] public section

/-!
# Section 12 — Sandwich constructions: pasted families

Pasted interpolation families, recurrence weights, and final operator families: the counterpart
of `MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Sandwich/PastedFamilies.lean` in the port of
`planning/c6b-plan.md` (milestone M11, section "Port conventions").

The slice family is an `IdxPolyFamily params 𝔓` and a strategy a `SymStrat params.next 𝔓 K`, so
the pasted, sandwiched, vertical-line and Bernoulli-tail families are local families in `𝔓`
(the vendored `Op ι`). Definitions that read no state and no slice family
(`hRestrictionToVerticalLine`, `pastedMeasurementTotal`) are generic over an ordered `⋆`-ring,
and the Bernoulli-tail submeasurement over any C*-algebra with its order, as the positivity
lemmas of `Co/Pasting/Sandwich/GHatSandwich.lean` are, so that it serves `𝔓` and `K →L[ℂ] K`
alike. The one placed family, `fromHToGTailStageFamily`, takes the symmetric model
`S : SymModel 𝔓 K` as its first explicit argument, in place of the vendored named carriers
`(ι₂ := ι)`, `(ι₁ := ι)`, and its operator `S.L (…) * S.R (…)` is the vendored
`leftTensor (…) * rightTensor (…)`.

## Not ported

- `pastedFallbackOutcome`: classical, imported.
- `verticalLine_pointAt_appendPoint`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel Fq Point PointTuple AxisParallelLine
  AxisLinePolynomial appendPoint truncatePoint pointHeight zeroCoord lastCoord
  uniformDistribution uniformDistribution_weight_sum_le_one)
open MIPStarRE.LDT.Pasting (GHatType GHatTupleOutcome SandwichedLineQuestion
  VerticalLineQuestion IsGloballyConsistent interpolateCompletedSlices distinctTupleDistribution
  distinctTupleDistribution_weight_sum_le_one outcomesByType pastedFallbackOutcome)
open MIPRE.LIDT.Co (SymModel SymStrat SubMeas Measurement IdxSubMeas OpFamily IdxOpFamily
  IdxPolyFamily postprocess averageIdxSubMeas constSubMeasFamily evaluateAt)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Source-style recurrence weight `S_{τtail}` from `lem:from-H-to-G`.

The parameter `prefixLen` is the number of type bits already converted into the
Bernoulli polynomial.  This is exactly `truncatedTypeSums` specialized to the
averaged complete operator `G = E_x ∑_g G^x_g`. -/
noncomputable def fromHToGRecurrenceWeight (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) (prefixLen : ℕ) {tailLen : ℕ}
    (τtail : GHatType tailLen) : 𝔓 :=
  truncatedTypeSums family.averagedSubMeas.total params.d prefixLen τtail

/-- The interpolated operator `H^{x_1,\dots,x_k}_h` restricted to tuples that are
globally consistent with a single polynomial.

The paper's definition (`references/ldt-paper/ld-pasting.tex` lines 474–495) sums
only tuples `(g_1,…,g_k)` in `Global_τ(x)` — those consistent with a single
polynomial `h` — and then interpolates. The `|τ| ≥ d+1` eligibility filter is
applied by `interpolationEligibleSandwichFamily`; this definition additionally
restricts to globally consistent tuples via `IsGloballyConsistent`.
Consequently, `pastedInterpolationFamily` is supported only on tuples satisfying
both restrictions, and any fallback or default value in
`interpolateCompletedSlices` is irrelevant off that restricted support. -/
noncomputable def pastedInterpolationFamily (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) (k : ℕ) :
    IdxSubMeas (PointTuple params k) (MIPStarRE.LDT.Polynomial params.next) 𝔓 :=
  fun xs =>
    postprocess
      (restrictSubMeas
        (interpolationEligibleSandwichFamily params family k xs)
        (IsGloballyConsistent params xs))
      (interpolateCompletedSlices params k xs)

/-- The averaged sandwiched family restricted to outcome tuples of type `τ`
with `|τ| ≥ d+1`, as in `lem:over-all-outcomes`. -/
noncomputable def averagedEligibleSandwichSubMeas (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) (k : ℕ) :
    SubMeas (GHatTupleOutcome params k) 𝔓 :=
  averageIdxSubMeas
    (uniformDistribution (PointTuple params k))
    (interpolationEligibleSandwichFamily params family k)
    (uniformDistribution_weight_sum_le_one (PointTuple params k))

/-- The specific pasted submeasurement constructed from the sandwich/interpolation scheme. -/
noncomputable def constructedPastedSubMeas (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) (k : ℕ) :
    SubMeas (MIPStarRE.LDT.Polynomial params.next) 𝔓 :=
  averageIdxSubMeas
    (distinctTupleDistribution params k)
    (pastedInterpolationFamily params family k)
    (distinctTupleDistribution_weight_sum_le_one params k)

/-- The specific pasted measurement obtained by completing the constructed pasted submeasurement.

The paper adds all missing mass `I - H_total` to a single distinguished polynomial
outcome `h₀` (the fallback interpolant).  So the outcome operator for `h₀` becomes
`H_{h₀} + (I - H_total)` while all other outcomes keep their original operators, and
the total is genuinely the identity `I`. -/
noncomputable def constructedPastedMeasurement (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) (k : ℕ) :
    Measurement (MIPStarRE.LDT.Polynomial params.next) 𝔓 :=
  Preliminaries.completeAtOutcome
    (constructedPastedSubMeas params family k)
    (pastedFallbackOutcome params)

/-- Degree-zero candidate pasted submeasurement obtained by averaging the slice
family and viewing each slice polynomial as a polynomial in one more variable.

Paper origin: `references/ldt-paper/ld-pasting.tex:12-55`.  This is a
Lean-only construction for the `d = 0` branch of `thm:ld-pasting`, where the
ordinary interpolation construction is not available because `d + 1 = 1`
collapses the distinct-height argument.  It introduces no additional
hypothesis. -/
noncomputable def averagedSliceAppendedSubMeas (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) : SubMeas (MIPStarRE.LDT.Polynomial params.next) 𝔓 :=
  postprocess family.averagedSubMeas
    (fun g => MIPStarRE.LDT.Polynomial.appendAtHeight params g zeroCoord)

/-- Evaluating the averaged appended-slice submeasurement at a next-level point
is the same as evaluating the averaged slice family at the truncated point.

This is the first formal step in the degree-zero branch of `thm:ld-pasting`;
the later consistency rectangle compares this averaged slice construction with
the point measurement. -/
theorem evaluateAt_averagedSliceAppendedSubMeas
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) (u : Point params.next) :
    evaluateAt params.next u (averagedSliceAppendedSubMeas params family) =
      evaluateAt params (truncatePoint params u) family.averagedSubMeas := by
  have hpoint :
      appendPoint params (truncatePoint params u) (pointHeight params u) = u :=
    (MIPStarRE.LDT.CommutativityPoints.pointNextEquiv params).left_inv u
  have h := evaluateAt_postprocess_appendAtHeight_appendPoint params family.averagedSubMeas
    zeroCoord (truncatePoint params u) (pointHeight params u)
  rw [hpoint] at h
  exact h

/-- Placeholder family for the vertical axis-parallel line measurement `B^u_f`. -/
noncomputable def verticalLineMeasurementFamily (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) :
    IdxSubMeas (VerticalLineQuestion params) (AxisLinePolynomial params.next) 𝔓 :=
  fun u =>
    let ℓ : AxisParallelLine params.next :=
      { base := appendPoint params u zeroCoord
        direction := lastCoord params }
    (strategy.axisParallelMeasurement ℓ).toSubMeas

/-- Pull back the vertical-line answer family along `truncatePoint`, then read
its line polynomial at the lifted point's final coordinate. -/
noncomputable def liftedVerticalLineAnswerFamily
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) :
    IdxSubMeas (Point params.next) (Fq params) 𝔓 :=
  fun u =>
    postprocess
      (verticalLineMeasurementFamily params strategy (truncatePoint params u))
      (fun f => f (pointHeight params u))

/-- In degree zero, the lifted vertical-line answer family is independent of
the height coordinate once the old point coordinates are fixed.

Lean-only helper for the degree-zero branch of `thm:ld-pasting`; it formalizes
the fact that a vertical line answer of degree zero is constant in the line
parameter.  The source context is `references/ldt-paper/ld-pasting.tex:12-55`. -/
theorem liftedVerticalLineAnswerFamily_eq_of_same_truncate_degree_zero
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (hd : params.d = 0)
    {u v : Point params.next} (hbase : truncatePoint params u = truncatePoint params v) :
    liftedVerticalLineAnswerFamily params strategy u =
      liftedVerticalLineAnswerFamily params strategy v := by
  unfold liftedVerticalLineAnswerFamily
  rw [hbase]
  congr
  funext f
  exact AxisLinePolynomial.apply_eq_apply_of_degree_zero f hd
    (pointHeight params u) (pointHeight params v)

/-- Explicit value extracted from the `i`-th genuine slice outcome at the test point.

The paper's one-point sandwich comparison only sums over tuples with
`g_i ≠ ⊥`; the `none` mass is therefore removed before postprocessing. -/
noncomputable def ldSandwichLineOnePointLeftFamily (params : Parameters) [FieldModel params.q]
    (_strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (k i : ℕ) : IdxSubMeas (SandwichedLineQuestion params k) (Option (Fq params)) 𝔓 :=
  fun q =>
    postprocess
      (restrictSubMeas (gHatSandwichFamily params family k q.2)
        (fun gs => if h : i < k then (gs ⟨i, h⟩).isSome = true else False))
      (fun gs => if h : i < k then Option.map (fun g => g q.1) (gs ⟨i, h⟩) else none)

/-- Explicit value extracted from the vertical line measurement `B^u` at the slice height `x_i`. -/
noncomputable def ldSandwichLineOnePointRightFamily (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (_family : IdxPolyFamily params 𝔓)
    (k i : ℕ) : IdxSubMeas (SandwichedLineQuestion params k) (Option (Fq params)) 𝔓 :=
  fun q =>
    postprocess (verticalLineMeasurementFamily params strategy q.1) (fun f =>
      if h : i < k then
        some (f (q.2 ⟨i, h⟩))
      else
        none)

section Generic

variable {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]

/-- Restrict a global polynomial-valued submeasurement to the vertical line through `u`. -/
noncomputable def hRestrictionToVerticalLine (params : Parameters) [FieldModel params.q]
    (H : SubMeas (MIPStarRE.LDT.Polynomial params.next) R) :
    IdxSubMeas (VerticalLineQuestion params) (AxisLinePolynomial params.next) R :=
  fun u =>
    let verticalLine : AxisParallelLine params.next :=
      { base := appendPoint params u zeroCoord
        direction := ⟨params.m, Nat.lt_succ_self params.m⟩ }
    postprocess H (fun h =>
      MIPStarRE.LDT.Polynomial.restrictToAxisParallelLine params.next h verticalLine)

/-- Collapse a submeasurement to its `Unit`-valued total operator. -/
noncomputable def pastedMeasurementTotal {α : Type*} [Fintype α] (H : SubMeas α R) :
    IdxSubMeas Unit Unit R :=
  constSubMeasFamily (postprocess H (fun _ => ()))

end Generic

/-- The expansion over all outcome types `τ`, written as the
total mass of the averaged sandwich family restricted to `|τ| ≥ d+1`. -/
noncomputable def allOutcomesExpansionFamily (params : Parameters) [FieldModel params.q]
    (_strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (k : ℕ) :
    IdxSubMeas Unit Unit 𝔓 :=
  pastedMeasurementTotal (averagedEligibleSandwichSubMeas params family k)

section Bernoulli

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The one-outcome submeasurement whose unique effect is the Bernoulli-tail
operator of `X`. -/
noncomputable def bernoulliTailSubMeas (k degree : ℕ) (X : A)
    (hXpsd : 0 ≤ X) (hXleOne : X ≤ 1) : SubMeas Unit A :=
  SubMeas.singleOutcome (bernoulliTailOperator k degree X)
    (bernoulliTailOperator_nonneg k degree X hXpsd hXleOne)
    (bernoulliTailOperator_le_one k degree X hXpsd hXleOne)

/-- The unique outcome of the Bernoulli-tail submeasurement is the Bernoulli-tail operator. -/
@[simp] theorem bernoulliTailSubMeas_outcome (k degree : ℕ) (X : A)
    (hXpsd : 0 ≤ X) (hXleOne : X ≤ 1) (u : Unit) :
    (bernoulliTailSubMeas k degree X hXpsd hXleOne).outcome u =
      bernoulliTailOperator k degree X :=
  rfl

/-- The total of the Bernoulli-tail submeasurement is the Bernoulli-tail operator. -/
@[simp] theorem bernoulliTailSubMeas_total (k degree : ℕ) (X : A)
    (hXpsd : 0 ≤ X) (hXleOne : X ≤ 1) :
    (bernoulliTailSubMeas k degree X hXpsd hXleOne).total =
      bernoulliTailOperator k degree X :=
  rfl

end Bernoulli

/-- The Bernoulli-tail polynomial in the averaged complete operator `G = E_x \sum_g G^x_g`. -/
noncomputable def bernoulliTailFromFamily (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) (k : ℕ) :
    IdxSubMeas Unit Unit 𝔓 :=
  constSubMeasFamily <|
    bernoulliTailSubMeas k params.d (IdxPolyFamily.averagedSubMeas family).total
      (IdxPolyFamily.averagedSubMeas family).total_nonneg
      (IdxPolyFamily.averagedSubMeas family).total_le_one

/-- Average the sandwiched completed-slice family over tuples whose completed/
incomplete pattern is exactly `τtail`.

This is the paper's operator
$$
\mathbb E_{x_{\ge \ell}} \sum_{g_{\ge \ell} \in \mathsf{Outcomes}_{\tau_{\ge \ell}}}
  \widehat H^{x_{\ge \ell}}_{g_{\ge \ell}},
$$
written in the existing `SubMeas Unit` API so that its total operator is the
relevant suffix-stage operator.  Unlike the old `fromHToG` recurrence families,
this keeps the `\widehat H^{x_{\ge \ell}}_{g_{\ge \ell}}` suffix visible instead
of collapsing immediately to the full `k`-step total mass.

When this is used in `fromHToG`, the suffix length is `tailLen = k - ℓ`, and
the expectation is the paper's independent uniform average over the remaining
slice points `x_{≥ℓ}`. -/
noncomputable def averagedSandwichByTypeSubMeas (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) (tailLen : ℕ) (τtail : GHatType tailLen) :
    SubMeas Unit 𝔓 :=
  open Classical in
    averageIdxSubMeas
      (uniformDistribution (PointTuple params tailLen))
      (fun xs =>
        postprocess
          (restrictSubMeas
            (gHatSandwichFamily params family tailLen xs)
            (fun gs => gs ∈ outcomesByType τtail))
          (fun _ => ()))
      (uniformDistribution_weight_sum_le_one (PointTuple params tailLen))

/-- The stage-`ℓ` suffix family from the proof of `lem:from-H-to-G`, for a fixed
remaining tail type `τ_{≥ℓ}`.

This is the operator-valued quantity displayed termwise in
`references/ldt-paper/ld-pasting.tex`, equation
`eq:i-think-this-is-what-i'm-supposed-to-prove-2` (lines 1386–1391).
The parameter `prefixLen` is the Lean 0-based stage index. In the ambient
`k`-step recurrence where this family is used, the remaining tail length is
`tailLen = k - prefixLen`, so Lean stage `prefixLen` corresponds to the paper's
stage `prefixLen + 1`.

Concretely, this records
$$
\mathbb E_{x_{\ge \ell}} \sum_{g_{\ge \ell} \in \mathsf{Outcomes}_{\tau_{\ge \ell}}}
  \widehat H^{x_{\ge \ell}}_{g_{\ge \ell}} \otimes S_{\tau_{\ge \ell}},
$$
the tensor product being `S.L (…) * S.R (…)` in the symmetric model `S`. -/
noncomputable def fromHToGTailStageFamily (S : SymModel 𝔓 K) (params : Parameters)
    [FieldModel params.q] (family : IdxPolyFamily params 𝔓) (prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    IdxOpFamily Unit Unit (K →L[ℂ] K) :=
  fun _ =>
    let base := averagedSandwichByTypeSubMeas params family tailLen τtail
    let weight := fromHToGRecurrenceWeight params family prefixLen τtail
    { outcome := fun _ => S.L base.total * S.R weight
      total := S.L base.total * S.R weight }

end MIPRE.LIDT.Co.Pasting

end

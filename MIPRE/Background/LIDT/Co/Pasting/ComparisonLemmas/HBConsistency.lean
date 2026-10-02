/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/
ComparisonLemmas/HBConsistency.lean, to the symmetric model of `planning/c6b-plan.md`; not a
vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.ComparisonLemmas.LdSandwichLineOnePoint.Core
public import MIPRE.Background.LIDT.Co.Pasting.ComparisonLemmas.LineInterpolation.HBError

@[expose] public section

/-!
# Section 12 pasting: H-B consistency

The aggregation theorem proving `lem:h-b-consistency` from the one-point line consistency
statements: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/ComparisonLemmas/HBConsistency.lean` in the port of
`planning/c6b-plan.md` (milestone M11, section "Port conventions").

A strategy is a `SymStrat params.next 𝔓 K` and the slice family an `IdxPolyFamily params 𝔓`;
the consistency statement is a `ConsRel` on `strategy.state`. The fixed-`u` defect, its
comparison with the bad mass and the aggregation of the one-point line estimates are the lemmas
of `Co/.../LineInterpolation/HBError.lean`; the nonnegativity of `ε`, `δ` and `ζ` is read off the
hypotheses through `S.bipartiteConsError_nonneg` and `S.bipartiteSSCError_nonneg`, and that of
`γ`, in `hBConsistency_ofLinePointBounds`, through `gamma_nonneg_of_isGood`. No statement
carries a swap or normalization hypothesis, the vendored statements having none.

## Not ported

Nothing: every vendored declaration has a counterpart of the same name.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel Point AxisParallelTestSample avgOver avgOver_mono
  uniformDistribution)
open MIPStarRE.LDT.Pasting (VerticalLineQuestion distinctTupleDistribution hBConsistencyError)
open MIPRE.LIDT.Co (SymStrat IdxProjMeas IdxPolyFamily gamma_nonneg_of_isGood
  axisParallelPointAnswerFamily axisParallelLineAnswerFamily)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Aggregate one-point consistency bounds over all slice indices,
plus the distinct-tuple approximation error.

Paper reference: `lem:h-b-consistency` proof in `ld-pasting.tex`
lines 1050–1091.

Steps:
1. Expand using degree constraints to find eligible index `i`
2. Switch from independent to distinct samples (`prop:ld-dnoteq`, cost `k²/q`)
3. Union bound over `k` indices, each contributing `ν₅`
4. Total: `k·ν₅ + k²/q ≤ 44k²m(...)` -/
theorem hBConsistency_core_of_axis_self
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma zeta : ℝ)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself_good : strategy.selfConsistencyFailureProbability ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hd : 0 < params.d)
    (family : IdxPolyFamily params 𝔓)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (_hself : family.StronglySelfConsistent strategy.state zeta)
    (_hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hline : ∀ i : ℕ, i < k →
      LdSandwichLineOnePointStatement params strategy family
        eps delta gamma zeta k i) :
    strategy.state.ConsRel
      (uniformDistribution (VerticalLineQuestion params))
      (hRestrictionToVerticalLine params
        (constructedPastedSubMeas params family k))
      (verticalLineMeasurementFamily params strategy)
      (hBConsistencyError params eps delta gamma zeta k) :=
  ⟨calc
    strategy.state.bipartiteConsError
        (uniformDistribution (VerticalLineQuestion params))
        (hRestrictionToVerticalLine params (constructedPastedSubMeas params family k))
        (verticalLineMeasurementFamily params strategy)
      ≤ avgOver (uniformDistribution (Point params)) (fun u =>
          avgOver (distinctTupleDistribution params k) (fun xs =>
            strategy.state.qBipartiteConsDefect
              (hRestrictionToVerticalLine params (pastedInterpolationFamily params family k xs) u)
              (verticalLineMeasurementFamily params strategy u))) :=
        avgOver_mono _ _ _ fun u =>
          hBConsistency_fixed_u_defect_le_avgOver_distinct params strategy family k u
    _ ≤ avgOver (uniformDistribution (Point params)) (fun u =>
          avgOver (distinctTupleDistribution params k) (fun xs =>
            hBConsistencyBadMass params strategy family u xs)) :=
        avgOver_mono _ _ _ fun u =>
          avgOver_distinct_pasted_defect_le_badMass params strategy family u
    _ ≤ hBConsistencyError params eps delta gamma zeta k :=
        avgOver_distinct_badMass_le_hBConsistencyError_ofLinePointBounds
          params strategy family eps delta gamma zeta k hd
          ((strategy.state.bipartiteConsError_nonneg
            (uniformDistribution (AxisParallelTestSample params.next))
            (axisParallelPointAnswerFamily strategy)
            (axisParallelLineAnswerFamily strategy)).trans haxis)
          ((strategy.state.bipartiteSSCError_nonneg
            (uniformDistribution (Point params.next))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)).trans hself_good)
          hgamma_nonneg
          (IdxPolyFamily.zeta_nonneg_of_consistentWithPoints strategy family hcons)
          hline⟩

/-- Internal form of `lem:h-b-consistency` after applying
`lem:ld-sandwich-line-one-point` at each coordinate.

**Source:** The proof in `references/ldt-paper/ld-pasting.tex:1075-1109`
uses the one-point line estimates and then performs the averaging and
distinct-tuple comparison.  The paper-facing theorem `hBConsistency` below
derives the one-point estimates from the source hypotheses. -/
theorem hBConsistency_ofLinePointBounds_of_axis_self
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma zeta : ℝ)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself_good : strategy.selfConsistencyFailureProbability ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hd : 0 < params.d)
    (family : IdxPolyFamily params 𝔓)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hline : ∀ i : ℕ, i < k →
      LdSandwichLineOnePointStatement params strategy family
        eps delta gamma zeta k i) :
    HBConsistencyStatement params strategy family
        eps delta gamma zeta k :=
  ⟨hBConsistency_core_of_axis_self params strategy eps delta gamma zeta
    haxis hself_good hgamma_nonneg hd family hcons hself hbound k hline⟩

/-- `lem:h-b-consistency` for a good strategy, from the one-point line estimates. -/
theorem hBConsistency_ofLinePointBounds
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma zeta : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (hd : 0 < params.d)
    (family : IdxPolyFamily params 𝔓)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hline : ∀ i : ℕ, i < k →
      LdSandwichLineOnePointStatement params strategy family
        eps delta gamma zeta k i) :
    HBConsistencyStatement params strategy family
        eps delta gamma zeta k :=
  hBConsistency_ofLinePointBounds_of_axis_self params strategy eps delta gamma zeta
    hgood.axisParallelTest hgood.selfConsistencyTest
    (gamma_nonneg_of_isGood params.next strategy hgood) hd family hcons hself hbound k hline

/-- `lem:h-b-consistency`, source-facing form. -/
theorem hBConsistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma zeta : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (hd : 0 < params.d)
    (family : IdxPolyFamily params 𝔓)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ) :
    HBConsistencyStatement params strategy family
        eps delta gamma zeta k :=
  hBConsistency_ofLinePointBounds params strategy eps delta gamma zeta
    hgood hd family hcons hself hbound k fun i hi =>
      ldSandwichLineOnePoint params strategy eps delta gamma zeta
        hgood hgamma_le hzeta_le hdq_le family hcons hself hbound k i hi

end MIPRE.LIDT.Co.Pasting

end

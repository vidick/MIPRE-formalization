/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/
ComparisonLemmas/LineInterpolation/HBError.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.ComparisonLemmas.LineInterpolation.BadMass
public import MIPRE.Background.LIDT.Co.Pasting.ComparisonLemmas.LineInterpolation.Averaging
public import MIPRE.Background.LIDT.Co.Pasting.ComparisonLemmas.LdSandwichLineOnePoint.Core
public import MIPRE.Background.LIDT.Co.Pasting.Core.DDistinct
public import MIPStarRE.LDT.Pasting.ComparisonLemmas.LineInterpolation.HBError

@[expose] public section

/-!
# Line interpolation: H-B consistency error aggregation

The counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/ComparisonLemmas/LineInterpolation/HBError.lean` in
the port of `planning/c6b-plan.md` (milestone M11, section "Port conventions").

The fixed-`u` defect of the pasted submeasurement restricted to a vertical line, its comparison
with the bad mass of `BadMass.lean` over distinct tuples, the passage from distinct to
independent tuples (`ldDnoteq`), and the aggregation of the one-point line estimates of
`lem:ld-sandwich-line-one-point` into `hBConsistencyError`, which drives `lem:h-b-consistency`.

A strategy is a `SymStrat params.next 𝔓 K` and the slice family an `IdxPolyFamily params 𝔓`;
the defects are read on `strategy.state`. The vendored file's five scalar lemmas (the expansion
of `hBConsistencyError`, the sum over `Fin k` of averages, and the bounds of the degree ratio and
of the distinct-tuple loss by the displayed error) are classical and imported from the vendored
file. The nonnegativity of `eps` and `delta` in `avgOver_distinct_badMass_le_hBConsistencyError`
comes from `eps_nonneg_of_isGood` and `delta_nonneg_of_isGood`, which unfold to the vendored
`bipartiteConsError_nonneg` and `bipartiteSSCError_nonneg` steps. No statement carries a swap or
normalization hypothesis, the vendored statements having none.

## Not ported

- `hBConsistencyError_eq_k_mul_ldSandwichLineOnePointError_add`: classical, imported.
- `avgOver_sum_fin`: classical, imported.
- `one_div_q_le_rpow_degreeRatio`: classical, imported.
- `dnoteq_term_le_hBConsistency_extra`: classical, imported.
- `hBConsistency_error_bound`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel Point PointTuple avgOver avgOver_mono avgOver_congr
  avgOver_add avgOver_uniform_const avgOver_uniform_prod uniformDistribution)
open MIPStarRE.LDT.Pasting (SandwichedLineQuestion distinctTupleDistribution
  distinctTupleDistribution_weight_sum_le_one distinctTupleDistribution_support
  mem_distinctTupleSupport ldDnoteq avgOver_distinct_bounded_le_avgOver_uniform_add_tv_of_any_k
  ldSandwichLineOnePointError hBConsistencyError avgOver_sum_fin hBConsistency_error_bound)
open MIPRE.LIDT.Co (SymStrat IdxPolyFamily averageIdxSubMeas eps_nonneg_of_isGood
  delta_nonneg_of_isGood gamma_nonneg_of_isGood)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- For a fixed base point `u`, the consistency defect of the constructed pasted submeasurement
restricted to the vertical line through `u` is at most the average over distinct tuples of the
defects of the pasted interpolations. -/
theorem hBConsistency_fixed_u_defect_le_avgOver_distinct
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (k : ℕ)
    (u : Point params) :
    strategy.state.qBipartiteConsDefect
      (hRestrictionToVerticalLine params (constructedPastedSubMeas params family k) u)
      (verticalLineMeasurementFamily params strategy u) ≤
        avgOver (distinctTupleDistribution params k)
          (fun xs =>
            strategy.state.qBipartiteConsDefect
              (hRestrictionToVerticalLine params (pastedInterpolationFamily params family k xs) u)
              (verticalLineMeasurementFamily params strategy u)) := by
  rw [constructedPastedSubMeas, hRestrictionToVerticalLine_averageIdxSubMeas]
  exact qBipartiteConsDefect_averageIdxSubMeas_left_le strategy.state
    (distinctTupleDistribution params k)
    (fun xs => hRestrictionToVerticalLine params (pastedInterpolationFamily params family k xs) u)
    (verticalLineMeasurementFamily params strategy u)
    (distinctTupleDistribution_weight_sum_le_one params k)

/-- Over distinct tuples, the average defect of the pasted interpolations on the vertical line
through `u` is at most the average bad mass. -/
theorem avgOver_distinct_pasted_defect_le_badMass
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    {k : ℕ} (u : Point params) :
    avgOver (distinctTupleDistribution params k) (fun xs =>
      strategy.state.qBipartiteConsDefect
        (hRestrictionToVerticalLine params (pastedInterpolationFamily params family k xs) u)
        (verticalLineMeasurementFamily params strategy u))
      ≤ avgOver (distinctTupleDistribution params k) (fun xs =>
          hBConsistencyBadMass params strategy family u xs) :=
  Finset.sum_le_sum fun xs hxs => mul_le_mul_of_nonneg_left
    (pastedInterpolation_verticalLine_defect_le_badMass params strategy family u xs
      ((mem_distinctTupleSupport params k xs).1
        ((distinctTupleDistribution_support params k).subset hxs)))
    ((distinctTupleDistribution params k).nonnegative xs)

/-- Passing from distinct to independent tuples costs at most `k² / q` on the bad mass. -/
theorem avgOver_distinct_badMass_le_avgOver_uniform_badMass_add_dnoteq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    {k : ℕ} (u : Point params) :
    avgOver (distinctTupleDistribution params k) (fun xs =>
      hBConsistencyBadMass params strategy family u xs)
      ≤ avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
            hBConsistencyBadMass params strategy family u xs) +
          ((k : ℝ) ^ (2 : ℕ)) / (params.q : ℝ) :=
  (avgOver_distinct_bounded_le_avgOver_uniform_add_tv_of_any_k params k
    (fun xs => hBConsistencyBadMass params strategy family u xs)
    (fun xs => hBConsistencyBadMass_nonneg params strategy family u xs)
    (fun xs => hBConsistencyBadMass_le_one params strategy family u xs)).trans
    (add_le_add le_rfl (ldDnoteq params k))

/-- Internal aggregation form after the one-point line estimates have been
supplied.

**Source:** In `references/ldt-paper/ld-pasting.tex:1075-1109`, the proof of
`lem:h-b-consistency` applies `lem:ld-sandwich-line-one-point` for each
coordinate and then sums the resulting bounds.  The paper-facing theorem below
derives these one-point estimates from the source hypotheses. -/
theorem avgOver_uniform_badMass_le_k_mul_ldSandwichLineOnePointError_ofLinePointBounds
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (eps delta gamma zeta : ℝ)
    (k : ℕ)
    (hline : ∀ i : ℕ, i < k →
      LdSandwichLineOnePointStatement params strategy family
        eps delta gamma zeta k i) :
    avgOver (uniformDistribution (Point params)) (fun u =>
      avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
        hBConsistencyBadMass params strategy family u xs))
      ≤ (k : ℝ) * ldSandwichLineOnePointError params eps delta gamma zeta k := by
  let defect : Fin k → SandwichedLineQuestion params k → ℝ := fun i q =>
    strategy.state.qBipartiteConsDefect
      ((ldSandwichLineOnePointLeftFamily params strategy family k i.1) q)
      ((ldSandwichLineOnePointRightFamily params strategy family k i.1) q)
  calc
    avgOver (uniformDistribution (Point params)) (fun u =>
      avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
        hBConsistencyBadMass params strategy family u xs))
      ≤ avgOver (uniformDistribution (Point params)) (fun u =>
          avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
            ∑ i : Fin k, defect i (u, xs))) :=
        avgOver_mono _ _ _ fun u => avgOver_mono _ _ _ fun xs =>
          hBConsistencyBadMass_le_linePointDefectSum params strategy family u xs
    _ = ∑ i : Fin k,
          avgOver (uniformDistribution (Point params)) (fun u =>
            avgOver (uniformDistribution (PointTuple params k)) (fun xs => defect i (u, xs))) :=
        (avgOver_congr _ _ _ fun u => avgOver_sum_fin _ k fun xs i => defect i (u, xs)).trans
          (avgOver_sum_fin _ k fun u i =>
            avgOver (uniformDistribution (PointTuple params k)) fun xs => defect i (u, xs))
    _ = ∑ i : Fin k,
          avgOver (uniformDistribution (SandwichedLineQuestion params k)) (defect i) :=
        Finset.sum_congr rfl fun i _ =>
          (avgOver_uniform_prod (f := fun u xs => defect i (u, xs))).symm
    _ ≤ ∑ _i : Fin k, ldSandwichLineOnePointError params eps delta gamma zeta k :=
        Finset.sum_le_sum fun i _ => (hline i.1 i.2).linePointComparison.offDiagonalBound
    _ = (k : ℝ) * ldSandwichLineOnePointError params eps delta gamma zeta k := by
        simp

/-- The independent-tuple bad mass is bounded by the sum of the one-point line
errors, in the source-facing Section 12 context. -/
theorem avgOver_uniform_badMass_le_k_mul_ldSandwichLineOnePointError
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (eps delta gamma zeta : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ) :
    avgOver (uniformDistribution (Point params)) (fun u =>
      avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
        hBConsistencyBadMass params strategy family u xs))
      ≤ (k : ℝ) * ldSandwichLineOnePointError params eps delta gamma zeta k :=
  avgOver_uniform_badMass_le_k_mul_ldSandwichLineOnePointError_ofLinePointBounds
    params strategy family eps delta gamma zeta k fun i hi =>
      ldSandwichLineOnePoint params strategy eps delta gamma zeta
        hgood hgamma_le hzeta_le hdq_le family hcons hself hbound k i hi

/-- Aggregate the one-point line comparison statements over all inserted vertical
lines and absorb the distinct-tuple loss into the displayed `hBConsistency`
error.

This is the reusable bad-mass aggregation from `ld-pasting.tex` lines
1186--1202 (also used in the proof of `lem:h-b-consistency`). -/
theorem avgOver_distinct_badMass_le_hBConsistencyError_ofLinePointBounds
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (eps delta gamma zeta : ℝ) (k : ℕ)
    (hd : 0 < params.d)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta)
    (hline : ∀ i : ℕ, i < k →
      LdSandwichLineOnePointStatement params strategy family
        eps delta gamma zeta k i) :
    avgOver (uniformDistribution (Point params)) (fun u =>
        avgOver (distinctTupleDistribution params k) (fun xs =>
          hBConsistencyBadMass params strategy family u xs)) ≤
      hBConsistencyError params eps delta gamma zeta k :=
  calc
    avgOver (uniformDistribution (Point params)) (fun u =>
        avgOver (distinctTupleDistribution params k) (fun xs =>
          hBConsistencyBadMass params strategy family u xs))
      ≤ avgOver (uniformDistribution (Point params)) (fun u =>
          avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
            hBConsistencyBadMass params strategy family u xs) +
          ((k : ℝ) ^ (2 : ℕ)) / (params.q : ℝ)) :=
        avgOver_mono _ _ _ fun u =>
          avgOver_distinct_badMass_le_avgOver_uniform_badMass_add_dnoteq
            params strategy family u
    _ = avgOver (uniformDistribution (Point params)) (fun u =>
          avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
            hBConsistencyBadMass params strategy family u xs)) +
        ((k : ℝ) ^ (2 : ℕ)) / (params.q : ℝ) :=
        (avgOver_add _ _ _).trans (congrArg _ (avgOver_uniform_const _))
    _ ≤ (k : ℝ) * ldSandwichLineOnePointError params eps delta gamma zeta k +
          ((k : ℝ) ^ (2 : ℕ)) / (params.q : ℝ) :=
        add_le_add
          (avgOver_uniform_badMass_le_k_mul_ldSandwichLineOnePointError_ofLinePointBounds
            params strategy family eps delta gamma zeta k hline) le_rfl
    _ ≤ hBConsistencyError params eps delta gamma zeta k :=
        hBConsistency_error_bound params eps delta gamma zeta k hd
          heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg

/-- Aggregate the one-point line comparison estimates and absorb the
distinct-tuple loss into the displayed `hBConsistency` error, deriving the
one-point estimates internally from `lem:ld-sandwich-line-one-point`. -/
theorem avgOver_distinct_badMass_le_hBConsistencyError
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (eps delta gamma zeta : ℝ) (k : ℕ)
    (hd : 0 < params.d)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    avgOver (uniformDistribution (Point params)) (fun u =>
        avgOver (distinctTupleDistribution params k) (fun xs =>
          hBConsistencyBadMass params strategy family u xs)) ≤
      hBConsistencyError params eps delta gamma zeta k :=
  avgOver_distinct_badMass_le_hBConsistencyError_ofLinePointBounds
    params strategy family eps delta gamma zeta k hd
    (eps_nonneg_of_isGood params.next strategy hgood)
    (delta_nonneg_of_isGood params.next strategy hgood)
    (gamma_nonneg_of_isGood params.next strategy hgood)
    (IdxPolyFamily.zeta_nonneg_of_consistentWithPoints strategy family hcons)
    fun i hi => ldSandwichLineOnePoint params strategy eps delta gamma zeta
      hgood hgamma_le hzeta_le hdq_le family hcons hself hbound k i hi

end MIPRE.LIDT.Co.Pasting

end

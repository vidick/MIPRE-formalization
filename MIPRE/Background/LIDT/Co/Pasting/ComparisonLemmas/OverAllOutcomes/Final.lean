/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/
ComparisonLemmas/OverAllOutcomes/Final.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.ComparisonLemmas.OverAllOutcomes.NonglobalDecomposition
public import MIPStarRE.LDT.Pasting.ComparisonLemmas.OverAllOutcomes.Final

@[expose] public section

/-!
# Section 12 pasting: over all outcomes — Schwartz–Zippel bounds and final assembly

Schwartz–Zippel aggregation, the line-consistent indicator bound, and the final chained
assembly of `lem:over-all-outcomes`: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/ComparisonLemmas/OverAllOutcomes/Final.lean`
in the port of `planning/c6b-plan.md` (milestone M11, section "Port conventions").

A strategy is a `SymStrat params.next 𝔓 K` and a slice family an `IdxPolyFamily params 𝔓`.
`avgOver_subMeasMass_restrict_liftLeft_eq_sum_coeff`, a lemma on a placement, takes the model
`S` as an explicit first argument and a local `A : SubMeas Outcome 𝔓`; its proof is
`S.ev_leftTensor_total_eq_sum_outcome` on the restricted submeasurement, where the vendored proof
unfolds `mkLeftPlacedSubMeas`. The vanishing of ineligible outcomes is `map_zero` and `S.ev_zero`,
where the vendored proof unfolds `leftTensor` and `ev`. No statement carries a swap or
normalization hypothesis: `heps_nonneg` and `hdelta_nonneg` of
`overAllOutcomes_ofGHatFacts_of_axis_self` come from `strategy.state.bipartiteConsError_nonneg`
and `strategy.state.bipartiteSSCError_nonneg`.

The pointwise Schwartz–Zippel bound `lineConsistentIndicator_probability_le_mdq` is classical:
this file imports the vendored file and names it, with the error arithmetic of `ErrorAndMass`,
through an explicit `open MIPStarRE.LDT.Pasting (…)` list.

## Not ported

- `lineConsistentIndicator_probability_le_mdq`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel Point PointTuple AxisParallelTestSample Distribution
  avgOver avgOver_congr avgOver_sum avgOver_mul_const avgOver_comm avgOver_mono_on_support
  avgOver_const uniformDistribution)
open MIPStarRE.LDT.Pasting (GHatTupleOutcome IsGloballyConsistent InterpolationEligible
  distinctTupleDistribution distinctTupleDistribution_weight_sum_le_one hBConsistencyError
  overAllOutcomesError dnoteq_term_le_overAllOutcomesError
  hBConsistencyError_add_mdq_add_dnoteq_le_overAllOutcomesError
  lineConsistentIndicator_probability_le_mdq)
open MIPRE.LIDT.Co (SymModel SymStrat SubMeas IdxProjMeas IdxPolyFamily)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Expand an averaged restricted lifted submeasurement into per-outcome masses
weighted by the probability of the restricting predicate. -/
theorem avgOver_subMeasMass_restrict_liftLeft_eq_sum_coeff
    {Question Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K)
    (𝒟 : Distribution Question)
    (A : SubMeas Outcome 𝔓)
    (P : Question → Outcome → Prop) [∀ q, DecidablePred (P q)] :
    avgOver 𝒟 (fun q => S.subMeasMass ((restrictSubMeas A (P q)).liftLeft S)) =
      ∑ a : Outcome,
        avgOver 𝒟 (fun q => if P q a then (1 : ℝ) else 0) * S.ev (S.L (A.outcome a)) := by
  calc
    avgOver 𝒟 (fun q => S.subMeasMass ((restrictSubMeas A (P q)).liftLeft S))
      = avgOver 𝒟 (fun q => ∑ a : Outcome,
          (if P q a then (1 : ℝ) else 0) * S.ev (S.L (A.outcome a))) :=
        avgOver_congr _ _ _ fun q =>
          (S.ev_leftTensor_total_eq_sum_outcome (restrictSubMeas A (P q))).trans <|
            Finset.sum_congr rfl fun a _ => by
              change S.ev (S.L (if P q a then A.outcome a else 0)) = _
              split_ifs
              · exact (one_mul _).symm
              · rw [map_zero, S.ev_zero, zero_mul]
    _ = ∑ a : Outcome,
        avgOver 𝒟 (fun q => if P q a then (1 : ℝ) else 0) * S.ev (S.L (A.outcome a)) :=
        (avgOver_sum _ _).trans (Finset.sum_congr rfl fun a _ => avgOver_mul_const _ _ _)

/-- Fixed-distinct-tuple form of the line-consistent Schwartz--Zippel bound. -/
theorem lineConsistentIndicatorLocal_avg_le_mdq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓) {k : ℕ}
    (xs : PointTuple params k)
    (hxs : Function.Injective xs) :
    avgOver (uniformDistribution (Point params)) (fun u =>
        overAllOutcomesLineConsistentIndicatorLocal params strategy family u xs) ≤
      ((params.m * params.d : ℕ) : ℝ) / (params.q : ℝ) := by
  set S := strategy.state
  set A := interpolationEligibleSandwichFamily params family k xs
  set δ : ℝ := ((params.m * params.d : ℕ) : ℝ) / (params.q : ℝ)
  have hδ : 0 ≤ δ := by positivity
  have hterm : ∀ gs : GHatTupleOutcome params k,
      avgOver (uniformDistribution (Point params)) (fun u =>
          if (¬ IsGloballyConsistent params xs gs) ∧
              ∃ f : MIPStarRE.LDT.AxisLinePolynomial params.next,
                ¬ (∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
                  ((gs i).get hiSome) u ≠ f (xs i)) then (1 : ℝ) else 0) *
          S.ev (S.L (A.outcome gs)) ≤
        δ * S.ev (S.L (A.outcome gs)) := fun gs => by
    by_cases hEligible : InterpolationEligible params gs
    · exact mul_le_mul_of_nonneg_right
        (by convert lineConsistentIndicator_probability_le_mdq params xs hxs gs hEligible)
        (S.ev_nonneg_of_psd _ (S.leftTensor_nonneg (A.outcome_pos gs)))
    · have hAout : A.outcome gs = 0 := ite_eq_right hEligible
      rw [hAout, map_zero, S.ev_zero, mul_zero, mul_zero]
  calc
    avgOver (uniformDistribution (Point params)) (fun u =>
        overAllOutcomesLineConsistentIndicatorLocal params strategy family u xs)
      = ∑ gs : GHatTupleOutcome params k,
          avgOver (uniformDistribution (Point params)) (fun u =>
            if (¬ IsGloballyConsistent params xs gs) ∧
                ∃ f : MIPStarRE.LDT.AxisLinePolynomial params.next,
                  ¬ (∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
                    ((gs i).get hiSome) u ≠ f (xs i)) then (1 : ℝ) else 0) *
            S.ev (S.L (A.outcome gs)) :=
        avgOver_subMeasMass_restrict_liftLeft_eq_sum_coeff S _ A _
    _ ≤ ∑ gs : GHatTupleOutcome params k, δ * S.ev (S.L (A.outcome gs)) :=
        Finset.sum_le_sum fun gs _ => hterm gs
    _ = δ * S.subMeasMass (A.liftLeft S) := by
        rw [← Finset.mul_sum, ← S.ev_leftTensor_total_eq_sum_outcome]
        rfl
    _ ≤ δ * 1 := mul_le_mul_of_nonneg_left (eligibleMass_le_one params strategy family xs) hδ
    _ = δ := mul_one δ

/-- The line-consistent Schwartz--Zippel aggregation after the insertion and
bad-line finite-sum split.

Paper anchor: `ld-pasting.tex` lines 1235--1275.  For every distinct tuple `xs`,
interpolation-eligible nonglobal outcome `gs`, and line-consistent answer `f`, the
paper chooses the interpolant `h*`; nonglobality gives a supported coordinate
where `gᵢ ≠ h*|_{xsᵢ}`, and Schwartz--Zippel bounds the probability over `u` that
this disagreement vanishes by `md/q`. -/
theorem overAllOutcomes_distinct_lineConsistent_indicator_mass_le_mdq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (k : ℕ) :
    overAllOutcomesDistinctLineConsistentIndicatorMass params strategy family k ≤
      ((params.m * params.d : ℕ) : ℝ) / (params.q : ℝ) := by
  set δ : ℝ := ((params.m * params.d : ℕ) : ℝ) / (params.q : ℝ)
  have hδ : 0 ≤ δ := by positivity
  calc
    overAllOutcomesDistinctLineConsistentIndicatorMass params strategy family k
      = avgOver (distinctTupleDistribution params k) (fun xs =>
          avgOver (uniformDistribution (Point params)) (fun u =>
            overAllOutcomesLineConsistentIndicatorLocal params strategy family u xs)) :=
        avgOver_comm _ _ _
    _ ≤ avgOver (distinctTupleDistribution params k) (fun _ => δ) :=
        avgOver_mono_on_support _ _ _ fun xs hxs =>
          lineConsistentIndicatorLocal_avg_le_mdq params strategy family xs
            (by simpa [distinctTupleDistribution] using hxs)
    _ ≤ δ :=
        (avgOver_const _ δ).trans_le <| (mul_le_mul_of_nonneg_right
          (distinctTupleDistribution_weight_sum_le_one params k) hδ).trans_eq (one_mul δ)

/-- The local finite-sum/SZ comparison after the one-point line-mismatch
aggregation has been separated off.

The insertion and finite-sum split from `ld-pasting.tex` lines 1174--1228 are
proved by `overAllOutcomes_distinct_nonglobal_mass_le_bad_line_mass_add_lineConsistent`.
The line-consistent remainder is exactly the Schwartz--Zippel aggregation proved
by `overAllOutcomes_distinct_lineConsistent_indicator_mass_le_mdq`, corresponding
to lines 1235--1275. -/
theorem overAllOutcomes_distinct_nonglobal_mass_le_bad_line_mass_add_mdq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (k : ℕ) :
    overAllOutcomesDistinctNonglobalMass params strategy family k ≤
      overAllOutcomesDistinctBadLineMass params strategy family k +
        ((params.m * params.d : ℕ) : ℝ) / (params.q : ℝ) :=
  (overAllOutcomes_distinct_nonglobal_mass_le_bad_line_mass_add_lineConsistent
    params strategy family k).trans <| add_le_add le_rfl <|
    (lineConsistentNonglobalMass_le_indicatorMass params strategy family k).trans
      (overAllOutcomes_distinct_lineConsistent_indicator_mass_le_mdq params strategy family k)

/-- If the distinct nonglobal mass is bounded by the paper's local
`k·ν₅ + k²/q + md/q` comparison, then the reverse half of
`lem:over-all-outcomes` follows.

The remaining hypothesis is exactly the content of `ld-pasting.tex` lines
1174--1275: insert the line measurement, pay the one-point line consistency
bound to add the consistency indicator, and use Schwartz--Zippel for the
indicator term. -/
theorem overAllOutcomes_reverse_mass_bound_of_nonglobal_mass_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (eps delta gamma zeta : ℝ) (k : ℕ)
    (hd : 0 < params.d)
    (hdq_le : params.d ≤ params.q)
    (hkEligible : params.d + 1 ≤ k)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta)
    (hnonglobal :
      overAllOutcomesDistinctNonglobalMass params strategy family k ≤
        hBConsistencyError params eps delta gamma zeta k +
          ((params.m * params.d : ℕ) : ℝ) / (params.q : ℝ)) :
    overAllOutcomesExpansionMass params strategy family k -
        overAllOutcomesPastedMass params strategy family k ≤
      overAllOutcomesError params eps delta gamma zeta k := by
  have hswap := avgOver_uniform_eligibleMass_le_distinct_add_dnoteq
    params strategy family k
  have hsplit := avgOver_distinct_eligibleMass_eq_global_add_nonglobal
    params strategy family k
  have hbound := hBConsistencyError_add_mdq_add_dnoteq_le_overAllOutcomesError
    params eps delta gamma zeta k hd hdq_le hkEligible
    heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg
  rw [overAllOutcomesExpansionMass_eq_avg_uniform_eligible,
    overAllOutcomesPastedMass_eq_avg_distinct_global]
  linarith

/-- The paper-local nonglobal mass comparison after the algebraic reductions.

The one-point line-comparison aggregation from `ld-pasting.tex` lines 1186--1202
is proved by `overAllOutcomes_distinct_bad_line_mass_le_hBConsistencyError`, and
the remaining insertion/Schwartz--Zippel estimate is
`overAllOutcomes_distinct_nonglobal_mass_le_bad_line_mass_add_mdq`. -/
theorem overAllOutcomes_distinct_nonglobal_mass_bound
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
    overAllOutcomesDistinctNonglobalMass params strategy family k ≤
      hBConsistencyError params eps delta gamma zeta k +
        ((params.m * params.d : ℕ) : ℝ) / (params.q : ℝ) :=
  (overAllOutcomes_distinct_nonglobal_mass_le_bad_line_mass_add_mdq params strategy family k).trans
    (add_le_add (overAllOutcomes_distinct_bad_line_mass_le_hBConsistencyError
      params strategy family eps delta gamma zeta k hd
      heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg hline) le_rfl)

/-- Reduction of `lem:over-all-outcomes` to a reverse mass comparison.

The forward direction
`overAllOutcomesPastedMass - overAllOutcomesExpansionMass` is now discharged by
expanding the pasted mass over distinct tuples, forgetting global consistency,
and paying only `ldDnoteq`.  The reverse loss
`overAllOutcomesExpansionMass - overAllOutcomesPastedMass` is the part of
`ld-pasting.tex` supplied below by the completed `ldSandwichLineOnePoint`
aggregation. -/
theorem overAllOutcomes_of_reverse_mass_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (eps delta gamma zeta : ℝ) (k : ℕ)
    (hd : 0 < params.d)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta)
    (hreverse :
      overAllOutcomesExpansionMass params strategy family k -
          overAllOutcomesPastedMass params strategy family k ≤
        overAllOutcomesError params eps delta gamma zeta k) :
    OverAllOutcomesStatement params strategy family eps delta gamma zeta k :=
  have hforward :
      overAllOutcomesPastedMass params strategy family k -
          overAllOutcomesExpansionMass params strategy family k ≤
        overAllOutcomesError params eps delta gamma zeta k :=
    (overAllOutcomes_pasted_sub_expansion_le_dnoteq params strategy family k).trans
      (dnoteq_term_le_overAllOutcomesError params eps delta gamma zeta k hd
        heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg)
  ⟨abs_le.mpr ⟨by linarith, hforward⟩⟩

/-- Internal form of `lem:over-all-outcomes` from the one-point sandwich
estimates.

The proof of the mass comparison uses the estimates
`lem:ld-sandwich-line-one-point` in the interpolation-eligible case.  Once those
estimates are supplied explicitly, the remaining argument only needs
nonnegativity of the scalar error parameters and the usual degree and field-size
side conditions. -/
theorem overAllOutcomes_ofLinePointBounds
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma zeta : ℝ)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta)
    (hdq_le : params.d ≤ params.q)
    (hd : 0 < params.d)
    (family : IdxPolyFamily params 𝔓)
    (k : ℕ)
    (hline : ∀ i : ℕ, i < k →
      LdSandwichLineOnePointStatement params strategy family
        eps delta gamma zeta k i) :
    OverAllOutcomesStatement params strategy family eps delta gamma zeta k := by
  refine overAllOutcomes_of_reverse_mass_bound params strategy family
    eps delta gamma zeta k hd heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg ?_
  by_cases hkEligible : params.d + 1 ≤ k
  · exact overAllOutcomes_reverse_mass_bound_of_nonglobal_mass_bound
      params strategy family eps delta gamma zeta k hd hdq_le hkEligible
      heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg
      (overAllOutcomes_distinct_nonglobal_mass_bound
        params strategy family eps delta gamma zeta k hd
        heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg hline)
  · exact overAllOutcomes_reverse_mass_bound_of_not_d_add_one_le
      params strategy family eps delta gamma zeta k hkEligible
      heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg

/-- Internal form of `lem:over-all-outcomes` from `cor:G-hat-facts`. -/
theorem overAllOutcomes_ofGHatFacts_of_axis_self
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma zeta : ℝ)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself_good : strategy.selfConsistencyFailureProbability ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (hd : 0 < params.d)
    (family : IdxPolyFamily params 𝔓)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hfacts : GHatFactsStatement params strategy.state family gamma zeta)
    (k : ℕ) :
    OverAllOutcomesStatement params strategy family eps delta gamma zeta k :=
  overAllOutcomes_ofLinePointBounds params strategy eps delta gamma zeta
    ((strategy.state.bipartiteConsError_nonneg
      (uniformDistribution (AxisParallelTestSample params.next))
      (axisParallelPointAnswerFamily strategy)
      (axisParallelLineAnswerFamily strategy)).trans haxis)
    ((strategy.state.bipartiteSSCError_nonneg
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)).trans hself_good)
    hgamma_nonneg hzeta_nonneg hdq_le hd family k fun i hi =>
    ldSandwichLineOnePoint_ofGHatFacts_of_axis_self params strategy
      eps delta gamma zeta haxis hself_good hgamma_nonneg hzeta_le
      family hcons hfacts k i hi

/-- Internal form of `lem:over-all-outcomes` from the Section 11 commutativity
conclusion. -/
theorem overAllOutcomes_ofComMain_of_axis_self
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma zeta : ℝ)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself_good : strategy.selfConsistencyFailureProbability ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_nonneg : 0 ≤ zeta)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (hd : 0 < params.d)
    (family : IdxPolyFamily params 𝔓)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hcom : Commutativity.ComMainConclusion params strategy family gamma zeta)
    (k : ℕ) :
    OverAllOutcomesStatement params strategy family eps delta gamma zeta k :=
  overAllOutcomes_ofGHatFacts_of_axis_self params strategy
    eps delta gamma zeta haxis hself_good hgamma_nonneg hzeta_nonneg hzeta_le
    hdq_le hd family hcons
    (gHatFacts_ofComMainAndSelfConsistency params strategy family gamma zeta
      hgamma_nonneg hgamma_le hzeta_nonneg hzeta_le hdq_le hcom hself) k

/-- `lem:over-all-outcomes`. -/
theorem overAllOutcomes
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
    OverAllOutcomesStatement params strategy family eps delta gamma zeta k :=
  overAllOutcomes_ofLinePointBounds params strategy eps delta gamma zeta
    (eps_nonneg_of_isGood params.next strategy hgood)
    (delta_nonneg_of_isGood params.next strategy hgood)
    (gamma_nonneg_of_isGood params.next strategy hgood)
    (IdxPolyFamily.zeta_nonneg_of_consistentWithPoints strategy family hcons)
    hdq_le hd family k fun i hi =>
    ldSandwichLineOnePoint params strategy eps delta gamma zeta
      hgood hgamma_le hzeta_le hdq_le family hcons hself hbound k i hi

end MIPRE.LIDT.Co.Pasting

end

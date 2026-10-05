/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/
ComparisonLemmas/OverAllOutcomes/ErrorAndMass.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.ComparisonLemmas.HAConsistency
public import MIPStarRE.LDT.Pasting.ComparisonLemmas.OverAllOutcomes.ErrorAndMass

@[expose] public section

/-!
# Section 12 pasting: over all outcomes — error terms and eligible mass

Eligible-mass bounds and mass identities that feed the final `lem:over-all-outcomes`
comparison: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/ComparisonLemmas/OverAllOutcomes/ErrorAndMass.lean`
in the port of `planning/c6b-plan.md` (milestone M11, section "Port conventions").

A strategy is a `SymStrat params.next 𝔓 K` and a slice family an `IdxPolyFamily params 𝔓`; the
masses are `strategy.state.subMeasMass` of left-placed submeasurements,
`(A.liftLeft strategy.state)`. The bound of an eligible mass by `1` (vendored through
`strategy.isNormalized`) uses `S.ev_one_of_isNormalized`, which takes no hypothesis. The two mass
identities are `S.ev_leftTensor_averageOperatorOverDistribution` up to definitional unfolding,
and the vanishing masses below `d + 1` coordinates and the monotonicity of the restricted mass are
`S.ev_zero` and `S.leftTensor_mono`, where the vendored proofs unfold `leftTensor` and `ev`.

The error arithmetic (`oneThirtySecondErrorSum_nonneg` and the two comparisons with
`overAllOutcomesError`) and the interpolation-uniqueness step are classical: this file imports the
vendored file and names them through an explicit `open MIPStarRE.LDT.Pasting (…)` list.

## Not ported

- `oneThirtySecondErrorSum_nonneg`: classical, imported.
- `dnoteq_term_le_overAllOutcomesError`: classical, imported.
- `hBConsistencyError_add_mdq_add_dnoteq_le_overAllOutcomesError`: classical, imported.
- `tupleInterpolatedVerticalLine_eq_of_no_supported_mismatch`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel PointTuple avgOver avgOver_mono avgOver_sub avgOver_zero
  avgOver_congr avgOver_uniform_const avgOver_uniform_le_const uniformDistribution)
open MIPStarRE.LDT.Pasting (GHatTupleOutcome InterpolationEligible gHatTupleHammingWeight
  gHatTupleSupport IsGloballyConsistent distinctTupleDistribution
  distinctTupleDistribution_weight_sum_eq_one_of_le
  avgOver_distinct_bounded_le_avgOver_uniform_add_tv_of_any_k
  avgOver_distinct_bounded_le_avgOver_uniform_add_tv ldDnoteq overAllOutcomesError
  oneThirtySecondErrorSum_nonneg)
open MIPRE.LIDT.Co (SymStrat SubMeas IdxSubMeas IdxPolyFamily)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- If `k < d+1`, the interpolation-eligible sandwich total vanishes. -/
theorem interpolationEligibleSandwich_total_eq_zero_of_not_d_add_one_le
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) {k : ℕ}
    (hnot : ¬ params.d + 1 ≤ k) (xs : PointTuple params k) :
    (interpolationEligibleSandwichFamily params family k xs).total = 0 :=
  Finset.sum_eq_zero fun gs hgs => absurd ((Finset.mem_filter.1 hgs).2.trans <| by
    simpa [gHatTupleHammingWeight, Fintype.card_fin] using
      Finset.card_le_univ (gHatTupleSupport gs)) hnot

/-- Eligible interpolation mass is nonnegative for every point tuple. -/
theorem eligibleMass_nonneg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓) {k : ℕ} (xs : PointTuple params k) :
    0 ≤ strategy.state.subMeasMass
      ((interpolationEligibleSandwichFamily params family k xs).liftLeft strategy.state) :=
  strategy.state.ev_nonneg_of_psd _ <| strategy.state.leftTensor_nonneg
    (SubMeas.total_nonneg (interpolationEligibleSandwichFamily params family k xs))

/-- Eligible interpolation mass is at most one for every point tuple. -/
theorem eligibleMass_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓) {k : ℕ} (xs : PointTuple params k) :
    strategy.state.subMeasMass
      ((interpolationEligibleSandwichFamily params family k xs).liftLeft strategy.state) ≤ 1 :=
  (strategy.state.ev_mono _ _ (strategy.state.leftTensor_le_one
    (interpolationEligibleSandwichFamily params family k xs).total_le_one)).trans_eq
    strategy.state.ev_one_of_isNormalized

/-- Distinct tuple averaging is bounded by uniform averaging plus `ldDnoteq`. -/
theorem avgOver_distinct_eligibleMass_le_uniform_add_dnoteq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (k : ℕ) :
    avgOver (distinctTupleDistribution params k) (fun xs =>
        strategy.state.subMeasMass
          ((interpolationEligibleSandwichFamily params family k xs).liftLeft strategy.state)) ≤
      avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
        strategy.state.subMeasMass
          ((interpolationEligibleSandwichFamily params family k xs).liftLeft strategy.state)) +
        ((k : ℝ) ^ (2 : ℕ)) / (params.q : ℝ) :=
  (avgOver_distinct_bounded_le_avgOver_uniform_add_tv_of_any_k params k _
    (eligibleMass_nonneg params strategy family) (eligibleMass_le_one params strategy family)).trans
    (add_le_add le_rfl (ldDnoteq params k))

/-- Uniform tuple averaging is bounded by distinct averaging plus `ldDnoteq`. -/
theorem avgOver_uniform_eligibleMass_le_distinct_add_dnoteq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (k : ℕ) :
    avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
        strategy.state.subMeasMass
          ((interpolationEligibleSandwichFamily params family k xs).liftLeft strategy.state)) ≤
      avgOver (distinctTupleDistribution params k) (fun xs =>
        strategy.state.subMeasMass
          ((interpolationEligibleSandwichFamily params family k xs).liftLeft strategy.state)) +
        ((k : ℝ) ^ (2 : ℕ)) / (params.q : ℝ) := by
  set F : PointTuple params k → ℝ := fun xs =>
    strategy.state.subMeasMass
      ((interpolationEligibleSandwichFamily params family k xs).liftLeft strategy.state)
  have hF0 : ∀ xs, 0 ≤ F xs := eligibleMass_nonneg params strategy family
  have hF1 : ∀ xs, F xs ≤ 1 := eligibleMass_le_one params strategy family
  have htv := ldDnoteq params k
  by_cases hk : k ≤ params.q
  · have hcomp := avgOver_distinct_bounded_le_avgOver_uniform_add_tv params k hk
      (fun xs => 1 - F xs) (fun xs => sub_nonneg.mpr (hF1 xs))
      (fun xs => by linarith [hF0 xs])
    have hDconst : avgOver (distinctTupleDistribution params k)
        (fun _ : PointTuple params k => (1 : ℝ)) = 1 := by
      simpa [avgOver] using distinctTupleDistribution_weight_sum_eq_one_of_le params k hk
    rw [avgOver_sub, avgOver_sub, hDconst, avgOver_uniform_const] at hcomp
    linarith
  · have hUle : avgOver (uniformDistribution (PointTuple params k)) F ≤ 1 :=
      avgOver_uniform_le_const F 1 hF1
    have hDnonneg : 0 ≤ avgOver (distinctTupleDistribution params k) F :=
      Finset.sum_nonneg fun xs _ =>
        mul_nonneg ((distinctTupleDistribution params k).nonnegative xs) (hF0 xs)
    have hq_pos : (0 : ℝ) < params.q := by exact_mod_cast params.hq
    have hk_cast : (params.q : ℝ) ≤ k := by exact_mod_cast (lt_of_not_ge hk).le
    have hk1 : (1 : ℝ) ≤ k := le_trans (by exact_mod_cast params.hq) hk_cast
    have hterm : (1 : ℝ) ≤ ((k : ℝ) ^ (2 : ℕ)) / (params.q : ℝ) := by
      rw [le_div_iff₀ hq_pos, one_mul, sq]
      exact hk_cast.trans (le_mul_of_one_le_right (by positivity) hk1)
    linarith

/-- The pasted mass is the distinct average of globally consistent eligible mass. -/
theorem overAllOutcomesPastedMass_eq_avg_distinct_global
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (k : ℕ) :
    overAllOutcomesPastedMass params strategy family k =
      avgOver (distinctTupleDistribution params k) (fun xs =>
        strategy.state.subMeasMass
          ((restrictSubMeas (interpolationEligibleSandwichFamily params family k xs)
            (IsGloballyConsistent params xs)).liftLeft strategy.state)) :=
  strategy.state.ev_leftTensor_averageOperatorOverDistribution
    (distinctTupleDistribution params k)
    (fun xs =>
      (restrictSubMeas (interpolationEligibleSandwichFamily params family k xs)
        (IsGloballyConsistent params xs)).total)

/-- The expansion mass is the uniform average of eligible interpolation mass. -/
theorem overAllOutcomesExpansionMass_eq_avg_uniform_eligible
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (k : ℕ) :
    overAllOutcomesExpansionMass params strategy family k =
      avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
        strategy.state.subMeasMass
          ((interpolationEligibleSandwichFamily params family k xs).liftLeft strategy.state)) :=
  strategy.state.ev_leftTensor_averageOperatorOverDistribution
    (uniformDistribution (PointTuple params k))
    (fun xs => (interpolationEligibleSandwichFamily params family k xs).total)

/-- If there are not enough coordinates to interpolate, both sides of the reverse
mass comparison are zero. -/
theorem overAllOutcomes_reverse_mass_bound_of_not_d_add_one_le
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (eps delta gamma zeta : ℝ) (k : ℕ)
    (hnot : ¬ params.d + 1 ≤ k)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta) :
    overAllOutcomesExpansionMass params strategy family k -
        overAllOutcomesPastedMass params strategy family k ≤
      overAllOutcomesError params eps delta gamma zeta k := by
  set S := strategy.state
  have hzero : ∀ {X : 𝔓}, X = 0 → S.ev (S.L X) = 0 := fun hX => by
    rw [hX, map_zero, S.ev_zero]
  have htotal := interpolationEligibleSandwich_total_eq_zero_of_not_d_add_one_le params family hnot
  have hUzero : avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
      S.subMeasMass ((interpolationEligibleSandwichFamily params family k xs).liftLeft S)) = 0 :=
    (avgOver_congr _ _ _ fun xs => hzero (htotal xs)).trans (avgOver_zero _)
  have hDzero : avgOver (distinctTupleDistribution params k) (fun xs =>
      S.subMeasMass ((restrictSubMeas (interpolationEligibleSandwichFamily params family k xs)
          (IsGloballyConsistent params xs)).liftLeft S)) = 0 :=
    (avgOver_congr _ _ _ fun xs => hzero <| le_antisymm
      ((restrictSubMeas_total_le_total _ _).trans_eq (htotal xs)) (SubMeas.total_nonneg _)).trans
      (avgOver_zero _)
  rw [overAllOutcomesExpansionMass_eq_avg_uniform_eligible,
    overAllOutcomesPastedMass_eq_avg_distinct_global, hUzero, hDzero, sub_zero]
  exact mul_nonneg (by positivity) (oneThirtySecondErrorSum_nonneg params eps delta gamma zeta
    heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg)

/-- The pasted-minus-expansion mass loss is bounded by the distinctness error. -/
theorem overAllOutcomes_pasted_sub_expansion_le_dnoteq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (k : ℕ) :
    overAllOutcomesPastedMass params strategy family k -
        overAllOutcomesExpansionMass params strategy family k ≤
      ((k : ℝ) ^ (2 : ℕ)) / (params.q : ℝ) := by
  have hdist :
      overAllOutcomesPastedMass params strategy family k ≤
        avgOver (distinctTupleDistribution params k) (fun xs =>
          strategy.state.subMeasMass
            ((interpolationEligibleSandwichFamily params family k xs).liftLeft
              strategy.state)) := by
    rw [overAllOutcomesPastedMass_eq_avg_distinct_global]
    exact avgOver_mono _ _ _ fun xs => strategy.state.ev_mono _ _ <|
      strategy.state.leftTensor_mono (restrictSubMeas_total_le_total _ _)
  have hswap := avgOver_distinct_eligibleMass_le_uniform_add_dnoteq params strategy family k
  rw [overAllOutcomesExpansionMass_eq_avg_uniform_eligible]
  linarith

end MIPRE.LIDT.Co.Pasting

end

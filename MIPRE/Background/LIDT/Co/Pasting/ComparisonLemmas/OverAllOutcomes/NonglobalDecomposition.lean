/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/
ComparisonLemmas/OverAllOutcomes/NonglobalDecomposition.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.ComparisonLemmas.OverAllOutcomes.ErrorAndMass

@[expose] public section

/-!
# Section 12 pasting: over all outcomes — nonglobal-mass decomposition

Nonglobal-mass definitions, the vertical-line insertion, and the line-consistency
decomposition that splits the nonglobal eligible mass into the bad-line event and
the line-consistent residual: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/ComparisonLemmas/OverAllOutcomes/NonglobalDecomposition.lean`
in the port of `planning/c6b-plan.md` (milestone M11, section "Port conventions").

A strategy is a `SymStrat params.next 𝔓 K` and a slice family an `IdxPolyFamily params 𝔓`; the
masses are `strategy.state.subMeasMass` of left-placed submeasurements and the inserted masses
`strategy.state.ev (strategy.state.opTensor T B_f)`. The vendored proofs unfold `leftTensor`,
`opTensor` and `ev` to matrices; here the insertion of the vertical-line measurement is
`S.L T = S.opTensor T 1` (`map_one`, `mul_one`) followed by `S.opTensor_sum_right_univ` and
`S.ev_sum`, and the pointwise splits are `S.ev_mono` and `S.opTensor_mono_left`.
`subMeasMass_restrict_add_not`, a lemma on a placement, takes the model `S` as an explicit
first argument.

The vendored file has no classical declaration of its own; the error `hBConsistencyError` and
the scalar averaging lemmas are named through explicit `open` lists.

## Not ported

Nothing: every vendored declaration has a counterpart of the same name.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel Point PointTuple AxisParallelLine AxisLinePolynomial
  appendPoint zeroCoord lastCoord avgOver avgOver_mono avgOver_congr avgOver_add avgOver_comm
  avgOver_uniform_const uniformDistribution)
open MIPStarRE.LDT.Pasting (GHatTupleOutcome IsGloballyConsistent distinctTupleDistribution
  hBConsistencyError)
open MIPRE.LIDT.Co (SymModel SymStrat SubMeas IdxPolyFamily)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Distinct-tuple mass of interpolation-eligible but globally inconsistent outcomes.

This is the scalar quantity bounded in `ld-pasting.tex` lines 1174--1275 when the
proof removes the `Global_τ(x)` restriction.  It is the exact local residual
between the all-outcomes expansion over distinct tuples and the pasted/global
part. -/
noncomputable def overAllOutcomesDistinctNonglobalMass
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (k : ℕ) : ℝ :=
  avgOver (distinctTupleDistribution params k) (fun xs =>
    strategy.state.subMeasMass
      ((restrictSubMeas (interpolationEligibleSandwichFamily params family k xs)
        (fun gs => ¬ IsGloballyConsistent params xs gs)).liftLeft strategy.state))

/-- Scalar mass splits into globally consistent and nonglobal parts. -/
theorem subMeasMass_restrict_add_not
    {α : Type*} [Fintype α] (S : SymModel 𝔓 K)
    (A : SubMeas α 𝔓) (p : α → Prop) [DecidablePred p] :
    S.subMeasMass (A.liftLeft S) =
      S.subMeasMass ((restrictSubMeas A p).liftLeft S) +
        S.subMeasMass ((restrictSubMeas A (fun a => ¬ p a)).liftLeft S) := by
  have htotal :
      (restrictSubMeas A p).total + (restrictSubMeas A (fun a => ¬ p a)).total = A.total :=
    (Finset.sum_filter_add_sum_filter_not _ p A.outcome).trans A.sum_eq_total
  change S.ev (S.L A.total) =
    S.ev (S.L (restrictSubMeas A p).total) + S.ev (S.L (restrictSubMeas A (fun a => ¬ p a)).total)
  rw [← htotal, map_add, S.ev_add]

/-- Distinct eligible mass splits into pasted/global mass plus nonglobal mass. -/
theorem avgOver_distinct_eligibleMass_eq_global_add_nonglobal
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (k : ℕ) :
    avgOver (distinctTupleDistribution params k) (fun xs =>
        strategy.state.subMeasMass
          ((interpolationEligibleSandwichFamily params family k xs).liftLeft strategy.state)) =
      avgOver (distinctTupleDistribution params k) (fun xs =>
        strategy.state.subMeasMass
          ((restrictSubMeas (interpolationEligibleSandwichFamily params family k xs)
            (IsGloballyConsistent params xs)).liftLeft strategy.state)) +
        overAllOutcomesDistinctNonglobalMass params strategy family k :=
  (avgOver_congr _ _ _ fun xs => subMeasMass_restrict_add_not strategy.state
    (interpolationEligibleSandwichFamily params family k xs)
    (IsGloballyConsistent params xs)).trans (avgOver_add _ _ _)

/-- The distinct-tuple line-mismatch mass that appears after inserting the
vertical-line measurement in `ld-pasting.tex` lines 1178--1202.

This is the part paid for by the already-available one-point line comparison
statements.  The remaining `md/q` Schwartz--Zippel term is kept separate below. -/
noncomputable def overAllOutcomesDistinctBadLineMass
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (k : ℕ) : ℝ :=
  avgOver (uniformDistribution (Point params)) (fun u =>
    avgOver (distinctTupleDistribution params k) (fun xs =>
      hBConsistencyBadMass params strategy family u xs))

/-- The one-point line comparison hypotheses bound the inserted line-mismatch
mass by the displayed `hBConsistency` error.

Paper route: this is the aggregation in `ld-pasting.tex` lines 1186--1202,
using `prop:ld-dnoteq` plus `lem:ld-sandwich-line-one-point`. -/
theorem overAllOutcomes_distinct_bad_line_mass_le_hBConsistencyError
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
    overAllOutcomesDistinctBadLineMass params strategy family k ≤
      hBConsistencyError params eps delta gamma zeta k :=
  avgOver_distinct_badMass_le_hBConsistencyError_ofLinePointBounds
    params strategy family eps delta gamma zeta k hd
    heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg hline

/-- The vertical-line measurement is a genuine measurement, so its total is `1`.
This is the formal counterpart of the line `because B is a measurement` at
`ld-pasting.tex` lines 1178--1180. -/
theorem verticalLineMeasurementFamily_total_eq_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (u : Point params) :
    (verticalLineMeasurementFamily params strategy u).total = 1 :=
  (strategy.axisParallelMeasurement
    { base := appendPoint params u zeroCoord
      direction := lastCoord params }).total_eq_one

/-- Local version of `eq:B-appears-out-of-thin-air` for one distinct tuple `xs` and
one vertical-line question `u`.

It inserts the vertical-line measurement into the nonglobal eligible mass. -/
noncomputable def overAllOutcomesNonglobalInsertedMassLocal
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓) {k : ℕ}
    (u : Point params) (xs : PointTuple params k) : ℝ :=
  ∑ f : AxisLinePolynomial params.next,
    strategy.state.ev
      (strategy.state.opTensor
        (∑ gs : GHatTupleOutcome params k,
          if IsGloballyConsistent params xs gs then 0
          else (interpolationEligibleSandwichFamily params family k xs).outcome gs)
        ((verticalLineMeasurementFamily params strategy u).outcome f))

/-- The residual line-consistent nonglobal mass after the line-mismatch event has
been split off.

This is the formal version of the `consistent indicator` term in
`ld-pasting.tex` lines 1204--1232, before applying the interpolant witness and
Schwartz--Zippel.  It keeps the inserted vertical-line measurement explicit: for
each line answer `f`, we retain exactly the nonglobal eligible outcomes for which
no supported slice disagrees with `f` along the sampled vertical line. -/
noncomputable def overAllOutcomesLineConsistentNonglobalLocal
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓) {k : ℕ}
    (u : Point params) (xs : PointTuple params k) : ℝ :=
  ∑ f : AxisLinePolynomial params.next,
    strategy.state.ev
      (strategy.state.opTensor
        (∑ gs : GHatTupleOutcome params k,
          if (¬ IsGloballyConsistent params xs gs) ∧
              ¬ (∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
                ((gs i).get hiSome) u ≠ f (xs i)) then
            (interpolationEligibleSandwichFamily params family k xs).outcome gs
          else 0)
        ((verticalLineMeasurementFamily params strategy u).outcome f))

/-- Distinct-tuple average of the line-consistent nonglobal mass.

Paper anchor: this is the explicit line-answer term just before the
`Consistent_τ(g,y,u)` indicator in `ld-pasting.tex` lines 1204--1232.  The next
lemmas sum out the inserted measurement and reduce it to that indicator. -/
noncomputable def overAllOutcomesDistinctLineConsistentNonglobalMass
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (k : ℕ) : ℝ :=
  avgOver (uniformDistribution (Point params)) (fun u =>
    avgOver (distinctTupleDistribution params k) (fun xs =>
      overAllOutcomesLineConsistentNonglobalLocal params strategy family u xs))

/-- Local consistency-indicator mass after summing out the inserted vertical-line
measurement.

For fixed `u` and `xs`, it retains nonglobal eligible tuples for which there
exists some degree-`d` vertical-line answer matching every supported slice at `u`.
This is the Lean counterpart of the indicator
`Consistent_τ(g,y,u)` introduced at `ld-pasting.tex` lines 1204--1219. -/
noncomputable def overAllOutcomesLineConsistentIndicatorLocal
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓) {k : ℕ}
    (u : Point params) (xs : PointTuple params k) : ℝ :=
  strategy.state.subMeasMass
    ((restrictSubMeas (interpolationEligibleSandwichFamily params family k xs)
      (fun gs => (¬ IsGloballyConsistent params xs gs) ∧
        ∃ f : AxisLinePolynomial params.next,
          ¬ (∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
            ((gs i).get hiSome) u ≠ f (xs i)))).liftLeft strategy.state)

/-- Distinct-tuple average of the consistency-indicator nonglobal mass. -/
noncomputable def overAllOutcomesDistinctLineConsistentIndicatorMass
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (k : ℕ) : ℝ :=
  avgOver (uniformDistribution (Point params)) (fun u =>
    avgOver (distinctTupleDistribution params k) (fun xs =>
      overAllOutcomesLineConsistentIndicatorLocal params strategy family u xs))

/-- Inserting the vertical-line measurement leaves the local nonglobal mass
unchanged. -/
theorem nonglobal_mass_eq_inserted_vertical_measurement
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓) {k : ℕ}
    (u : Point params) (xs : PointTuple params k) :
    strategy.state.subMeasMass
        ((restrictSubMeas (interpolationEligibleSandwichFamily params family k xs)
          (fun gs => ¬ IsGloballyConsistent params xs gs)).liftLeft strategy.state) =
      overAllOutcomesNonglobalInsertedMassLocal params strategy family u xs := by
  set S := strategy.state
  set A := interpolationEligibleSandwichFamily params family k xs
  set B := verticalLineMeasurementFamily params strategy u
  have hT : (restrictSubMeas A (fun gs => ¬ IsGloballyConsistent params xs gs)).total =
      ∑ gs : GHatTupleOutcome params k,
        if IsGloballyConsistent params xs gs then 0 else A.outcome gs :=
    (Finset.sum_filter _ _).trans (Finset.sum_congr rfl fun gs _ => ite_not _ _ _)
  change S.ev (S.L _) = _
  rw [hT, ← mul_one (S.L _), ← map_one S.R, ← verticalLineMeasurementFamily_total_eq_one params
    strategy u, ← B.sum_eq_total]
  exact (congrArg S.ev (S.opTensor_sum_right_univ _ _)).trans (S.ev_sum _)

/-- Pointwise split: after inserting the vertical-line measurement, every nonglobal
outcome either contributes to the already-paid bad-line event or to the
line-consistent residual. -/
theorem nonglobal_insertedMass_le_badLineMass_add_lineConsistentLocal
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓) {k : ℕ}
    (u : Point params) (xs : PointTuple params k) :
    overAllOutcomesNonglobalInsertedMassLocal params strategy family u xs ≤
      hBConsistencyBadMass params strategy family u xs +
        overAllOutcomesLineConsistentNonglobalLocal params strategy family u xs := by
  set S := strategy.state
  unfold overAllOutcomesNonglobalInsertedMassLocal hBConsistencyBadMass
    overAllOutcomesLineConsistentNonglobalLocal
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun f _ => ?_
  rw [← S.ev_add, ← S.opTensor_add_left_local, ← Finset.sum_add_distrib]
  refine S.ev_mono _ _ (S.opTensor_mono_left (Finset.sum_le_sum fun gs _ => ?_)
    ((verticalLineMeasurementFamily params strategy u).outcome_pos f))
  have hA := (interpolationEligibleSandwichFamily params family k xs).outcome_pos gs
  by_cases hglobal : IsGloballyConsistent params xs gs <;>
    by_cases hbad : ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
      ((gs i).get hiSome) u ≠ f (xs i) <;>
    simp only [hglobal, hbad, ite_true, ite_false, not_true, not_false_eq_true, and_true,
      and_false, add_zero, zero_add, le_refl, hA]

/-- The explicit line-answer version of the line-consistent residual is bounded by
its consistency-indicator version, after summing out the vertical-line
measurement. -/
theorem lineConsistentLocal_le_indicatorLocal
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓) {k : ℕ}
    (u : Point params) (xs : PointTuple params k) :
    overAllOutcomesLineConsistentNonglobalLocal params strategy family u xs ≤
      overAllOutcomesLineConsistentIndicatorLocal params strategy family u xs := by
  set S := strategy.state
  set A := interpolationEligibleSandwichFamily params family k xs
  set B := verticalLineMeasurementFamily params strategy u
  set T : 𝔓 := ∑ gs : GHatTupleOutcome params k,
      if (¬ IsGloballyConsistent params xs gs) ∧
          ∃ f : AxisLinePolynomial params.next,
            ¬ (∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
              ((gs i).get hiSome) u ≠ f (xs i)) then
        A.outcome gs
      else 0 with hTdef
  have hterm : ∀ f : AxisLinePolynomial params.next,
      S.ev (S.opTensor
          (∑ gs : GHatTupleOutcome params k,
            if (¬ IsGloballyConsistent params xs gs) ∧
                ¬ (∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
                  ((gs i).get hiSome) u ≠ f (xs i)) then
              A.outcome gs
            else 0)
          (B.outcome f)) ≤
        S.ev (S.opTensor T (B.outcome f)) := fun f =>
    S.ev_mono _ _ <| S.opTensor_mono_left (Finset.sum_le_sum fun gs _ => by
      split_ifs with hlocal hind hind
      · exact le_rfl
      · exact absurd ⟨hlocal.1, f, hlocal.2⟩ hind
      · exact A.outcome_pos gs
      · exact le_rfl) (B.outcome_pos f)
  calc
    overAllOutcomesLineConsistentNonglobalLocal params strategy family u xs
      ≤ ∑ f : AxisLinePolynomial params.next, S.ev (S.opTensor T (B.outcome f)) :=
        Finset.sum_le_sum fun f _ => hterm f
    _ = S.ev (S.L T * S.R B.total) := by
        rw [← S.ev_sum, ← S.opTensor_sum_right_univ, B.sum_eq_total]
    _ = overAllOutcomesLineConsistentIndicatorLocal params strategy family u xs := by
        rw [verticalLineMeasurementFamily_total_eq_one, map_one, mul_one]
        exact congrArg (S.ev ∘ S.L) (Finset.sum_filter _ _).symm

/-- Averaged line-consistent residual after the explicit line answer is summed out. -/
theorem lineConsistentNonglobalMass_le_indicatorMass
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (k : ℕ) :
    overAllOutcomesDistinctLineConsistentNonglobalMass params strategy family k ≤
      overAllOutcomesDistinctLineConsistentIndicatorMass params strategy family k :=
  avgOver_mono _ _ _ fun u => avgOver_mono _ _ _ fun xs =>
    lineConsistentLocal_le_indicatorLocal params strategy family u xs

/-- Strict reduction of the old local residual: the nonglobal mass is bounded by
the already-isolated line-mismatch mass plus the narrower line-consistent nonglobal
residual.

This proves the insertion and finite-sum split from `ld-pasting.tex` lines
1174--1228.  The following indicator lemma then sums out the inserted measurement;
together they reduce the residual to the Schwartz--Zippel estimate at lines
1235--1275. -/
theorem overAllOutcomes_distinct_nonglobal_mass_le_bad_line_mass_add_lineConsistent
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (k : ℕ) :
    overAllOutcomesDistinctNonglobalMass params strategy family k ≤
      overAllOutcomesDistinctBadLineMass params strategy family k +
        overAllOutcomesDistinctLineConsistentNonglobalMass params strategy family k :=
  calc
    overAllOutcomesDistinctNonglobalMass params strategy family k
      = avgOver (distinctTupleDistribution params k) (fun xs =>
          avgOver (uniformDistribution (Point params)) (fun u =>
            overAllOutcomesNonglobalInsertedMassLocal params strategy family u xs)) :=
        avgOver_congr _ _ _ fun xs => (avgOver_uniform_const _).symm.trans <|
          avgOver_congr _ _ _ fun u =>
            nonglobal_mass_eq_inserted_vertical_measurement params strategy family u xs
    _ = avgOver (uniformDistribution (Point params)) (fun u =>
          avgOver (distinctTupleDistribution params k) (fun xs =>
            overAllOutcomesNonglobalInsertedMassLocal params strategy family u xs)) :=
        avgOver_comm _ _ _
    _ ≤ avgOver (uniformDistribution (Point params)) (fun u =>
          avgOver (distinctTupleDistribution params k) (fun xs =>
            hBConsistencyBadMass params strategy family u xs +
              overAllOutcomesLineConsistentNonglobalLocal params strategy family u xs)) :=
        avgOver_mono _ _ _ fun u => avgOver_mono _ _ _ fun xs =>
          nonglobal_insertedMass_le_badLineMass_add_lineConsistentLocal
            params strategy family u xs
    _ = _ := (avgOver_congr _ _ _ fun _ => avgOver_add _ _ _).trans (avgOver_add _ _ _)

end MIPRE.LIDT.Co.Pasting

end

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/
ComparisonLemmas/LdSandwichLineOnePoint/Endpoint.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.ComparisonLemmas.LdSandwichLineOnePoint.EndpointEquivs
public import MIPRE.Background.LIDT.Co.Pasting.Core.LdGbcon
public import MIPRE.Background.LIDT.MIPStarRE.LDT.Pasting.ComparisonLemmas.LdSandwichLineOnePoint.Endpoint

@[expose] public section

/-!
# Section 12 pasting: line one-point transport — endpoint lemmas

The endpoint lemmas of the line one-point transport: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/ComparisonLemmas/LdSandwichLineOnePoint/Endpoint.lean`
in the port of `planning/c6b-plan.md` (milestone M11, section "Port conventions").

A strategy is a `SymStrat params.next 𝔓 K` and the slice family an `IdxPolyFamily params 𝔓`, so
the right endpoint measurement is a local measurement in `𝔓`, and the two endpoint consistency
statements are `ConsRel`s on `strategy.state`. They come from `ldGbcon_of_axis_self` of
`Co/Pasting/Core/LdGbcon.lean`, reindexed along `pointNextEquiv` and then along the split of a
sandwiched-line question at its `i`-th coordinate; no swap or normalization hypothesis appears,
the vendored statements having none.

The left endpoint identity `ldSandwichLineOnePointLeftFamily_zero_eq_endpoint` (the sandwich
`Ĝ^{x_1} ⋯ Ĝ^{x_k} ⋯ Ĝ^{x_1}`, restricted to `g_1 ≠ ⊥` and read at `u`, is the evaluation of
`G^{x_1}` at `u`) holds in any ordered `⋆`-ring, and is proved here in `𝔓`: the tail of the
sandwich sums to the identity and `G^{x_1}_g` is a projection.

## Not ported

- `ldSandwichLineOnePoint_endpoint_sqrt_bound`: classical, imported.
- `ldSandwichLineOnePoint_endpoint_error_le`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel Fq Point PointTuple AxisParallelLine appendPoint
  truncatePoint pointHeight zeroCoord lastCoord uniformDistribution truncatePoint_appendPoint
  pointHeight_appendPoint)
open MIPStarRE.LDT.CommutativityPoints (pointNextEquiv)
open MIPStarRE.LDT.Pasting (GHatOutcome GHatTupleOutcome SandwichedLineQuestion pointTupleTail
  gHatTupleOutcomeConsEquiv' sandwichedLineQuestionSplitAtEquiv)
open MIPRE.LIDT.Co (SymStrat SubMeas Measurement IdxSubMeas IdxProjSubMeas IdxPolyFamily
  ProjSubMeas postprocess evaluateAt evaluateFiberFamilyAtNextPoint completeSubMeas)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The vertical-line measurement through `(u, 0)`, read at the height `x`: the right endpoint
`B^u_{f(x)}` of the line one-point transport, as a measurement. -/
noncomputable def ldSandwichLineOnePointRightEndpointMeasurement
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (ux : Point params × Fq params) : Measurement (Fq params) 𝔓 :=
  let ℓ : AxisParallelLine params.next :=
    { base := appendPoint params ux.1 zeroCoord
      direction := lastCoord params }
  postprocessMeasurement (strategy.axisParallelMeasurement ℓ).toMeasurement (fun f => f ux.2)

/-- The right endpoint measurement is the postprocessed vertical-line family. -/
theorem ldSandwichLineOnePointRightEndpointMeasurement_toSubMeas
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (ux : Point params × Fq params) :
    (ldSandwichLineOnePointRightEndpointMeasurement params strategy ux).toSubMeas =
      postprocess (verticalLineMeasurementFamily params strategy ux.1) (fun f => f ux.2) :=
  rfl

/-- The slice family evaluated at `u` is consistent with the vertical-line answer through
`(u, 0)` read at the height `x`, uniformly over `(u, x)`, with the error of `ldGbcon`. -/
theorem ldSandwichLineOnePoint_endpoint_ldGbcon_of_axis_self
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta zeta : ℝ)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself : strategy.selfConsistencyFailureProbability ≤ delta)
    (family : IdxPolyFamily params 𝔓)
    (hcons : family.ConsistentWithPoints strategy zeta) :
    strategy.state.ConsRel
      (uniformDistribution (Point params × Fq params))
      (fun ux => postprocess (evaluateAt params ux.1 ((family.meas ux.2).toSubMeas)) some)
      (fun ux =>
        postprocess
          (ldSandwichLineOnePointRightEndpointMeasurement params strategy ux).toSubMeas
          some)
        (zeta + Real.sqrt (8 * (params.m : ℝ) * eps + 4 * delta)) := by
  have hgb := ldGbcon_of_axis_self params strategy eps delta zeta haxis hself family hcons
  have hprod := (Preliminaries.consRel_uniform_equiv (pointNextEquiv params) strategy.state
    (evaluateFiberFamilyAtNextPoint params (IdxProjSubMeas.toIdxSubMeas family.meas))
    (fun u =>
      postprocess
        (verticalLineMeasurementFamily params strategy (truncatePoint params u))
        (fun f => f (pointHeight params u)))
    (zeta + Real.sqrt (8 * (params.m : ℝ) * eps + 4 * delta))).1 hgb
  have hproc := Preliminaries.consRelDataProcessing_questionDependent strategy.state
    (uniformDistribution (Point params × Fq params)) _ _ _ (fun _ a => some a) hprod
  simp only [pointNextEquiv, evaluateFiberFamilyAtNextPoint, IdxProjSubMeas.toIdxSubMeas,
    Equiv.coe_fn_symm_mk, truncatePoint_appendPoint, pointHeight_appendPoint] at hproc
  exact hproc

/-- The endpoint consistency of `ldSandwichLineOnePoint_endpoint_ldGbcon_of_axis_self`, lifted
to sandwiched-line questions through their split at the `i`-th coordinate. -/
theorem ldSandwichLineOnePoint_endpoint_ldGbcon_lift_of_axis_self
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta zeta : ℝ)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself : strategy.selfConsistencyFailureProbability ≤ delta)
    (family : IdxPolyFamily params 𝔓)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (k i : ℕ) (hi : i < k) :
    strategy.state.ConsRel
      (uniformDistribution (SandwichedLineQuestion params k))
      (fun q =>
        postprocess
          (evaluateAt params q.1 ((family.meas (q.2 ⟨i, hi⟩)).toSubMeas))
          some)
      (ldSandwichLineOnePointRightFamily params strategy family k i)
      (zeta + Real.sqrt (8 * (params.m : ℝ) * eps + 4 * delta)) := by
  let iFin : Fin k := ⟨i, hi⟩
  let Rest := {j : Fin k // j ≠ iFin} → Fq params
  let e := sandwichedLineQuestionSplitAtEquiv params iFin
  let endpointLeft : IdxSubMeas (SandwichedLineQuestion params k) (Option (Fq params)) 𝔓 :=
    fun q =>
      postprocess
        (evaluateAt params q.1 ((family.meas (q.2 iFin)).toSubMeas))
        some
  let endpointRight : IdxSubMeas (SandwichedLineQuestion params k) (Option (Fq params)) 𝔓 :=
    ldSandwichLineOnePointRightFamily params strategy family k i
  have hbase := ldSandwichLineOnePoint_endpoint_ldGbcon_of_axis_self
    params strategy eps delta zeta haxis hself family hcons
  have hprod := Preliminaries.consRel_uniform_prod_fst (β := Rest) strategy.state
    (fun ux : Point params × Fq params =>
      postprocess (evaluateAt params ux.1 ((family.meas ux.2).toSubMeas)) some)
    (fun ux : Point params × Fq params =>
      postprocess
        (ldSandwichLineOnePointRightEndpointMeasurement params strategy ux).toSubMeas
        some)
    (zeta + Real.sqrt (8 * (params.m : ℝ) * eps + 4 * delta)) hbase
  refine (Preliminaries.consRel_uniform_equiv e strategy.state endpointLeft endpointRight
    (zeta + Real.sqrt (8 * (params.m : ℝ) * eps + 4 * delta))).2 ?_
  convert hprod using 2
  · simp [e, endpointLeft, iFin, sandwichedLineQuestionSplitAtEquiv]
  · simp only [ne_eq, sandwichedLineQuestionSplitAtEquiv, Equiv.coe_fn_symm_mk,
      ldSandwichLineOnePointRightFamily, hi, ↓reduceDIte, Equiv.funSplitAt_symm_apply,
      ldSandwichLineOnePointRightEndpointMeasurement_toSubMeas, endpointRight, iFin, e]
    exact (postprocess_postprocess _ _ _).symm

/-- The `some a` outcome of `Ĝ^x` read at `u` is the outcome `a` of `G^x` evaluated at `u`. -/
theorem gHatIdxMeas_outcome_some_eq_evaluateAt
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    (x : Fq params) (u : Point params) (a : Fq params) :
    (∑ g : GHatOutcome params,
      if Option.map (fun g' : MIPStarRE.LDT.Polynomial params => g' u) g = some a then
        (gHatIdxMeas params family x).outcome g
      else
        0) =
      (evaluateAt params u ((family.meas x).toSubMeas)).outcome a := by
  rw [Fintype.sum_option]
  simp [gHatIdxMeas, completeSubMeas, evaluateAt, postprocess, Finset.sum_filter]

/-- The `some a` outcome of the sandwich restricted to `g_1 ≠ ⊥` and read at `u`, as a sum of
squared half-products. -/
theorem gHatSandwichFamily_restrict_zero_outcome_some
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    {n : ℕ} (xs : PointTuple params (n + 1))
    (u : Point params) (a : Fq params) :
    (postprocess
      (restrictSubMeas (gHatSandwichFamily params family (n + 1) xs)
        (fun gs => (gs 0).isSome = true))
      (fun gs => Option.map (fun g : MIPStarRE.LDT.Polynomial params => g u) (gs 0))).outcome
        (some a) =
      ∑ gs : GHatTupleOutcome params (n + 1),
        if Option.map (fun g : MIPStarRE.LDT.Polynomial params => g u) (gs 0) = some a then
          let half := gHatHalfProductOutcomeOperator params family (n + 1) xs gs
          half * star half
        else
          0 := by
  simp only [postprocess, restrictSubMeas, gHatSandwichFamily, Finset.sum_filter]
  refine Finset.sum_congr rfl fun gs _ => ?_
  by_cases hmap : Option.map (fun g : MIPStarRE.LDT.Polynomial params => g u) (gs 0) = some a
  · obtain ⟨g, hgs0, _⟩ := Option.map_eq_some_iff.mp hmap
    simp [hgs0]
  · simp [hmap]

/-- Evaluating a polynomial submeasurement and tagging the result with `some` puts no mass
on `none`. -/
theorem evaluateAt_postprocess_some_outcome_none_eq_zero
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    (x : Fq params) (u : Point params) :
    (postprocess (evaluateAt params u ((family.meas x).toSubMeas)) some).outcome none = 0 := by
  simp [evaluateAt, postprocess]

/-- The sandwich restricted to `g_1 ≠ ⊥` and read at `u` puts no mass on `none`. -/
theorem gHatSandwichFamily_restrict_zero_outcome_none_eq_zero
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    {n : ℕ} (xs : PointTuple params (n + 1))
    (u : Point params) :
    (postprocess
      (restrictSubMeas (gHatSandwichFamily params family (n + 1) xs)
        (fun gs => (gs 0).isSome = true))
      (fun gs => Option.map (fun g : MIPStarRE.LDT.Polynomial params => g u) (gs 0))).outcome
        none = 0 := by
  simp only [postprocess, restrictSubMeas, gHatSandwichFamily, Finset.sum_filter]
  refine Finset.sum_eq_zero fun gs _ => ?_
  by_cases hsome : (gs 0).isSome = true
  · obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp hsome
    simp [hg]
  · simp [hsome]

/-- The `some a` outcome of the left family at the first coordinate is the outcome `a` of
`G^{x_1}` evaluated at `u`. -/
theorem ldSandwichLineOnePointLeftFamily_zero_outcome_some_eq_endpoint
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    {k : ℕ} (hk : 0 < k)
    (q : SandwichedLineQuestion params k) (a : Fq params) :
    ((ldSandwichLineOnePointLeftFamily params strategy family k 0) q).outcome (some a) =
      (evaluateAt params q.1 ((family.meas (q.2 ⟨0, hk⟩)).toSubMeas)).outcome a := by
  cases k with
  | zero => cases hk
  | succ r =>
      let xs : PointTuple params (r + 1) := q.2
      let u : Point params := q.1
      let G : GHatOutcome params → 𝔓 := fun g =>
        (gHatIdxMeas params family (xs 0)).outcome g
      let T : GHatTupleOutcome params r → 𝔓 := fun gs =>
        gHatHalfProductOutcomeOperator params family r (pointTupleTail xs) gs
      have hleft :
          ((ldSandwichLineOnePointLeftFamily params strategy family (r + 1) 0) q).outcome
              (some a) =
            ∑ gs : GHatTupleOutcome params (r + 1),
              if Option.map (fun g : MIPStarRE.LDT.Polynomial params => g u) (gs 0) = some a then
                let half := gHatHalfProductOutcomeOperator params family (r + 1) xs gs
                half * star half
              else
                0 := by
        exact gHatSandwichFamily_restrict_zero_outcome_some params family xs u a
      have htail : (∑ gs : GHatTupleOutcome params r, T gs * star (T gs)) = 1 := by
        refine (gHatSandwichFamily params family r (pointTupleTail xs)).sum_eq_total.trans ?_
        change gHatHalfProductTotalOperator params family r (pointTupleTail xs) *
          star (gHatHalfProductTotalOperator params family r (pointTupleTail xs)) = 1
        rw [gHatHalfProductTotalOperator_eq_one, star_one, mul_one]
      have hterm : ∀ g : GHatOutcome params,
          (∑ gs : GHatTupleOutcome params r,
            if Option.map (fun g' : MIPStarRE.LDT.Polynomial params => g' u) g = some a then
              (G g * T gs) * star (G g * T gs)
            else
              0) =
            if Option.map (fun g' : MIPStarRE.LDT.Polynomial params => g' u) g = some a then
              G g
            else
              0 := by
        intro g
        by_cases hmap : Option.map (fun g' : MIPStarRE.LDT.Polynomial params => g' u) g = some a
        · have hherm : star (G g) = G g := (gHatIdxMeas params family (xs 0)).outcome_hermitian g
          have hproj : G g * G g = G g := gHatIdxMeas_proj params family (xs 0) g
          simp only [hmap, ite_true]
          calc
            (∑ gs : GHatTupleOutcome params r, (G g * T gs) * star (G g * T gs))
                = G g * (∑ gs : GHatTupleOutcome params r, T gs * star (T gs)) * G g := by
                  rw [Finset.mul_sum, Finset.sum_mul]
                  refine Finset.sum_congr rfl fun gs _ => ?_
                  rw [star_mul, hherm]
                  simp only [mul_assoc]
            _ = G g := by rw [htail, mul_one, hproj]
        · simp [hmap]
      calc
        ((ldSandwichLineOnePointLeftFamily params strategy family (r + 1) 0) q).outcome
            (some a)
            = ∑ gs : GHatTupleOutcome params (r + 1),
              if Option.map (fun g : MIPStarRE.LDT.Polynomial params => g u) (gs 0) = some a then
                let half := gHatHalfProductOutcomeOperator params family (r + 1) xs gs
                half * star half
              else
                0 := hleft
        _ = ∑ p : GHatOutcome params × GHatTupleOutcome params r,
              if Option.map (fun g : MIPStarRE.LDT.Polynomial params => g u) p.1 = some a then
                (G p.1 * T p.2) * star (G p.1 * T p.2)
              else
                0 :=
          Fintype.sum_equiv (gHatTupleOutcomeConsEquiv' params r) _ _ fun _ => rfl
        _ = ∑ g : GHatOutcome params,
              if Option.map (fun g' : MIPStarRE.LDT.Polynomial params => g' u) g = some a then
                G g
              else
                0 := by
          rw [Fintype.sum_prod_type]
          exact Finset.sum_congr rfl fun g _ => hterm g
        _ = (evaluateAt params u ((family.meas (xs 0)).toSubMeas)).outcome a :=
          gHatIdxMeas_outcome_some_eq_evaluateAt params family (xs 0) u a

/-- The left family at the first coordinate is the evaluation of `G^{x_1}` at `u`, tagged with
`some`: the left endpoint of the line one-point transport. -/
theorem ldSandwichLineOnePointLeftFamily_zero_eq_endpoint
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    {k : ℕ} (hk : 0 < k) :
    ldSandwichLineOnePointLeftFamily params strategy family k 0 =
      (fun q : SandwichedLineQuestion params k =>
        postprocess
          (evaluateAt params q.1 ((family.meas (q.2 ⟨0, hk⟩)).toSubMeas))
          some) := by
  funext q
  have houtcome : ∀ o : Option (Fq params),
      ((ldSandwichLineOnePointLeftFamily params strategy family k 0) q).outcome o =
        (postprocess
          (evaluateAt params q.1 ((family.meas (q.2 ⟨0, hk⟩)).toSubMeas)) some).outcome o := by
    intro o
    cases o with
    | none =>
        cases k with
        | zero => cases hk
        | succ r =>
            have hleftNone :
                ((ldSandwichLineOnePointLeftFamily params strategy family (r + 1) 0) q).outcome
                    none = 0 := by
              simpa [ldSandwichLineOnePointLeftFamily] using
                gHatSandwichFamily_restrict_zero_outcome_none_eq_zero params family q.2 q.1
            rw [hleftNone,
              evaluateAt_postprocess_some_outcome_none_eq_zero params family (q.2 ⟨0, hk⟩) q.1]
    | some a =>
        simpa [postprocess, Finset.sum_filter] using
          ldSandwichLineOnePointLeftFamily_zero_outcome_some_eq_endpoint
            params strategy family hk q a
  refine SubMeas.ext houtcome ?_
  rw [← ((ldSandwichLineOnePointLeftFamily params strategy family k 0) q).sum_eq_total,
    ← (postprocess
      (evaluateAt params q.1 ((family.meas (q.2 ⟨0, hk⟩)).toSubMeas)) some).sum_eq_total]
  exact Finset.sum_congr rfl fun o _ => houtcome o

end MIPRE.LIDT.Co.Pasting

end

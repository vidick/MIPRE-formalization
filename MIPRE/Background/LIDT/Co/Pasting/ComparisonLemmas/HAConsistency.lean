/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/
ComparisonLemmas/HAConsistency.lean, to the symmetric model of `planning/c6b-plan.md`; not a
vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.ComparisonLemmas.HBConsistency
public import MIPRE.Background.LIDT.Co.Pasting.CommutingWithG.Incomplete

@[expose] public section

/-!
# Section 12 pasting: H-A consistency

The vertical-line to point-consistency transport and the completed-measurement statement of
`cor:h-a-consistency`: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/ComparisonLemmas/HAConsistency.lean` in the port of
`planning/c6b-plan.md` (milestone M11, section "Port conventions").

A strategy is a `SymStrat params.next 𝔓 K`, a slice family an `IdxPolyFamily params 𝔓` and a
candidate polynomial submeasurement `H : SubMeas (Polynomial params.next) 𝔓`; the consistency
statements are `ConsRel`s on `strategy.state`, and the completeness hypothesis is
`strategy.state.CompletenessAtLeast (H.liftLeft strategy.state) …`. Three uses of the vendored
strategy fields become theorems of the model:
- the bounds of the two failure probabilities by `1` (vendored through `strategy.isNormalized`)
  are `S.bipartiteConsError_uniform_le_one` and `Pasting.bipartiteSSCError_uniform_le_one`;
- the swap of the consistency relation (vendored through `strategy.densityFixed`) is
  `S.consRel_symm_of_density_fixed`, and the triangle step `Preliminaries.triangleSub_right`
  takes no normalization argument;
- the residual mass `ev(R(1 − H.total)) = 1 − ev(L H.total)` (vendored through
  `strategy.permInvState.swap_ev`, an entrywise Kronecker identity and
  `ev_one_of_isNormalized`) is `S.ev_L_eq_ev_R`, `S.leftTensor_sub` and
  `S.ev_one_of_isNormalized`.
No statement carries a swap or normalization hypothesis, the vendored statements having none.

## Not ported

Nothing: every vendored declaration has a counterpart of the same name.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel Fq Point AxisParallelTestSample avgOver avgOver_mono
  avgOver_add avgOver_uniform_const uniformDistribution uniformDistribution_weight_sum_le_one
  appendPoint truncatePoint zeroCoord lastCoord pointHeight)
open MIPStarRE.LDT.CommutativityPoints (pointNextEquiv)
open MIPStarRE.LDT.MainInductionStep (ldPastingInInductionNu ldPastingInInductionError)
open MIPStarRE.LDT.Pasting (VerticalLineQuestion hBConsistencyError
  hAConsistency_error_le_nu_of_pos ldPastingCompletenessLowerBound pastedFallbackOutcome)
open MIPRE.LIDT.Co (SymStrat SubMeas IdxMeas IdxProjMeas IdxPolyFamily postprocess evaluateAt
  polynomialEvaluationFamily gamma_nonneg_of_isGood axisParallelPointAnswerFamily
  axisParallelLineAnswerFamily)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Convert source-style vertical-line consistency to point consistency using only
the axis-parallel and self-consistency estimates.

This is the main estimate in `cor:h-a-consistency`, stated without the
intermediate `HBConsistencyStatement` type.  It takes only the line-consistency estimate
for a candidate polynomial submeasurement `H`, restricts that estimate to the
point on each vertical line, and then applies the good-strategy
point-to-vertical-line comparison.  The diagonal-line estimate in
`strategy.IsGood` is not used in this transport step; it enters earlier in the
construction of the line-consistency estimate.

Paper reference: `cor:h-a-consistency` proof in `ld-pasting.tex`
lines 1098–1117.

Steps:
1. Restrict the line-consistency hypothesis to a single point on the line
2. Apply `triangleSub` with the `A-B` consistency bound from `hgood`
3. Error bound: `ν₆ + √(8mε + 4δ) ≤ 47k²m(...) ≤ 100k²m(...)`.

The completion and large-`k` hypotheses are carried by the downstream
completed-measurement theorem; this submeasurement argument only uses the positive
`k` regime and the displayed line-consistency estimate. -/
theorem hAConsistency_submeas_from_lineConsistency_of_axis_self
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (H : SubMeas (MIPStarRE.LDT.Polynomial params.next) 𝔓)
    (eps delta gamma zeta : ℝ)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself_good : strategy.selfConsistencyFailureProbability ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (hline :
      strategy.state.ConsRel (uniformDistribution (Point params))
        (hRestrictionToVerticalLine params H)
        (verticalLineMeasurementFamily params strategy)
        (hBConsistencyError params eps delta gamma zeta k)) :
    strategy.state.ConsRel (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next H)
        (ldPastingInInductionNu params k eps delta gamma zeta) := by
  let pointLineMeas : IdxMeas (Point params.next) (Fq params.next) 𝔓 := fun u =>
    { toSubMeas := liftedVerticalLineAnswerFamily params strategy u
      total_eq_one :=
        (strategy.axisParallelMeasurement
          { base := appendPoint params (truncatePoint params u) zeroCoord
            direction := lastCoord params }).total_eq_one }
  let pointMeas : IdxMeas (Point params.next) (Fq params.next) 𝔓 :=
    fun u => (strategy.pointMeasurement u).toMeasurement
  let νB := hBConsistencyError params eps delta gamma zeta k
  let eps' : ℝ := min eps 1
  let delta' : ℝ := min delta 1
  have haxis_small : strategy.axisParallelFailureProbability ≤ eps' :=
    le_min haxis (strategy.state.bipartiteConsError_uniform_le_one
      (axisParallelPointAnswerFamily strategy) (axisParallelLineAnswerFamily strategy))
  have hself_small : strategy.selfConsistencyFailureProbability ≤ delta' :=
    le_min hself_good (bipartiteSSCError_uniform_le_one strategy.state
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
  have heps_nonneg : 0 ≤ eps :=
    (strategy.state.bipartiteConsError_nonneg
      (uniformDistribution (AxisParallelTestSample params.next))
      (axisParallelPointAnswerFamily strategy)
      (axisParallelLineAnswerFamily strategy)).trans haxis
  have hdelta_nonneg : 0 ≤ delta :=
    (strategy.state.bipartiteSSCError_nonneg
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)).trans hself_good
  have hline_next :
      strategy.state.ConsRel (uniformDistribution (Point params.next))
        (fun u => hRestrictionToVerticalLine params H (truncatePoint params u))
        (fun u => verticalLineMeasurementFamily params strategy (truncatePoint params u))
        νB :=
    (Preliminaries.consRel_uniform_equiv (pointNextEquiv params).symm strategy.state
      (fun ux => hRestrictionToVerticalLine params H ux.1)
      (fun ux => verticalLineMeasurementFamily params strategy ux.1) νB).1
      (consRel_uniform_fst (β := Fq params) strategy.state
        (hRestrictionToVerticalLine params H)
        (verticalLineMeasurementFamily params strategy) νB hline)
  have hline_point :
      strategy.state.ConsRel (uniformDistribution (Point params.next))
        (polynomialEvaluationFamily params.next H)
        (IdxMeas.toIdxSubMeas pointLineMeas)
        νB := by
    have hproc :=
      Preliminaries.consRelDataProcessing_questionDependent strategy.state
        (uniformDistribution (Point params.next))
        (fun u => hRestrictionToVerticalLine params H (truncatePoint params u))
        (fun u => verticalLineMeasurementFamily params strategy (truncatePoint params u))
        νB (fun u f => f (pointHeight params u)) hline_next
    rw [show (fun u : Point params.next =>
        postprocess (hRestrictionToVerticalLine params H (truncatePoint params u))
          (fun f => f (pointHeight params u))) = polynomialEvaluationFamily params.next H from
      funext fun u => postprocess_hRestrictionToVerticalLine_eq_evaluateAt params H u] at hproc
    exact hproc
  have hpoint_sdd :
      strategy.state.SDDRel (uniformDistribution (Point params.next))
        (IdxSubMeas.liftRight strategy.state (IdxMeas.toIdxSubMeas pointLineMeas))
        (IdxSubMeas.liftRight strategy.state (IdxMeas.toIdxSubMeas pointMeas))
        (8 * (params.m : ℝ) * eps' + 4 * delta') :=
    Preliminaries.sddRel_symm strategy.state.toVecState (uniformDistribution (Point params.next))
      (IdxSubMeas.liftRight strategy.state (IdxMeas.toIdxSubMeas pointMeas))
      (IdxSubMeas.liftRight strategy.state (IdxMeas.toIdxSubMeas pointLineMeas)) _
      (pointVerticalLineSdd_liftedVerticalLine_of_axis_self params strategy eps' delta'
        haxis_small hself_small)
  have htri :=
    Preliminaries.triangleSub_right strategy.state (uniformDistribution (Point params.next))
      (by simpa using uniformDistribution_weight_sum_le_one (Point params.next))
      (polynomialEvaluationFamily params.next H) pointLineMeas pointMeas νB
      (8 * (params.m : ℝ) * eps' + 4 * delta') hline_point hpoint_sdd
  exact ⟨((strategy.state.consRel_symm_of_density_fixed _ _ _ _ htri).offDiagonalBound).trans
    (hAConsistency_error_le_nu_of_pos params eps delta gamma zeta k hk_pos
      heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg)⟩

/-- Convert source-style vertical-line consistency to point consistency.

This source-style restatement specializes
`hAConsistency_submeas_from_lineConsistency_of_axis_self` to the two estimates
contained in `strategy.IsGood`. -/
theorem hAConsistency_submeas_from_lineConsistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (H : SubMeas (MIPStarRE.LDT.Polynomial params.next) 𝔓)
    (eps delta gamma zeta : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (hline :
      strategy.state.ConsRel (uniformDistribution (Point params))
        (hRestrictionToVerticalLine params H)
        (verticalLineMeasurementFamily params strategy)
        (hBConsistencyError params eps delta gamma zeta k)) :
    strategy.state.ConsRel (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next H)
        (ldPastingInInductionNu params k eps delta gamma zeta) :=
  hAConsistency_submeas_from_lineConsistency_of_axis_self params strategy H
    eps delta gamma zeta hgood.axisParallelTest hgood.selfConsistencyTest
    hgamma_nonneg hzeta_nonneg k hk_pos hline

/-- Specialization of `hAConsistency_submeas_from_lineConsistency` to the
constructed pasted submeasurement. -/
theorem hAConsistency_submeas_core_of_axis_self
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (eps delta gamma zeta : ℝ)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself_good : strategy.selfConsistencyFailureProbability ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (hHB : HBConsistencyStatement params strategy family
        eps delta gamma zeta k) :
    strategy.state.ConsRel (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next
        (constructedPastedSubMeas params family k))
        (ldPastingInInductionNu params k eps delta gamma zeta) :=
  hAConsistency_submeas_from_lineConsistency_of_axis_self params strategy
    (constructedPastedSubMeas params family k) eps delta gamma zeta
    haxis hself_good hgamma_nonneg hzeta_nonneg k hk_pos hHB.lineConsistency

/-- Internal form of `cor:h-a-consistency` from the one-point sandwich estimates.

This theorem separates the genuinely earlier pasting input from the diagonal
test.  Once the estimates of `lem:ld-sandwich-line-one-point` are known for all
positions, the passage from `H-B` consistency to `H-A` consistency uses only the
axis-parallel and self-consistency estimates of the ambient strategy. -/
theorem hAConsistency_submeas_ofLinePointBounds_of_axis_self
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma zeta : ℝ)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself_good : strategy.selfConsistencyFailureProbability ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta)
    (hd : 0 < params.d)
    (family : IdxPolyFamily params 𝔓)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (hline : ∀ i : ℕ, i < k →
      LdSandwichLineOnePointStatement params strategy family
        eps delta gamma zeta k i) :
    strategy.state.ConsRel (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next
          (constructedPastedSubMeas params family k))
        (ldPastingInInductionNu params k eps delta gamma zeta) :=
  hAConsistency_submeas_core_of_axis_self params strategy family
    eps delta gamma zeta haxis hself_good hgamma_nonneg hzeta_nonneg k hk_pos
    (hBConsistency_ofLinePointBounds_of_axis_self params strategy
      eps delta gamma zeta haxis hself_good hgamma_nonneg hd
      family hcons hself hbound k hline)

/-- Internal form of `cor:h-a-consistency` from `cor:G-hat-facts`.

This is the same proof as
`hAConsistency_submeas_ofLinePointBounds_of_axis_self`, with the one-point
sandwich estimates constructed from `GHatFactsStatement`. -/
theorem hAConsistency_submeas_ofGHatFacts_of_axis_self
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma zeta : ℝ)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself_good : strategy.selfConsistencyFailureProbability ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta)
    (hzeta_le : zeta ≤ 1)
    (hd : 0 < params.d)
    (family : IdxPolyFamily params 𝔓)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (hfacts : GHatFactsStatement params strategy.state family gamma zeta)
    (k : ℕ)
    (hk_pos : 1 ≤ k) :
    strategy.state.ConsRel (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next
          (constructedPastedSubMeas params family k))
        (ldPastingInInductionNu params k eps delta gamma zeta) :=
  hAConsistency_submeas_ofLinePointBounds_of_axis_self params strategy
    eps delta gamma zeta haxis hself_good hgamma_nonneg hzeta_nonneg hd
    family hcons hself hbound k hk_pos fun i hi =>
      ldSandwichLineOnePoint_ofGHatFacts_of_axis_self params strategy
        eps delta gamma zeta haxis hself_good hgamma_nonneg hzeta_le
        family hcons hfacts k i hi

/-- Internal form of `cor:h-a-consistency` from the Section 11 commutativity
conclusion.

This exposes the precise upstream mathematical input needed for the `G-hat`
construction.  The diagonal-line estimate is not used in the `H-B` to `H-A`
transport; it is used only insofar as it is needed to prove the commutativity
conclusion supplied here. -/
theorem hAConsistency_submeas_ofComMain_of_axis_self
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
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (hcom : Commutativity.ComMainConclusion params strategy family gamma zeta)
    (k : ℕ)
    (hk_pos : 1 ≤ k) :
    strategy.state.ConsRel (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next
          (constructedPastedSubMeas params family k))
        (ldPastingInInductionNu params k eps delta gamma zeta) :=
  hAConsistency_submeas_ofGHatFacts_of_axis_self params strategy
    eps delta gamma zeta haxis hself_good hgamma_nonneg hzeta_nonneg
    hzeta_le hd family hcons hself hbound
    (gHatFacts_ofComMainAndSelfConsistency params strategy family gamma zeta
      hgamma_nonneg hgamma_le hzeta_nonneg hzeta_le hdq_le hcom hself) k hk_pos

/-- `cor:h-a-consistency`.

This is the point-consistency part of the pasted-submeasurement chain.  The
completed-measurement consistency is deliberately separated as
`hAConsistency_completed`, since the paper proves it only after
`cor:ld-pasting-N-completeness`. -/
theorem hAConsistency_submeas
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
    (k : ℕ)
    (hk_pos : 1 ≤ k) :
    strategy.state.ConsRel (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next
          (constructedPastedSubMeas params family k))
        (ldPastingInInductionNu params k eps delta gamma zeta) :=
  hAConsistency_submeas_core_of_axis_self params strategy family
    eps delta gamma zeta hgood.axisParallelTest hgood.selfConsistencyTest
    (gamma_nonneg_of_isGood params.next strategy hgood)
    (IdxPolyFamily.zeta_nonneg_of_consistentWithPoints strategy family hcons) k hk_pos
    (hBConsistency params strategy eps delta gamma zeta
      hgood hgamma_le hzeta_le hdq_le hd family hcons hself hbound k)

/-- Complete a polynomial submeasurement after its point consistency and mass
lower bound have been proved.

This is the completion step in `cor:h-a-consistency`, stated for an arbitrary
submeasurement `H`.  The source argument first proves point consistency for a
submeasurement and then completes it by adding the missing mass to a fixed
fallback polynomial. -/
theorem hAConsistency_completed_from_submeas
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma kappa zeta : ℝ)
    (H : SubMeas (MIPStarRE.LDT.Polynomial params.next) 𝔓)
    (k : ℕ)
    (hsubmeas :
      strategy.state.ConsRel (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next H)
        (ldPastingInInductionNu params k eps delta gamma zeta))
    (hcomplete :
      strategy.state.CompletenessAtLeast (H.liftLeft strategy.state)
        (ldPastingCompletenessLowerBound params kappa
          (ldPastingInInductionNu params k eps delta gamma zeta) k)) :
    strategy.state.ConsRel (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params.next
        (Preliminaries.completeAtOutcome H (pastedFallbackOutcome params)).toSubMeas)
      (ldPastingInInductionError params k eps delta gamma kappa zeta) := by
  set ν := ldPastingInInductionNu params k eps delta gamma zeta
  set S := strategy.state
  have hcompletedEval :
      (fun u => (Preliminaries.completeAtOutcome (evaluateAt params.next u H)
          ((pastedFallbackOutcome params) u)).toSubMeas) =
        polynomialEvaluationFamily params.next
          (Preliminaries.completeAtOutcome H (pastedFallbackOutcome params)).toSubMeas :=
    funext fun u => (Preliminaries.evaluateAt_completeAtOutcome params.next H
      (pastedFallbackOutcome params) u).symm
  have hresidualMass :
      S.ev (S.R (1 - H.total)) ≤
        kappa * (1 + 1 / (100 * (params.m : ℝ))) + ν +
          Real.exp (-((k : ℝ) / (80000 * ((params.m : ℝ) ^ (2 : ℕ))))) := by
    have hmass : S.ev (S.L H.total) ≥ ldPastingCompletenessLowerBound params kappa ν k :=
      hcomplete.lowerBound
    rw [← S.ev_L_eq_ev_R, ← S.leftTensor_sub, S.leftTensor_one, S.ev_sub,
      S.ev_one_of_isNormalized]
    have hlb : ldPastingCompletenessLowerBound params kappa ν k =
        1 - (kappa * (1 + 1 / (100 * (params.m : ℝ))) + ν +
          Real.exp (-((k : ℝ) / (80000 * ((params.m : ℝ) ^ (2 : ℕ)))))) := by
      simp [ldPastingCompletenessLowerBound]
      ring
    linarith
  have hcompleted :
      S.bipartiteConsError (uniformDistribution (Point params.next))
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          (fun u => (Preliminaries.completeAtOutcome (evaluateAt params.next u H)
            ((pastedFallbackOutcome params) u)).toSubMeas) ≤
        ν + S.ev (S.R (1 - H.total)) :=
    calc
      _ ≤ avgOver (uniformDistribution (Point params.next)) (fun u =>
            S.qBipartiteConsDefect (strategy.pointMeasurement u).toSubMeas
                (evaluateAt params.next u H) +
              S.ev (S.R (1 - H.total))) :=
        avgOver_mono _ _ _ fun u =>
          Preliminaries.qBipartiteConsDefect_completeAtOutcome_right_le S
            (strategy.pointMeasurement u).toMeasurement (evaluateAt params.next u H)
            ((pastedFallbackOutcome params) u)
      _ = S.bipartiteConsError (uniformDistribution (Point params.next))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
            (polynomialEvaluationFamily params.next H) +
          S.ev (S.R (1 - H.total)) :=
        (avgOver_add _ _ _).trans (congrArg _ (avgOver_uniform_const _))
      _ ≤ ν + S.ev (S.R (1 - H.total)) :=
        add_le_add hsubmeas.offDiagonalBound le_rfl
  refine ⟨hcompletedEval ▸ hcompleted.trans ((add_le_add le_rfl hresidualMass).trans_eq ?_)⟩
  simp [ldPastingInInductionError, ν]
  ring

/-- Completed-measurement version of `cor:h-a-consistency`.

This theorem is intentionally downstream of `cor:ld-pasting-N-completeness`:
it may use the submeasurement consistency together with the completeness bound
for the constructed pasted submeasurement to control the added completion mass. -/
theorem hAConsistency_completed
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma kappa zeta : ℝ)
    (family : IdxPolyFamily params 𝔓)
    (k : ℕ)
    (hsubmeas :
      strategy.state.ConsRel (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next
          (constructedPastedSubMeas params family k))
        (ldPastingInInductionNu params k eps delta gamma zeta))
    (hcomplete :
      strategy.state.CompletenessAtLeast
        ((constructedPastedSubMeas params family k).liftLeft strategy.state)
        (ldPastingCompletenessLowerBound params kappa
          (ldPastingInInductionNu params k eps delta gamma zeta) k)) :
    strategy.state.ConsRel (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params.next
        (constructedPastedMeasurement params family k).toSubMeas)
      (ldPastingInInductionError params k eps delta gamma kappa zeta) :=
  hAConsistency_completed_from_submeas params strategy eps delta gamma kappa zeta
    (constructedPastedSubMeas params family k) k hsubmeas hcomplete

end MIPRE.LIDT.Co.Pasting

end

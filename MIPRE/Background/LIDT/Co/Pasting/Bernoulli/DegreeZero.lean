/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/Bernoulli/
DegreeZero.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.Bernoulli.ScalarBounds
public import MIPRE.Background.LIDT.Co.Pasting.ComparisonLemmas.HAConsistency
public import MIPStarRE.LDT.Pasting.Bernoulli.DegreeZero

@[expose] public section

/-!
# Section 12 pasting: degree-zero branch

Auxiliary constructions for the `d = 0` complementary branch of `thm:ld-pasting`: the
counterpart of `MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Bernoulli/DegreeZero.lean` in the port
of `planning/c6b-plan.md` (milestone M11, section "Port conventions").

A strategy is a `SymStrat params.next 𝔓 K` and a slice family an `IdxPolyFamily params 𝔓`; the
candidate is the averaged slice family viewed as a polynomial in one more variable,
`averagedSliceAppendedSubMeas`, and the consistency statements are `ConsRel`s on
`strategy.state`. Three uses of the vendored strategy fields become theorems of the model:
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

The proofs are shorter than the vendored ones. The good-strategy forms
`degreeZero_averagedSlice_liftedVerticalLineConsistency`,
`degreeZero_averagedSlice_pointConsistency` and `degreeZeroPastedPointConsistency` are their
axis/self-consistency forms applied to `hgood.axisParallelTest` and `hgood.selfConsistencyTest`,
so each is declared after its `_of_axis_self` form, the reverse of the vendored order. The
height averaging of the lifted-line estimate decomposes both sides through
`avgOver_uniform_pointNext_decompose` once each.

## Not ported

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel Fq Point avgOver avgOver_mono avgOver_congr
  avgOver_add avgOver_uniform_const avgOver_uniform_comm uniformDistribution
  uniformDistribution_weight_sum_le_one appendPoint truncatePoint zeroCoord lastCoord
  truncatePoint_appendPoint pointHeight_appendPoint)
open MIPStarRE.LDT.CommutativityPoints (avgOver_uniform_pointNext_decompose)
open MIPStarRE.LDT.MainInductionStep (ldPastingInInductionNu ldPastingInInductionError)
open MIPStarRE.LDT.Pasting (pastedFallbackOutcome one_le_ldPastingError_of_k_eq_zero)
open MIPRE.LIDT.Co (SymStrat SubMeas Measurement IdxMeas IdxProjMeas IdxPolyFamily
  averageIdxSubMeas evaluateAt polynomialEvaluationFamily axisParallelPointAnswerFamily
  axisParallelLineAnswerFamily)

/-- Upstream keeps this helper `private` since its Lean-module port (`LionSR/MIPStarRE` at `5fc363b`); the port carries its own copy, with upstream's proof.

Scalar absorption for the degree-zero submeasurement consistency error. -/
theorem degreeZero_submeas_error_le_two_nu
    (params : Parameters) [FieldModel params.q]
    (eps delta gamma zeta : ℝ) (k : ℕ)
    (hk_pos : 1 ≤ k)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta) :
    min zeta 1 +
        2 * Real.sqrt (8 * (params.m : ℝ) * min eps 1 + 4 * min delta 1) ≤
      2 * MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta := by
  let C : ℝ := ((k : ℝ) ^ (2 : ℕ)) * (params.m : ℝ)
  let epsTerm : ℝ := Real.rpow eps (1 / (32 : ℝ))
  let deltaTerm : ℝ := Real.rpow delta (1 / (32 : ℝ))
  let gammaTerm : ℝ := Real.rpow gamma (1 / (32 : ℝ))
  let zetaTerm : ℝ := Real.rpow zeta (1 / (32 : ℝ))
  let degreeTerm : ℝ :=
    Real.rpow (((params.d : ℝ) / (params.q : ℝ))) (1 / (32 : ℝ))
  let S : ℝ := epsTerm + deltaTerm + gammaTerm + zetaTerm + degreeTerm
  have hC_one : (1 : ℝ) ≤ C := by
    have hkE_one : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_pos
    have hmE_one : (1 : ℝ) ≤ (params.m : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt params.hm)
    dsimp [C]
    nlinarith [sq_nonneg (k : ℝ)]
  have hC_nonneg : 0 ≤ C := le_trans zero_le_one hC_one
  have hepsTerm_nonneg : 0 ≤ epsTerm := by
    dsimp [epsTerm]
    exact Real.rpow_nonneg heps_nonneg _
  have hdeltaTerm_nonneg : 0 ≤ deltaTerm := by
    dsimp [deltaTerm]
    exact Real.rpow_nonneg hdelta_nonneg _
  have hgammaTerm_nonneg : 0 ≤ gammaTerm := by
    dsimp [gammaTerm]
    exact Real.rpow_nonneg hgamma_nonneg _
  have hzetaTerm_nonneg : 0 ≤ zetaTerm := by
    dsimp [zetaTerm]
    exact Real.rpow_nonneg hzeta_nonneg _
  have hdegreeTerm_nonneg : 0 ≤ degreeTerm := by
    dsimp [degreeTerm]
    exact Real.rpow_nonneg (ldPasting_degreeRatio_nonneg params) _
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    nlinarith
  have hzeta_min_le_C : min zeta 1 ≤ C * zetaTerm := by
    have hmin_nonneg : 0 ≤ min zeta 1 := by positivity
    have hmin_le_one : min zeta 1 ≤ 1 := min_le_right _ _
    have hzeta_min_le : min zeta 1 ≤ zetaTerm := by
      calc
        min zeta 1 ≤ Real.rpow (min zeta 1) (1 / (32 : ℝ)) := by
            simpa [Real.rpow_one] using
              (Real.rpow_le_rpow_of_exponent_ge' hmin_nonneg hmin_le_one
                (show 0 ≤ (1 / (32 : ℝ)) by norm_num)
                (show 1 / (32 : ℝ) ≤ (1 : ℝ) by norm_num))
        _ ≤ zetaTerm := by
            dsimp [zetaTerm]
            exact Real.rpow_le_rpow hmin_nonneg (min_le_left _ _) (by positivity)
    calc
      min zeta 1 ≤ zetaTerm := hzeta_min_le
      _ = (1 : ℝ) * zetaTerm := by ring
      _ ≤ C * zetaTerm := by
          exact mul_le_mul_of_nonneg_right hC_one hzetaTerm_nonneg
  have hsqrt_le_CS :
      Real.sqrt (8 * (params.m : ℝ) * min eps 1 + 4 * min delta 1) ≤ 3 * C * S := by
    calc
      Real.sqrt (8 * (params.m : ℝ) * min eps 1 + 4 * min delta 1)
          ≤ 3 * ((k : ℝ) ^ (2 : ℕ)) * (params.m : ℝ) *
              (Real.rpow eps (1 / (32 : ℝ)) + Real.rpow delta (1 / (32 : ℝ))) :=
            hAConsistency_sqrt_bound_of_pos params eps delta k hk_pos
              heps_nonneg hdelta_nonneg
      _ = 3 * C * (epsTerm + deltaTerm) := by ring
      _ ≤ 3 * C * S := by
          have hsum_le : epsTerm + deltaTerm ≤ S := by
            dsimp [S]
            nlinarith
          exact mul_le_mul_of_nonneg_left hsum_le (by positivity)
  calc
    min zeta 1 +
        2 * Real.sqrt (8 * (params.m : ℝ) * min eps 1 + 4 * min delta 1)
      ≤ C * zetaTerm + 2 * (3 * C * S) := by
          exact add_le_add hzeta_min_le_C
            (mul_le_mul_of_nonneg_left hsqrt_le_CS (by norm_num))
    _ ≤ 7 * C * S := by
          have hzeta_le_S : zetaTerm ≤ S := by
            dsimp [S]
            nlinarith
          have hCzeta_le_CS : C * zetaTerm ≤ C * S := by
            exact mul_le_mul_of_nonneg_left hzeta_le_S hC_nonneg
          nlinarith
    _ ≤ 200 * C * S := by
          have hCS_nonneg : 0 ≤ C * S := mul_nonneg hC_nonneg hS_nonneg
          nlinarith
    _ = 2 * MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta := by
          simp [MainInductionStep.ldPastingInInductionNu, C, S, epsTerm, deltaTerm,
            gammaTerm, zetaTerm, degreeTerm]
          ring

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Evaluating the degree-zero appended-slice candidate is the height average of
the original evaluated slice family at the same old point. -/
theorem polynomialEvaluation_averagedSliceAppendedSubMeas_eq_average
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    (u : Point params.next) :
    polynomialEvaluationFamily params.next
        (averagedSliceAppendedSubMeas params family) u =
      averageIdxSubMeas (uniformDistribution (Fq params))
        (fun x =>
          family.evaluatedAtNextPoint
            (appendPoint params (truncatePoint params u) x))
        (uniformDistribution_weight_sum_le_one (Fq params)) := by
  refine (evaluateAt_averagedSliceAppendedSubMeas params family u).trans <|
    (evaluateAt_averageIdxSubMeas params (truncatePoint params u)
      (uniformDistribution (Fq params)) (fun x => (family.meas x).toSubMeas)
      (uniformDistribution_weight_sum_le_one (Fq params))).trans ?_
  congr 1
  funext x
  simp only [IdxPolyFamily.evaluatedAtNextPoint, truncatePoint_appendPoint,
    pointHeight_appendPoint]

/-- The point-consistency hypothesis may be truncated at the trivial unit bound. -/
theorem consistentWithPoints_min_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (zeta : ℝ)
    (hcons : family.ConsistentWithPoints strategy zeta) :
    family.ConsistentWithPoints strategy (min zeta 1) :=
  ⟨⟨le_min hcons.pointConsistency.offDiagonalBound
    (strategy.state.bipartiteConsError_uniform_le_one
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) family.evaluatedAtNextPoint)⟩⟩

/-- Axis/self-consistency form of the degree-zero lifted-line consistency
estimate.

The degree-zero averaging argument uses the axis-parallel test and
self-consistency, but not the diagonal-line test. -/
theorem degreeZero_averagedSlice_liftedVerticalLineConsistency_of_axis_self
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta zeta : ℝ)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself : strategy.selfConsistencyFailureProbability ≤ delta)
    (family : IdxPolyFamily params 𝔓)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hd_zero : params.d = 0) :
    strategy.state.ConsRel (uniformDistribution (Point params.next))
      (polynomialEvaluationFamily params.next
        (averagedSliceAppendedSubMeas params family))
      (liftedVerticalLineAnswerFamily params strategy)
      (min zeta 1 +
        Real.sqrt (8 * (params.m : ℝ) * min eps 1 + 4 * min delta 1)) := by
  set S := strategy.state
  have hgb := ldGbcon_liftedVerticalLine_of_axis_self params strategy
    (min eps 1) (min delta 1) (min zeta 1)
    (le_min haxis (S.bipartiteConsError_uniform_le_one
      (axisParallelPointAnswerFamily strategy) (axisParallelLineAnswerFamily strategy)))
    (le_min hself (bipartiteSSCError_uniform_le_one S
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)))
    family (consistentWithPoints_min_one params strategy family zeta hcons)
  let F : Point params → Fq params → ℝ := fun u x =>
    S.qBipartiteConsDefect
      (family.evaluatedAtNextPoint (appendPoint params u x))
      (liftedVerticalLineAnswerFamily params strategy (appendPoint params u x))
  -- Both sides are the uniform average of `F` over `Point params × Fq params`.
  have hleft :
      avgOver (uniformDistribution (Point params.next))
          (fun u => avgOver (uniformDistribution (Fq params))
            (fun x => F (truncatePoint params u) x)) =
        avgOver (uniformDistribution (Point params))
          (fun u => avgOver (uniformDistribution (Fq params)) (fun x => F u x)) := by
    rw [avgOver_uniform_pointNext_decompose]
    simp only [truncatePoint_appendPoint]
    exact avgOver_uniform_const _
  have hright :
      S.bipartiteConsError (uniformDistribution (Point params.next))
          family.evaluatedAtNextPoint (liftedVerticalLineAnswerFamily params strategy) =
        avgOver (uniformDistribution (Point params))
          (fun u => avgOver (uniformDistribution (Fq params)) (fun x => F u x)) :=
    (avgOver_uniform_pointNext_decompose params _).trans (avgOver_uniform_comm F).symm
  refine ⟨le_trans ?_ (hright.symm.trans_le hgb.offDiagonalBound)⟩
  rw [← hleft]
  refine avgOver_mono _ _ _ fun u => ?_
  rw [polynomialEvaluation_averagedSliceAppendedSubMeas_eq_average params family u]
  refine (qBipartiteConsDefect_averageIdxSubMeas_left_le S (uniformDistribution (Fq params))
    _ _ (uniformDistribution_weight_sum_le_one (Fq params))).trans_eq
    (avgOver_congr _ _ _ fun x => congrArg (S.qBipartiteConsDefect _)
      (liftedVerticalLineAnswerFamily_eq_of_same_truncate_degree_zero params strategy hd_zero
        (truncatePoint_appendPoint params (truncatePoint params u) x)).symm)

/-- The averaged degree-zero pasted submeasurement is consistent with the lifted
vertical-line answers. -/
theorem degreeZero_averagedSlice_liftedVerticalLineConsistency
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma zeta : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params 𝔓)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hd_zero : params.d = 0) :
    strategy.state.ConsRel (uniformDistribution (Point params.next))
      (polynomialEvaluationFamily params.next
        (averagedSliceAppendedSubMeas params family))
      (liftedVerticalLineAnswerFamily params strategy)
      (min zeta 1 +
        Real.sqrt (8 * (params.m : ℝ) * min eps 1 + 4 * min delta 1)) :=
  degreeZero_averagedSlice_liftedVerticalLineConsistency_of_axis_self params strategy
    eps delta zeta hgood.axisParallelTest hgood.selfConsistencyTest family hcons hd_zero

/-- Axis/self-consistency form of the degree-zero point-consistency estimate
before completion. -/
theorem degreeZero_averagedSlice_pointConsistency_of_axis_self
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta zeta : ℝ)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself : strategy.selfConsistencyFailureProbability ≤ delta)
    (family : IdxPolyFamily params 𝔓)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hd_zero : params.d = 0) :
    strategy.state.ConsRel (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params.next
        (averagedSliceAppendedSubMeas params family))
      (min zeta 1 +
        2 * Real.sqrt (8 * (params.m : ℝ) * min eps 1 + 4 * min delta 1)) := by
  let lineMeas : IdxMeas (Point params.next) (Fq params.next) 𝔓 := fun u =>
    { toSubMeas := liftedVerticalLineAnswerFamily params strategy u
      total_eq_one :=
        (strategy.axisParallelMeasurement
          { base := appendPoint params (truncatePoint params u) zeroCoord
            direction := lastCoord params }).total_eq_one }
  let pointMeas : IdxMeas (Point params.next) (Fq params.next) 𝔓 :=
    fun u => (strategy.pointMeasurement u).toMeasurement
  have hpoint_sdd :
      strategy.state.SDDRel (uniformDistribution (Point params.next))
        (IdxSubMeas.liftRight strategy.state (IdxMeas.toIdxSubMeas lineMeas))
        (IdxSubMeas.liftRight strategy.state (IdxMeas.toIdxSubMeas pointMeas))
        (8 * (params.m : ℝ) * min eps 1 + 4 * min delta 1) :=
    Preliminaries.sddRel_symm strategy.state.toVecState (uniformDistribution (Point params.next))
      (IdxSubMeas.liftRight strategy.state (IdxMeas.toIdxSubMeas pointMeas))
      (IdxSubMeas.liftRight strategy.state (IdxMeas.toIdxSubMeas lineMeas)) _
      (pointVerticalLineSdd_liftedVerticalLine_of_axis_self params strategy
        (min eps 1) (min delta 1)
        (le_min haxis (strategy.state.bipartiteConsError_uniform_le_one
          (axisParallelPointAnswerFamily strategy) (axisParallelLineAnswerFamily strategy)))
        (le_min hself (bipartiteSSCError_uniform_le_one strategy.state
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))))
  have htri :=
    Preliminaries.triangleSub_right strategy.state (uniformDistribution (Point params.next))
      (by simpa using uniformDistribution_weight_sum_le_one (Point params.next))
      (polynomialEvaluationFamily params.next (averagedSliceAppendedSubMeas params family))
      lineMeas pointMeas _ _
      (degreeZero_averagedSlice_liftedVerticalLineConsistency_of_axis_self params strategy
        eps delta zeta haxis hself family hcons hd_zero)
      hpoint_sdd
  exact (strategy.state.consRel_symm_of_density_fixed _ _ _ _ htri).mono
    (le_of_eq (by ring))

/-- The averaged degree-zero pasted submeasurement is point-consistent before
completion. -/
theorem degreeZero_averagedSlice_pointConsistency
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma zeta : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params 𝔓)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hd_zero : params.d = 0) :
    strategy.state.ConsRel (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params.next
        (averagedSliceAppendedSubMeas params family))
      (min zeta 1 +
        2 * Real.sqrt (8 * (params.m : ℝ) * min eps 1 + 4 * min delta 1)) :=
  degreeZero_averagedSlice_pointConsistency_of_axis_self params strategy
    eps delta zeta hgood.axisParallelTest hgood.selfConsistencyTest family hcons hd_zero

/-- Axis/self-consistency form of the degree-zero point-consistency
construction.

This is the same construction as `degreeZeroPastedPointConsistency`, with the
ordinary good-strategy hypotheses replaced by the two estimates actually used in
the proof. -/
theorem degreeZeroPastedPointConsistency_of_axis_self
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma kappa zeta : ℝ)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hselfBound : strategy.selfConsistencyFailureProbability ≤ delta)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (family : IdxPolyFamily params 𝔓)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hd_zero : params.d = 0)
    (k : ℕ) :
    ∃ H : Measurement (MIPStarRE.LDT.Polynomial params.next) 𝔓,
      H =
          Preliminaries.completeAtOutcome
            (averagedSliceAppendedSubMeas params family)
            (pastedFallbackOutcome params) ∧
        strategy.state.ConsRel (uniformDistribution (Point params.next))
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          (polynomialEvaluationFamily params.next H.toSubMeas)
          (ldPastingInInductionError params k eps delta gamma kappa zeta) := by
  refine ⟨_, rfl, ?_⟩
  set S := strategy.state
  set A := averagedSliceAppendedSubMeas params family
  have hkappa_nonneg : 0 ≤ kappa := kappa_nonneg_of_complete params strategy family hcomplete
  by_cases hk_pos : 1 ≤ k
  swap
  · exact ⟨(S.bipartiteConsError_uniform_le_one _ _).trans
      (one_le_ldPastingError_of_k_eq_zero params k eps delta gamma kappa zeta hkappa_nonneg
        (by omega))⟩
  set η := min zeta 1 + 2 * Real.sqrt (8 * (params.m : ℝ) * min eps 1 + 4 * min delta 1)
  have hsubmeas : S.ConsRel (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params.next A) η :=
    degreeZero_averagedSlice_pointConsistency_of_axis_self params strategy
      eps delta zeta haxis hselfBound family hcons hd_zero
  have hcompletedEval :
      (fun u => (Preliminaries.completeAtOutcome (evaluateAt params.next u A)
          ((pastedFallbackOutcome params) u)).toSubMeas) =
        polynomialEvaluationFamily params.next
          (Preliminaries.completeAtOutcome A (pastedFallbackOutcome params)).toSubMeas :=
    funext fun u => (Preliminaries.evaluateAt_completeAtOutcome params.next A
      (pastedFallbackOutcome params) u).symm
  have hresidualMass : S.ev (S.R (1 - A.total)) ≤ kappa := by
    have hmass : S.ev (S.L A.total) ≥ 1 - kappa := hcomplete.averageCompleteness.lowerBound
    rw [← S.ev_L_eq_ev_R, ← S.leftTensor_sub, S.leftTensor_one, S.ev_sub,
      S.ev_one_of_isNormalized]
    linarith
  have hcompleted :
      S.bipartiteConsError (uniformDistribution (Point params.next))
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          (fun u => (Preliminaries.completeAtOutcome (evaluateAt params.next u A)
            ((pastedFallbackOutcome params) u)).toSubMeas) ≤
        η + S.ev (S.R (1 - A.total)) :=
    calc
      _ ≤ avgOver (uniformDistribution (Point params.next)) (fun u =>
            S.qBipartiteConsDefect (strategy.pointMeasurement u).toSubMeas
                (evaluateAt params.next u A) +
              S.ev (S.R (1 - A.total))) :=
        avgOver_mono _ _ _ fun u =>
          Preliminaries.qBipartiteConsDefect_completeAtOutcome_right_le S
            (strategy.pointMeasurement u).toMeasurement (evaluateAt params.next u A)
            ((pastedFallbackOutcome params) u)
      _ = S.bipartiteConsError (uniformDistribution (Point params.next))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
            (polynomialEvaluationFamily params.next A) +
          S.ev (S.R (1 - A.total)) :=
        (avgOver_add _ _ _).trans (congrArg _ (avgOver_uniform_const _))
      _ ≤ η + S.ev (S.R (1 - A.total)) :=
        add_le_add hsubmeas.offDiagonalBound le_rfl
  have heta_le : η ≤ 2 * ldPastingInInductionNu params k eps delta gamma zeta :=
    degreeZero_submeas_error_le_two_nu params eps delta gamma zeta k hk_pos
      heps_nonneg hdelta_nonneg hgamma_nonneg
      (IdxPolyFamily.zeta_nonneg_of_consistentWithPoints strategy family hcons)
  have hkappa_le : kappa ≤ kappa * (1 + 1 / (100 * (params.m : ℝ))) :=
    le_mul_of_one_le_right hkappa_nonneg (le_add_of_nonneg_right (by positivity))
  have hexp := Real.exp_pos (-((k : ℝ) / (80000 * ((params.m : ℝ) ^ (2 : ℕ)))))
  refine ⟨hcompletedEval ▸ hcompleted.trans ?_⟩
  simp only [ldPastingInInductionError]
  linarith

/-- Degree-zero point-consistency construction for `thm:ld-pasting`.

Paper origin: `references/ldt-paper/ld-pasting.tex:12-55`.  In the degree-zero
branch the slice polynomials and the last-coordinate line answers are constant
on their respective domains.  The measurement is the completion of
`averagedSliceAppendedSubMeas`, the averaged slice family viewed as a global
polynomial family by ignoring the appended variable. -/
theorem degreeZeroPastedPointConsistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma kappa zeta : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params 𝔓)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hd_zero : params.d = 0)
    (k : ℕ) :
    ∃ H : Measurement (MIPStarRE.LDT.Polynomial params.next) 𝔓,
      H =
          Preliminaries.completeAtOutcome
            (averagedSliceAppendedSubMeas params family)
            (pastedFallbackOutcome params) ∧
        strategy.state.ConsRel (uniformDistribution (Point params.next))
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          (polynomialEvaluationFamily params.next H.toSubMeas)
          (ldPastingInInductionError params k eps delta gamma kappa zeta) :=
  degreeZeroPastedPointConsistency_of_axis_self params strategy eps delta gamma kappa zeta
    hgood.axisParallelTest hgood.selfConsistencyTest
    (eps_nonneg_of_isGood params.next strategy hgood)
    (delta_nonneg_of_isGood params.next strategy hgood)
    (gamma_nonneg_of_isGood params.next strategy hgood)
    family hcomplete hcons hd_zero k

end MIPRE.LIDT.Co.Pasting

end

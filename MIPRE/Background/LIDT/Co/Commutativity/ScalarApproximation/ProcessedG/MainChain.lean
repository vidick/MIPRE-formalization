/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
Commutativity/ScalarApproximation/ProcessedG/MainChain.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Commutativity.ScalarApproximation.Core
public import MIPRE.Background.LIDT.Co.Commutativity.ScalarApproximation.PaperChainReverse
public import MIPRE.Background.LIDT.Co.Commutativity.ScalarApproximation.PaperChainTail
public import MIPRE.Background.LIDT.Co.Commutativity.EvaluatedSliceCommutation.Consequences
public import MIPRE.Background.LIDT.Co.Commutativity.GCommStability.Scalar.RawSecond
public import MIPRE.Background.LIDT.Co.Commutativity.ScalarApproximation.ProcessedG.PhaseTwo

@[expose] public section

/-!
# Main scalar chain assembly

The core lemma `evaluatedSlice_scalar_chain_bound` that assembles the ten-step scalar
approximation chain for `lem:comm-data-processed-g`: the counterpart of
`Commutativity/ScalarApproximation/ProcessedG/MainChain.lean` under
`MIPRE/Background/LIDT/MIPStarRE/LDT/` in the port of `planning/c6b-plan.md` (milestone M7,
section "Port conventions"). Phases 1, 3, 4, 6–7 and 8–9 are supplied by the reverse and tail
parts of the paper chain; Phase 2 uses the reindexing of `ProcessedG/PhaseTwo`.

The endpoints are real expectations `strategy.state.ev (strategy.state.L … * strategy.state.R …)`
on the symmetric model of the strategy, and the families `C` of the point-swap lemmas are joint
operators `K →L[ℂ] K`, with `star` for the vendored `ᴴ`. The vendored
`evaluatedSlicePointSwapRightPrefix` places its prefix with `leftTensor (ι₂ := ι)`, which needs no
state; here the placement is `S.L`, so it and
`evaluatedSlice_pointSwap_right_prefix_normalization` take the symmetric model `S` as an explicit
first argument, as M1's placement helpers do (`planning/c6b-plan.md`, "Departures in M1").

The vendored hypothesis `hnorm : strategy.state.IsNormalized` is dropped from
`evaluatedSlice_pointSwap_right_bound_of_norms` (where it stood between `gamma` and `hcomm`) and
from `evaluatedSlice_scalar_chain_bound` (between `gamma zeta` and `hcomm`), as the port
conventions drop `hψ : ψ.IsNormalized`; no lemma the chain calls takes it. The unused hypothesis
`_hself` of `evaluatedSlice_scalar_chain_bound` is kept, so that callers pass the vendored
argument list without `hnorm`.

The proofs are shorter than the vendored ones. The point measurement is
`evaluatedSlicePointMeas` itself, not a cast of `strategy.pointMeasurement`; the transfer of
`prop:cons-sub-meas` to the two question coordinates is `avgOver_uniform_fst`/`_snd`, as in
`EvaluatedSliceCommutation/Consequences`. The placement algebra of phases 3–4 is the keystone's
`opTensor_mul_leftTensor` and `opTensor_mul`, in place of the vendored `simp` calls with
`opTensor_mul` and `mul_assoc`, and the final assembly reads each phase bound through
`abs_sub_le_iff` and closes by `linarith`.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Commutativity

open MIPStarRE.LDT (Parameters FieldModel Point Fq pointHeight avgOver avgOver_congr
  avgOver_uniform_fst avgOver_uniform_snd uniformDistribution
  uniformDistribution_weight_sum_le_one)
open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)
open MIPStarRE.LDT.CommutativityPoints (commutativityPointsError)
open MIPStarRE.LDT.Commutativity (EvaluatedSliceQuestion EvaluatedSliceOutcome
  commDataProcessedGError)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The phase-four endpoint before the right-register point swap:
`∑_{ab} ⟨ψ, C_{ab} (I ⊗ A^{q₂}_b A^{q₁}_a) ψ⟩`. -/
noncomputable def evaluatedSlicePhaseFourInserted
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (C : EvaluatedSliceQuestion params → EvaluatedSliceOutcome params → K →L[ℂ] K) :
    EvaluatedSliceQuestion params → ℝ := fun q =>
  ∑ ab : EvaluatedSliceOutcome params,
    strategy.state.ev
      (C q ab *
        strategy.state.R
          (((evaluatedSlicePointMeas params strategy q.2).outcome ab.2) *
            ((evaluatedSlicePointMeas params strategy q.1).outcome ab.1)))

/-- The phase-four endpoint after the right-register point swap:
`∑_{ab} ⟨ψ, C_{ab} (I ⊗ A^{q₁}_a A^{q₂}_b) ψ⟩`. -/
noncomputable def evaluatedSlicePhaseFourSwapped
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (C : EvaluatedSliceQuestion params → EvaluatedSliceOutcome params → K →L[ℂ] K) :
    EvaluatedSliceQuestion params → ℝ := fun q =>
  ∑ ab : EvaluatedSliceOutcome params,
    strategy.state.ev
      (C q ab *
        strategy.state.R
          (((evaluatedSlicePointMeas params strategy q.1).outcome ab.1) *
            ((evaluatedSlicePointMeas params strategy q.2).outcome ab.2)))

/-- Shared left-register prefix for the ProcessedG right-register point-swap bounds:
`(G^{u,x}_a G^{v,y}_b T_q) ⊗ I`, placed by `S.L`. -/
noncomputable def evaluatedSlicePointSwapRightPrefix
    (S : SymModel 𝔓 K)
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    (T : EvaluatedSliceQuestion params → 𝔓) :
    EvaluatedSliceQuestion params → EvaluatedSliceOutcome params → K →L[ℂ] K :=
  fun q ab =>
    S.L
      (((evaluatedSliceFirstFactor params family q).outcome ab.1) *
        ((evaluatedSliceSecondFactor params family q).outcome ab.2) *
        T q)

/-- Normalization for the shared ProcessedG right-register point-swap prefix. -/
lemma evaluatedSlice_pointSwap_right_prefix_normalization
    (S : SymModel 𝔓 K)
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    (T : EvaluatedSliceQuestion params → 𝔓)
    (hT_nonneg : ∀ q, 0 ≤ T q)
    (hT_le_one : ∀ q, T q ≤ 1) :
    ∀ q,
      ∑ ab : EvaluatedSliceOutcome params,
        evaluatedSlicePointSwapRightPrefix S params family T q ab *
            star (evaluatedSlicePointSwapRightPrefix S params family T q ab) ≤
          1 := fun q =>
  leftTensor_prefix_total_normalization S (evaluatedSliceFirstFactor params family q)
    (evaluatedSliceSecondFactor params family q) (T q) (hT_nonneg q) (hT_le_one q)

/-- The right-register point swap, for any two endpoints whose averages are those of
`evaluatedSlicePhaseFourInserted` and `evaluatedSlicePhaseFourSwapped`. -/
lemma evaluatedSlice_pointSwap_right_bound_of_norms
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (gamma : ℝ)
    (hcomm :
      strategy.state.SDDOpRel
        (uniformDistribution (PointPairQuestion params.next))
        (CommutativityPoints.pointMeasurementProductLeft params.next strategy)
        (CommutativityPoints.pointMeasurementProductRight params.next strategy)
        (commutativityPointsError params.next gamma))
    (C : EvaluatedSliceQuestion params → EvaluatedSliceOutcome params → K →L[ℂ] K)
    (hC : ∀ q, ∑ ab : EvaluatedSliceOutcome params, C q ab * star (C q ab) ≤ 1)
    (lhs rhs : EvaluatedSliceQuestion params → ℝ)
    (hlhs : avgOver (uniformDistribution (EvaluatedSliceQuestion params)) lhs =
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (evaluatedSlicePhaseFourInserted params strategy C))
    (hrhs : avgOver (uniformDistribution (EvaluatedSliceQuestion params)) rhs =
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (evaluatedSlicePhaseFourSwapped params strategy C)) :
    |avgOver (uniformDistribution (EvaluatedSliceQuestion params)) lhs -
        avgOver (uniformDistribution (EvaluatedSliceQuestion params)) rhs| ≤
      6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : ℝ)) := by
  rw [hlhs, hrhs]
  exact evaluatedSlice_phaseFour_pointSwap_right_bound_of_commutativityPoints params strategy
    gamma hcomm C hC

/-- Scalar approximation chain for the evaluated-slice commutation.

This is the core of the paper's proof of `lem:comm-data-processed-g`
(`references/ldt-paper/commutativity-G.tex`, lines 72–131, upstream).
Starting from `E[∑ ABAB]`, the proof applies ten approximation steps:

1. `≈_{2√ζ}`: insert Bob's measurement via `closenessOfIP` + `eq:add-an-a`
2. `≈_{√ζ}`: remove trailing `G^y` (`clm:g-comm-stability`)
3. `≈_{2√ζ}`: insert Bob's second measurement via `closenessOfIP` + `eq:add-an-a`
4. `≈_{6√(γ(m+1))}`: swap Bob's measurements via `closenessOfIP` + `commutativityPoints`
5a. `≈_{6√(γ(m+1))}`: the point-measurement swap contribution internal to the paper's
    `clm:g-comm-stability2` accounting
5b. `≈_{√ζ}`: remove trailing `G^x` by the boundedness part of `gCommStabilityTwo_raw_scalar`
6–7. `≈_{2√ζ + 2√ζ}`: reverse the `eq:add-an-a` insertions
8–9. `≈_{√ζ + √ζ}`: apply postprocessed self-consistency twice

Summing: `Σεᵢ = 12√ζ + 12√(γ(m+1))`, so `2 * Σεᵢ ≤ 48m(√γ + √ζ)`. The chain ends at `BAB`,
whose average is that of `ABA` by the swap of the question coordinates
(`evaluatedSliceCommutation_avg_swap_terms`). -/
lemma evaluatedSlice_scalar_chain_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (gamma zeta : ℝ)
    (hcomm :
      strategy.state.SDDOpRel
        (uniformDistribution (PointPairQuestion params.next))
        (CommutativityPoints.pointMeasurementProductLeft params.next strategy)
        (CommutativityPoints.pointMeasurementProductRight params.next strategy)
        (commutativityPointsError params.next gamma))
    (hgamma_nonneg : 0 ≤ gamma)
    (family : IdxPolyFamily params 𝔓)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (_hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (hpostSSC : strategy.state.SDDRel
      (uniformDistribution (Point params.next))
      (evaluatedPointFamilyLeft strategy.state params family)
      (evaluatedPointFamilyRight strategy.state params family)
      zeta) :
    2 *
      (avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => ∑ ab : EvaluatedSliceOutcome params,
            evaluatedSliceABATerm params strategy family q ab) -
        avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => ∑ ab : EvaluatedSliceOutcome params,
            evaluatedSliceABABTerm params strategy family q ab)) ≤
      commDataProcessedGError params gamma zeta := by
  let S := strategy.state
  let 𝒟 := uniformDistribution (EvaluatedSliceQuestion params)
  let F := evaluatedPointFamily params family
  let M := evaluatedSlicePointMeas params strategy
  let A := evaluatedSliceFirstFactor params family
  let B := evaluatedSliceSecondFactor params family
  let s := Real.sqrt (gamma * (((params.m + 1 : ℕ)) : ℝ))
  have hpostSSC_snd := evaluatedPointSelfConsistency_snd params strategy family zeta hpostSSC
  -- `prop:cons-sub-meas` for the evaluated family against the point measurement, moved to
  -- either coordinate of an evaluated-slice question.
  have hconsSub := Preliminaries.consSubMeas S (uniformDistribution (Point params.next)) F M zeta
    (evaluatedPointFamily_pointConsistency_swapped params strategy family zeta hcons)
  have hcombined_snd : S.SDDRel 𝒟 (fun q => evaluatedPointFamilyLeft S params family q.2)
      (fun q => Preliminaries.totalSandwichFamily S F M q.2) (4 * zeta) :=
    ⟨(avgOver_uniform_snd (α := Point params.next) fun u =>
        S.qSDD (IdxSubMeas.liftLeft S F u) (Preliminaries.totalSandwichFamily S F M u)).trans_le
      hconsSub.combinedControl.squaredDistanceBound⟩
  have hcombined_fst : S.SDDRel 𝒟 (fun q => evaluatedPointFamilyLeft S params family q.1)
      (fun q => Preliminaries.totalSandwichFamily S F M q.1) (4 * zeta) :=
    ⟨(avgOver_uniform_fst (β := Point params.next) fun u =>
        S.qSDD (IdxSubMeas.liftLeft S F u) (Preliminaries.totalSandwichFamily S F M u)).trans_le
      hconsSub.combinedControl.squaredDistanceBound⟩
  -- The endpoints of the chain.
  let avgABAB : EvaluatedSliceQuestion params → ℝ := fun q =>
    ∑ ab : EvaluatedSliceOutcome params, evaluatedSliceABABTerm params strategy family q ab
  let avgABA : EvaluatedSliceQuestion params → ℝ := fun q =>
    ∑ ab : EvaluatedSliceOutcome params, evaluatedSliceABATerm params strategy family q ab
  let avgBAB : EvaluatedSliceQuestion params → ℝ := fun q =>
    ∑ ab : EvaluatedSliceOutcome params, evaluatedSliceBABTerm params strategy family q ab
  let phase1Inserted : EvaluatedSliceQuestion params → ℝ := fun q =>
    ∑ b : Fq params, ∑ a : Fq params,
      S.ev (S.L ((A q).outcome a * (B q).outcome b * (A q).outcome a) *
        (Preliminaries.totalSandwichFamily S F M q.2).outcome b)
  let phase2Removed : EvaluatedSliceQuestion params → ℝ := fun q =>
    ∑ b : Fq params, ∑ a : Fq params,
      S.ev (S.L ((A q).outcome a * (B q).outcome b * (A q).outcome a) *
        S.R ((M q.2).outcome b))
  -- Paper line 86: insert the first-coordinate point measurement after `gcom9`.
  let phase3PaperInserted : EvaluatedSliceQuestion params → ℝ := fun q =>
    ∑ a : Fq params, ∑ b : Fq params,
      S.ev ((S.L ((A q).outcome a * (B q).outcome b) * S.R ((M q.2).outcome b)) *
        (Preliminaries.totalSandwichFamily S F M q.1).outcome a)
  -- Paper line 87: swap the two right-register point measurements.
  let phase4PaperSwapped : EvaluatedSliceQuestion params → ℝ := fun q =>
    ∑ a : Fq params, ∑ b : Fq params,
      S.ev (S.L ((A q).outcome a * (B q).outcome b * (A q).total) *
        S.R ((M q.1).outcome a * (M q.2).outcome b))
  let phase5PaperRemoved := evaluatedSlicePhaseFivePaperRemoved params strategy family
  let phase7GonnaCite := evaluatedSlicePhaseSevenGonnaCite params strategy family
  let phase8TailRight := evaluatedSlicePhaseEightTailRight params strategy family
  -- Phase 1: `eq:gcom8 -> eq:apply-add-an-a-once`.
  have hphase1 : |avgOver 𝒟 avgABAB - avgOver 𝒟 phase1Inserted| ≤ 2 * Real.sqrt zeta :=
    evaluatedSlice_phaseOne_insert_bound params strategy zeta family hcombined_snd
  -- Phase 2: remove the trailing `G^y` (`clm:g-comm-stability`).
  have hphase2 : |avgOver 𝒟 phase1Inserted - avgOver 𝒟 phase2Removed| ≤ Real.sqrt zeta := by
    rw [show avgOver 𝒟 phase1Inserted - avgOver 𝒟 phase2Removed = _ from
        evaluatedSlice_phaseTwo_avg_diff_eq_neg_questionDefect params strategy family G hG,
      abs_neg, evaluatedSlice_phaseTwo_questionDefect_avg_eq_stabilityDefect]
    exact evaluatedSlice_phaseTwo_stability_defect_bound params strategy zeta family G hG hbound
  -- Phase 3 (paper line 86): insert `G^x ⊗ A^{u,x}_a` by `closenessOfIP`.
  have hphase3paper :
      |avgOver 𝒟 phase2Removed - avgOver 𝒟 phase3PaperInserted| ≤ 2 * Real.sqrt zeta := by
    let Aop : EvaluatedSliceQuestion params → Fq params → K →L[ℂ] K :=
      fun q a => S.L ((A q).outcome a)
    let Bop : EvaluatedSliceQuestion params → Fq params → K →L[ℂ] K :=
      fun q a => (Preliminaries.totalSandwichFamily S F M q.1).outcome a
    let C : EvaluatedSliceQuestion params → Fq params → Fq params → K →L[ℂ] K :=
      fun q a b => S.L ((A q).outcome a * (B q).outcome b) * S.R ((M q.2).outcome b)
    have hremoved : avgOver 𝒟 phase2Removed =
        avgOver 𝒟 (fun q => ∑ a : Fq params, ∑ b : Fq params, S.ev (C q a b * Aop q a)) :=
      avgOver_congr 𝒟 _ _ fun q => Finset.sum_comm.trans <|
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
          change _ = S.ev (S.opTensor _ _ * S.L _)
          rw [S.opTensor_mul_leftTensor]
    have hclose := Preliminaries.closenessOfIP S.toVecState 𝒟
      (uniformDistribution_weight_sum_le_one (EvaluatedSliceQuestion params)) Aop Bop C
      (4 * zeta) hcombined_fst.squaredDistanceBound
      (fun q => leftRightTensor_prefix_pointMeasurement_normalization S (A q) (B q)
        (strategy.pointMeasurement q.2))
    rw [hremoved]
    refine hclose.trans_eq ?_
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
      show Real.sqrt 4 = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  -- Phase 4 (paper line 87): commute the two right-register point measurements.
  have hphase4paper :
      |avgOver 𝒟 phase3PaperInserted - avgOver 𝒟 phase4PaperSwapped| ≤ 6 * s := by
    let C := evaluatedSlicePointSwapRightPrefix S params family fun q => (A q).total
    refine evaluatedSlice_pointSwap_right_bound_of_norms params strategy gamma hcomm C
      (evaluatedSlice_pointSwap_right_prefix_normalization S params family _
        (fun q => (A q).total_nonneg) fun q => (A q).total_le_one)
      phase3PaperInserted phase4PaperSwapped
      (avgOver_congr 𝒟 _ _ fun q => ?_) (avgOver_congr 𝒟 _ _ fun q => ?_)
    · refine (Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_).trans
        (Fintype.sum_prod_type _).symm
      change S.ev (S.opTensor _ _ * S.opTensor _ _) = _
      rw [S.opTensor_mul]
      rfl
    · rw [evaluatedSlicePhaseFourSwapped, Fintype.sum_prod_type]; rfl
  -- Phase 5 (paper line 87): remove the trailing `G^x` total; the defect costs one more
  -- right-register swap and the raw scalar stability bound of `clm:g-comm-stability2`.
  have hphase5paper :
      |avgOver 𝒟 phase4PaperSwapped - avgOver 𝒟 phase5PaperRemoved| ≤
        Real.sqrt zeta + 6 * s := by
    let orderedDefect := evaluatedSlicePhaseFivePaperOrderedDefect params strategy family G
    let swappedDefect := evaluatedSlicePhaseFivePaperSwappedDefect params strategy family G
    have hraw : |avgOver 𝒟 swappedDefect| ≤ Real.sqrt zeta := by
      rw [evaluatedSlice_phaseFivePaper_reindex_to_raw_defect params strategy family G hG]
      exact gCommStabilityTwo_raw_scalar params strategy zeta family G hG hbound
    have hswap : |avgOver 𝒟 swappedDefect - avgOver 𝒟 orderedDefect| ≤ 6 * s := by
      let T : EvaluatedSliceQuestion params → 𝔓 := fun q =>
        1 - (G (pointHeight params q.1)).total
      refine evaluatedSlice_pointSwap_right_bound_of_norms params strategy gamma hcomm
        (evaluatedSlicePointSwapRightPrefix S params family T)
        (evaluatedSlice_pointSwap_right_prefix_normalization S params family T
          (fun q => sub_nonneg.mpr (G (pointHeight params q.1)).total_le_one)
          fun q => sub_le_self 1 (G (pointHeight params q.1)).total_nonneg)
        swappedDefect orderedDefect
        (avgOver_congr 𝒟 _ _ fun q => by
          rw [evaluatedSlicePhaseFourInserted, Fintype.sum_prod_type]; rfl)
        (avgOver_congr 𝒟 _ _ fun q => by
          rw [evaluatedSlicePhaseFourSwapped, Fintype.sum_prod_type]; rfl)
    rw [show avgOver 𝒟 phase4PaperSwapped - avgOver 𝒟 phase5PaperRemoved = _ from
        evaluatedSlice_phaseFivePaper_avg_diff_eq_neg_orderedDefect params strategy family G hG,
      abs_neg]
    have := abs_sub_le (avgOver 𝒟 orderedDefect) (avgOver 𝒟 swappedDefect) 0
    rw [sub_zero, sub_zero, abs_sub_comm] at this
    linarith
  -- Phases 6–7 (paper lines 99–104): reverse the two `eq:add-an-a` insertions.
  have hphase67paper :
      |avgOver 𝒟 phase5PaperRemoved - avgOver 𝒟 phase7GonnaCite| ≤ 4 * Real.sqrt zeta :=
    evaluatedSlice_phaseSixSeven_reverse_bound params strategy zeta family hcombined_fst
      hcombined_snd
  -- Phases 8–9 (paper lines 117–119): postprocessed self-consistency, there and back.
  have htail8 : |avgOver 𝒟 phase7GonnaCite - avgOver 𝒟 phase8TailRight| ≤ Real.sqrt zeta :=
    evaluatedSlice_phaseEight_tail_bound params strategy zeta family hpostSSC_snd
  have htail9 : |avgOver 𝒟 phase8TailRight - avgOver 𝒟 avgBAB| ≤ Real.sqrt zeta :=
    evaluatedSlice_phaseNine_tail_bound params strategy zeta family hpostSSC_snd
  -- Final assembly: the chain ends at `BAB`, whose average is that of `ABA`.
  have hBABeqABA : avgOver 𝒟 avgBAB = avgOver 𝒟 avgABA :=
    (evaluatedSliceCommutation_avg_swap_terms params strategy family).1
  have hchain : avgOver 𝒟 avgABA - avgOver 𝒟 avgABAB ≤ 12 * Real.sqrt zeta + 12 * s := by
    have h1 := (abs_sub_le_iff.mp hphase1).2
    have h2 := (abs_sub_le_iff.mp hphase2).2
    have h3 := (abs_sub_le_iff.mp hphase3paper).2
    have h4 := (abs_sub_le_iff.mp hphase4paper).2
    have h5 := (abs_sub_le_iff.mp hphase5paper).2
    have h67 := (abs_sub_le_iff.mp hphase67paper).2
    have h8 := (abs_sub_le_iff.mp htail8).2
    have h9 := (abs_sub_le_iff.mp htail9).2
    linarith
  have hm : (1 : ℝ) ≤ params.m := by exact_mod_cast params.hm
  have hsqrt_m : Real.sqrt (((params.m + 1 : ℕ)) : ℝ) ≤ 2 * (params.m : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by linarith, by
      push_cast
      linarith [mul_le_mul_of_nonneg_left hm (by linarith : (0 : ℝ) ≤ 4 * params.m)]⟩
  have hs : s ≤ 2 * (params.m : ℝ) * Real.sqrt gamma := by
    change Real.sqrt (gamma * _) ≤ _
    rw [Real.sqrt_mul hgamma_nonneg, mul_comm (2 * (params.m : ℝ))]
    exact mul_le_mul_of_nonneg_left hsqrt_m (Real.sqrt_nonneg gamma)
  have hzeta := mul_le_mul_of_nonneg_right hm (Real.sqrt_nonneg zeta)
  have herror : commDataProcessedGError params gamma zeta =
      48 * (params.m : ℝ) * (Real.sqrt gamma + Real.sqrt zeta) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    rfl
  rw [herror]
  change 2 * (avgOver 𝒟 avgABA - avgOver 𝒟 avgABAB) ≤ _
  linarith [Real.sqrt_nonneg zeta]

end MIPRE.LIDT.Co.Commutativity

end

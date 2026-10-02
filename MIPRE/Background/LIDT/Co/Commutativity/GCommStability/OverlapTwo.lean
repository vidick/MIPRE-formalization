/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
Commutativity/GCommStability/OverlapTwo.lean, to the symmetric model of `planning/c6b-plan.md`;
not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Commutativity.GCommStability.OverlapOne
public import MIPRE.Background.LIDT.Co.Preliminaries.CompletionTransfer

@[expose] public section

/-!
# Section 11 commutativity: `G`-stability overlap (step two)

Second overlap-averaging step for the `G`-stability argument: completes the integral reduction
begun in `OverlapOne`. This is the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/GCommStability/OverlapTwo.lean` in the port
of `planning/c6b-plan.md` (milestone M7, section "Port conventions").

The relation of `gCommStabilityTwo_overlap` is `strategy.state.SDDOpRel`, a vector-state
relation on joint operators, and the placements are `strategy.state.L` and `strategy.state.R`.
The vendored hypothesis `hnorm : strategy.state.IsNormalized` of `gCommStabilityTwo_overlap` is
dropped, as the port conventions drop `hψ : ψ.IsNormalized` and as `OverlapOne` drops it from
`gCommStability_raw_le_one_of`: a vector state has `ev 1 = 1`
(`VecState.ev_one_of_isNormalized`). Callers omit that argument, which stood between `gamma
zeta` and `family`.

The proofs are shorter than the vendored ones. The vendored self-adjointness of `G^x` through
`Matrix.PosSemidef` is `IsSelfAdjoint.of_nonneg`, the entrywise `ᴴ` computation of
`gCommStabilityTwo_pointwise_summand_bound` is `star_mul` with the self-adjointness of the
evaluated outcomes, and the vendored `simpa` through `leftTensor_mul_rightTensor_eq_opTensor` is
the keystone's `opTensor_mono_left`, `S.opTensor A B` being `S.L A * S.R B` by definition.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Commutativity

open MIPStarRE.LDT (Parameters FieldModel Fq truncatePoint pointHeight uniformDistribution)
open MIPStarRE.LDT.Commutativity (EvaluatedSliceQuestion StabilityTwoOutcome)
open MIPRE.LIDT.Co.CommutativityPoints (orderedProductOpFamily)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Summing the stability-two comparison family leaves only the overlap term
for `G^x`. -/
lemma gCommStabilityTwo_pointwise_sum_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (q : EvaluatedSliceQuestion params) :
    (∑ gb : StabilityTwoOutcome params,
        strategy.state.ev
          (strategy.state.L
              ((1 - (G (pointHeight params q.1)).total) *
                (evaluatedPointFamily params family q.2).outcome gb.2 *
                (1 - (G (pointHeight params q.1)).total)) *
            strategy.state.R ((G (pointHeight params q.1)).outcome gb.1))) ≤
      gCommOverlapTerm params strategy G (pointHeight params q.1) := by
  set S := strategy.state
  set x := pointHeight params q.1
  set B := evaluatedPointFamily params family q.2
  have hGx_sq : (G x).total * (G x).total = (G x).total := by
    rw [hG]
    exact Preliminaries.projSubMeas_total_proj (family.meas x)
  calc
    ∑ gb : StabilityTwoOutcome params,
        S.ev (S.L ((1 - (G x).total) * B.outcome gb.2 * (1 - (G x).total)) *
          S.R ((G x).outcome gb.1))
      = ∑ ab : Fq params × MIPStarRE.LDT.Polynomial params,
          S.ev (S.L ((1 - (G x).total) * B.outcome ab.1 * (1 - (G x).total)) *
            S.R ((G x).outcome ab.2)) :=
        Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun _ => rfl
    _ ≤ gCommOverlapTerm params strategy G x :=
        gCommStability_pointwise_sum_bound_core S B (G x) hGx_sq

/-- A single stability-two summand is controlled by replacing the inner ordered
product square by the corresponding evaluated point outcome. -/
lemma gCommStabilityTwo_pointwise_summand_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (q : EvaluatedSliceQuestion params)
    (gb : StabilityTwoOutcome params) :
    strategy.state.ev
      (strategy.state.L
          ((1 - (G (pointHeight params q.1)).total) *
            (star ((orderedProductOpFamily
                (evaluatedSliceFirstFactor params family q)
                (evaluatedSliceSecondFactor params family q)).outcome
                (gb.1 (truncatePoint params q.1), gb.2)) *
              (orderedProductOpFamily
                (evaluatedSliceFirstFactor params family q)
                (evaluatedSliceSecondFactor params family q)).outcome
                (gb.1 (truncatePoint params q.1), gb.2)) *
            (1 - (G (pointHeight params q.1)).total)) *
        strategy.state.R ((G (pointHeight params q.1)).outcome gb.1)) ≤
      strategy.state.ev
        (strategy.state.L
            ((1 - (G (pointHeight params q.1)).total) *
              (evaluatedPointFamily params family q.2).outcome gb.2 *
              (1 - (G (pointHeight params q.1)).total)) *
          strategy.state.R ((G (pointHeight params q.1)).outcome gb.1)) := by
  set x := pointHeight params q.1
  set T := (G x).total
  set A := evaluatedPointFamily params family q.1
  set B := evaluatedPointFamily params family q.2
  set a := gb.1 (truncatePoint params q.1)
  have hTc : IsSelfAdjoint (1 - T) :=
    IsSelfAdjoint.of_nonneg (sub_nonneg.2 (G x).total_le_one)
  have hS_sq_le_B :
      star ((orderedProductOpFamily
          (evaluatedSliceFirstFactor params family q)
          (evaluatedSliceSecondFactor params family q)).outcome (a, gb.2)) *
        (orderedProductOpFamily
          (evaluatedSliceFirstFactor params family q)
          (evaluatedSliceSecondFactor params family q)).outcome (a, gb.2) ≤
      B.outcome gb.2 :=
    calc star (A.outcome a * B.outcome gb.2) * (A.outcome a * B.outcome gb.2)
        = B.outcome gb.2 * A.outcome a * B.outcome gb.2 := by
          rw [star_mul, A.outcome_hermitian a, B.outcome_hermitian gb.2, mul_assoc,
            ← mul_assoc (A.outcome a), evaluatedPointFamily_outcome_proj params family q.1 a,
            ← mul_assoc]
      _ ≤ B.outcome gb.2 * 1 * B.outcome gb.2 :=
          IsSelfAdjoint.conjugate_le_conjugate (A.outcome_le_one a) (B.outcome_hermitian gb.2)
      _ = B.outcome gb.2 := by
          rw [mul_one, evaluatedPointFamily_outcome_proj params family q.2 gb.2]
  exact strategy.state.ev_mono _ _ <| strategy.state.opTensor_mono_left
    (IsSelfAdjoint.conjugate_le_conjugate hS_sq_le_B hTc) ((G x).outcome_pos gb.1)

/-- The full stability-two defect is bounded by the overlap term for the
target slice measurement `G^x`. -/
lemma gCommStabilityTwo_pointwise_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hG : ∀ x, G x = (family.meas x).toSubMeas) :
    ∀ q : EvaluatedSliceQuestion params,
      strategy.state.qSDDOp
        (commDataProcessedGStabilityTwoLeft params strategy family G q)
        (commDataProcessedGStabilityTwoRight params strategy family G q) ≤
      strategy.state.ev
        (strategy.state.L (1 - (G (pointHeight params q.1)).total) *
          strategy.state.R ((G (pointHeight params q.1)).total)) := by
  intro q
  rw [commDataProcessedGStabilityTwo_qSDDOp_expand params strategy family G hG q]
  exact (Finset.sum_le_sum fun gb _ =>
    gCommStabilityTwo_pointwise_summand_bound params strategy family G q gb).trans
    (gCommStabilityTwo_pointwise_sum_bound params strategy family G hG q)

/-- Overlap-only version of the second stability estimate.

This removes the trailing `G^x` in the current SDD package via slice SSC overlap.
The paper's `clm:g-comm-stability2` first transports the right-register point
operators with `commutativityPoints`, then applies the boundedness witness
`Z^x`; that scalar mechanism is not what this internal lemma proves. The vendored theorem asks
for a normalized state. -/
theorem gCommStabilityTwo_overlap
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (gamma zeta : ℝ)
    (family : IdxPolyFamily params 𝔓)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    strategy.state.SDDOpRel
      (uniformDistribution (EvaluatedSliceQuestion params))
      (commDataProcessedGStabilityTwoLeft params strategy family G)
      (commDataProcessedGStabilityTwoRight params strategy family G)
      (Real.sqrt zeta + 6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : ℝ))) := by
  have hz_nonneg : 0 ≤ zeta :=
    (strategy.state.sddError_nonneg (uniformDistribution (Fq params)) _ _).trans
      hself.sliceSelfConsistency.squaredDistanceBound
  have hpointwise := gCommStabilityTwo_pointwise_bound params strategy family G hG
  -- The SSC argument gives the stronger `sqrt zeta` bound directly; it is then relaxed by
  -- monotonicity to the paper's displayed error term.
  exact Preliminaries.sddOpRel_mono strategy.state.toVecState
    (uniformDistribution (EvaluatedSliceQuestion params))
    (commDataProcessedGStabilityTwoLeft params strategy family G)
    (commDataProcessedGStabilityTwoRight params strategy family G)
    (Real.sqrt zeta) _
    (sddOpRel_of_sqrt_bound_from_half_one strategy.state.toVecState
      (uniformDistribution (EvaluatedSliceQuestion params))
      (commDataProcessedGStabilityTwoLeft params strategy family G)
      (commDataProcessedGStabilityTwoRight params strategy family G)
      zeta hz_nonneg
      (gCommStability_raw_le_half_of params strategy zeta family G hG hself _ _ Prod.fst
        (gCommOverlap_avgOver_fst params strategy G) hpointwise)
      (gCommStability_raw_le_one_of params strategy G _ _ Prod.fst hpointwise))
    (le_add_of_nonneg_right (by positivity))

end MIPRE.LIDT.Co.Commutativity

end

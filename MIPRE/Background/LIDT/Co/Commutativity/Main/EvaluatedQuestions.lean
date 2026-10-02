/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
Commutativity/Main/EvaluatedQuestions.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Commutativity.Main.Auxiliary.HEvalTransport
public import MIPRE.Background.LIDT.Co.Commutativity.Main.Auxiliary.ScalarMarginalization

@[expose] public section

/-!
# Section 11 commutativity: evaluated-question transport

Core Schwartz–Zippel transport on the evaluated-question space, comparing full-polynomial and
point-evaluated outcomes: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/Main/EvaluatedQuestions.lean` in the port of
`planning/c6b-plan.md` (milestone M7, section "Port conventions").

The vendored hypothesis `hnorm : strategy.state.IsNormalized` is dropped from
`fullSliceCommutation_of_evaluated_on_evaluated_questions`: normalization is a theorem of the
model (`VecState.ev_one_of_isNormalized`), and none of the lemmas the proof composes takes it
any more. Callers pass `params strategy family gamma zeta hgamma_nonneg hzeta_nonneg hself hEval`.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Commutativity

open MIPStarRE.LDT (Parameters FieldModel uniformDistribution)
open MIPStarRE.LDT.Commutativity (EvaluatedSliceQuestion fullSliceQuestionOfEvaluatedSlice
  commDataProcessedGError comMainError)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Core Schwartz-Zippel transport on the evaluated-question space.

This is the substantive remaining step: compare the full polynomial outcomes
with their point-evaluated postprocessings while paying the two `md/q`
Schwartz-Zippel losses and the self-consistency bookkeeping. -/
lemma fullSliceCommutation_of_evaluated_on_evaluated_questions
    (params : Parameters) [FieldModel params.q] (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (gamma zeta : ℝ)
    (hgamma_nonneg : 0 ≤ gamma) (hzeta_nonneg : 0 ≤ zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hEval :
      strategy.state.SDDOpRel
        (uniformDistribution (EvaluatedSliceQuestion params))
        (evaluatedFromFullSliceProductLeft params strategy family)
        (evaluatedFromFullSliceProductRight params strategy family)
        (commDataProcessedGError params gamma zeta)) :
    strategy.state.SDDOpRel
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => fullSliceProductLeft params strategy family
        (fullSliceQuestionOfEvaluatedSlice params q))
      (fun q => fullSliceProductRight params strategy family
        (fullSliceQuestionOfEvaluatedSlice params q))
      (comMainError params gamma zeta) := by
  /-
  Paper reference: `references/ldt-paper/commutativity-G.tex`, theorem `thm:com-main`,
  especially the passage from `eq:evaluate-gcom-at-points` to
  `eq:evaluate-gcom-at-points-part-dos` and the final displayed error estimate.

  The paper first reduces to the small-parameter regime `γ ≤ 1`, `ζ ≤ 1`, `d / q ≤ 1`;
  otherwise `comMainError ≥ 30 m ≥ 30` while `sddErrorOp ≤ 4` by the sub-measurement bound.
  In the small-parameter case two Schwartz-Zippel marginalizations and the evaluated
  commutation estimate obtained from `hEval` give the displayed error chain, which is then
  absorbed into `comMainError`.
  -/
  let 𝒟 := uniformDistribution (EvaluatedSliceQuestion params)
  let P := fun q => fullSliceProductLeft params strategy family
    (fullSliceQuestionOfEvaluatedSlice params q)
  let Q := fun q => fullSliceProductRight params strategy family
    (fullSliceQuestionOfEvaluatedSlice params q)
  have hm_ge : (1 : ℝ) ≤ (params.m : ℝ) :=
    Nat.one_le_cast.mpr (Nat.succ_le_of_lt params.hm)
  have hm0 : (0 : ℝ) ≤ params.m := Nat.cast_nonneg _
  have hdq_nn : 0 ≤ (params.d : ℝ) / (params.q : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hg4 : 0 ≤ Real.rpow gamma (1 / (4 : ℝ)) := Real.rpow_nonneg hgamma_nonneg _
  have hz4 : 0 ≤ Real.rpow zeta (1 / (4 : ℝ)) := Real.rpow_nonneg hzeta_nonneg _
  have hdq4 : 0 ≤ Real.rpow ((params.d : ℝ) / (params.q : ℝ)) (1 / (4 : ℝ)) :=
    Real.rpow_nonneg hdq_nn _
  by_cases hsmall : gamma ≤ 1 ∧ zeta ≤ 1 ∧ (params.d : ℝ) / (params.q : ℝ) ≤ 1
  · -- Small-parameter case: γ, ζ, d/q ≤ 1.
    obtain ⟨-, hzeta_le, hdq_le⟩ := hsmall
    -- Step 1, the Schwartz-Zippel transport: `sddErrorOp = 2 (fullABA − fullABAB)`, and
    -- `|fullABA − fullABAB| ≤ |fullABA − evalABA| + |evalABA − evalABAB| + |evalABAB − fullABAB|
    --   ≤ 4√ζ + √ν + (2md/q + 4√ζ)`.
    have hTransport :
        strategy.state.sddErrorOp 𝒟 P Q ≤
          16 * Real.sqrt zeta + 4 * (↑params.m * ↑params.d / ↑params.q) +
            2 * Real.sqrt (commDataProcessedGError params gamma zeta) := by
      have hMargX :=
        fullSlice_scalar_marginalize_x params strategy family zeta hself
      have hMargY :=
        fullSlice_scalar_marginalize_y params strategy family zeta hself
      have hClose :=
        fullSlice_closenessOfIP_CAB_hEval_sqrt params strategy family gamma zeta hEval
      rw [abs_sub_comm] at hMargY
      have h₁ := abs_sub_le (fullSliceABAAvg params strategy family)
        (evaluatedSliceABAAvg params strategy family) (fullSliceABABAvg params strategy family)
      have h₂ := abs_sub_le (evaluatedSliceABAAvg params strategy family)
        (evaluatedSliceABABAvg params strategy family) (fullSliceABABAvg params strategy family)
      have h₃ := le_abs_self
        (fullSliceABAAvg params strategy family - fullSliceABABAvg params strategy family)
      rw [fullSliceCommutation_qSDDOp_avg_eq params strategy family]
      linarith only [hMargX, hMargY, hClose, h₁, h₂, h₃]
    -- Step 2, the error arithmetic:
    -- `16√ζ + 4md/q + 2√(48m(√γ + √ζ)) ≤ 30m(γ^¼ + ζ^¼ + (d/q)^¼)`.
    have hArith :
        16 * Real.sqrt zeta + 4 * (↑params.m * ↑params.d / ↑params.q) +
            2 * Real.sqrt (commDataProcessedGError params gamma zeta) ≤
          comMainError params gamma zeta := by
      unfold commDataProcessedGError comMainError
      -- `√ζ ≤ ζ^¼` and `d/q ≤ (d/q)^¼`.
      have h_sqrt_z : Real.sqrt zeta ≤ Real.rpow zeta (1 / (4 : ℝ)) := by
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow_of_exponent_ge' hzeta_nonneg hzeta_le (by norm_num)
          (by norm_num)
      have h_dq : (params.d : ℝ) / params.q ≤
          Real.rpow ((params.d : ℝ) / params.q) (1 / (4 : ℝ)) := by
        conv_lhs => rw [← Real.rpow_one ((params.d : ℝ) / params.q)]
        exact Real.rpow_le_rpow_of_exponent_ge' hdq_nn hdq_le (by norm_num) (by norm_num)
      -- `(x^¼)² = x^½`.
      have hsq : ∀ x : ℝ, 0 ≤ x →
          (Real.rpow x (1 / (4 : ℝ))) ^ (2 : ℕ) = Real.rpow x (1 / (2 : ℝ)) := by
        intro x hx
        change (x ^ (1 / (4 : ℝ))) ^ (2 : ℕ) = x ^ (1 / (2 : ℝ))
        rw [← Real.rpow_mul_natCast hx]
        norm_num
      -- `√(48m(γ^½ + ζ^½)) ≤ √(48m) (γ^¼ + ζ^¼)`, from `a² + b² ≤ (a + b)²`.
      have hsqrt_cdpg :
          Real.sqrt (48 * ↑params.m *
            (Real.rpow gamma (1 / (2 : ℝ)) + Real.rpow zeta (1 / (2 : ℝ)))) ≤
          Real.sqrt (48 * ↑params.m) *
            (Real.rpow gamma (1 / (4 : ℝ)) + Real.rpow zeta (1 / (4 : ℝ))) := by
        rw [← hsq gamma hgamma_nonneg, ← hsq zeta hzeta_nonneg,
          ← Real.sqrt_sq (add_nonneg hg4 hz4), ← Real.sqrt_mul (by positivity)]
        refine Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left ?_ (by positivity))
        rw [add_sq]
        linarith only [mul_nonneg (mul_nonneg zero_le_two hg4) hz4]
      -- `√(48m) ≤ 7m`, since `48m ≤ 49m²` for `m ≥ 1`.
      have hsqrt_48m : Real.sqrt (48 * ↑params.m) ≤ 7 * ↑params.m := by
        rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 7 * ↑params.m)]
        refine Real.sqrt_le_sqrt ?_
        rw [mul_pow]
        linarith only [le_self_pow₀ hm_ge two_ne_zero, hm0]
      have hA : 16 * Real.sqrt zeta ≤ 16 * ↑params.m * Real.rpow zeta (1 / (4 : ℝ)) := by
        linarith only [h_sqrt_z, le_mul_of_one_le_left hz4 hm_ge]
      have hB : 4 * (↑params.m * ↑params.d / ↑params.q) ≤
          6 * ↑params.m * Real.rpow ((params.d : ℝ) / params.q) (1 / (4 : ℝ)) := by
        rw [mul_div_assoc]
        linarith only [mul_le_mul_of_nonneg_left h_dq hm0, mul_nonneg hm0 hdq4]
      have hC : 2 * Real.sqrt (48 * ↑params.m *
            (Real.rpow gamma (1 / (2 : ℝ)) + Real.rpow zeta (1 / (2 : ℝ)))) ≤
          14 * ↑params.m *
            (Real.rpow gamma (1 / (4 : ℝ)) + Real.rpow zeta (1 / (4 : ℝ))) := by
        linarith only [hsqrt_cdpg, mul_le_mul_of_nonneg_right hsqrt_48m (add_nonneg hg4 hz4)]
      -- `14m γ^¼ + 30m ζ^¼ + 6m (d/q)^¼ ≤ 30m (γ^¼ + ζ^¼ + (d/q)^¼)`.
      linarith only [hA, hB, hC, mul_nonneg hm0 hg4, mul_nonneg hm0 hdq4]
    exact ⟨hTransport.trans hArith⟩
  · -- Large-parameter case: `sddErrorOp ≤ 4` by the triangle inequality through the zero
    -- family, while `comMainError ≥ 30 m ≥ 30`, since some `x^¼ ≥ 1`.
    have hfour : strategy.state.SDDOpRel 𝒟 P Q 4 :=
      Preliminaries.stateDependentDistanceOpRel_mono strategy.state.toVecState 𝒟 P Q
        (2 * (1 + 1)) 4 (by norm_num)
        (Preliminaries.stateDependentDistanceOpRel_triangle strategy.state.toVecState 𝒟 P
          (fun _ => zeroFullSliceOpFamily (R := K →L[ℂ] K) params) Q 1 1
          (fullSliceProductLeft_to_zero_le_one params strategy family)
          (zero_to_fullSliceProductRight_le_one params strategy family))
    have hsum_ge_one :
        1 ≤ Real.rpow gamma (1 / (4 : ℝ)) + Real.rpow zeta (1 / (4 : ℝ)) +
          Real.rpow ((params.d : ℝ) / params.q) (1 / (4 : ℝ)) := by
      have hone : ∀ x : ℝ, 1 < x → 1 ≤ Real.rpow x (1 / (4 : ℝ)) := fun x hx =>
        Real.one_le_rpow hx.le (by norm_num)
      rcases not_and_or.mp hsmall with hg | hzdq
      · linarith only [hone _ (lt_of_not_ge hg), hz4, hdq4]
      rcases not_and_or.mp hzdq with hz | hdq
      · linarith only [hone _ (lt_of_not_ge hz), hg4, hdq4]
      · linarith only [hone _ (lt_of_not_ge hdq), hg4, hz4]
    have hcom_ge_four : 4 ≤ comMainError params gamma zeta := by
      unfold comMainError
      linarith only [one_le_mul_of_one_le_of_one_le hm_ge hsum_ge_one]
    exact Preliminaries.stateDependentDistanceOpRel_mono strategy.state.toVecState 𝒟 P Q
      4 (comMainError params gamma zeta) hcom_ge_four hfour

end MIPRE.LIDT.Co.Commutativity

end

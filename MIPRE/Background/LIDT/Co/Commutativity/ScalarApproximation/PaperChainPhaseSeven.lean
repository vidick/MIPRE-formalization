/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
Commutativity/ScalarApproximation/PaperChainPhaseSeven.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Commutativity.ScalarApproximation.PaperChainPhaseFive

@[expose] public section

/-!
# Section 11 commutativity: the phase-seven reverse insertion of the evaluated-slice paper chain

The second reverse `eq:add-an-a` bound used after the paper line-87 phase-five removal: the
counterpart of `Commutativity/ScalarApproximation/PaperChainPhaseSeven.lean` under
`MIPRE/Background/LIDT/MIPStarRE/LDT/` in the port of `planning/c6b-plan.md` (milestone M7,
section "Port conventions").

`evaluatedSlice_phaseSeven_second_reverse_bound` drops the vendored hypothesis
`hnorm : strategy.state.IsNormalized`, a theorem of the model, so its arguments are
`params strategy zeta family hcombined_snd`; `hcombined_snd` is stated with
`evaluatedPointFamilyLeft strategy.state` and `Preliminaries.totalSandwichFamily strategy.state`,
which take the model explicitly in the port. The vendored proof absorbs the inserted total with
`simp [opTensor_mul, …]`; here it is one `opTensor_mul` and
`Preliminaries.projSubMeas_outcome_mul_total_eq_outcome`.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Commutativity

open MIPStarRE.LDT (Parameters FieldModel Fq avgOver avgOver_congr uniformDistribution
  uniformDistribution_weight_sum_le_one)
open MIPStarRE.LDT.Commutativity (EvaluatedSliceQuestion)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Paper lines 103--104: reverse the second `eq:add-an-a` insertion. -/
lemma evaluatedSlice_phaseSeven_second_reverse_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (zeta : ℝ)
    (family : IdxPolyFamily params 𝔓)
    (hcombined_snd : strategy.state.SDDRel
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => evaluatedPointFamilyLeft strategy.state params family q.2)
      (fun q =>
        (Preliminaries.totalSandwichFamily strategy.state
          (evaluatedPointFamily params family)
          (evaluatedSlicePointMeas params strategy) q.2))
      (4 * zeta)) :
    let 𝒟 := uniformDistribution (EvaluatedSliceQuestion params)
    let phase6FirstRemoved : EvaluatedSliceQuestion params → ℝ :=
      evaluatedSlicePhaseSixFirstRemoved params strategy family
    let phase7GonnaCite : EvaluatedSliceQuestion params → ℝ :=
      evaluatedSlicePhaseSevenGonnaCite params strategy family
    |avgOver 𝒟 phase6FirstRemoved - avgOver 𝒟 phase7GonnaCite| ≤
      2 * Real.sqrt zeta := by
  intro 𝒟 phase6FirstRemoved phase7GonnaCite
  let S := strategy.state
  let A := evaluatedSliceFirstFactor params family
  let B := evaluatedSliceSecondFactor params family
  let T := Preliminaries.totalSandwichFamily S (evaluatedPointFamily params family)
    (evaluatedSlicePointMeas params strategy)
  let Aop : EvaluatedSliceQuestion params → Fq params → K →L[ℂ] K :=
    fun q b => S.L ((B q).outcome b)
  let Bop : EvaluatedSliceQuestion params → Fq params → K →L[ℂ] K :=
    fun q b => (T q.2).outcome b
  let C : EvaluatedSliceQuestion params → Fq params → Fq params → K →L[ℂ] K :=
    fun q b a => S.L ((A q).outcome a * (B q).outcome b)
  have hremoved :
      avgOver 𝒟 phase6FirstRemoved =
        avgOver 𝒟 (fun q => ∑ b : Fq params, ∑ a : Fq params, S.ev (C q b a * Bop q b)) :=
    avgOver_congr 𝒟 _ _ fun q => (Finset.sum_comm).trans <|
      Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by
        have htotal : (B q).outcome b * (evaluatedPointFamily params family q.2).total =
            (B q).outcome b :=
          Preliminaries.projSubMeas_outcome_mul_total_eq_outcome
            (evaluatedSliceSecondProj params family q) b
        change _ = S.ev (S.L _ * (S.L _ * S.R _))
        rw [← mul_assoc, S.leftTensor_mul_leftTensor, mul_assoc ((A q).outcome a), htotal]
  have hgonna :
      avgOver 𝒟 phase7GonnaCite =
        avgOver 𝒟 (fun q => ∑ b : Fq params, ∑ a : Fq params, S.ev (C q b a * Aop q b)) :=
    avgOver_congr 𝒟 _ _ fun q => (Finset.sum_comm).trans <|
      Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by
        simp only [C, Aop, S.leftTensor_mul_leftTensor]
        rfl
  have hclose :=
    Preliminaries.closenessOfIP S.toVecState 𝒟
      (uniformDistribution_weight_sum_le_one (EvaluatedSliceQuestion params)) Aop Bop C
      (4 * zeta) hcombined_snd.squaredDistanceBound
      (fun q => leftTensor_pair_prefix_normalization S (A q) (B q))
  rw [hremoved, hgonna, abs_sub_comm]
  refine hclose.trans_eq ?_
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), show Real.sqrt 4 = 2 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]]

end MIPRE.LIDT.Co.Commutativity

end

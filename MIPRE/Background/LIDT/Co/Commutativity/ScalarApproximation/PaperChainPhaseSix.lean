/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
Commutativity/ScalarApproximation/PaperChainPhaseSix.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Commutativity.ScalarApproximation.PaperChainPhaseFive

@[expose] public section

/-!
# Section 11 commutativity: the phase-six reverse insertion of the evaluated-slice paper chain

The first reverse `eq:add-an-a` bound used after the paper line-87 phase-five removal: the
counterpart of `Commutativity/ScalarApproximation/PaperChainPhaseSix.lean` under
`MIPRE/Background/LIDT/MIPStarRE/LDT/` in the port of `planning/c6b-plan.md` (milestone M7,
section "Port conventions").

`evaluatedSlice_phaseSix_first_reverse_bound` drops the vendored hypothesis
`hnorm : strategy.state.IsNormalized`, a theorem of the model, so its arguments are
`params strategy zeta family hcombined_fst`; `hcombined_fst` is stated with
`evaluatedPointFamilyLeft strategy.state` and `Preliminaries.totalSandwichFamily strategy.state`,
which take the model explicitly in the port. The vendored proof obtains the self-adjointness of
the two families from `Matrix.PosSemidef`; here it is `IsSelfAdjoint.of_nonneg`, and the
absorption of the inserted total into the first factor is one `opTensor_mul`.

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

/-- Paper lines 99--102: reverse the first `eq:add-an-a` insertion after `eq:gcom10`. -/
lemma evaluatedSlice_phaseSix_first_reverse_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (zeta : ℝ)
    (family : IdxPolyFamily params 𝔓)
    (hcombined_fst : strategy.state.SDDRel
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => evaluatedPointFamilyLeft strategy.state params family q.1)
      (fun q =>
        (Preliminaries.totalSandwichFamily strategy.state
          (evaluatedPointFamily params family)
          (evaluatedSlicePointMeas params strategy) q.1))
      (4 * zeta)) :
    let 𝒟 := uniformDistribution (EvaluatedSliceQuestion params)
    let phase5PaperRemoved : EvaluatedSliceQuestion params → ℝ :=
      evaluatedSlicePhaseFivePaperRemoved params strategy family
    let phase6FirstRemoved : EvaluatedSliceQuestion params → ℝ :=
      evaluatedSlicePhaseSixFirstRemoved params strategy family
    |avgOver 𝒟 phase5PaperRemoved - avgOver 𝒟 phase6FirstRemoved| ≤
      2 * Real.sqrt zeta := by
  intro 𝒟 phase5PaperRemoved phase6FirstRemoved
  let S := strategy.state
  let M := evaluatedSlicePointMeas params strategy
  let A := evaluatedSliceFirstFactor params family
  let B := evaluatedSliceSecondFactor params family
  let T := Preliminaries.totalSandwichFamily S (evaluatedPointFamily params family) M
  let Aop : EvaluatedSliceQuestion params → Fq params → K →L[ℂ] K :=
    fun q a => S.L ((A q).outcome a)
  let Bop : EvaluatedSliceQuestion params → Fq params → K →L[ℂ] K :=
    fun q a => (T q.1).outcome a
  let C : EvaluatedSliceQuestion params → Fq params → Fq params → K →L[ℂ] K :=
    fun q a b => S.L ((A q).outcome a * (B q).outcome b) * S.R ((M q.2).outcome b)
  have hAB :
      avgOver 𝒟 (fun q => S.qSDDCore (fun a => star (Aop q a)) (fun a => star (Bop q a))) ≤
        4 * zeta := by
    refine le_of_eq_of_le (avgOver_congr 𝒟 _ _ fun q => ?_) hcombined_fst.squaredDistanceBound
    have hA : ∀ a, star (Aop q a) = Aop q a := fun a =>
      (IsSelfAdjoint.of_nonneg (S.leftTensor_nonneg ((A q).outcome_pos a))).star_eq
    have hB : ∀ a, star (Bop q a) = Bop q a := fun a =>
      (IsSelfAdjoint.of_nonneg ((T q.1).outcome_pos a)).star_eq
    simp only [hA, hB]
    rfl
  have hreverse :
      avgOver 𝒟 phase6FirstRemoved =
        avgOver 𝒟 (fun q => ∑ a : Fq params, ∑ b : Fq params, S.ev (Aop q a * C q a b)) :=
    avgOver_congr 𝒟 _ _ fun q =>
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
        have hAproj : (A q).outcome a * (A q).outcome a = (A q).outcome a :=
          evaluatedPointFamily_outcome_proj params family q.1 a
        simp only [Aop, C, ← mul_assoc, S.leftTensor_mul_leftTensor, hAproj]
        rfl
  have hpaper :
      avgOver 𝒟 phase5PaperRemoved =
        avgOver 𝒟 (fun q => ∑ a : Fq params, ∑ b : Fq params, S.ev (Bop q a * C q a b)) :=
    avgOver_congr 𝒟 _ _ fun q =>
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
        have htotal : (evaluatedPointFamily params family q.1).total * (A q).outcome a =
            (A q).outcome a :=
          projSubMeas_total_mul_outcome_eq_outcome (evaluatedSliceFirstProj params family q) a
        change _ = S.ev (S.opTensor _ _ * S.opTensor _ _)
        rw [S.opTensor_mul, ← mul_assoc, htotal]
  have hclose :=
    Preliminaries.closenessOfIPAdjoint S.toVecState 𝒟
      (uniformDistribution_weight_sum_le_one (EvaluatedSliceQuestion params)) Aop Bop C
      (4 * zeta) hAB
      (fun q => leftRightTensor_prefix_pointMeasurement_adjoint_normalization S (A q) (B q)
        (strategy.pointMeasurement q.2))
  rw [abs_sub_comm, hpaper, hreverse]
  refine hclose.trans_eq ?_
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), show Real.sqrt 4 = 2 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]]

end MIPRE.LIDT.Co.Commutativity

end

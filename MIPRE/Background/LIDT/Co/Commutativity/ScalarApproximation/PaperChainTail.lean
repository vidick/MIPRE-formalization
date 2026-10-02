/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
Commutativity/ScalarApproximation/PaperChainTail.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Commutativity.ScalarApproximation.PaperChainPhaseFive

@[expose] public section

/-!
# Section 11 commutativity: the tail endpoints of the evaluated-slice paper chain

The two postprocessed self-consistency moves at the end of the paper-faithful scalar chain:
the counterpart of `Commutativity/ScalarApproximation/PaperChainTail.lean` under
`MIPRE/Background/LIDT/MIPStarRE/LDT/` in the port of `planning/c6b-plan.md` (milestone M7,
section "Port conventions").

Both lemmas drop the vendored hypothesis `hnorm : strategy.state.IsNormalized`, a theorem of the
model, so their arguments are `params strategy zeta family hpostSSC_snd`; `hpostSSC_snd` is
stated with `evaluatedPointFamilyLeft strategy.state` and `evaluatedPointFamilyRight
strategy.state`, which take the model explicitly in the port. The vendored proof of the
phase-nine bound obtains the self-adjointness of the placed families from `Matrix.PosSemidef`;
here it is `IsSelfAdjoint.of_nonneg`, and the right placement commutes past the left one by
`rightTensor_mul_leftTensor_eq_opTensor`.

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
open MIPStarRE.LDT.Commutativity (EvaluatedSliceQuestion EvaluatedSliceOutcome)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Paper line 117--118: move the second-coordinate factor to the right register. -/
lemma evaluatedSlice_phaseEight_tail_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (zeta : ℝ)
    (family : IdxPolyFamily params 𝔓)
    (hpostSSC_snd : strategy.state.SDDRel
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => evaluatedPointFamilyLeft strategy.state params family q.2)
      (fun q => evaluatedPointFamilyRight strategy.state params family q.2)
      zeta) :
    let 𝒟 := uniformDistribution (EvaluatedSliceQuestion params)
    let phase7GonnaCite : EvaluatedSliceQuestion params → ℝ :=
      evaluatedSlicePhaseSevenGonnaCite params strategy family
    let phase8TailRight : EvaluatedSliceQuestion params → ℝ :=
      evaluatedSlicePhaseEightTailRight params strategy family
    |avgOver 𝒟 phase7GonnaCite - avgOver 𝒟 phase8TailRight| ≤ Real.sqrt zeta := by
  intro 𝒟 phase7GonnaCite phase8TailRight
  let S := strategy.state
  let A := evaluatedSliceFirstFactor params family
  let B := evaluatedSliceSecondFactor params family
  let Aop : EvaluatedSliceQuestion params → Fq params → K →L[ℂ] K :=
    fun q b => S.L ((B q).outcome b)
  let Bop : EvaluatedSliceQuestion params → Fq params → K →L[ℂ] K :=
    fun q b => S.R ((B q).outcome b)
  let C : EvaluatedSliceQuestion params → Fq params → Fq params → K →L[ℂ] K :=
    fun q b a => S.L ((A q).outcome a * (B q).outcome b)
  have hgonna :
      avgOver 𝒟 phase7GonnaCite =
        avgOver 𝒟 (fun q => ∑ b : Fq params, ∑ a : Fq params, S.ev (C q b a * Aop q b)) :=
    avgOver_congr 𝒟 _ _ fun q => (Finset.sum_comm).trans <|
      Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by
        simp only [C, Aop, S.leftTensor_mul_leftTensor]
        rfl
  have htail :
      avgOver 𝒟 phase8TailRight =
        avgOver 𝒟 (fun q => ∑ b : Fq params, ∑ a : Fq params, S.ev (C q b a * Bop q b)) :=
    avgOver_congr 𝒟 _ _ fun q => Finset.sum_comm
  rw [hgonna, htail]
  exact Preliminaries.closenessOfIP S.toVecState 𝒟
    (uniformDistribution_weight_sum_le_one (EvaluatedSliceQuestion params)) Aop Bop C zeta
    hpostSSC_snd.squaredDistanceBound
    (fun q => leftTensor_pair_prefix_normalization S (A q) (B q))

/-- Paper line 118--119: move the second-coordinate factor back to the left register. -/
lemma evaluatedSlice_phaseNine_tail_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (zeta : ℝ)
    (family : IdxPolyFamily params 𝔓)
    (hpostSSC_snd : strategy.state.SDDRel
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => evaluatedPointFamilyLeft strategy.state params family q.2)
      (fun q => evaluatedPointFamilyRight strategy.state params family q.2)
      zeta) :
    let 𝒟 := uniformDistribution (EvaluatedSliceQuestion params)
    let phase8TailRight : EvaluatedSliceQuestion params → ℝ :=
      evaluatedSlicePhaseEightTailRight params strategy family
    let avgBAB : EvaluatedSliceQuestion params → ℝ := fun q =>
      ∑ ab : EvaluatedSliceOutcome params,
        evaluatedSliceBABTerm params strategy family q ab
    |avgOver 𝒟 phase8TailRight - avgOver 𝒟 avgBAB| ≤ Real.sqrt zeta := by
  intro 𝒟 phase8TailRight avgBAB
  let S := strategy.state
  let A := evaluatedSliceFirstFactor params family
  let B := evaluatedSliceSecondFactor params family
  let Aop : EvaluatedSliceQuestion params → Fq params → K →L[ℂ] K :=
    fun q b => S.L ((B q).outcome b)
  let Bop : EvaluatedSliceQuestion params → Fq params → K →L[ℂ] K :=
    fun q b => S.R ((B q).outcome b)
  let C : EvaluatedSliceQuestion params → Fq params → Fq params → K →L[ℂ] K :=
    fun q b a => S.L ((A q).outcome a * (B q).outcome b)
  have hAB :
      avgOver 𝒟 (fun q => S.qSDDCore (fun b => star (Aop q b)) (fun b => star (Bop q b))) ≤
        zeta := by
    refine le_of_eq_of_le (avgOver_congr 𝒟 _ _ fun q => ?_) hpostSSC_snd.squaredDistanceBound
    have hA : ∀ b, star (Aop q b) = Aop q b := fun b =>
      (IsSelfAdjoint.of_nonneg (S.leftTensor_nonneg ((B q).outcome_pos b))).star_eq
    have hB : ∀ b, star (Bop q b) = Bop q b := fun b =>
      (IsSelfAdjoint.of_nonneg (S.rightTensor_nonneg ((B q).outcome_pos b))).star_eq
    simp only [hA, hB]
    rfl
  have htail :
      avgOver 𝒟 phase8TailRight =
        avgOver 𝒟 (fun q => ∑ b : Fq params, ∑ a : Fq params, S.ev (Bop q b * C q b a)) :=
    avgOver_congr 𝒟 _ _ fun q => (Finset.sum_comm).trans <|
      Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ =>
        congrArg S.ev (S.rightTensor_mul_leftTensor_eq_opTensor _ _).symm
  have hbab :
      avgOver 𝒟 avgBAB =
        avgOver 𝒟 (fun q => ∑ b : Fq params, ∑ a : Fq params, S.ev (Aop q b * C q b a)) :=
    avgOver_congr 𝒟 _ _ fun q => (Fintype.sum_prod_type _).trans <| (Finset.sum_comm).trans <|
      Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by
        simp only [Aop, C, S.leftTensor_mul_leftTensor, ← mul_assoc]
        rfl
  rw [htail, hbab, abs_sub_comm]
  exact Preliminaries.closenessOfIPAdjoint S.toVecState 𝒟
    (uniformDistribution_weight_sum_le_one (EvaluatedSliceQuestion params)) Aop Bop C zeta hAB
    (fun q => leftTensor_pair_prefix_adjoint_normalization S (A q) (B q))

end MIPRE.LIDT.Co.Commutativity

end

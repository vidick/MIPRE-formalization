/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
Commutativity/EvaluatedSliceBounds/PhaseOneThree.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Commutativity.Scaffold.Products
public import MIPRE.Background.LIDT.Co.Preliminaries.CauchySchwarz

@[expose] public section

/-!
# Section 11 commutativity: the phase-1 evaluated-slice insertion bound

Closeness-of-inner-product side conditions for inserting Bob's measurement into the first
evaluated-slice step of the paper proof, and the phase-1 insertion estimate itself: the
counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/EvaluatedSliceBounds/PhaseOneThree.lean` in
the port of `planning/c6b-plan.md` (milestone M7, section "Port conventions").

The left placement of the vendored `leftTensor (ι₂ := ι)` is the model's `S.L`, so
`leftTensor_normalizationConditionSquare_le_one` takes the symmetric model `S` as an explicit
first argument, as M3's placement lemmas do (`planning/c6b-plan.md`, "Departures in M3 and
M5"). `evaluatedSlice_phaseOne_insert_bound` drops the vendored hypothesis
`hnorm : strategy.state.IsNormalized`, a theorem of the model, and its `hcombined_snd` is stated
with `evaluatedPointFamilyLeft strategy.state` and
`Preliminaries.totalSandwichFamily strategy.state`, which take the model explicitly in the port.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Commutativity

open MIPStarRE.LDT (Parameters FieldModel Point Fq Distribution avgOver avgOver_congr
  uniformDistribution uniformDistribution_weight_sum_le_one)
open MIPStarRE.LDT.Commutativity (EvaluatedSliceQuestion EvaluatedSliceOutcome)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The left placement of the sandwiched totals `∑_b Q_b P_a Q_b` satisfies the normalization
condition `∑_a (∑_b L(Q_b P_a Q_b)) (∑_b L(Q_b P_a Q_b))^* ≤ 1` of `closenessOfIP`. -/
lemma leftTensor_normalizationConditionSquare_le_one
    (S : SymModel 𝔓 K)
    {OutcomeA OutcomeB : Type*} [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA 𝔓) (Q : ProjSubMeas OutcomeB 𝔓) :
    ∑ a : OutcomeA,
        (∑ b : OutcomeB, S.L (Q.outcome b * P.outcome a * Q.outcome b)) *
        star (∑ b : OutcomeB, S.L (Q.outcome b * P.outcome a * Q.outcome b)) ≤
      1 := by
  simp only [S.leftTensor_finset_sum, S.leftTensor_conjTranspose, S.leftTensor_mul_leftTensor]
  exact S.leftTensor_le_one (normalizationConditionSquareFamily P Q).total_le_one

/-- View the `params.next` point measurement with the outcome type rewritten as
`Fq params`. -/
noncomputable def evaluatedSlicePointMeas
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) :
    IdxMeas (Point params.next) (Fq params) 𝔓 :=
  fun u => (strategy.pointMeasurement u).toMeasurement

/-- Phase-1 insertion step for `evaluatedSlice_scalar_chain_bound`.

This is the `eq:gcom8 -> eq:apply-add-an-a-once` comparison: transport the
pointwise `consSubMeas` control to the second coordinate of an evaluated-slice
question, then apply `closenessOfIP` with the left-sandwich family
`G_a^{u,x} G_b^{v,y} G_a^{u,x}`.  The inserted term is kept in the explicit
`G^y \otimes A_b^{v,y}` form coming from `totalSandwichFamily`. -/
lemma evaluatedSlice_phaseOne_insert_bound
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
    let inserted : EvaluatedSliceQuestion params → ℝ := fun q =>
      ∑ b : Fq params, ∑ a : Fq params,
        strategy.state.ev
          (strategy.state.L
              (((evaluatedSliceFirstFactor params family q).outcome a) *
                ((evaluatedSliceSecondFactor params family q).outcome b) *
                ((evaluatedSliceFirstFactor params family q).outcome a)) *
            ((Preliminaries.totalSandwichFamily strategy.state
              (evaluatedPointFamily params family)
              (evaluatedSlicePointMeas params strategy) q.2).outcome b))
    |avgOver 𝒟
        (fun q => ∑ ab : EvaluatedSliceOutcome params,
          evaluatedSliceABABTerm params strategy family q ab) -
      avgOver 𝒟 inserted| ≤ 2 * Real.sqrt zeta := by
  intro 𝒟 inserted
  let S := strategy.state
  let A : EvaluatedSliceQuestion params → Fq params → K →L[ℂ] K :=
    fun q b => S.L ((evaluatedSliceSecondFactor params family q).outcome b)
  let B : EvaluatedSliceQuestion params → Fq params → K →L[ℂ] K :=
    fun q b =>
      (Preliminaries.totalSandwichFamily S (evaluatedPointFamily params family)
        (evaluatedSlicePointMeas params strategy) q.2).outcome b
  let C : EvaluatedSliceQuestion params → Fq params → Fq params → K →L[ℂ] K :=
    fun q b a =>
      S.L (((evaluatedSliceFirstFactor params family q).outcome a) *
        ((evaluatedSliceSecondFactor params family q).outcome b) *
        ((evaluatedSliceFirstFactor params family q).outcome a))
  have hABAB :
      avgOver 𝒟
          (fun q => ∑ ab : EvaluatedSliceOutcome params,
            evaluatedSliceABABTerm params strategy family q ab) =
        avgOver 𝒟 (fun q => ∑ b : Fq params, ∑ a : Fq params, S.ev (C q b a * A q b)) := by
    refine avgOver_congr 𝒟 _ _ fun q => ?_
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    simp only [C, A, S.leftTensor_mul_leftTensor]
    rfl
  have hclose :=
    Preliminaries.closenessOfIP S.toVecState 𝒟
      (uniformDistribution_weight_sum_le_one (EvaluatedSliceQuestion params)) A B C (4 * zeta)
      hcombined_snd.squaredDistanceBound
      (fun q => leftTensor_normalizationConditionSquare_le_one S
        (evaluatedSliceSecondFactor params family q) (evaluatedSliceFirstProj params family q))
  rw [hABAB]
  refine hclose.trans_eq ?_
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), show Real.sqrt 4 = 2 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]]

end MIPRE.LIDT.Co.Commutativity

end

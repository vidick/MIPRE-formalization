/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
Commutativity/Transport/EvaluationSpecialization.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Commutativity.GCommStability.OverlapTwo
public import MIPRE.Background.LIDT.Co.CommutativityPoints.SharedHelpers.Core

@[expose] public section

/-!
# Section 11 commutativity: transport via evaluation specialization

Postprocessing identities for `leftPlacedOpFamily` of bilinear products, used to transport
bounds across evaluation specializations of the full-slice commutation argument: the
counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/Transport/EvaluationSpecialization.lean` in
the port of `planning/c6b-plan.md` (milestone M7, section "Port conventions").

The vendored placement `OpFamily.leftPlacedOpFamily (ιB := ι)` is
`OpFamily.leftPlacedOpFamily S` for a symmetric model `S`, which
`postprocess_leftPlacedOpFamily_product_outcome` takes as an explicit first argument, as the
placement lemmas of M1 and M3 do. The distance statements are `strategy.state.sddErrorOp` and
`strategy.state.SDDOpRel`, vector-state quantities on joint operators.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Commutativity

open MIPStarRE.LDT (Parameters FieldModel truncatePoint pointHeight uniformDistribution)
open MIPStarRE.LDT.Commutativity (EvaluatedSliceQuestion EvaluatedSliceOutcome
  fullSliceQuestionOfEvaluatedSlice evaluateFullSliceOutcomeAtQuestion)
open MIPRE.LIDT.Co.CommutativityPoints (orderedProductOpFamily reversedProductOpFamily)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Postprocessing a `leftPlacedOpFamily` of a bilinear product equals
the `leftPlacedOpFamily` of the product of postprocessed submeasurements,
for any binary operation `g` that factors over finite sums. -/
lemma postprocess_leftPlacedOpFamily_product_outcome
    (S : SymModel 𝔓 K)
    {α₁ α₂ β₁ β₂ : Type*}
    [Fintype α₁] [Fintype α₂] [Fintype β₁] [Fintype β₂]
    (A : SubMeas α₁ 𝔓) (B : SubMeas α₂ 𝔓)
    (f₁ : α₁ → β₁) (f₂ : α₂ → β₂) (b₁ : β₁) (b₂ : β₂)
    (g : 𝔓 → 𝔓 → 𝔓)
    (hg_factor : ∀ (S : Finset α₁) (T : Finset α₂) (fA : α₁ → 𝔓) (fB : α₂ → 𝔓),
      ∑ a ∈ S ×ˢ T, g (fA a.1) (fB a.2) = g (∑ a ∈ S, fA a) (∑ b ∈ T, fB b)) :
    (OpFamily.postprocess
      (OpFamily.leftPlacedOpFamily S
        (⟨fun ab => g (A.outcome ab.1) (B.outcome ab.2),
          g A.total B.total⟩ : OpFamily (α₁ × α₂) 𝔓))
      (fun ab => (f₁ ab.1, f₂ ab.2))).outcome (b₁, b₂) =
    (OpFamily.leftPlacedOpFamily S
      (⟨fun ab => g ((postprocess A f₁).outcome ab.1)
          ((postprocess B f₂).outcome ab.2),
        g (postprocess A f₁).total
          (postprocess B f₂).total⟩ :
          OpFamily (β₁ × β₂) 𝔓)).outcome (b₁, b₂) := by
  classical
  simp only [OpFamily.postprocess, OpFamily.leftPlacedOpFamily, OpFamily.map_outcome, postprocess]
  rw [S.leftTensor_finset_sum]
  refine congrArg S.L ((Finset.sum_congr ?_ fun _ _ => rfl).trans (hg_factor _ _ _ _))
  ext ⟨x, y⟩
  simp

/-- The evaluated-from-full-slice ordered product equals the
evaluated-slice ordered product at each question-outcome pair. -/
lemma evaluatedFromFullSliceProductLeft_outcome_eq
    (params : Parameters) [FieldModel params.q] (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (q : EvaluatedSliceQuestion params)
    (ab : EvaluatedSliceOutcome params) :
    (evaluatedFromFullSliceProductLeft params strategy family q).outcome ab =
    (evaluatedSliceProductLeft params strategy family q).outcome ab :=
  postprocess_leftPlacedOpFamily_product_outcome strategy.state
    (fullSliceFirstFactor params family (pointHeight params q.1, pointHeight params q.2))
    (fullSliceSecondFactor params family (pointHeight params q.1, pointHeight params q.2))
    (fun g => g (truncatePoint params q.1)) (fun h => h (truncatePoint params q.2)) ab.1 ab.2
    (· * ·) fun S T fA fB => by
      rw [Finset.sum_product]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]

/-- The evaluated-from-full-slice reversed product equals the
evaluated-slice reversed product at each question-outcome pair. -/
lemma evaluatedFromFullSliceProductRight_outcome_eq
    (params : Parameters) [FieldModel params.q] (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (q : EvaluatedSliceQuestion params)
    (ab : EvaluatedSliceOutcome params) :
    (evaluatedFromFullSliceProductRight params strategy family q).outcome ab =
    (evaluatedSliceProductRight params strategy family q).outcome ab :=
  postprocess_leftPlacedOpFamily_product_outcome strategy.state
    (fullSliceFirstFactor params family (pointHeight params q.1, pointHeight params q.2))
    (fullSliceSecondFactor params family (pointHeight params q.1, pointHeight params q.2))
    (fun g => g (truncatePoint params q.1)) (fun h => h (truncatePoint params q.2)) ab.1 ab.2
    (fun x y => y * x) fun S T fA fB => by
      rw [Finset.sum_product]
      simp_rw [← Finset.sum_mul]
      rw [← Finset.mul_sum]

/-- The evaluated-from-full-slice SDD error equals the evaluated-slice
SDD error, because the postprocessed product equals the product of
postprocessed submeasurements at every question-outcome pair. -/
lemma evaluationSpecialization_sddErrorOp_eq
    (params : Parameters) [FieldModel params.q] (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓) :
    strategy.state.sddErrorOp
      (uniformDistribution (EvaluatedSliceQuestion params))
      (evaluatedFromFullSliceProductLeft params strategy family)
      (evaluatedFromFullSliceProductRight params strategy family) =
    strategy.state.sddErrorOp
      (uniformDistribution (EvaluatedSliceQuestion params))
      (evaluatedSliceProductLeft params strategy family)
      (evaluatedSliceProductRight params strategy family) := by
  simp only [VecState.sddErrorOp, VecState.qSDDOp, VecState.qSDDCore,
    evaluatedFromFullSliceProductLeft_outcome_eq, evaluatedFromFullSliceProductRight_outcome_eq]

/-- Restate the evaluated-from-full-slice commutation bound as a bound for the
evaluated-slice product families, using the pointwise postprocessing identities. -/
lemma evaluatedSliceCommutation_of_evaluationSpecialization
    (params : Parameters) [FieldModel params.q] (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (δ : ℝ)
    (hEval :
      strategy.state.SDDOpRel
        (uniformDistribution (EvaluatedSliceQuestion params))
        (evaluatedFromFullSliceProductLeft params strategy family)
        (evaluatedFromFullSliceProductRight params strategy family)
        δ) :
    strategy.state.SDDOpRel
      (uniformDistribution (EvaluatedSliceQuestion params))
      (evaluatedSliceProductLeft params strategy family)
      (evaluatedSliceProductRight params strategy family)
      δ :=
  CommutativityPoints.sddOpRel_congr_outcome strategy.state.toVecState
    (uniformDistribution (EvaluatedSliceQuestion params))
    (evaluatedFromFullSliceProductLeft params strategy family)
    (evaluatedFromFullSliceProductRight params strategy family)
    (evaluatedSliceProductLeft params strategy family)
    (evaluatedSliceProductRight params strategy family) δ
    (evaluatedFromFullSliceProductLeft_outcome_eq params strategy family)
    (evaluatedFromFullSliceProductRight_outcome_eq params strategy family)
    hEval

end MIPRE.LIDT.Co.Commutativity

end

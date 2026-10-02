/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/
SwitcherooSetup/Terms.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored
file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.SwitcherooSetup.Centers

@[expose] public section

/-!
# Section 12 pasting: switcheroo aggregate terms

The remaining switcheroo aggregate terms and split formulas: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/SwitcherooSetup/Terms.lean` in the port of
`planning/c6b-plan.md` (milestone M11, section "Port conventions").

The vendored second bipartite state `ψbi : QuantumState (ι × ι)` is the symmetric model
`S : SymModel 𝔓 K`, in the vendored argument position; the slice family is an
`IdxPolyFamily params 𝔓` and the auxiliary family `M` an `IdxProjSubMeas (Fq params) Outcome 𝔓`.

`switcherooAggregateThirdTerm_eq_fourthTerm` takes the adjoint in the local algebra, through
`S.ev_conjTranspose` and `S.leftTensor_conjTranspose`, in place of the vendored
`conjTranspose_opTensor` with the identity, and the Hermitian facts come from
`IsSelfAdjoint.of_nonneg` rather than `Matrix.PosSemidef`. `switcherooAggregateFourthTerm_eq_split`
inserts `G = ∑_g G_g G_g` in the local algebra and pulls the sum out through
`S.leftTensor_finset_sum` and `S.ev_sum`.

## Not ported

Nothing: every declaration of the vendored file is ported here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel Fq avgOver avgOver_congr uniformDistribution)
open MIPStarRE.LDT.Pasting (SliceQuestion SlicePairQuestion)
open MIPRE.LIDT.Co (SymModel SubMeas ProjSubMeas IdxProjSubMeas IdxPolyFamily)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The one-outcome projective family whose sole effect is the complete slice part `G^x`. -/
noncomputable def completePartProjFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) :
    IdxProjSubMeas (SliceQuestion params) Unit 𝔓 :=
  fun x =>
    { toSubMeas := completePartSubMeas params family x
      proj := ProjSubMeas.postprocess_outcome_proj (family.meas x) (fun _ => ()) }

/-- The second positive term in the switcheroo expansion. -/
noncomputable def switcherooAggregateSecondTerm
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓) : ℝ :=
  avgOver (uniformDistribution (SlicePairQuestion params)) fun q =>
    ∑ o : Outcome,
      S.ev
        (S.L
          ((completePartSubMeas params family q.1).total * (M q.2).outcome o *
            (completePartSubMeas params family q.1).total))

/-- The third (negative) term in the switcheroo expansion. -/
noncomputable def switcherooAggregateThirdTerm
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓) : ℝ :=
  avgOver (uniformDistribution (SlicePairQuestion params)) fun q =>
    ∑ o : Outcome,
      S.ev
        (S.L
          ((M q.2).outcome o *
            (completePartSubMeas params family q.1).total *
            (M q.2).outcome o *
            (completePartSubMeas params family q.1).total))

/-- The fourth (negative) term in the switcheroo expansion. -/
noncomputable def switcherooAggregateFourthTerm
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓) : ℝ :=
  avgOver (uniformDistribution (SlicePairQuestion params)) fun q =>
    ∑ o : Outcome,
      S.ev
        (S.L
          ((completePartSubMeas params family q.1).total *
            (M q.2).outcome o *
            (completePartSubMeas params family q.1).total *
            (M q.2).outcome o))

/-- The third and fourth switcheroo terms agree: their summands are adjoint to each other. -/
theorem switcherooAggregateThirdTerm_eq_fourthTerm
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓) :
    switcherooAggregateThirdTerm params S family M =
      switcherooAggregateFourthTerm params S family M := by
  refine avgOver_congr _ _ _ fun q => Finset.sum_congr rfl fun o _ => ?_
  have hG : IsSelfAdjoint (completePartSubMeas params family q.1).total :=
    IsSelfAdjoint.of_nonneg (completePartSubMeas params family q.1).total_nonneg
  have hMo : IsSelfAdjoint ((M q.2).outcome o) := (M q.2).outcome_hermitian o
  rw [← S.ev_conjTranspose, S.leftTensor_conjTranspose]
  simp only [star_mul, hG.star_eq, hMo.star_eq, mul_assoc]

/-- Split the fourth switcheroo term by inserting the complete-part projector
resolution `G = ∑_g G_g`. -/
theorem switcherooAggregateFourthTerm_eq_split
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓) :
    switcherooAggregateFourthTerm params S family M =
      avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
        ∑ go : MIPStarRE.LDT.Polynomial params × Outcome,
          S.ev
            (S.L
              ((completePartSubMeas params family q.1).total *
                (M q.2).outcome go.2 *
                (family.meas q.1).outcome go.1 *
                (family.meas q.1).outcome go.1 *
                (M q.2).outcome go.2))) := by
  refine avgOver_congr _ _ _ fun q => ?_
  have hG : (completePartSubMeas params family q.1).total =
      ∑ g, (family.meas q.1).outcome g * (family.meas q.1).outcome g := by
    rw [completePartSubMeas_total, ← (family.meas q.1).sum_eq_total]
    exact Finset.sum_congr rfl fun g _ => ((family.meas q.1).proj g).symm
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [← S.ev_sum, S.leftTensor_finset_sum]
  congr 2
  calc _ = (completePartSubMeas params family q.1).total * (M q.2).outcome o *
        (∑ g, (family.meas q.1).outcome g * (family.meas q.1).outcome g) * (M q.2).outcome o := by
        rw [← hG]
    _ = _ := by simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]

end MIPRE.LIDT.Co.Pasting

end

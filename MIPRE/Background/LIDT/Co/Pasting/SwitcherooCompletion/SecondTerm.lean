/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/
SwitcherooCompletion/SecondTerm.lean, to the symmetric model of `planning/c6b-plan.md`; not a
vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.SwitcherooCompletion.Expansion

@[expose] public section

/-!
# Section 12 pasting: switcheroo second term

Complete-part self-consistency and the second switcheroo term: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/SwitcherooCompletion/SecondTerm.lean` in the port of
`planning/c6b-plan.md` (milestone M11, section "Port conventions").

The vendored second bipartite state `ψbi : QuantumState (ι × ι)` is the symmetric model
`S : SymModel 𝔓 K`, in the vendored argument position; the slice family is an
`IdxPolyFamily params 𝔓` and the auxiliary family `M` an `IdxProjSubMeas (Fq params) Outcome 𝔓`.
The vendored hypothesis `hnorm : ψbi.IsNormalized` of `switcheroo_second_aggregate_term_close`
is dropped, normalization being a theorem of the model (section "Swap symmetry is a theorem"):
callers pass `params S family M zeta hselfG`.

`completePartProjFamily_selfConsistency_generic` is `qSDD_completePart_le_slice` averaged, the
placed families agreeing by definition. `switcheroo_second_aggregate_term_close` reads the second
term as an iterated average by `avgOver_uniform_prod_swap` (in place of the vendored
`avgOver_uniform_equiv` along `Prod.swap` followed by `avgOver_uniform_prod`) and merges the
placements by `S.leftTensor_mul_leftTensor`, the switch sandwich doing the rest. The two
`opTensor` forms of the centres reduce to `S.L A * S.R B`, which is `S.opTensor A B` by
definition, after pulling the outcome sum through `S.R` by `S.rightTensor_finset_sum`.

## Not ported

Nothing: every declaration of the vendored file is ported here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel Fq Distribution avgOver avgOver_congr avgOver_mono
  avgOver_sub avgOver_uniform_prod_swap avgOver_uniform_le_const uniformDistribution
  uniformDistribution_weight_sum_le_one)
open MIPStarRE.LDT.Pasting (SliceQuestion SlicePairQuestion avgOver_abs_le_avgOver_abs)
open MIPRE.LIDT.Co (SymModel IdxProjSubMeas IdxPolyFamily)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The one-outcome complete-part family inherits self-consistency from the slice family. -/
theorem completePartProjFamily_selfConsistency_generic
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (zeta : ℝ)
    (hself : GCompleteSelfConsistencyStatement params S family zeta) :
    S.SDDRel
      (uniformDistribution (SliceQuestion params))
      (switcherooSelfConsistencyLeft S params (completePartProjFamily params family))
      (switcherooSelfConsistencyRight S params (completePartProjFamily params family))
      zeta :=
  ⟨le_trans (avgOver_mono _ _ _ fun x => qSDD_completePart_le_slice params S family x)
    hself.completePartSelfConsistency.squaredDistanceBound⟩

/-- The second positive switcheroo term is close to the swapped center coming
from the complete-part family.

This aggregate form matches the four-term `qSDDOp` expansion: the projective
family in the sandwich is the one-outcome complete part `G^x`, not the original
slice-outcome family. -/
theorem switcheroo_second_aggregate_term_close
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓)
    (zeta : ℝ)
    (hselfG : GCompleteSelfConsistencyStatement params S family zeta) :
    let secondTerm := switcherooAggregateSecondTerm params S family M
    let commonTerm :=
      avgOver (uniformDistribution (SliceQuestion params))
        (fun y => Preliminaries.middleSandwichExpectation S
          (uniformDistribution (SliceQuestion params))
          (completePartProjFamily params family) (((M y).toSubMeas).total))
    |secondTerm - commonTerm| ≤ 2 * Real.sqrt zeta := by
  intro secondTerm commonTerm
  let 𝒟x : Distribution (SliceQuestion params) := uniformDistribution (SliceQuestion params)
  let Gcomplete : IdxProjSubMeas (SliceQuestion params) Unit 𝔓 :=
    completePartProjFamily params family
  let L : Fq params → ℝ := fun y =>
    Preliminaries.leftSandwichExpectation S 𝒟x Gcomplete (((M y).toSubMeas).total)
  let C : Fq params → ℝ := fun y =>
    Preliminaries.middleSandwichExpectation S 𝒟x Gcomplete (((M y).toSubMeas).total)
  have hselfG_bip := switcherooSelfConsistency_bip params S Gcomplete zeta
    (completePartProjFamily_selfConsistency_generic params S family zeta hselfG)
  have hpoint : ∀ y, |L y - C y| ≤ 2 * Real.sqrt zeta := fun y =>
    (Preliminaries.switchSandwich S 𝒟x
      (uniformDistribution_weight_sum_le_one (SliceQuestion params))
      Gcomplete
      (((M y).toSubMeas).total)
      ⟨((M y).toSubMeas).total_nonneg, sub_nonneg.mpr ((M y).toSubMeas).total_le_one⟩
      zeta
      hselfG_bip).leftSandwichTransfer
  have hsecond_eq : secondTerm = avgOver 𝒟x L := by
    refine (avgOver_uniform_prod_swap (α := SliceQuestion params) (β := SliceQuestion params)
      (fun x y => ∑ o : Outcome, S.ev (S.L ((completePartSubMeas params family x).total *
        (M y).outcome o * (completePartSubMeas params family x).total)))).trans ?_
    refine avgOver_congr _ _ _ fun y => avgOver_congr _ _ _ fun x => ?_
    change _ = ∑ _u : Unit,
      S.ev (S.L ((completePartSubMeas params family x).outcome ()) *
        S.L (((M y).toSubMeas).total) * S.L ((completePartSubMeas params family x).outcome ()))
    rw [Fintype.sum_unique (ι := Unit), completePartSubMeas_outcome_unit, S.leftTensor_mul_leftTensor,
      S.leftTensor_mul_leftTensor, ← (M y).sum_eq_total, Finset.mul_sum, Finset.sum_mul,
      ← S.leftTensor_finset_sum, S.ev_sum]
  calc |secondTerm - commonTerm|
      = |avgOver 𝒟x (fun y => L y - C y)| := by
        rw [hsecond_eq, avgOver_sub]
    _ ≤ avgOver 𝒟x (fun y => |L y - C y|) := avgOver_abs_le_avgOver_abs _ _
    _ ≤ 2 * Real.sqrt zeta :=
        avgOver_uniform_le_const (fun y : SliceQuestion params => |L y - C y|)
          (2 * Real.sqrt zeta) hpoint

/-- The complete-part `M ⊗ G` switcheroo center, expressed as a slice-pair
`opTensor` average over the `M`-totals and complete-part `G`-totals. -/
theorem switcherooAggregateMGCenterComplete_eq_opTensor_avg
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓) :
    avgOver (uniformDistribution (SliceQuestion params))
        (fun y =>
          Preliminaries.middleSandwichExpectation S
            (uniformDistribution (SliceQuestion params))
            (completePartProjFamily params family) (((M y).toSubMeas).total)) =
      avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
        S.ev
          (S.opTensor
            (((M q.2).toSubMeas).total)
            ((completePartSubMeas params family q.1).total))) := by
  refine ((avgOver_uniform_prod_swap (α := SliceQuestion params) (β := SliceQuestion params)
    (fun x y => S.ev (S.opTensor (((M y).toSubMeas).total)
      ((completePartSubMeas params family x).total)))).trans ?_).symm
  refine avgOver_congr _ _ _ fun y => avgOver_congr _ _ _ fun x => ?_
  change _ = ∑ _u : Unit,
    S.ev (S.L (((M y).toSubMeas).total) * S.R ((completePartSubMeas params family x).outcome ()))
  rw [Fintype.sum_unique (ι := Unit), completePartSubMeas_outcome_unit]

/-- The `G ⊗ M` switcheroo center, expressed as a slice-pair `opTensor` average
over the complete-part `G`-totals and `M`-totals. -/
theorem switcherooAggregateTarget_eq_opTensor_avg
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓) :
    switcherooAggregateTarget params S family M =
      avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
        S.ev
          (S.opTensor
            ((completePartSubMeas params family q.1).total)
            (((M q.2).toSubMeas).total))) := by
  refine avgOver_congr _ _ _ fun q => ?_
  rw [← S.ev_sum, ← Finset.mul_sum, S.rightTensor_finset_sum, (M q.2).sum_eq_total]

end MIPRE.LIDT.Co.Pasting

end

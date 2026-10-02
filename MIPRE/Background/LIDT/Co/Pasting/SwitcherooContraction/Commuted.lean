/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/
SwitcherooContraction/Commuted.lean, to the symmetric model of `planning/c6b-plan.md`; not a
vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.SwitcherooContraction.Split

@[expose] public section

/-!
# Section 12 pasting: switcheroo commuted contraction

The once-commuted contraction step and the split-by-`g` rewrite: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/SwitcherooContraction/Commuted.lean` in the port of
`planning/c6b-plan.md` (milestone M11, section "Port conventions").

The vendored second bipartite state `ψbi : QuantumState (ι × ι)` is the symmetric model
`S : SymModel 𝔓 K`, in the vendored argument position; the slice family is an
`IdxPolyFamily params 𝔓` and the auxiliary family `M` an `IdxProjSubMeas (Fq params) Outcome 𝔓`.

The right-action contraction witness places operators by `leftTensor (ι₂ := ι)` without a state
in the vendored file; here it takes the model as an explicit first argument
(`switcherooAggregateFourthTerm_once_commuted_contraction_right S params family M q`), as the
witnesses of `Co/Pasting/SwitcherooContraction/Split.lean` do. It is proved in the local algebra
`𝔓` and pushed through `S.L` by `S.leftTensor_le_one`, in place of the vendored
`conjTranspose_opTensor` and `opTensor_mono_left` with the identity on the second factor.
`switcherooAggregateFirstTerm_eq_split_by_g` inserts `G = ∑_g G_g` in the local algebra and
pulls the sum out through `S.leftTensor_finset_sum` and `S.ev_sum`, as
`switcherooAggregateFourthTerm_eq_split` does.

## Not ported

Nothing: every declaration of the vendored file is ported here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel Fq avgOver avgOver_congr uniformDistribution)
open MIPStarRE.LDT.Pasting (SlicePairQuestion)
open MIPRE.LIDT.Co (SymModel IdxProjSubMeas IdxPolyFamily)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Right-action contraction witness for the second `sqrt zeta` transfer. -/
theorem switcherooAggregateFourthTerm_once_commuted_contraction_right
    (S : SymModel 𝔓 K)
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓)
    (q : SlicePairQuestion params) :
    (∑ g : MIPStarRE.LDT.Polynomial params,
        star (∑ o : Outcome,
            S.L
              ((completePartSubMeas params family q.1).total *
                (M q.2).outcome o *
                (family.meas q.1).outcome g *
                (M q.2).outcome o)) *
          (∑ o : Outcome,
            S.L
              ((completePartSubMeas params family q.1).total *
                (M q.2).outcome o *
                (family.meas q.1).outcome g *
                (M q.2).outcome o))) ≤ 1 := by
  set G : 𝔓 := (completePartSubMeas params family q.1).total
  set X : MIPStarRE.LDT.Polynomial params → 𝔓 := switcherooAggregateFourthTermX params family M q
  have hG : star G = G := switcherooCompletePartTotal_hermitian params family q
  have hGsq : G * G = G := switcherooCompletePartTotal_sq params family q
  have hGle : G ≤ 1 := switcherooCompletePartTotal_le_one params family q
  have hX : ∀ g, star (X g) = X g := switcherooAggregateFourthTermX_hermitian params family M q
  have hXsq : ∀ g, X g * X g ≤ X g := switcherooAggregateFourthTermX_sq_le params family M q
  have hrow : ∀ g, ∑ o : Outcome,
      G * (M q.2).outcome o * (family.meas q.1).outcome g * (M q.2).outcome o = G * X g :=
    fun g => by
      simp only [X, switcherooAggregateFourthTermX, Finset.mul_sum, mul_assoc]
  -- The sum, bounded in the local algebra.
  have hlocal : ∑ g, star (G * X g) * (G * X g) ≤ 1 :=
    calc ∑ g, star (G * X g) * (G * X g)
        = ∑ g, X g * G * X g := Finset.sum_congr rfl fun g _ => by
          rw [star_mul, hX, hG, mul_assoc, ← mul_assoc G G, hGsq, mul_assoc]
      _ ≤ ∑ g, X g * 1 * X g := Finset.sum_le_sum fun g _ =>
          IsSelfAdjoint.conjugate_le_conjugate hGle (hX g)
      _ ≤ ∑ g, X g := Finset.sum_le_sum fun g _ => by rw [mul_one]; exact hXsq g
      _ ≤ 1 := by
          rw [switcherooAggregateFourthTermX_sum params family M q]
          exact switcherooAggregateFourthTerm_middle_sum_le_one params family M q
  simp only [S.leftTensor_finset_sum, hrow, S.leftTensor_conjTranspose,
    S.leftTensor_mul_leftTensor]
  exact S.leftTensor_le_one hlocal

/-- Collapse the split-by-`g` raw expression back to the first positive
switcheroo term. -/
theorem switcherooAggregateFirstTerm_eq_split_by_g
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓) :
    avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
      ∑ go : MIPStarRE.LDT.Polynomial params × Outcome,
        S.ev
          (S.L
            ((M q.2).outcome go.2 *
              (family.meas q.1).outcome go.1 *
              (M q.2).outcome go.2))) =
      switcherooAggregateFirstTerm params S family M := by
  refine avgOver_congr _ _ _ fun q => ?_
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun o _ => ?_
  dsimp only
  rw [← S.ev_sum, S.leftTensor_finset_sum, ← Finset.sum_mul, ← Finset.mul_sum,
    (family.meas q.1).sum_eq_total]
  rfl

end MIPRE.LIDT.Co.Pasting

end

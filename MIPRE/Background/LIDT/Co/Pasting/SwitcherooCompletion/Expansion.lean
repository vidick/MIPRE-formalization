/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/
SwitcherooCompletion/Expansion.lean, to the symmetric model of `planning/c6b-plan.md`; not a
vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.SwitcherooContraction.ScalarTerms

@[expose] public section

/-!
# Section 12 pasting: switcheroo expansion

Expansion identities and the left-front contraction bound: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/SwitcherooCompletion/Expansion.lean` in the port of
`planning/c6b-plan.md` (milestone M11, section "Port conventions").

The vendored second bipartite state `ψbi : QuantumState (ι × ι)` is the symmetric model
`S : SymModel 𝔓 K`, in the vendored argument position; the slice family is an
`IdxPolyFamily params 𝔓` and the auxiliary family `M` an `IdxProjSubMeas (Fq params) Outcome 𝔓`.

The contraction witness `switcherooAggregateLeftFront_contraction` places operators by
`leftTensor (ι₂ := ι)` without a state in the vendored file; here it takes the model as an
explicit first argument (`switcherooAggregateLeftFront_contraction S params family M q`), as the
witnesses of `Co/Pasting/SwitcherooContraction/Split.lean` do. It computes the sum in the local
algebra `𝔓`, where it is `∑_g X_g` with `switcherooAggregateFourthTermX`, and pushes the bound
`switcherooAggregateFourthTerm_middle_sum_le_one` through `S.L` by `S.leftTensor_le_one`, in
place of the vendored `conjTranspose_opTensor` and `opTensor_mono_left` with the identity on the
second factor. The two pointwise normalizations unfold the ordered and reversed product families
by `change` and merge the placements by `S.leftTensor_conjTranspose` and
`S.leftTensor_mul_leftTensor`; the averaged expansion is `switcherooAggregate_qSDDOp_expand`
followed by `avgOver_add` and `avgOver_sub`, the four averages being the four terms by
definitional equality.

## Not ported

Nothing: every declaration of the vendored file is ported here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel Fq avgOver avgOver_congr avgOver_add avgOver_sub
  uniformDistribution)
open MIPStarRE.LDT.Pasting (SlicePairQuestion)
open MIPRE.LIDT.Co (SymModel IdxProjSubMeas IdxPolyFamily)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Contraction witness for the final `sqrt chi` left-front overlap step. -/
theorem switcherooAggregateLeftFront_contraction
    (S : SymModel 𝔓 K)
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓)
    (q : SlicePairQuestion params) :
    (∑ go : MIPStarRE.LDT.Polynomial params × Outcome,
        star (∑ _u : Unit,
            S.L (((family.meas q.1).outcome go.1) * (M q.2).outcome go.2)) *
          (∑ _u : Unit,
            S.L (((family.meas q.1).outcome go.1) * (M q.2).outcome go.2))) ≤ 1 := by
  set Gq : MIPStarRE.LDT.Polynomial params → 𝔓 := (family.meas q.1).outcome
  set Mo : Outcome → 𝔓 := (M q.2).outcome
  have hMo : ∀ o, star (Mo o) = Mo o := switcherooMeasuredOutcome_hermitian params M q
  have hGq : ∀ g, star (Gq g) = Gq g := switcherooSliceOutcome_hermitian params family q
  -- The sum, computed in the local algebra.
  have hlocal : ∑ go : MIPStarRE.LDT.Polynomial params × Outcome,
      star (Gq go.1 * Mo go.2) * (Gq go.1 * Mo go.2) =
        ∑ g, switcherooAggregateFourthTermX params family M q g := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun o _ => ?_
    rw [star_mul, hMo, hGq, mul_assoc, ← mul_assoc (Gq g), (family.meas q.1).proj g, mul_assoc]
  have hle : ∑ go : MIPStarRE.LDT.Polynomial params × Outcome,
      star (Gq go.1 * Mo go.2) * (Gq go.1 * Mo go.2) ≤ 1 := by
    rw [hlocal, switcherooAggregateFourthTermX_sum params family M q]
    exact switcherooAggregateFourthTerm_middle_sum_le_one params family M q
  simp only [Fintype.sum_unique, S.leftTensor_conjTranspose, S.leftTensor_mul_leftTensor]
  rw [S.leftTensor_finset_sum]
  exact S.leftTensor_le_one hle

/-- Normalize the pointwise self-product in the final switcheroo left-front
step to the split-by-`g` scalar. -/
theorem switcherooPointProductLeft_self_eq_firstSplit_point
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓)
    (q : SlicePairQuestion params)
    (go : MIPStarRE.LDT.Polynomial params × Outcome) :
    S.ev
      (star ((switcherooPointProductLeft S params family M q).outcome go) *
        (switcherooPointProductLeft S params family M q).outcome go) =
      S.ev
        (S.L
          ((M q.2).outcome go.2 *
            (family.meas q.1).outcome go.1 *
            (M q.2).outcome go.2)) := by
  set G : 𝔓 := (family.meas q.1).outcome go.1
  set Mo : 𝔓 := (M q.2).outcome go.2
  have hG : star G = G := switcherooSliceOutcome_hermitian params family q go.1
  have hMo : star Mo = Mo := switcherooMeasuredOutcome_hermitian params M q go.2
  change S.ev (star (S.L (G * Mo)) * S.L (G * Mo)) = _
  rw [S.leftTensor_conjTranspose, S.leftTensor_mul_leftTensor, star_mul, hG, hMo, mul_assoc,
    ← mul_assoc G, (family.meas q.1).proj go.1, ← mul_assoc]

/-- Normalize the pointwise mixed product in the final switcheroo left-front step
into the left-front scalar form. -/
theorem switcherooPointProductRightLeft_eq_leftFront_point
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓)
    (q : SlicePairQuestion params)
    (go : MIPStarRE.LDT.Polynomial params × Outcome) :
    S.ev
      (star ((switcherooPointProductRight S params family M q).outcome go) *
        (switcherooPointProductLeft S params family M q).outcome go) =
      S.ev
        (S.L
          (((family.meas q.1).outcome go.1) *
            (M q.2).outcome go.2 *
            (family.meas q.1).outcome go.1 *
            (M q.2).outcome go.2)) := by
  set G : 𝔓 := (family.meas q.1).outcome go.1
  set Mo : 𝔓 := (M q.2).outcome go.2
  have hG : star G = G := switcherooSliceOutcome_hermitian params family q go.1
  have hMo : star Mo = Mo := switcherooMeasuredOutcome_hermitian params M q go.2
  change S.ev (star (S.L (Mo * G)) * S.L (G * Mo)) = _
  rw [S.leftTensor_conjTranspose, S.leftTensor_mul_leftTensor, star_mul, hG, hMo]
  simp only [mul_assoc]

/-- Average the single-question four-term `qSDDOp` expansion over the
slice-pair distribution. -/
theorem switcherooAggregate_qSDDOp_expand_avg
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓) :
    avgOver (uniformDistribution (SlicePairQuestion params))
        (fun q => S.qSDDOp
          (switcherooAggregateLeft S params family M q)
          (switcherooAggregateRight S params family M q)) =
      switcherooAggregateFirstTerm params S family M +
        switcherooAggregateSecondTerm params S family M -
        switcherooAggregateThirdTerm params S family M -
        switcherooAggregateFourthTerm params S family M := by
  rw [avgOver_congr _ _ _ fun q => (switcherooAggregate_qSDDOp_expand params S family M q).trans
    (by rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]),
    avgOver_sub, avgOver_sub, avgOver_add]
  rfl

end MIPRE.LIDT.Co.Pasting

end

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/
SwitcherooCompletion/FourthTermChain.lean, to the symmetric model of `planning/c6b-plan.md`; not a
vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.SwitcherooContraction.ScalarTerms
public import MIPRE.Background.LIDT.Co.Pasting.SwitcherooCompletion.Expansion

@[expose] public section

/-!
# Section 12 pasting: fourth-term chain helpers

The steps of the fourth-term chain in `commutativitySwitcheroo`: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/SwitcherooCompletion/FourthTermChain.lean` in the port
of `planning/c6b-plan.md` (milestone M11, section "Port conventions").

The vendored second bipartite state `ψbi : QuantumState (ι × ι)` is the symmetric model
`S : SymModel 𝔓 K`, in the vendored argument position; the slice family is an
`IdxPolyFamily params 𝔓` and the auxiliary family `M` an `IdxProjSubMeas (Fq params) Outcome 𝔓`.
The vendored hypothesis `hnorm : ψbi.IsNormalized` of the three closeness steps is dropped,
normalization being a theorem of the model (section "Swap symmetry is a theorem"): callers pass
`params S family M zeta hselfG` and `params S family M chi hcomm`.

The pointwise mixed identity is the commutation `S.L_comm_R` of the two placements, in place of
the vendored pair of `opTensor` rewrites. The left-front comparison merges the placements by
`S.leftTensor_mul_leftTensor` and absorbs the complete-part total by
`Preliminaries.projSubMeas_outcome_mul_total_eq_outcome`. The last `√χ` step applies
`Preliminaries.closenessOfInnerProduct_right` to the state `S.toVecState`, passed explicitly, with
the contraction witness `switcherooAggregateLeftFront_contraction S params family M q` and the two
pointwise normalizations of `Co/Pasting/SwitcherooCompletion/Expansion.lean`.

## Not ported

Nothing: every declaration of the vendored file is ported here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel Fq avgOver avgOver_congr uniformDistribution
  uniformDistribution_weight_sum_le_one)
open MIPStarRE.LDT.Pasting (SlicePairQuestion)
open MIPRE.LIDT.Co (SymModel IdxProjSubMeas IdxPolyFamily)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Pointwise identity rewriting the mixed scalar expression into right/left tensor order. -/
theorem switcherooAggregateMixedScalar_point
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓)
    (q : SlicePairQuestion params) :
    (∑ g : MIPStarRE.LDT.Polynomial params, ∑ o : Outcome,
        S.ev
          (S.R ((family.meas q.1).outcome g) *
            S.L
              ((completePartSubMeas params family q.1).total *
                (M q.2).outcome o *
                (family.meas q.1).outcome g *
                (M q.2).outcome o))) =
      ∑ g : MIPStarRE.LDT.Polynomial params, ∑ o : Outcome,
        S.ev
          (S.L
            ((completePartSubMeas params family q.1).total *
              (M q.2).outcome o *
              (family.meas q.1).outcome g *
              (M q.2).outcome o) *
            S.R ((family.meas q.1).outcome g)) :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    congrArg S.ev (S.L_comm_R _ _).eq.symm

/-- The mixed scalar expression is within `√ζ` of the left-front scalar expression. -/
theorem switcherooAggregateMixedScalar_close_leftFrontScalar
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓)
    (zeta : ℝ)
    (hselfG : GCompleteSelfConsistencyStatement params S family zeta) :
    |switcherooAggregateMixedScalar params S family M -
        switcherooAggregateLeftFrontScalar params S family M| ≤ Real.sqrt zeta := by
  have hleft :
      avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
          ∑ g : MIPStarRE.LDT.Polynomial params, ∑ o : Outcome,
            S.ev
              (S.L ((family.meas q.1).outcome g) *
                S.L
                  ((completePartSubMeas params family q.1).total *
                    (M q.2).outcome o *
                    (family.meas q.1).outcome g *
                    (M q.2).outcome o))) =
        switcherooAggregateLeftFrontScalar params S family M := by
    refine avgOver_congr _ _ _ fun q => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun o _ => ?_
    rw [S.leftTensor_mul_leftTensor]
    simp only [← mul_assoc, completePartSubMeas_total,
      Preliminaries.projSubMeas_outcome_mul_total_eq_outcome]
  have hright :
      avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
          ∑ g : MIPStarRE.LDT.Polynomial params, ∑ o : Outcome,
            S.ev
              (S.R ((family.meas q.1).outcome g) *
                S.L
                  ((completePartSubMeas params family q.1).total *
                    (M q.2).outcome o *
                    (family.meas q.1).outcome g *
                    (M q.2).outcome o))) =
        switcherooAggregateMixedScalar params S family M :=
    avgOver_congr _ _ _ fun q => switcherooAggregateMixedScalar_point params S family M q
  rw [← hleft, ← hright, abs_sub_comm]
  exact switcherooAggregateFourthTerm_mixed_close_left_front_scalar params S family M zeta hselfG

/-- Sum-rewrite identity collapsing the product-type sum for the once-commuted scalar. -/
theorem switcherooAggregateOnceCommutedScalar_point
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓)
    (q : SlicePairQuestion params) :
    (∑ g : MIPStarRE.LDT.Polynomial params, ∑ o : Outcome,
        S.ev
          (S.L
            ((completePartSubMeas params family q.1).total *
              (M q.2).outcome o *
              (family.meas q.1).outcome g *
              (M q.2).outcome o *
              (family.meas q.1).outcome g))) =
      ∑ go : MIPStarRE.LDT.Polynomial params × Outcome,
        S.ev
          (S.L
            ((completePartSubMeas params family q.1).total *
              (M q.2).outcome go.2 *
              (family.meas q.1).outcome go.1 *
              (M q.2).outcome go.2 *
              (family.meas q.1).outcome go.1)) :=
  (Fintype.sum_prod_type' (f := fun g o =>
    S.ev
      (S.L
        ((completePartSubMeas params family q.1).total *
          (M q.2).outcome o *
          (family.meas q.1).outcome g *
          (M q.2).outcome o *
          (family.meas q.1).outcome g)))).symm

/-- The once-commuted scalar expression is within `√ζ` of the mixed scalar expression. -/
theorem switcherooAggregateOnceCommutedScalar_close_mixed
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓)
    (zeta : ℝ)
    (hselfG : GCompleteSelfConsistencyStatement params S family zeta) :
    |switcherooAggregateOnceCommutedScalar params S family M -
        switcherooAggregateMixedScalar params S family M| ≤ Real.sqrt zeta := by
  have h :=
    switcherooAggregateFourthTerm_once_commuted_close_mixed params S family M zeta hselfG
  rw [avgOver_congr _ _ _ fun q =>
    switcherooAggregateOnceCommutedScalar_point params S family M q] at h
  exact h

-- The last `χ`-step needs only pointwise normalization for the `G_g M_o`
-- factors inside `closenessOfInnerProduct_right`; the adjoint rewrites are
-- the two pointwise lemmas of `Co/Pasting/SwitcherooCompletion/Expansion.lean`.
/-- The final `sqrt chi` comparison in the fourth-term chain: compare the left-front
scalar expression with the split-by-`g` scalar that later collapses to the first
positive switcheroo term. -/
theorem switcherooAggregateLeftFrontScalar_close_firstSplitScalar
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓)
    (chi : ℝ)
    (hcomm : S.SDDOpRel
      (uniformDistribution (SlicePairQuestion params))
      (switcherooPointProductLeft S params family M)
      (switcherooPointProductRight S params family M)
      chi) :
    |switcherooAggregateLeftFrontScalar params S family M -
        switcherooAggregateFirstSplitScalar params S family M| ≤
      Real.sqrt chi := by
  let A : SlicePairQuestion params → MIPStarRE.LDT.Polynomial params × Outcome → K →L[ℂ] K :=
    fun q go => star ((switcherooPointProductLeft S params family M q).outcome go)
  let B : SlicePairQuestion params → MIPStarRE.LDT.Polynomial params × Outcome → K →L[ℂ] K :=
    fun q go => star ((switcherooPointProductRight S params family M q).outcome go)
  let C : SlicePairQuestion params → MIPStarRE.LDT.Polynomial params × Outcome → Unit →
      K →L[ℂ] K :=
    fun q go _ => (switcherooPointProductLeft S params family M q).outcome go
  have hAB : avgOver (uniformDistribution (SlicePairQuestion params))
      (fun q => S.toVecState.qSDDCore (fun go => star (A q go)) (fun go => star (B q go))) ≤
        chi := by
    simpa only [A, B, star_star] using
      switcherooPointProductCommutation_coreBound params S family M chi hcomm
  have hC : ∀ q,
      (∑ go : MIPStarRE.LDT.Polynomial params × Outcome,
          star (∑ u : Unit, C q go u) * (∑ u : Unit, C q go u)) ≤ 1 := fun q =>
    switcherooAggregateLeftFront_contraction S params family M q
  have hleft :
      avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
          ∑ go : MIPStarRE.LDT.Polynomial params × Outcome,
            ∑ u : Unit, S.ev (A q go * C q go u)) =
        switcherooAggregateFirstSplitScalar params S family M := by
    refine avgOver_congr _ _ _ fun q => Finset.sum_congr rfl fun go _ => ?_
    rw [Fintype.sum_unique (ι := Unit)]
    exact (switcherooPointProductLeft_self_eq_firstSplit_point params S family M q go).trans
      (congrArg (fun X => S.ev (S.L X)) (mul_assoc _ _ _))
  have hright :
      avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
          ∑ go : MIPStarRE.LDT.Polynomial params × Outcome,
            ∑ u : Unit, S.ev (B q go * C q go u)) =
        switcherooAggregateLeftFrontScalar params S family M := by
    refine avgOver_congr _ _ _ fun q => Finset.sum_congr rfl fun go _ => ?_
    rw [Fintype.sum_unique (ι := Unit)]
    exact switcherooPointProductRightLeft_eq_leftFront_point params S family M q go
  rw [← hleft, ← hright, abs_sub_comm]
  exact Preliminaries.closenessOfInnerProduct_right S.toVecState _
    (uniformDistribution_weight_sum_le_one (SlicePairQuestion params)) A B C chi hAB hC

end MIPRE.LIDT.Co.Pasting

end

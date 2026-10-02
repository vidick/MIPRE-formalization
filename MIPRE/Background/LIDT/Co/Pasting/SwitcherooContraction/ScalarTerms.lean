/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/
SwitcherooContraction/ScalarTerms.lean, to the symmetric model of `planning/c6b-plan.md`; not a
vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.SwitcherooContraction.Commuted

@[expose] public section

/-!
# Section 12 pasting: switcheroo scalar expressions

Named scalar expressions for the switcheroo contraction chain: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/SwitcherooContraction/ScalarTerms.lean` in the port
of `planning/c6b-plan.md` (milestone M11, section "Port conventions").

The vendored second bipartite state `ψbi : QuantumState (ι × ι)` is the symmetric model
`S : SymModel 𝔓 K`, in the vendored argument position; the slice family is an
`IdxPolyFamily params 𝔓` and the auxiliary family `M` an `IdxProjSubMeas (Fq params) Outcome 𝔓`.
The vendored hypothesis `hnorm : ψbi.IsNormalized` of
`switcherooAggregateFourthTerm_close_once_commuted_scalar` and
`switcherooAggregateFourthTerm_mixed_close_left_front_scalar` is dropped, normalization being a
theorem of the model (section "Swap symmetry is a theorem"): callers pass
`params S family M chi hcomm` and `params S family M zeta hselfG`.

The first restatement is `switcherooAggregateFourthTerm_split_close_once_commuted` by
definitional unfolding. The second applies `Preliminaries.closenessOfInnerProduct_right` to the
state `S.toVecState`, passed explicitly; its adjoint form of the self-consistency bound comes
from `switcherooCompletePartSelfConsistency_pairBound` by `S.leftTensor_conjTranspose`,
`S.rightTensor_conjTranspose` and the self-adjointness of the slice outcomes, in place of the
vendored `Matrix.PosSemidef` argument.

## Not ported

Nothing: every declaration of the vendored file is ported here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel Fq Distribution avgOver avgOver_congr
  uniformDistribution uniformDistribution_weight_sum_le_one)
open MIPStarRE.LDT.Pasting (SlicePairQuestion)
open MIPRE.LIDT.Co (SymModel IdxProjSubMeas IdxPolyFamily)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The post-second-`√ζ` left-front expression in the paper's cross-term chain. -/
noncomputable def switcherooAggregateLeftFrontScalar
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓) : ℝ :=
  avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
    ∑ go : MIPStarRE.LDT.Polynomial params × Outcome,
      S.ev
        (S.L
          (((family.meas q.1).outcome go.1) *
            (M q.2).outcome go.2 *
            (family.meas q.1).outcome go.1 *
            (M q.2).outcome go.2)))

/-- The split-by-`g` expression that collapses back to the first positive term. -/
noncomputable def switcherooAggregateFirstSplitScalar
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓) : ℝ :=
  avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
    ∑ go : MIPStarRE.LDT.Polynomial params × Outcome,
      S.ev
        (S.L
          ((M q.2).outcome go.2 *
            ((family.meas q.1).outcome go.1 *
              (M q.2).outcome go.2))))

/-- The post-first-`√χ` scalar expression in the fourth-term chain. -/
noncomputable def switcherooAggregateOnceCommutedScalar
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓) : ℝ :=
  avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
    ∑ go : MIPStarRE.LDT.Polynomial params × Outcome,
      S.ev
        (S.L
          ((completePartSubMeas params family q.1).total *
            (M q.2).outcome go.2 *
            (family.meas q.1).outcome go.1 *
            (M q.2).outcome go.2 *
            (family.meas q.1).outcome go.1)))

/-- Restate the first `sqrt chi` step using the named scalar expression. -/
theorem switcherooAggregateFourthTerm_close_once_commuted_scalar
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
    |switcherooAggregateFourthTerm params S family M -
        switcherooAggregateOnceCommutedScalar params S family M| ≤
      Real.sqrt chi :=
  switcherooAggregateFourthTerm_split_close_once_commuted params S family M chi hcomm

/-- The post-first-`√ζ` mixed tensor scalar expression in the fourth-term chain. -/
noncomputable def switcherooAggregateMixedScalar
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓) : ℝ :=
  avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
    ∑ g : MIPStarRE.LDT.Polynomial params, ∑ o : Outcome,
      S.ev
        (S.L
          ((completePartSubMeas params family q.1).total *
            (M q.2).outcome o *
            (family.meas q.1).outcome g *
            (M q.2).outcome o) *
          S.R ((family.meas q.1).outcome g)))

/-- Restate the second `sqrt zeta` step using the named left-front scalar
expression. -/
theorem switcherooAggregateFourthTerm_mixed_close_left_front_scalar
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓)
    (zeta : ℝ)
    (hselfG : GCompleteSelfConsistencyStatement params S family zeta) :
    |avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
        ∑ g : MIPStarRE.LDT.Polynomial params, ∑ o : Outcome,
          S.ev
            (S.L ((family.meas q.1).outcome g) *
              S.L
                ((completePartSubMeas params family q.1).total *
                  (M q.2).outcome o *
                  (family.meas q.1).outcome g *
                  (M q.2).outcome o))) -
      avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
        ∑ g : MIPStarRE.LDT.Polynomial params, ∑ o : Outcome,
          S.ev
            (S.R ((family.meas q.1).outcome g) *
              S.L
                ((completePartSubMeas params family q.1).total *
                  (M q.2).outcome o *
                  (family.meas q.1).outcome g *
                  (M q.2).outcome o)))| ≤
      Real.sqrt zeta := by
  let 𝒟q : Distribution (SlicePairQuestion params) :=
    uniformDistribution (SlicePairQuestion params)
  let A : SlicePairQuestion params → MIPStarRE.LDT.Polynomial params → K →L[ℂ] K :=
    fun q g => S.L ((family.meas q.1).outcome g)
  let B : SlicePairQuestion params → MIPStarRE.LDT.Polynomial params → K →L[ℂ] K :=
    fun q g => S.R ((family.meas q.1).outcome g)
  let C : SlicePairQuestion params → MIPStarRE.LDT.Polynomial params → Outcome → K →L[ℂ] K :=
    fun q g o =>
      S.L
        ((completePartSubMeas params family q.1).total *
          (M q.2).outcome o *
          (family.meas q.1).outcome g *
          (M q.2).outcome o)
  have h𝒟q : ∑ q ∈ 𝒟q.support, 𝒟q.weight q ≤ 1 :=
    uniformDistribution_weight_sum_le_one (SlicePairQuestion params)
  have hAB : avgOver 𝒟q
      (fun q => S.toVecState.qSDDCore (fun g => star (A q g)) (fun g => star (B q g))) ≤
        zeta := by
    refine le_of_eq_of_le (avgOver_congr _ _ _ fun q => ?_)
      (switcherooCompletePartSelfConsistency_pairBound params S family zeta hselfG)
    simp only [A, B, S.leftTensor_conjTranspose, S.rightTensor_conjTranspose,
      switcherooSliceOutcome_hermitian params family q]
  have hC : ∀ q,
      (∑ g : MIPStarRE.LDT.Polynomial params,
          star (∑ o : Outcome, C q g o) * (∑ o : Outcome, C q g o)) ≤ 1 := fun q =>
    switcherooAggregateFourthTerm_once_commuted_contraction_right S params family M q
  exact Preliminaries.closenessOfInnerProduct_right S.toVecState 𝒟q h𝒟q A B C zeta hAB hC

end MIPRE.LIDT.Co.Pasting

end

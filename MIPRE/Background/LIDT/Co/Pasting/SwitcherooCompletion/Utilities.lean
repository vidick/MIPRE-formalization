/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/
SwitcherooCompletion/Utilities.lean, to the symmetric model of `planning/c6b-plan.md`; not a
vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.SwitcherooCompletion.SecondTerm

@[expose] public section

/-!
# Section 12 pasting: switcheroo completion utilities

Post-theorem convenience lemmas: question-swapping, complete-part reinterpretations, and
self-consistency inheritance. This is the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/SwitcherooCompletion/Utilities.lean` in the port of
`planning/c6b-plan.md` (milestone M11, section "Port conventions").

`sddOpRel_swap_questions` uses only the state, on joint operator families, so its vendored
`ψbi` is a vector state `V : VecState K` in the vendored argument position (callers pass `S` or
`strategy.state`); `pointWithCompletePart_as_switcheroo_input` places families, so its `ψbi` is
the symmetric model `S : SymModel 𝔓 K`; `completePartProjFamily_selfConsistency` takes a
`SymStrat params.next 𝔓 K`. The slice family is an `IdxPolyFamily params 𝔓`.

`sddOpRel_swap_questions` is `avgOver_uniform_equiv` along `Equiv.prodComm`, whose inverse is
`Prod.swap` by definition. `pointWithCompletePart_as_switcheroo_input` splits the
`Polynomial params × Unit` sum by `Fintype.sum_prod_type` and `Fintype.sum_unique`, and matches
the outcomes by `change` (the ordered and reversed product families unfold on a pair) and
`completePartSubMeas_outcome_unit`, in place of the vendored `simp` over the family definitions.

## Not ported

Nothing: every declaration of the vendored file is ported here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel Fq avgOver_congr avgOver_uniform_equiv
  uniformDistribution)
open MIPStarRE.LDT.Pasting (SliceQuestion SlicePairQuestion)
open MIPRE.LIDT.Co (SymModel VecState SymStrat IdxOpFamily IdxPolyFamily)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Reindexing a uniform slice-pair average along `Prod.swap` preserves `SDDOpRel`. -/
theorem sddOpRel_swap_questions
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (V : VecState K)
    (A B : IdxOpFamily (SlicePairQuestion params) Outcome (K →L[ℂ] K))
    (δ : ℝ) :
    V.SDDOpRel
      (uniformDistribution (SlicePairQuestion params))
      A B δ →
      V.SDDOpRel
        (uniformDistribution (SlicePairQuestion params))
        (fun q => A (q.2, q.1))
        (fun q => B (q.2, q.1))
        δ := fun ⟨hAB⟩ =>
  ⟨((avgOver_uniform_equiv (α := SlicePairQuestion params) (β := SlicePairQuestion params)
    (Equiv.prodComm (Fq params) (Fq params)) (fun q => V.qSDDOp (A q) (B q))).symm).trans_le hAB⟩

/-- Reinterpret the point-with-complete-part commutation bound as a relation on the
`Polynomial × Unit` outcome type expected by `commutativitySwitcheroo`. -/
theorem pointWithCompletePart_as_switcheroo_input
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (gamma : ℝ)
    (hcomm : S.SDDOpRel
      (uniformDistribution (SlicePairQuestion params))
      (completePartPointProductLeft S params family)
      (completePartPointProductRight S params family)
      gamma) :
    S.SDDOpRel
      (uniformDistribution (SlicePairQuestion params))
      (switcherooPointProductLeft S params family (completePartProjFamily params family))
      (switcherooPointProductRight S params family (completePartProjFamily params family))
      gamma := by
  refine ⟨le_of_eq_of_le (avgOver_congr _ _ _ fun q => ?_) hcomm.squaredDistanceBound⟩
  change ∑ gu : MIPStarRE.LDT.Polynomial params × Unit,
      S.ev (star (S.L ((family.meas q.1).outcome gu.1 *
          (completePartSubMeas params family q.2).outcome gu.2) -
        S.L ((completePartSubMeas params family q.2).outcome gu.2 *
          (family.meas q.1).outcome gu.1)) *
        (S.L ((family.meas q.1).outcome gu.1 *
          (completePartSubMeas params family q.2).outcome gu.2) -
        S.L ((completePartSubMeas params family q.2).outcome gu.2 *
          (family.meas q.1).outcome gu.1))) =
    ∑ g : MIPStarRE.LDT.Polynomial params,
      S.ev (star (S.L ((family.meas q.1).outcome g *
          (completePartSubMeas params family q.2).total) -
        S.L ((completePartSubMeas params family q.2).total * (family.meas q.1).outcome g)) *
        (S.L ((family.meas q.1).outcome g * (completePartSubMeas params family q.2).total) -
        S.L ((completePartSubMeas params family q.2).total * (family.meas q.1).outcome g)))
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Fintype.sum_unique (ι := Unit), completePartSubMeas_outcome_unit]

/-- The complete-part family inherits self-consistency from the slice family by
pointwise comparison of the `qSDD` defect. -/
theorem completePartProjFamily_selfConsistency
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (zeta : ℝ)
    (hself : GCompleteSelfConsistencyStatement params strategy.state family zeta) :
    strategy.state.SDDRel
      (uniformDistribution (SliceQuestion params))
      (switcherooSelfConsistencyLeft strategy.state params (completePartProjFamily params family))
      (switcherooSelfConsistencyRight strategy.state params (completePartProjFamily params family))
      zeta :=
  completePartProjFamily_selfConsistency_generic params strategy.state family zeta hself

end MIPRE.LIDT.Co.Pasting

end

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
Commutativity/EvaluatedSliceCommutation/Averages.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Commutativity.EvaluatedSliceBounds.PhaseOneThree

@[expose] public section

/-!
# Section 11 commutativity: evaluated-slice averaged expansion

Averaged evaluated-slice expansion of `qSDDOp` into the four projector terms
`BAB + ABA - BABA - ABAB`, used to reduce the commutation to per-projector estimates: the
counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/EvaluatedSliceCommutation/Averages.lean` in
the port of `planning/c6b-plan.md` (milestone M7, section "Port conventions").

The vendored proof of the expansion works with the Kronecker placements `leftTensor (ι₂ := ι) A`
and proves their self-adjointness through `Matrix.PosSemidef`; here the commutator identity
`(AB − BA)^*(AB − BA) = BAB + ABA − BABA − ABAB` is proved in the local algebra `𝔓` and placed
once by `strategy.state.L`. The two swap identities are one reindexing helper applied twice.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Commutativity

open MIPStarRE.LDT (Parameters FieldModel Fq avgOver avgOver_congr avgOver_add avgOver_sub
  avgOver_uniform_equiv uniformDistribution)
open MIPStarRE.LDT.Commutativity (EvaluatedSliceQuestion EvaluatedSliceOutcome)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Expand the averaged evaluated-slice `qSDDOp` into the four projector terms
`BAB + ABA - BABA - ABAB`. -/
lemma evaluatedSliceCommutation_qSDDOp_avg_expand
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓) :
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q =>
          strategy.state.qSDDOp
            (evaluatedSliceProductLeft params strategy family q)
            (evaluatedSliceProductRight params strategy family q)) =
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q =>
          ∑ ab : EvaluatedSliceOutcome params,
            (evaluatedSliceBABTerm params strategy family q ab +
              evaluatedSliceABATerm params strategy family q ab -
              evaluatedSliceBABATerm params strategy family q ab -
              evaluatedSliceABABTerm params strategy family q ab)) := by
  refine avgOver_congr _ _ _ fun q => Finset.sum_congr rfl fun ab _ => ?_
  let S := strategy.state
  let A := (evaluatedPointFamily params family q.1).outcome ab.1
  let B := (evaluatedPointFamily params family q.2).outcome ab.2
  have hA : star A = A := (evaluatedPointFamily params family q.1).outcome_hermitian ab.1
  have hB : star B = B := (evaluatedPointFamily params family q.2).outcome_hermitian ab.2
  have hA2 : A * A = A := evaluatedPointFamily_outcome_proj params family q.1 ab.1
  have hB2 : B * B = B := evaluatedPointFamily_outcome_proj params family q.2 ab.2
  have hmain : star (A * B - B * A) * (A * B - B * A) =
      B * A * B + A * B * A - B * A * B * A - A * B * A * B := by
    rw [star_sub, star_mul, star_mul, hA, hB]
    calc (B * A - A * B) * (A * B - B * A)
        = B * (A * A) * B - B * A * B * A - A * B * A * B + A * (B * B) * A := by noncomm_ring
      _ = _ := by rw [hA2, hB2]; abel
  change S.ev (star (S.L (A * B) - S.L (B * A)) * (S.L (A * B) - S.L (B * A))) =
    S.ev (S.L (B * A * B)) + S.ev (S.L (A * B * A)) - S.ev (S.L (B * A * B * A)) -
      S.ev (S.L (A * B * A * B))
  rw [S.leftTensor_sub, S.leftTensor_conjTranspose, S.leftTensor_mul_leftTensor, hmain,
    map_sub S.L, map_sub S.L, map_add S.L, S.ev_sub, S.ev_sub, S.ev_add]

/-- Reindexing by the swap of the question and of the outcome: if `f q (a, b)` is
`g (q.2, q.1) (b, a)`, then the averaged sums of `f` and `g` agree. -/
private theorem avg_sum_eq_of_swap (params : Parameters) [FieldModel params.q]
    (f g : EvaluatedSliceQuestion params → EvaluatedSliceOutcome params → ℝ)
    (h : ∀ q ab, f q ab = g q.swap ab.swap) :
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => ∑ ab : EvaluatedSliceOutcome params, f q ab) =
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => ∑ ab : EvaluatedSliceOutcome params, g q ab) := by
  refine ((avgOver_congr _ _ _ fun q => ?_).trans
    (avgOver_uniform_equiv (Equiv.prodComm _ _)
      (fun q => ∑ ab : EvaluatedSliceOutcome params, g q ab)).symm)
  simp_rw [h]
  exact Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun _ => rfl

/-- Swapping the evaluated question and outcome identifies the averaged
`BAB`/`ABA` terms and the averaged `BABA`/`ABAB` terms. -/
lemma evaluatedSliceCommutation_avg_swap_terms
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓) :
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => ∑ ab : EvaluatedSliceOutcome params,
          evaluatedSliceBABTerm params strategy family q ab) =
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => ∑ ab : EvaluatedSliceOutcome params,
          evaluatedSliceABATerm params strategy family q ab) ∧
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => ∑ ab : EvaluatedSliceOutcome params,
          evaluatedSliceBABATerm params strategy family q ab) =
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => ∑ ab : EvaluatedSliceOutcome params,
          evaluatedSliceABABTerm params strategy family q ab) :=
  ⟨avg_sum_eq_of_swap params _ _ fun _ _ => rfl, avg_sum_eq_of_swap params _ _ fun _ _ => rfl⟩

/-- Averaged evaluated-slice `qSDDOp` collapses to the paper's two scalar terms
after swapping the sampled questions and outcomes. -/
lemma evaluatedSliceCommutation_qSDDOp_avg_eq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓) :
    strategy.state.sddErrorOp
      (uniformDistribution (EvaluatedSliceQuestion params))
      (evaluatedSliceProductLeft params strategy family)
      (evaluatedSliceProductRight params strategy family) =
      2 *
        (avgOver (uniformDistribution (EvaluatedSliceQuestion params))
            (fun q => ∑ ab : EvaluatedSliceOutcome params,
              evaluatedSliceABATerm params strategy family q ab) -
          avgOver (uniformDistribution (EvaluatedSliceQuestion params))
            (fun q => ∑ ab : EvaluatedSliceOutcome params,
              evaluatedSliceABABTerm params strategy family q ab)) := by
  obtain ⟨hBAB, hBABA⟩ := evaluatedSliceCommutation_avg_swap_terms params strategy family
  unfold VecState.sddErrorOp
  rw [evaluatedSliceCommutation_qSDDOp_avg_expand]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [avgOver_sub, avgOver_sub, avgOver_add, hBAB, hBABA]
  ring

end MIPRE.LIDT.Co.Commutativity

end

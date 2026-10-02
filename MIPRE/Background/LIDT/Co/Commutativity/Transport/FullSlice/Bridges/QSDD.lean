/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
Commutativity/Transport/FullSlice/Bridges/QSDD.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Commutativity.Transport.FullSlice.Averages

@[expose] public section

/-!
# Full-slice `qSDDOp` averaging identity

Averaging identities expanding the full-slice `qSDDOp` and proving the scalar commutation
identity `fullSliceCommutation_qSDDOp_avg_eq`: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/Transport/FullSlice/Bridges/QSDD.lean` in the
port of `planning/c6b-plan.md` (milestone M7, section "Port conventions"). This scalar expansion
is used by the full-slice transport theorems that compare the quartic scalar averages appearing
in `commutativity-G.tex`.

The vendored proof of the expansion works with the Kronecker placements `leftTensor (ι₂ := ι) A`
and proves their self-adjointness through `Matrix.PosSemidef`; here the commutator identity
`(AB − BA)^*(AB − BA) = BAB + ABA − BABA − ABAB` is proved in the local algebra `𝔓` and placed
once by `strategy.state.L`, as in `EvaluatedSliceCommutation/Averages.lean`.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Commutativity

open MIPStarRE.LDT (Parameters FieldModel avgOver avgOver_congr avgOver_add avgOver_sub
  uniformDistribution)
open MIPStarRE.LDT.Commutativity (EvaluatedSliceQuestion FullSliceQuestion FullSliceOutcome
  fullSliceQuestionOfEvaluatedSlice)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Expand the averaged full-slice `qSDDOp` into the four projector terms
`BAB + ABA - BABA - ABAB`. -/
lemma fullSliceCommutation_qSDDOp_avg_expand_full
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓) :
    avgOver (uniformDistribution (FullSliceQuestion params))
        (fun q =>
          strategy.state.qSDDOp
            (fullSliceProductLeft params strategy family q)
            (fullSliceProductRight params strategy family q)) =
      avgOver (uniformDistribution (FullSliceQuestion params))
        (fun q =>
          ∑ gh : FullSliceOutcome params,
            (fullSliceBABTerm params strategy family q gh +
              fullSliceABATerm params strategy family q gh -
              fullSliceBABATerm params strategy family q gh -
              fullSliceABABTerm params strategy family q gh)) := by
  refine avgOver_congr _ _ _ fun q => Finset.sum_congr rfl fun gh _ => ?_
  let S := strategy.state
  let A := (family.meas q.1).toSubMeas.outcome gh.1
  let B := (family.meas q.2).toSubMeas.outcome gh.2
  have hA : star A = A := (family.meas q.1).toSubMeas.outcome_hermitian gh.1
  have hB : star B = B := (family.meas q.2).toSubMeas.outcome_hermitian gh.2
  have hA2 : A * A = A := (family.meas q.1).proj gh.1
  have hB2 : B * B = B := (family.meas q.2).proj gh.2
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

/-- Paper `eq:gcomterms` (`commutativity-G.tex` lines 286-290).

Full-slice analog of `evaluatedSliceCommutation_qSDDOp_avg_eq`: the pulled-back `sddErrorOp`
on the full-slice product equals `2·(ABAAvg − ABABAvg)` after using projectivity and the
`(x,g) ↔ (y,h)` symmetry to collapse `BAB + ABA − BABA − ABAB` into the two surviving scalar
quartic terms. -/
lemma fullSliceCommutation_qSDDOp_avg_eq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓) :
    strategy.state.sddErrorOp
        (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => fullSliceProductLeft params strategy family
          (fullSliceQuestionOfEvaluatedSlice params q))
        (fun q => fullSliceProductRight params strategy family
          (fullSliceQuestionOfEvaluatedSlice params q)) =
      2 * (fullSliceABAAvg params strategy family -
        fullSliceABABAvg params strategy family) := by
  obtain ⟨hBAB, hBABA⟩ := fullSliceCommutation_avg_swap_terms params strategy family
  have hABA : fullSliceABAAvg params strategy family =
      avgOver (uniformDistribution (FullSliceQuestion params))
        (fun q => ∑ gh : FullSliceOutcome params,
          fullSliceABATerm params strategy family q gh) := rfl
  have hABAB : fullSliceABABAvg params strategy family =
      avgOver (uniformDistribution (FullSliceQuestion params))
        (fun q => ∑ gh : FullSliceOutcome params,
          fullSliceABABTerm params strategy family q gh) := rfl
  rw [sddErrorOp_pullback_fullSliceQuestion_eq params strategy.state.toVecState]
  unfold VecState.sddErrorOp
  rw [fullSliceCommutation_qSDDOp_avg_expand_full]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [avgOver_sub, avgOver_sub, avgOver_add, hBAB, hBABA, hABA, hABAB]
  ring

end MIPRE.LIDT.Co.Commutativity

end

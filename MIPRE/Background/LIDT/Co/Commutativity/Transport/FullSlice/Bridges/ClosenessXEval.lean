/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
Commutativity/Transport/FullSlice/Bridges/ClosenessXEval.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Commutativity.Transport.FullSlice.Averages
public import MIPRE.Background.LIDT.Co.Commutativity.Transport.FullSlice.Machinery.Marginalization.Y
public import MIPRE.Background.LIDT.Co.Commutativity.Transport.FullSlice.Machinery.Normalization

@[expose] public section

/-!
# X-evaluated full-slice closeness comparison

The single `closenessOfIP` comparison for the x-evaluated/full-y scalar-to-tensor transition:
the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/Transport/FullSlice/Bridges/ClosenessXEval.lean`
in the port of `planning/c6b-plan.md` (milestone M7, section "Port conventions").

The comparison is stated on the symmetric model of a strategy
`strategy : SymStrat params.next 𝔓 K`, the vendored `leftTensor (ι₂ := ι)` and
`rightTensor (ι₁ := ι)` being `strategy.state.L` and `strategy.state.R`. The vendored hypothesis
`hnorm : strategy.state.IsNormalized` is a theorem of the model and is dropped, as the ported
`Preliminaries.closenessOfIP` no longer takes it.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Commutativity

open MIPStarRE.LDT (Parameters FieldModel Point Fq avgOver avgOver_congr avgOver_uniform_snd
  uniformDistribution uniformDistribution_weight_sum_le_one)
open MIPStarRE.LDT.Commutativity (FullSliceQuestion)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- X-evaluated/full-y scalar-to-tensor comparison for paper line 360 (the vendored hypothesis
`hnorm : strategy.state.IsNormalized` is a theorem of the model).

After the x-side Schwartz--Zippel step, the first family has already been
postprocessed at `u`, while the y-family is still full-polynomial.  This lemma
proves the second `closenessOfIP` move in `commutativity-G.tex` lines 356--360:
move the trailing `G^y_h` in
`G^x_[g(u)=a] G^y_h G^x_[g(u)=a] G^y_h ⊗ I` to the right register, yielding
`G^x_[g(u)=a] G^y_h G^x_[g(u)=a] ⊗ G^y_h`.

The preceding line-359 comparison from the `BAB ⊗ A` tensor endpoint to this
scalar endpoint remains separate because it follows a different `closenessOfIP`
leg. -/
lemma xEvaluatedFullSliceABABAvg_to_xEvaluatedFullSliceABABtensorAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (zeta : ℝ)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    |xEvaluatedFullSliceABABAvg params strategy family -
        xEvaluatedFullSliceABABtensorAvg params strategy family| ≤ Real.sqrt zeta := by
  let 𝒟 := uniformDistribution (Point params × FullSliceQuestion params)
  let X : Point params × FullSliceQuestion params → SubMeas (Fq params) 𝔓 :=
    fun ux => evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)
  let A : Point params × FullSliceQuestion params → MIPStarRE.LDT.Polynomial params →
      K →L[ℂ] K :=
    fun ux h => strategy.state.L ((family.meas ux.2.2).toSubMeas.outcome h)
  let B : Point params × FullSliceQuestion params → MIPStarRE.LDT.Polynomial params →
      K →L[ℂ] K :=
    fun ux h => strategy.state.R ((family.meas ux.2.2).toSubMeas.outcome h)
  let C : Point params × FullSliceQuestion params → MIPStarRE.LDT.Polynomial params →
      Fq params → K →L[ℂ] K :=
    fun ux h a =>
      strategy.state.L
        ((X ux).outcome a * (family.meas ux.2.2).toSubMeas.outcome h * (X ux).outcome a)
  have hAB : avgOver 𝒟 (fun ux => strategy.state.qSDDCore (A ux) (B ux)) ≤ zeta :=
    (avgOver_uniform_snd (α := Point params) fun xy : FullSliceQuestion params =>
      strategy.state.qSDDCore
        (fun h : MIPStarRE.LDT.Polynomial params =>
          strategy.state.L ((family.meas xy.2).toSubMeas.outcome h))
        (fun h : MIPStarRE.LDT.Polynomial params =>
          strategy.state.R ((family.meas xy.2).toSubMeas.outcome h))).trans_le
      (fullSlice_selfConsistency_snd_bound params strategy family zeta hself)
  have hclose := Preliminaries.closenessOfIP strategy.state.toVecState 𝒟
    (uniformDistribution_weight_sum_le_one _) A B C zeta hAB
    fun ux => leftTensor_normalizationCondition_sandwich_bound strategy.state
      (family.meas ux.2.2).toSubMeas (evaluateAtProjSubMeas params ux.1 (family.meas ux.2.1))
  have hScalar :
      avgOver 𝒟 (fun ux => ∑ h : MIPStarRE.LDT.Polynomial params, ∑ a : Fq params,
          strategy.state.ev (C ux h a * A ux h)) =
        xEvaluatedFullSliceABABAvg params strategy family :=
    avgOver_congr 𝒟 _ _ fun ux => Finset.sum_comm.trans <|
      (Fintype.sum_congr _ _ fun a => Fintype.sum_congr _ _ fun h =>
        congrArg strategy.state.ev (strategy.state.leftTensor_mul_leftTensor _ _)).trans
        (Fintype.sum_prod_type' _).symm
  have hTensor :
      avgOver 𝒟 (fun ux => ∑ h : MIPStarRE.LDT.Polynomial params, ∑ a : Fq params,
          strategy.state.ev (C ux h a * B ux h)) =
        xEvaluatedFullSliceABABtensorAvg params strategy family :=
    avgOver_congr 𝒟 _ _ fun ux => Finset.sum_comm.trans (Fintype.sum_prod_type' _).symm
  rw [← hScalar, ← hTensor]
  exact hclose

end MIPRE.LIDT.Co.Commutativity

end

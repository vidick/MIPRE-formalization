/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
Commutativity/Transport/FullSlice/Bridges/ClosenessCore.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Commutativity.Transport.FullSlice.Averages
public import MIPRE.Background.LIDT.Co.Commutativity.Transport.FullSlice.Machinery.Marginalization.Y
public import MIPRE.Background.LIDT.Co.Commutativity.Transport.FullSlice.Machinery.Normalization

@[expose] public section

/-!
# Core full-slice closeness-of-inner-product comparison

The standalone `closenessOfIP` scalar↔tensor comparison lemma, which moves a trailing
measurement outcome between the scalar quartic and a manifestly positive tensor register: the
counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/Transport/FullSlice/Bridges/ClosenessCore.lean`
in the port of `planning/c6b-plan.md` (milestone M7, section "Port conventions").

The comparison is stated on the symmetric model of a strategy
`strategy : SymStrat params.next 𝔓 K`, the vendored `leftTensor (ι₂ := ι)` and
`rightTensor (ι₁ := ι)` being `strategy.state.L` and `strategy.state.R`. The vendored hypothesis
`hnorm : strategy.state.IsNormalized` is a theorem of the model and is dropped, as the ported
`Preliminaries.closenessOfIP` no longer takes it. The tensor-form lemmas are internal to the
scalar/tensor comparison recorded upstream in `docs/decisions/713-scalar-tensor-decision.md`;
downstream code should use the scalar API of `Closeness.lean` and `ClosenessXEval.lean`.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Commutativity

open MIPStarRE.LDT (Parameters FieldModel avgOver avgOver_congr uniformDistribution
  uniformDistribution_weight_sum_le_one)
open MIPStarRE.LDT.Commutativity (FullSliceQuestion FullSliceOutcome)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Scalar-to-tensor comparison for paper `eq:gcom4`
(`commutativity-G.tex` lines 332-337); the vendored hypothesis
`hnorm : strategy.state.IsNormalized` is a theorem of the model.

One `closenessOfIP` application moves the trailing `G^x_g` in the scalar quartic
`G^y_h G^x_g G^y_h G^x_g ⊗ I` to the right register, producing the manifestly
PSD tensor form `G^y_h G^x_g G^y_h ⊗ G^x_g`.  The scalar side is stated as
`fullSliceABABAvg`; the proof first uses the `(x,g) ↔ (y,h)` swap symmetry
to identify the averaged `BABA` scalar with the averaged `ABAB` scalar. -/
lemma fullSliceABAB_scalar_to_BABAtensor
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (zeta : ℝ)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    |fullSliceABABAvg params strategy family -
        fullSliceBABAtensorAvg params strategy family| ≤ Real.sqrt zeta := by
  let 𝒟 := uniformDistribution (FullSliceQuestion params)
  let A : FullSliceQuestion params → MIPStarRE.LDT.Polynomial params → K →L[ℂ] K :=
    fun xy g => strategy.state.L ((family.meas xy.1).toSubMeas.outcome g)
  let B : FullSliceQuestion params → MIPStarRE.LDT.Polynomial params → K →L[ℂ] K :=
    fun xy g => strategy.state.R ((family.meas xy.1).toSubMeas.outcome g)
  let C : FullSliceQuestion params → MIPStarRE.LDT.Polynomial params →
      MIPStarRE.LDT.Polynomial params → K →L[ℂ] K :=
    fun xy g h =>
      strategy.state.L
        ((family.meas xy.2).toSubMeas.outcome h *
          (family.meas xy.1).toSubMeas.outcome g *
          (family.meas xy.2).toSubMeas.outcome h)
  have hclose := Preliminaries.closenessOfIP strategy.state.toVecState 𝒟
    (uniformDistribution_weight_sum_le_one _) A B C zeta
    (fullSlice_selfConsistency_fst_bound params strategy family zeta hself)
    fun xy => leftTensor_normalizationCondition_sandwich_bound strategy.state
      (family.meas xy.1).toSubMeas (family.meas xy.2)
  have hScalar :
      avgOver 𝒟 (fun xy => ∑ g : MIPStarRE.LDT.Polynomial params,
          ∑ h : MIPStarRE.LDT.Polynomial params, strategy.state.ev (C xy g h * A xy g)) =
        fullSliceABABAvg params strategy family := by
    refine (avgOver_congr 𝒟 _
      (fun xy => ∑ gh : FullSliceOutcome params, fullSliceBABATerm params strategy family xy gh)
      fun xy => ?_).trans (fullSliceCommutation_avg_swap_terms params strategy family).2
    rw [Fintype.sum_prod_type]
    exact Fintype.sum_congr _ _ fun g => Fintype.sum_congr _ _ fun h =>
      congrArg strategy.state.ev (strategy.state.leftTensor_mul_leftTensor _ _)
  have hTensor :
      avgOver 𝒟 (fun xy => ∑ g : MIPStarRE.LDT.Polynomial params,
          ∑ h : MIPStarRE.LDT.Polynomial params, strategy.state.ev (C xy g h * B xy g)) =
        fullSliceBABAtensorAvg params strategy family :=
    avgOver_congr 𝒟 _ _ fun xy => (Fintype.sum_prod_type' _).symm
  rw [← hScalar, ← hTensor]
  exact hclose

end MIPRE.LIDT.Co.Commutativity

end

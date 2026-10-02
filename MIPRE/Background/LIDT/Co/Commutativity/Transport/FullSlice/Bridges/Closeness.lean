/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
Commutativity/Transport/FullSlice/Bridges/Closeness.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Commutativity.Transport.FullSlice.Averages
public import MIPRE.Background.LIDT.Co.Commutativity.Transport.FullSlice.Machinery.Marginalization.Y
public import MIPRE.Background.LIDT.Co.Commutativity.Transport.FullSlice.Machinery.Normalization
public import MIPRE.Background.LIDT.Co.Commutativity.Transport.FullSlice.Bridges.ClosenessCore

@[expose] public section

/-!
# Full-slice scalar-to-tensor closeness comparison

`closenessOfIP` comparisons transform scalar quartic averages into manifestly positive
tensor-form partners, and the same route includes the tensor-marginalization identities
connecting full-slice and evaluated-slice `ABAB` averages: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/Transport/FullSlice/Bridges/Closeness.lean`
in the port of `planning/c6b-plan.md` (milestone M7, section "Port conventions"). The core
comparison `fullSliceABAB_scalar_to_BABAtensor` is in `ClosenessCore.lean`.

The comparisons are stated on the symmetric model of a strategy
`strategy : SymStrat params.next 𝔓 K`, the vendored `leftTensor (ι₂ := ι)` and
`rightTensor (ι₁ := ι)` being `strategy.state.L` and `strategy.state.R`. The vendored hypothesis
`hnorm : strategy.state.IsNormalized` is a theorem of the model and is dropped from every
statement, as the ported `Preliminaries.closenessOfIP` and `closenessOfIPAdjoint` no longer take
it. `leftTensor_sandwich_adjoint_normalization_family` is a placement lemma and takes the model
`(S : SymModel 𝔓 K)` as its first explicit argument. The tensor-form lemmas are internal to the
scalar/tensor comparison recorded upstream in `docs/decisions/713-scalar-tensor-decision.md`;
downstream code should use the scalar API exposed by the full-slice transport theorems.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Commutativity

open MIPStarRE.LDT (Parameters FieldModel Point Fq avgOver avgOver_congr uniformDistribution
  uniformDistribution_weight_sum_le_one)
open MIPStarRE.LDT.Commutativity (EvaluatedSliceQuestion FullSliceQuestion)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The adjoint-side placed normalization condition for a family of sandwiches
`C^ω_{a,b} = Q^ω_b P^ω_a Q^ω_b ⊗ I`, one for each index `ω`: the `C`-hypothesis of
`closenessOfIPAdjoint`. -/
lemma leftTensor_sandwich_adjoint_normalization_family
    {Ω α β : Type*} [Fintype α] [Fintype β]
    (S : SymModel 𝔓 K) (P : Ω → SubMeas α 𝔓) (Q : Ω → ProjSubMeas β 𝔓) :
    ∀ ω,
      ∑ a : α,
          star (∑ b : β, S.L ((Q ω).outcome b * (P ω).outcome a * (Q ω).outcome b)) *
            (∑ b : β, S.L ((Q ω).outcome b * (P ω).outcome a * (Q ω).outcome b)) ≤
        1 :=
  fun ω => leftTensor_normalizationCondition_sandwich_adjoint_bound S (P ω) (Q ω)

/-- X-evaluated `BAB ⊗ A` tensor to x-evaluated scalar quartic (paper `commutativity-G.tex`
line 359; the vendored hypothesis `hnorm : strategy.state.IsNormalized` is a theorem of the
model): one `closenessOfIPAdjoint` application moves the evaluated `G^x_[g(u)=a]` from the right
register to the front of the left one. -/
lemma xEvaluatedSliceBABAtensor_to_xEvaluatedFullSliceABABAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (zeta : ℝ)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    |xEvaluatedSliceBABAtensorAvg params strategy family -
        xEvaluatedFullSliceABABAvg params strategy family| ≤ Real.sqrt zeta := by
  let 𝒟 := uniformDistribution (Point params × FullSliceQuestion params)
  let X : Point params × FullSliceQuestion params → SubMeas (Fq params) 𝔓 :=
    fun ux => evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)
  let A : Point params × FullSliceQuestion params → Fq params → K →L[ℂ] K :=
    fun ux a => strategy.state.L ((X ux).outcome a)
  let B : Point params × FullSliceQuestion params → Fq params → K →L[ℂ] K :=
    fun ux a => strategy.state.R ((X ux).outcome a)
  let C : Point params × FullSliceQuestion params → Fq params →
      MIPStarRE.LDT.Polynomial params → K →L[ℂ] K :=
    fun ux a h => strategy.state.L
      ((family.meas ux.2.2).toSubMeas.outcome h * (X ux).outcome a *
        (family.meas ux.2.2).toSubMeas.outcome h)
  have hA : ∀ ux a, star (A ux a) = A ux a := fun ux a =>
    (IsSelfAdjoint.of_nonneg (strategy.state.leftTensor_nonneg ((X ux).outcome_pos a))).star_eq
  have hB : ∀ ux a, star (B ux a) = B ux a := fun ux a =>
    (IsSelfAdjoint.of_nonneg (strategy.state.rightTensor_nonneg ((X ux).outcome_pos a))).star_eq
  have hAB : avgOver 𝒟 (fun ux => strategy.state.qSDDCore
      (fun a => star (A ux a)) (fun a => star (B ux a))) ≤ zeta := by
    simp only [hA, hB]
    exact xEvaluated_selfConsistency_fst_bound params strategy family zeta hself
  have hclose := Preliminaries.closenessOfIPAdjoint strategy.state.toVecState 𝒟
    (uniformDistribution_weight_sum_le_one _) A B C zeta hAB
    (leftTensor_sandwich_adjoint_normalization_family strategy.state X
      fun ux => family.meas ux.2.2)
  have hScalar :
      avgOver 𝒟 (fun ux => ∑ a : Fq params, ∑ h : MIPStarRE.LDT.Polynomial params,
          strategy.state.ev (A ux a * C ux a h)) =
        xEvaluatedFullSliceABABAvg params strategy family := by
    refine avgOver_congr 𝒟 _ _ fun ux => ?_
    simp only [A, C, strategy.state.leftTensor_mul_leftTensor, mul_assoc]
    exact (Fintype.sum_prod_type' _).symm
  have hTensor :
      avgOver 𝒟 (fun ux => ∑ a : Fq params, ∑ h : MIPStarRE.LDT.Polynomial params,
          strategy.state.ev (B ux a * C ux a h)) =
        xEvaluatedSliceBABAtensorAvg params strategy family :=
    (avgOver_congr 𝒟 _ _ fun ux => Fintype.sum_congr _ _ fun a => Fintype.sum_congr _ _ fun h =>
      congrArg strategy.state.ev (strategy.state.L_comm_R _ _).eq.symm).trans
      (xEvaluatedSliceBABAtensorAvg_eq_xFullData params strategy family).symm
  rw [← hScalar, ← hTensor, abs_sub_comm]
  exact hclose

/-- Evaluated-slice y-side scalar-to-tensor comparison (the vendored hypothesis
`hnorm : strategy.state.IsNormalized` is a theorem of the model): move the trailing
`G^y_[h(v)=b]` in the scalar quartic to the right register, producing the tensor form in paper
`commutativity-G.tex` line 360. -/
lemma evaluatedSliceABAB_scalar_to_ABABtensor
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (zeta : ℝ)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    |evaluatedSliceABABAvg params strategy family -
        evaluatedSliceABABtensorAvg params strategy family| ≤ Real.sqrt zeta := by
  let 𝒟 := uniformDistribution (EvaluatedSliceQuestion params)
  let A : EvaluatedSliceQuestion params → Fq params → K →L[ℂ] K :=
    fun q b => strategy.state.L ((evaluatedSliceSecondFactor params family q).outcome b)
  let B : EvaluatedSliceQuestion params → Fq params → K →L[ℂ] K :=
    fun q b => strategy.state.R ((evaluatedSliceSecondFactor params family q).outcome b)
  let C : EvaluatedSliceQuestion params → Fq params → Fq params → K →L[ℂ] K :=
    fun q b a =>
      strategy.state.L
        ((evaluatedSliceFirstFactor params family q).outcome a *
          (evaluatedSliceSecondFactor params family q).outcome b *
          (evaluatedSliceFirstFactor params family q).outcome a)
  have hclose := Preliminaries.closenessOfIP strategy.state.toVecState 𝒟
    (uniformDistribution_weight_sum_le_one _) A B C zeta
    (evaluatedSlice_selfConsistency_snd_bound params strategy family zeta hself)
    fun q => leftTensor_normalizationCondition_sandwich_bound strategy.state
      (evaluatedSliceSecondFactor params family q) (evaluatedSliceFirstProj params family q)
  have hScalar :
      avgOver 𝒟 (fun q => ∑ b : Fq params, ∑ a : Fq params,
          strategy.state.ev (C q b a * A q b)) =
        evaluatedSliceABABAvg params strategy family := by
    refine avgOver_congr 𝒟 _ _ fun q => ?_
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    exact Fintype.sum_congr _ _ fun b => Fintype.sum_congr _ _ fun a =>
      congrArg strategy.state.ev (strategy.state.leftTensor_mul_leftTensor _ _)
  have hTensor :
      avgOver 𝒟 (fun q => ∑ b : Fq params, ∑ a : Fq params,
          strategy.state.ev (C q b a * B q b)) =
        evaluatedSliceABABtensorAvg params strategy family :=
    avgOver_congr 𝒟 _ _ fun q => Finset.sum_comm.trans (Fintype.sum_prod_type' _).symm
  rw [← hScalar, ← hTensor]
  exact hclose

/-- Proved x-prefix from the full scalar quartic to the x-evaluated `BAB ⊗ A`
tensor endpoint (the vendored hypothesis `hnorm : strategy.state.IsNormalized` is a theorem of
the model).

This combines the first two paper steps for the second term in
`commutativity-G.tex` lines 332--354: the `eq:gcom4` scalar-to-`BAB ⊗ A`
comparison costs `√ζ`, and the `eq:gcom4-diff` Schwartz--Zippel
postprocessing of the `x` polynomial outcome costs `md/q`. The remaining
paper lines 356--360 are intentionally not included here; they are the two
`closenessOfIP` legs from `xEvaluatedSliceBABAtensorAvg` to
`xEvaluatedFullSliceABABtensorAvg`. -/
lemma fullSliceABAB_to_xEvaluatedSliceBABAtensorAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (zeta : ℝ)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    |fullSliceABABAvg params strategy family -
        xEvaluatedSliceBABAtensorAvg params strategy family| ≤
      (params.m : ℝ) * params.d / params.q + Real.sqrt zeta := by
  have hComparison := fullSliceABAB_scalar_to_BABAtensor params strategy family zeta hself
  have hx := fullSliceBABA_tensor_marginalize_x params strategy family
  have htri :=
    abs_sub_le
      (fullSliceABABAvg params strategy family)
      (fullSliceBABAtensorAvg params strategy family)
      (xEvaluatedSliceBABAtensorAvg params strategy family)
  linarith

/-- Proved y-tail from the mixed `ABA ⊗ B` tensor endpoint to the evaluated
scalar quartic (the vendored hypothesis `hnorm : strategy.state.IsNormalized` is a theorem of
the model).

This combines the paper steps after the x-stage has already reached
`xEvaluatedFullSliceABABtensorAvg`: y-Schwartz-Zippel marginalization
(`commutativity-G.tex` lines 369--385) followed by the `√ζ`
`closenessOfIP` move that swaps a trailing `G^y_{[h(v)=b]}` between the
scalar quartic and the `ABA ⊗ B` tensor -- the doubly-evaluated analogue
of paper line 360, exposed via `evaluatedSliceABAB_scalar_to_ABABtensor`. -/
lemma xEvaluatedFullSliceABABtensor_to_evaluatedSliceABABAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (zeta : ℝ)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    |xEvaluatedFullSliceABABtensorAvg params strategy family -
        evaluatedSliceABABAvg params strategy family| ≤
      (params.m : ℝ) * params.d / params.q + Real.sqrt zeta := by
  have hyTensor := fullSliceABAB_tensor_marginalize_y params strategy family
  have hevalComparison :=
    evaluatedSliceABAB_scalar_to_ABABtensor params strategy family zeta hself
  rw [abs_sub_comm] at hevalComparison
  have htri :=
    abs_sub_le
      (xEvaluatedFullSliceABABtensorAvg params strategy family)
      (evaluatedSliceABABtensorAvg params strategy family)
      (evaluatedSliceABABAvg params strategy family)
  linarith

end MIPRE.LIDT.Co.Commutativity

end

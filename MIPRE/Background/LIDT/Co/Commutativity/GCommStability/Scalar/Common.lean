/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
Commutativity/GCommStability/Scalar/Common.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Basic.QuantumState
public import MIPRE.Background.LIDT.Co.Basic.SubMeasurementFamilies
public import MIPRE.Background.LIDT.Co.Commutativity.GCommStability.OverlapOne
public import MIPRE.Background.LIDT.Co.Preliminaries.CauchySchwarz

@[expose] public section

/-!
# Section 11 commutativity: shared scalar stability helpers

Auxiliary positivity, order, and bounded-residual lemmas used by the scalar stability estimates:
the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/GCommStability/Scalar/Common.lean` in the
port of `planning/c6b-plan.md` (milestone M7, section "Port conventions").

The averaged slice point operator `E_u A^{u,x}_{g(u)}` lives in the local C*-algebra `𝔓`, and
the Cauchy–Schwarz estimate `scalar_pointwise_cauchy_schwarz_bound` is stated with the
placements `strategy.state.L` and `strategy.state.R`.
`averagedSlicePointEvaluationOperator_hermitian` states `star W = W` for the vendored `Wᴴ = W`.

The proofs are shorter than the vendored ones. Self-adjointness through `Matrix.PosSemidef` is
`IsSelfAdjoint.of_nonneg`, the Kronecker positivity of `storedResidual_nonneg` is the keystone's
`opTensor_nonneg`, and the entrywise `ᴴ` and product computations of the Cauchy–Schwarz factors
are the keystone's `conjTranspose_opTensor`, `opTensor_mul` and `leftTensor_mul_leftTensor`.
The finite sum over outcomes collapses through `opTensor_sum_left_univ` and `ev_sum`.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Commutativity

open MIPStarRE.LDT (Parameters FieldModel Point Fq appendPoint uniformDistribution)

namespace GCommStability.Scalar

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The averaged slice point operator `E_u A^{u,x}_{g(u)}` is positive. -/
lemma averagedSlicePointEvaluationOperator_nonneg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (x : Fq params) (g : MIPStarRE.LDT.Polynomial params) :
    0 ≤ IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g :=
  averageOperatorOverDistribution_nonneg (uniformDistribution (Point params))
    (fun u => (strategy.pointMeasurement (appendPoint params u x)).toSubMeas.outcome (g u))
    (fun u => (strategy.pointMeasurement (appendPoint params u x)).outcome_pos (g u))

/-- The averaged slice point operator `E_u A^{u,x}_{g(u)}` is at most `1`. -/
lemma averagedSlicePointEvaluationOperator_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (x : Fq params) (g : MIPStarRE.LDT.Polynomial params) :
    IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g ≤ 1 :=
  averageOperatorOverDistribution_uniform_le_one
    (fun u => (strategy.pointMeasurement (appendPoint params u x)).toSubMeas.outcome (g u))
    (fun u => (strategy.pointMeasurement (appendPoint params u x)).outcome_le_one (g u))

/-- The averaged slice point operator `E_u A^{u,x}_{g(u)}` is self-adjoint. -/
lemma averagedSlicePointEvaluationOperator_hermitian
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (x : Fq params) (g : MIPStarRE.LDT.Polynomial params) :
    star (IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g) =
      IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g :=
  (IsSelfAdjoint.of_nonneg
    (averagedSlicePointEvaluationOperator_nonneg params strategy x g)).star_eq

/-- The averaged slice point operator `W = E_u A^{u,x}_{g(u)}` satisfies `W² ≤ W`. -/
lemma averagedSlicePointEvaluationOperator_sq_le_self
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (x : Fq params) (g : MIPStarRE.LDT.Polynomial params) :
    IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g *
        IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g ≤
      IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g :=
  sq_le_self
    (averagedSlicePointEvaluationOperator_nonneg params strategy x g)
    (averagedSlicePointEvaluationOperator_le_one params strategy x g)

/-- The stored boundedness residual `⟨Ψ, (I - G^x) ⊗ Z^x Ψ⟩` is nonnegative. -/
lemma storedResidual_nonneg
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (zeta : ℝ)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    ∀ x : Fq params, 0 ≤ hbound.storedResidual G x := fun x =>
  strategy.state.ev_nonneg_of_psd _ <| strategy.state.opTensor_nonneg
    (sub_nonneg.2 (G x).total_le_one) (hbound.sliceOpPSD x)

/-- Common pointwise Cauchy--Schwarz estimate for the scalar `G`-commutativity
stability bounds.

The proof applies to either scalar stability estimate once the intermediate
submeasurement `R` and its first Cauchy--Schwarz factor are supplied. -/
lemma scalar_pointwise_cauchy_schwarz_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (zeta : ℝ)
    (family : IdxPolyFamily params 𝔓)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (R : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (x : Fq params)
    (hfirstR :
      ∑ g : MIPStarRE.LDT.Polynomial params,
        strategy.state.ev (strategy.state.L (R.outcome g)) ≤ 1) :
    |∑ g : MIPStarRE.LDT.Polynomial params,
        strategy.state.ev
          (strategy.state.L (R.outcome g * (1 - (G x).total)) *
            strategy.state.R
              (IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g))|
      ≤ Real.sqrt (hbound.storedResidual G x) := by
  have hT_proj : (G x).total * (G x).total = (G x).total := by
    rw [hG]
    exact Preliminaries.projSubMeas_total_proj (family.meas x)
  set S := strategy.state
  set T := (G x).total
  set W := IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x
  set s : MIPStarRE.LDT.Polynomial params → 𝔓 := fun g => CFC.sqrt (R.outcome g)
  have hs_sq (g) : s g * s g = R.outcome g := sqrt_subMeas_outcome_mul_self R g
  have hs_herm (g) : star (s g) = s g := (CFC.sqrt_nonneg (R.outcome g)).isSelfAdjoint.star_eq
  have hTc : IsSelfAdjoint (1 - T) :=
    IsSelfAdjoint.of_nonneg (sub_nonneg.2 (G x).total_le_one)
  let X : MIPStarRE.LDT.Polynomial params → K →L[ℂ] K := fun g => S.L (s g)
  let Y : MIPStarRE.LDT.Polynomial params → K →L[ℂ] K := fun g =>
    S.L (s g * (1 - T)) * S.R (W g)
  have hfirst : ∑ g, S.ev (X g * star (X g)) ≤ 1 := by
    refine le_of_eq_of_le (Finset.sum_congr rfl fun g _ => ?_) hfirstR
    change S.ev (S.L (s g) * star (S.L (s g))) = _
    rw [S.leftTensor_conjTranspose, hs_herm, S.leftTensor_mul_leftTensor, hs_sq]
  have hYY (g) : star (Y g) * Y g =
      S.opTensor ((1 - T) * R.outcome g * (1 - T)) (W g * W g) := by
    change star (S.opTensor _ _) * S.opTensor _ _ = _
    rw [S.conjTranspose_opTensor, S.opTensor_mul, star_mul, hTc.star_eq, hs_herm,
      averagedSlicePointEvaluationOperator_hermitian, mul_assoc, ← mul_assoc (s g), hs_sq,
      ← mul_assoc]
  have hsecond : ∑ g, S.ev (star (Y g) * Y g) ≤ hbound.storedResidual G x := by
    have hRg (g) : 0 ≤ (1 - T) * R.outcome g * (1 - T) :=
      hTc.conjugate_nonneg (R.outcome_pos g)
    calc ∑ g, S.ev (star (Y g) * Y g)
        = ∑ g, S.ev (S.opTensor ((1 - T) * R.outcome g * (1 - T)) (W g * W g)) :=
          Finset.sum_congr rfl fun g _ => by rw [hYY]
      _ ≤ ∑ g, S.ev (S.opTensor ((1 - T) * R.outcome g * (1 - T)) (family.witness x)) :=
          Finset.sum_le_sum fun g _ => S.ev_mono _ _ <| S.opTensor_mono_right (hRg g)
            ((averagedSlicePointEvaluationOperator_sq_le_self params strategy x g).trans
              (hbound.averagedPoint_le_witness x g))
      _ = S.ev (S.opTensor ((1 - T) * R.total * (1 - T)) (family.witness x)) := by
          rw [← S.ev_sum, ← S.opTensor_sum_left_univ, ← Finset.sum_mul, ← Finset.mul_sum,
            R.sum_eq_total]
      _ ≤ S.ev (S.opTensor ((1 - T) * 1 * (1 - T)) (family.witness x)) :=
          S.ev_mono _ _ <| S.opTensor_mono_left
            (hTc.conjugate_le_conjugate R.total_le_one) (hbound.sliceOpPSD x)
      _ = hbound.storedResidual G x := by
          rw [mul_one, sub_mul, one_mul, mul_sub, mul_one, hT_proj, sub_self, sub_zero]
          rfl
  have hXY (g) : X g * Y g = S.L (R.outcome g * (1 - T)) * S.R (W g) := by
    change S.L (s g) * (S.L (s g * (1 - T)) * S.R (W g)) = _
    rw [← mul_assoc, S.leftTensor_mul_leftTensor, ← mul_assoc, hs_sq]
  calc |∑ g, S.ev (S.L (R.outcome g * (1 - T)) * S.R (W g))|
      = |∑ g, S.ev (X g * Y g)| := by simp only [hXY]
    _ ≤ Real.sqrt (∑ g, S.ev (X g * star (X g))) *
          Real.sqrt (∑ g, S.ev (star (Y g) * Y g)) :=
        Preliminaries.sum_ev_mul_le_sqrt S.toVecState X Y
    _ ≤ Real.sqrt 1 * Real.sqrt (hbound.storedResidual G x) :=
        mul_le_mul (Real.sqrt_le_sqrt hfirst) (Real.sqrt_le_sqrt hsecond)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = Real.sqrt (hbound.storedResidual G x) := by rw [Real.sqrt_one, one_mul]

end GCommStability.Scalar

end MIPRE.LIDT.Co.Commutativity

end

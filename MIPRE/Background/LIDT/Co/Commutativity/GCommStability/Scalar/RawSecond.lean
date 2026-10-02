/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
Commutativity/GCommStability/Scalar/RawSecond.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Commutativity.GCommStability.Scalar.Common

@[expose] public section

/-!
# Section 11 commutativity: raw second scalar stability bound

The raw uncollapsed form of the second scalar stability estimate: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/GCommStability/Scalar/RawSecond.lean` in the
port of `planning/c6b-plan.md` (milestone M7, section "Port conventions").

The raw defect is stated with the placements `strategy.state.L` and `strategy.state.R`, and the
two helpers `avgOver_right_linear` and `sum_ev_leftTensor_mul_rightTensor_const` take the
symmetric model `S` where the vendored ones take the state `ψ`, in the same position. The vendored
hypothesis `hnorm : strategy.state.IsNormalized` of `gCommStabilityTwo_raw_scalar_pointwise_bound`
and `gCommStabilityTwo_raw_scalar` is dropped, as the port conventions drop `hψ : ψ.IsNormalized`:
the first Cauchy–Schwarz factor is bounded through `VecState.ev_one_of_isNormalized`, which takes
no hypothesis. Callers omit that argument, which stood between `zeta` and `family`.

The proofs are shorter than the vendored ones. Self-adjointness through `Matrix.PosSemidef` is
`IsSelfAdjoint.of_nonneg`; the Kronecker computations of the Cauchy–Schwarz factors are the
keystone's `conjTranspose_opTensor` and `opTensor_mul`, and their positivity and monotonicity
`opTensor_nonneg`, `opTensor_mono_left` and `opTensor_mono_right`. The inner bound of
`gCommStabilityTwo_raw_left_sum_le` is the total bound of `sandwichByOuterSubMeas`, reindexed by
`Equiv.prodComm`, and `avgOver_right_linear` pulls the average through the right placement with
`ev_opTensor_averageOperatorOverDistribution_right`.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Commutativity

open MIPStarRE.LDT (Parameters FieldModel Point Fq Distribution appendPoint avgOver avgOver_mono
  avgOver_sum avgOver_uniform_const uniformDistribution uniformDistribution_weight_sum_le_one)
open GCommStability.Scalar

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Averaging over `u` commutes with the finite sums and passes into the right placement:
`E_u ∑_{g,a} ⟨L_{g,a} ⊗ P_a Q_{u,g}⟩ = ∑_{g,a} ⟨L_{g,a} ⊗ P_a (E_u Q_{u,g})⟩`. -/
lemma avgOver_right_linear
    {U Γ Aidx : Type*} [Fintype Γ] [Fintype Aidx]
    (𝒟U : Distribution U)
    (S : SymModel 𝔓 K)
    (L : Γ → Aidx → 𝔓)
    (P : Aidx → 𝔓)
    (Q : U → Γ → 𝔓) :
    avgOver 𝒟U (fun u =>
      ∑ g : Γ, ∑ a : Aidx, S.ev (S.L (L g a) * S.R (P a * Q u g))) =
    ∑ g : Γ, ∑ a : Aidx,
      S.ev (S.L (L g a) * S.R (P a * averageOperatorOverDistribution 𝒟U (fun u => Q u g))) := by
  simp only [avgOver_sum]
  refine Fintype.sum_congr _ _ fun g => Fintype.sum_congr _ _ fun a => ?_
  have h : P a * averageOperatorOverDistribution 𝒟U (fun u => Q u g) =
      averageOperatorOverDistribution 𝒟U (fun u => P a * Q u g) := by
    simp only [averageOperatorOverDistribution, Finset.mul_sum, mul_smul_comm]
  rw [h]
  exact (S.ev_opTensor_averageOperatorOverDistribution_right 𝒟U (L g a) _).symm

/-- A finite sum of left placements against a fixed right placement collapses into the left
factor. -/
lemma sum_ev_leftTensor_mul_rightTensor_const
    {α : Type*} (s : Finset α)
    (S : SymModel 𝔓 K)
    (L : α → 𝔓)
    (R : 𝔓) :
    ∑ a ∈ s, S.ev (S.L (L a) * S.R R) = S.ev (S.L (∑ a ∈ s, L a) * S.R R) := by
  rw [← S.ev_finset_sum, ← Finset.sum_mul, S.leftTensor_finset_sum]

/-- Raw uncollapsed scalar defect for the paper's second `G`-commutativity
stability estimate after the right-register point-product swap.

For fixed slice height `x`, this is the expression from
`commutativity-G.tex`, `clm:g-comm-stability2`, before collapsing the
`(v,y), b`-average into `gCommStabilityTwoR`.  The left register contains
`G^x_g B^{v,y}_b (1-G^x)`, while the right register contains the swapped point
product `P^{v,y}_b P^{u,x}_{g(u)}`. -/
noncomputable def gCommStabilityTwoRawScalarDefect
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (x : Fq params) : ℝ :=
  avgOver (uniformDistribution (Point params.next)) fun vy =>
    avgOver (uniformDistribution (Point params)) fun u =>
      ∑ g : MIPStarRE.LDT.Polynomial params, ∑ b : Fq params,
        strategy.state.ev
          (strategy.state.L
              ((G x).outcome g *
                (evaluatedPointFamily params family vy).outcome b *
                (1 - (G x).total)) *
            strategy.state.R
              ((strategy.pointMeasurement vy).toSubMeas.outcome b *
                (strategy.pointMeasurement (appendPoint params u x)).toSubMeas.outcome (g u)))

/-- The left-register sandwiches of the raw second defect sum to at most `1 - G^x`:
`∑_{g,b} (1 - G^x) B_b G^x_g B_b (1 - G^x) ≤ 1 - G^x` for projective `G^x`. -/
lemma gCommStabilityTwo_raw_left_sum_le
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (x : Fq params) (vy : Point params.next) :
    ∑ gb : MIPStarRE.LDT.Polynomial params × Fq params,
        ((1 - (G x).total) *
          ((evaluatedPointFamily params family vy).outcome gb.2 *
            (G x).outcome gb.1 *
            (evaluatedPointFamily params family vy).outcome gb.2) *
          (1 - (G x).total)) ≤
      1 - (G x).total := by
  have hT_proj : (G x).total * (G x).total = (G x).total := by
    rw [hG]
    exact Preliminaries.projSubMeas_total_proj (family.meas x)
  set T := (G x).total
  set B := evaluatedPointFamily params family vy
  have hTc : IsSelfAdjoint (1 - T) :=
    IsSelfAdjoint.of_nonneg (sub_nonneg.2 (G x).total_le_one)
  have hinner :
      ∑ gb : MIPStarRE.LDT.Polynomial params × Fq params,
          B.outcome gb.2 * (G x).outcome gb.1 * B.outcome gb.2 ≤ 1 := by
    refine le_of_eq_of_le ?_ (sandwichByOuterSubMeas B (G x)).total_le_one
    rw [← (sandwichByOuterSubMeas B (G x)).sum_eq_total]
    exact Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun _ => rfl
  calc ∑ gb : MIPStarRE.LDT.Polynomial params × Fq params,
        (1 - T) * (B.outcome gb.2 * (G x).outcome gb.1 * B.outcome gb.2) * (1 - T)
      = (1 - T) *
          (∑ gb : MIPStarRE.LDT.Polynomial params × Fq params,
            B.outcome gb.2 * (G x).outcome gb.1 * B.outcome gb.2) * (1 - T) := by
        rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ (1 - T) * 1 * (1 - T) := hTc.conjugate_le_conjugate hinner
    _ = 1 - T := by
        rw [mul_one, sub_mul, one_mul, mul_sub, mul_one, hT_proj, sub_self, sub_zero]

/-- Pointwise Cauchy–Schwarz bound for the raw second scalar defect:
`|raw defect at x| ≤ √⟨Ψ, (1 - G^x) ⊗ Z^x Ψ⟩`. -/
lemma gCommStabilityTwo_raw_scalar_pointwise_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (zeta : ℝ)
    (family : IdxPolyFamily params 𝔓)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    ∀ x : Fq params,
      |gCommStabilityTwoRawScalarDefect params strategy family G x| ≤
        Real.sqrt (hbound.storedResidual G x) := by
  intro x
  set S := strategy.state
  set T := (G x).total
  set W := IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x
  let 𝒟V : Distribution (Point params.next) := uniformDistribution (Point params.next)
  let B : Point params.next → SubMeas (Fq params) 𝔓 := fun vy =>
    evaluatedPointFamily params family vy
  let P : Point params.next → SubMeas (Fq params) 𝔓 := fun vy =>
    (strategy.pointMeasurement vy).toSubMeas
  let X : Point params.next → MIPStarRE.LDT.Polynomial params × Fq params → K →L[ℂ] K :=
    fun vy gb => S.L ((G x).outcome gb.1) * S.R ((P vy).outcome gb.2)
  let Y : Point params.next → MIPStarRE.LDT.Polynomial params × Fq params → K →L[ℂ] K :=
    fun vy gb => S.L ((G x).outcome gb.1 * (B vy).outcome gb.2 * (1 - T)) * S.R (W gb.1)
  let xDiag : Point params.next → MIPStarRE.LDT.Polynomial params × Fq params → ℝ :=
    fun vy gb => S.ev (X vy gb * star (X vy gb))
  let yDiag : Point params.next → MIPStarRE.LDT.Polynomial params × Fq params → ℝ :=
    fun vy gb => S.ev (S.L ((1 - T) * ((B vy).outcome gb.2 * (G x).outcome gb.1 *
      (B vy).outcome gb.2) * (1 - T)) * S.R (family.witness x))
  let t : Point params.next → MIPStarRE.LDT.Polynomial params × Fq params → ℝ :=
    fun vy gb => S.ev (S.L ((G x).outcome gb.1 * (B vy).outcome gb.2 * (1 - T)) *
      S.R ((P vy).outcome gb.2 * W gb.1))
  have hraw_eq : gCommStabilityTwoRawScalarDefect params strategy family G x =
      avgOver 𝒟V (fun vy => ∑ gb, t vy gb) := by
    refine congrArg (avgOver 𝒟V) (funext fun vy => ?_)
    exact (avgOver_right_linear (uniformDistribution (Point params)) S
      (fun g b => (G x).outcome g * (B vy).outcome b * (1 - T)) (fun b => (P vy).outcome b)
      (fun u g => (strategy.pointMeasurement (appendPoint params u x)).toSubMeas.outcome
        (g u))).trans (Fintype.sum_prod_type (t vy)).symm
  have hTc : IsSelfAdjoint (1 - T) :=
    IsSelfAdjoint.of_nonneg (sub_nonneg.2 (G x).total_le_one)
  have hGproj (g) : (G x).outcome g * (G x).outcome g = (G x).outcome g := by
    rw [hG x]
    exact (family.meas x).proj g
  have hleft_pos (vy) (gb : MIPStarRE.LDT.Polynomial params × Fq params) :
      0 ≤ (1 - T) * ((B vy).outcome gb.2 * (G x).outcome gb.1 * (B vy).outcome gb.2) *
        (1 - T) :=
    hTc.conjugate_nonneg <|
      IsSelfAdjoint.conjugate_nonneg ((G x).outcome_pos gb.1) ((B vy).outcome_hermitian gb.2)
  have hX_expand (vy) (gb : MIPStarRE.LDT.Polynomial params × Fq params) :
      X vy gb * star (X vy gb) = S.opTensor ((G x).outcome gb.1) ((P vy).outcome gb.2) := by
    change S.opTensor _ _ * star (S.opTensor _ _) = _
    rw [S.conjTranspose_opTensor, S.opTensor_mul, SubMeas.outcome_hermitian,
      SubMeas.outcome_hermitian, hGproj, (strategy.pointMeasurement vy).proj gb.2]
  have hY_le (vy) (gb : MIPStarRE.LDT.Polynomial params × Fq params) :
      S.ev (star (Y vy gb) * Y vy gb) ≤ yDiag vy gb := by
    have hA : star ((G x).outcome gb.1 * (B vy).outcome gb.2 * (1 - T)) *
          ((G x).outcome gb.1 * (B vy).outcome gb.2 * (1 - T)) =
        (1 - T) * ((B vy).outcome gb.2 * (G x).outcome gb.1 * (B vy).outcome gb.2) *
          (1 - T) := by
      rw [star_mul, star_mul, hTc.star_eq, SubMeas.outcome_hermitian,
        SubMeas.outcome_hermitian]
      simp only [mul_assoc]
      rw [← mul_assoc ((G x).outcome gb.1) ((G x).outcome gb.1), hGproj]
    change S.ev (star (S.opTensor _ _) * S.opTensor _ _) ≤ _
    rw [S.conjTranspose_opTensor, S.opTensor_mul, hA,
      averagedSlicePointEvaluationOperator_hermitian]
    exact S.ev_mono _ _ <| S.opTensor_mono_right (hleft_pos vy gb)
      ((averagedSlicePointEvaluationOperator_sq_le_self params strategy x gb.1).trans
        (hbound.averagedPoint_le_witness x gb.1))
  have ht (vy) (gb : MIPStarRE.LDT.Polynomial params × Fq params) :
      |t vy gb| ≤ Real.sqrt (xDiag vy gb) * Real.sqrt (yDiag vy gb) := by
    have hXY : X vy gb * Y vy gb =
        S.L ((G x).outcome gb.1 * (B vy).outcome gb.2 * (1 - T)) *
          S.R ((P vy).outcome gb.2 * W gb.1) := by
      change S.opTensor _ _ * S.opTensor _ _ = S.opTensor _ _
      rw [S.opTensor_mul, ← mul_assoc, ← mul_assoc, hGproj]
    calc |t vy gb| = |S.ev (X vy gb * Y vy gb)| := by rw [hXY]
      _ ≤ Real.sqrt (xDiag vy gb) * Real.sqrt (S.ev (star (Y vy gb) * Y vy gb)) :=
          S.toVecState.ev_abs_mul_le_sqrt (X vy gb) (Y vy gb)
      _ ≤ Real.sqrt (xDiag vy gb) * Real.sqrt (yDiag vy gb) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hY_le vy gb)) (Real.sqrt_nonneg _)
  have hx (vy) (gb : MIPStarRE.LDT.Polynomial params × Fq params) : 0 ≤ xDiag vy gb := by
    have h := S.ev_adjoint_self_nonneg (star (X vy gb))
    rwa [star_star] at h
  have hy (vy) (gb : MIPStarRE.LDT.Polynomial params × Fq params) : 0 ≤ yDiag vy gb :=
    S.ev_nonneg_of_psd _ <| S.opTensor_nonneg (hleft_pos vy gb) (hbound.sliceOpPSD x)
  have hfirst_point (vy) : ∑ gb, xDiag vy gb ≤ 1 := by
    calc ∑ gb, xDiag vy gb
        = ∑ g, ∑ b, S.ev (S.opTensor ((G x).outcome g) ((P vy).outcome b)) := by
          rw [← Fintype.sum_prod_type']
          exact Finset.sum_congr rfl fun gb _ => congrArg S.ev (hX_expand vy gb)
      _ = S.ev (S.opTensor T 1) := by
          simp only [← S.ev_sum, ← S.opTensor_sum_right_univ, ← S.opTensor_sum_left_univ,
            SubMeas.sum_eq_total]
          change S.ev (S.opTensor T (strategy.pointMeasurement vy).total) = _
          rw [(strategy.pointMeasurement vy).total_eq_one]
      _ ≤ S.ev 1 := S.ev_mono _ _ (S.opTensor_le_one (G x).total_nonneg (G x).total_le_one le_rfl)
      _ = 1 := S.ev_one_of_isNormalized
  have hfirst : avgOver 𝒟V (fun vy => ∑ gb, xDiag vy gb) ≤ 1 :=
    (avgOver_mono 𝒟V _ _ hfirst_point).trans_eq (avgOver_uniform_const 1)
  have hsecond : avgOver 𝒟V (fun vy => ∑ gb, yDiag vy gb) ≤ hbound.storedResidual G x := by
    refine (avgOver_mono 𝒟V _ _ fun vy => ?_).trans_eq (avgOver_uniform_const _)
    exact (sum_ev_leftTensor_mul_rightTensor_const Finset.univ S
      (fun gb : MIPStarRE.LDT.Polynomial params × Fq params =>
        (1 - T) * ((B vy).outcome gb.2 * (G x).outcome gb.1 * (B vy).outcome gb.2) * (1 - T))
      (family.witness x)).trans_le <|
      S.ev_mono _ _ <| S.opTensor_mono_left
        (gCommStabilityTwo_raw_left_sum_le params family G hG x vy) (hbound.sliceOpPSD x)
  calc |gCommStabilityTwoRawScalarDefect params strategy family G x|
      = |avgOver 𝒟V (fun vy => ∑ gb, t vy gb)| := by rw [hraw_eq]
    _ ≤ Real.sqrt (avgOver 𝒟V (fun vy => ∑ gb, xDiag vy gb)) *
          Real.sqrt (avgOver 𝒟V (fun vy => ∑ gb, yDiag vy gb)) :=
        MIPStarRE.LDT.Preliminaries.weightedFinsetCauchySchwarz 𝒟V t xDiag yDiag ht hx hy
    _ ≤ Real.sqrt 1 * Real.sqrt (hbound.storedResidual G x) :=
        mul_le_mul (Real.sqrt_le_sqrt hfirst) (Real.sqrt_le_sqrt hsecond)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = Real.sqrt (hbound.storedResidual G x) := by rw [Real.sqrt_one, one_mul]

/-- Raw paper form of the second scalar `G`-commutativity stability estimate.

This bounds the uncollapsed post-swap defect used in the paper line-87 removal:
the defect still averages over `(v,y), u, g, b` rather than first packaging the
left-register sandwich as `gCommStabilityTwoR`. The vendored theorem asks for a normalized
state. -/
theorem gCommStabilityTwo_raw_scalar
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (zeta : ℝ)
    (family : IdxPolyFamily params 𝔓)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    |avgOver (uniformDistribution (Fq params))
      (gCommStabilityTwoRawScalarDefect params strategy family G)| ≤ Real.sqrt zeta :=
  (MIPStarRE.LDT.Preliminaries.avgOver_abs_le_sqrt_of_pointwise
    (uniformDistribution (Fq params))
    (gCommStabilityTwoRawScalarDefect params strategy family G)
    (fun x => hbound.storedResidual G x)
    (gCommStabilityTwo_raw_scalar_pointwise_bound params strategy zeta family G hG hbound)
    (storedResidual_nonneg params strategy family G zeta hbound)
    (by simpa using uniformDistribution_weight_sum_le_one (Fq params))).trans
    (Real.sqrt_le_sqrt (hbound.storedBoundedResidualBound G hG))

end MIPRE.LIDT.Co.Commutativity

end

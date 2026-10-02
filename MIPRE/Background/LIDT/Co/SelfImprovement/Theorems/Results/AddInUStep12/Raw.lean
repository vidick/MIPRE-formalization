/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
SelfImprovement/Theorems/Results/AddInUStep12/Raw.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Results.AddInUStep12.Algebra

@[expose] public section

/-!
# Unselected add-in-u Step 1/2 Cauchy--Schwarz bounds

Unselected-family contraction inputs and raw `√(2δ)` estimates for the first two add-in-u moves
in the self-improvement chain: the counterpart of the vendored
`SelfImprovement/Theorems/Results/AddInUStep12/Raw.lean` (under
`MIPRE/Background/LIDT/MIPStarRE/LDT/`) in the port of `planning/c6b-plan.md` (milestone M10,
section "Port conventions").

## Contents

- `addInU_step1_C_contraction`, `addInU_step2_C_contraction`: the contraction side conditions
  `∑ₐ C_a^* C_a ≤ 1` and `∑ₐ C_a C_a^* ≤ 1` of the weighted Cauchy--Schwarz bounds, as
  inequalities in `K →L[ℂ] K`.
- `addInU_cs_chain_step1_abs_le_sqrt_two_delta`, `addInU_cs_chain_step2_abs_le_sqrt_two_delta`:
  `|Q₀ − Q₁| ≤ √(2δ)` and `|Q₁ − Q₂| ≤ √(2δ)`.

Every scalar is `strategy.state.ev` of a joint operator; `leftTensor A`, `rightTensor A` and
`opTensor A B` are `strategy.state.L A`, `strategy.state.R A` and `strategy.state.opTensor A B`,
and `Xᴴ` is `star X`. The vendored Hermitian facts `(Matrix.nonneg_iff_posSemidef.mp
(…outcome_pos _)).isHermitian.eq` and the `Matrix.conjTranspose_sum`/`conjTranspose_opTensor`
computation of `Kᴴ = K` are `(IsSelfAdjoint.of_nonneg …).star_eq`, the positivity coming from the
keystone (`opTensor_nonneg`, `rightTensor_nonneg`, `leftTensor_nonneg`). The vendored proofs pass
`strategy.isNormalized` to `closenessOfInnerProduct_right`/`_left`; the ported Cauchy--Schwarz
bounds (Co `Preliminaries/SwitchSandwichPrep/InnerProduct`) have no normalization hypothesis, so
it is dropped. No statement of the vendored file carries a swap, density or normalization
hypothesis.

The two contraction proofs share the step `∑ₐ Pₐ K²ₐ Pₐ ≤ ∑ₐ Pₐ = 1` for self-adjoint idempotents
`Pₐ` summing to one and `K²ₐ ≤ 1`, which is `addInU_sum_projection_sandwich_le_one` over any
star-ordered ring; the vendored proofs repeat it inline.

## Not ported

Every declaration of the vendored file has a counterpart here.

## New here

- `addInU_sum_projection_sandwich_le_one`: the sandwich step shared by the two contraction lemmas.
- `addInU_sum_fiber_collapse`: the collapse of `∑ₐ ∑_h` onto the fibre `a = h(v)`, shared by the
  two raw bounds (the vendored proofs repeat it inline as `hAvg`).

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/self_improvement.tex` lines 255–297 (`eq:move-one`,
  `eq:move-another`)
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.SelfImprovement

open MIPStarRE.LDT (Parameters FieldModel Point Fq avgOver uniformDistribution avgOver_congr
  avgOver_sub uniformDistribution_weight_sum_le_one)
open MIPRE.LIDT.Co.GlobalVariance (pointConditionedOutcomeOperatorAtPolynomial)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The sandwich step of the two contraction lemmas: if the `Pₐ` are self-adjoint idempotents
summing to `1` and `Kₐ Kₐ ≤ 1`, then `∑ₐ Pₐ (Kₐ Kₐ) Pₐ ≤ 1`. -/
theorem addInU_sum_projection_sandwich_le_one {R ι : Type*} [Ring R] [StarRing R]
    [PartialOrder R] [StarOrderedRing R] [Fintype ι] (Kf P : ι → R)
    (hK : ∀ a, Kf a * Kf a ≤ 1) (hP : ∀ a, IsSelfAdjoint (P a))
    (hPP : ∀ a, P a * P a = P a) (hsum : ∑ a, P a = 1) :
    ∑ a, P a * (Kf a * Kf a) * P a ≤ 1 :=
  (Finset.sum_le_sum fun a _ =>
    (IsSelfAdjoint.conjugate_le_conjugate (hK a) (hP a)).trans_eq
      ((congrArg (· * P a) (mul_one (P a))).trans (hPP a))).trans_eq hsum

/-- Collapsing a double sum `∑ₐ ∑_h ev(X a h)` onto the fibre `a = h(v)`, when `X a h` vanishes
off it: the step that turns the fibre-indexed Cauchy--Schwarz sums of the two raw bounds into the
single sums over `h` of the algebraic alignment. -/
theorem addInU_sum_fiber_collapse {params : Parameters} [FieldModel params.q]
    (V : VecState K) (v : Point params)
    (X : Fq params → MIPStarRE.LDT.Polynomial params → K →L[ℂ] K)
    (hX : ∀ a h, h v ≠ a → X a h = 0) :
    ∑ a : Fq params, ∑ h : MIPStarRE.LDT.Polynomial params, V.ev (X a h) =
      ∑ h : MIPStarRE.LDT.Polynomial params, V.ev (X (h v) h) :=
  Finset.sum_comm.trans <| Finset.sum_congr rfl fun h _ =>
    Finset.sum_eq_single (h v) (fun a _ ha => by rw [hX a h (Ne.symm ha), V.ev_zero])
      fun hm => (hm (Finset.mem_univ _)).elim

/-! ### Raw Cauchy--Schwarz bound for the add-in-u Step 1 difference

This section proves the raw `|Q₀ - Q₁| ≤ √(2δ)` bound from
`references/ldt-paper/self_improvement.tex`, lines 255--277 (`eq:move-one`).

The proof combines:
* `addInU_cs_chain_step1_diff_eq` (algebraic alignment to commutator-times-PSD),
* `addInU_pointMeasurement_snd_selfConsistency` (`A^v` self-consistency lifted
  to the `(u, v)` average),
* `addInU_filtered_sandwiched_tensor_sum_le_one` (filtered sandwich-tensor mass
  is a contraction),
* `Preliminaries.closenessOfInnerProduct_right` (the weighted Cauchy--Schwarz
  inner-product bound from `prop:closeness-of-ip`, `eq:closeness4`).

The analogous Step 2 bound (`|Q₁ - Q₂| ≤ √(2δ)`) is proved by the same
strategy with `closenessOfInnerProduct_left` and the `S.L`-sandwiched
analogue of the Step 1 contraction lemma. -/

/-- Cauchy--Schwarz contraction side condition for Step 1.

For a fixed `(u, v)`, the right-placed sandwiched sum
`Σ_a (K_{u,v,a} · R A^v_a)^* · (K_{u,v,a} · R A^v_a) ≤ 1`
where `K_{u,v,a} = Σ_{h: h(v)=a} (M^u_h ⊗ T_h)`.  This is the C side condition
fed to `closenessOfInnerProduct_right` in the Step 1 raw bound proof. -/
theorem addInU_step1_C_contraction
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (uv : Point params × Point params) :
    ∑ a : Fq params,
        star (∑ h : MIPStarRE.LDT.Polynomial params,
            (if h uv.2 = a then
              strategy.state.opTensor
                  ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
                  (T.outcome h) *
                strategy.state.R ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
            else 0)) *
          (∑ h : MIPStarRE.LDT.Polynomial params,
            (if h uv.2 = a then
              strategy.state.opTensor
                  ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
                  (T.outcome h) *
                strategy.state.R ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
            else 0)) ≤
      (1 : K →L[ℂ] K) := by
  classical
  let Kf : Fq params → K →L[ℂ] K := fun a =>
    ∑ h ∈ Finset.univ.filter (fun h : MIPStarRE.LDT.Polynomial params => h uv.2 = a),
      strategy.state.opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
        (T.outcome h)
  let P : Fq params → K →L[ℂ] K := fun a =>
    strategy.state.R ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
  have hK0 : ∀ a, 0 ≤ Kf a := fun a => Finset.sum_nonneg fun h _ =>
    strategy.state.opTensor_nonneg
      ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome_pos h) (T.outcome_pos h)
  have hK1 : ∀ a, Kf a ≤ 1 := fun a =>
    addInU_filtered_sandwiched_tensor_sum_le_one params strategy T uv.1 uv.2 a
  have hP : ∀ a, IsSelfAdjoint (P a) := fun a => IsSelfAdjoint.of_nonneg
    (strategy.state.rightTensor_nonneg ((strategy.pointMeasurement uv.2).toSubMeas.outcome_pos a))
  refine le_of_eq_of_le (Finset.sum_congr rfl fun a _ => ?_)
    (addInU_sum_projection_sandwich_le_one Kf P
      (fun a => (MIPRE.LIDT.Co.sq_le_self (hK0 a) (hK1 a)).trans (hK1 a)) hP
      (fun a => (strategy.state.rightTensor_mul_rightTensor _ _).trans
        (congrArg strategy.state.R ((strategy.pointMeasurement uv.2).proj a)))
      ((strategy.state.rightTensor_finset_sum _ _).trans <| by
        rw [(strategy.pointMeasurement uv.2).toSubMeas.sum_eq_total,
          (strategy.pointMeasurement uv.2).total_eq_one, strategy.state.rightTensor_one]))
  rw [← Finset.sum_filter, ← Finset.sum_mul]
  change star (Kf a * P a) * (Kf a * P a) = P a * (Kf a * Kf a) * P a
  rw [star_mul, (hP a).star_eq, (IsSelfAdjoint.of_nonneg (hK0 a)).star_eq]
  simp only [mul_assoc]

/-- Raw `|Q₀ - Q₁| ≤ √(2δ)` bound for the add-in-u Step 1 Cauchy--Schwarz move.

Proves the paper's `eq:move-one` bound from
`references/ldt-paper/self_improvement.tex`, lines 255--277, as a completed
construction.  The proof combines the algebraic alignment
`addInU_cs_chain_step1_diff_eq` with the weighted Cauchy--Schwarz inner-product
bound `Preliminaries.closenessOfInnerProduct_right`, the `A^v` self-consistency
input via `addInU_pointMeasurement_snd_selfConsistency`, and the
filtered-tensor contraction `addInU_filtered_sandwiched_tensor_sum_le_one`.

The hypothesis is the bipartite SSC for the unlifted point measurement on the
single-point distribution; the lifted `2δ` bound is constructed inside the
proof via `addInU_pointMeasurement_snd_selfConsistency`. -/
theorem addInU_cs_chain_step1_abs_le_sqrt_two_delta
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (delta : ℝ)
    (hssc : strategy.state.BipartiteSSCRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta) :
    |addInUCSChainQ0 params strategy T - addInUCSChainQ1 params strategy T| ≤
      Real.sqrt (2 * delta) := by
  classical
  let Aop : Point params × Point params → Fq params → K →L[ℂ] K :=
    fun uv a => strategy.state.L ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
  let Bop : Point params × Point params → Fq params → K →L[ℂ] K :=
    fun uv a => strategy.state.R ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
  let Cop : Point params × Point params → Fq params → MIPStarRE.LDT.Polynomial params →
      K →L[ℂ] K :=
    fun uv a h =>
      if h uv.2 = a then
        strategy.state.opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
            (T.outcome h) *
          strategy.state.R ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
      else 0
  have hAB :
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        strategy.state.qSDDCore
          (fun a : Fq params => star (Aop uv a)) (fun a : Fq params => star (Bop uv a))) ≤
        2 * delta := by
    refine le_of_eq_of_le (avgOver_congr _ _ _ fun uv => ?_)
      (addInU_pointMeasurement_snd_selfConsistency params strategy delta hssc).squaredDistanceBound
    have hpos := fun a => (strategy.pointMeasurement uv.2).toSubMeas.outcome_pos a
    simp only [Aop, Bop,
      (IsSelfAdjoint.of_nonneg (strategy.state.leftTensor_nonneg (hpos _))).star_eq,
      (IsSelfAdjoint.of_nonneg (strategy.state.rightTensor_nonneg (hpos _))).star_eq]
    rfl
  have hcs := Preliminaries.closenessOfInnerProduct_right strategy.state
    (uniformDistribution (Point params × Point params))
    (uniformDistribution_weight_sum_le_one (Point params × Point params))
    Aop Bop Cop (2 * delta) hAB (addInU_step1_C_contraction params strategy T)
  -- Collapse each `Σ_a Σ_h` onto the fiber `a = h v`, then factor the difference.
  have hmatch_pointwise : ∀ uv : Point params × Point params,
      (∑ a : Fq params, ∑ h : MIPStarRE.LDT.Polynomial params,
          strategy.state.ev (Aop uv a * Cop uv a h)) -
        (∑ a : Fq params, ∑ h : MIPStarRE.LDT.Polynomial params,
          strategy.state.ev (Bop uv a * Cop uv a h)) =
      ∑ h : MIPStarRE.LDT.Polynomial params,
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
        let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
        strategy.state.ev
          ((strategy.state.L Av - strategy.state.R Av) *
            (strategy.state.opTensor Mh (T.outcome h) * strategy.state.R Av)) := by
    intro uv
    have hCop : ∀ a h, h uv.2 ≠ a → Cop uv a h = 0 := fun _ _ ha => ite_eq_right ha
    rw [addInU_sum_fiber_collapse strategy.state uv.2 (fun a h => Aop uv a * Cop uv a h)
        fun a h ha => by rw [hCop a h ha, mul_zero],
      addInU_sum_fiber_collapse strategy.state uv.2 (fun a h => Bop uv a * Cop uv a h)
        fun a h ha => by rw [hCop a h ha, mul_zero],
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [show Cop uv (h uv.2) h = _ from ite_eq_left rfl, ← strategy.state.ev_sub, ← sub_mul]
    rfl
  rw [abs_sub_comm, addInU_cs_chain_step1_diff_eq params strategy T,
    avgOver_congr _ _ _ fun uv => (hmatch_pointwise uv).symm, avgOver_sub]
  exact hcs

/-- Cauchy--Schwarz contraction side condition for Step 2.

For a fixed `(u, v)`, the left-placed sandwiched sum
`Σ_a (L A^v_a · K_{u,v,a}) · (L A^v_a · K_{u,v,a})^* ≤ 1`
where `K_{u,v,a} = Σ_{h: h(v)=a} (M^u_h ⊗ T_h)`.  This is the C side condition
fed to `closenessOfInnerProduct_left` in the Step 2 raw bound proof. -/
theorem addInU_step2_C_contraction
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (uv : Point params × Point params) :
    ∑ a : Fq params,
        (∑ h : MIPStarRE.LDT.Polynomial params,
            (if h uv.2 = a then
              strategy.state.L ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
                strategy.state.opTensor
                  ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
                  (T.outcome h)
            else 0)) *
          star (∑ h : MIPStarRE.LDT.Polynomial params,
            (if h uv.2 = a then
              strategy.state.L ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
                strategy.state.opTensor
                  ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
                  (T.outcome h)
            else 0)) ≤
      (1 : K →L[ℂ] K) := by
  classical
  let Kf : Fq params → K →L[ℂ] K := fun a =>
    ∑ h ∈ Finset.univ.filter (fun h : MIPStarRE.LDT.Polynomial params => h uv.2 = a),
      strategy.state.opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
        (T.outcome h)
  let P : Fq params → K →L[ℂ] K := fun a =>
    strategy.state.L ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
  have hK0 : ∀ a, 0 ≤ Kf a := fun a => Finset.sum_nonneg fun h _ =>
    strategy.state.opTensor_nonneg
      ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome_pos h) (T.outcome_pos h)
  have hK1 : ∀ a, Kf a ≤ 1 := fun a =>
    addInU_filtered_sandwiched_tensor_sum_le_one params strategy T uv.1 uv.2 a
  have hP : ∀ a, IsSelfAdjoint (P a) := fun a => IsSelfAdjoint.of_nonneg
    (strategy.state.leftTensor_nonneg ((strategy.pointMeasurement uv.2).toSubMeas.outcome_pos a))
  refine le_of_eq_of_le (Finset.sum_congr rfl fun a _ => ?_)
    (addInU_sum_projection_sandwich_le_one Kf P
      (fun a => (MIPRE.LIDT.Co.sq_le_self (hK0 a) (hK1 a)).trans (hK1 a)) hP
      (fun a => (strategy.state.leftTensor_mul_leftTensor _ _).trans
        (congrArg strategy.state.L ((strategy.pointMeasurement uv.2).proj a)))
      ((strategy.state.leftTensor_finset_sum _ _).trans <| by
        rw [(strategy.pointMeasurement uv.2).toSubMeas.sum_eq_total,
          (strategy.pointMeasurement uv.2).total_eq_one, strategy.state.leftTensor_one]))
  rw [← Finset.sum_filter, ← Finset.mul_sum]
  change P a * Kf a * star (P a * Kf a) = P a * (Kf a * Kf a) * P a
  rw [star_mul, (hP a).star_eq, (IsSelfAdjoint.of_nonneg (hK0 a)).star_eq]
  simp only [mul_assoc]

/-- Raw `|Q₁ - Q₂| ≤ √(2δ)` bound for the add-in-u Step 2 Cauchy--Schwarz move.

Proves the paper's `eq:move-another` bound from
`references/ldt-paper/self_improvement.tex`, lines 279--297, as a completed
construction.  The proof combines the algebraic alignment
`addInU_cs_chain_step2_diff_eq` with the weighted Cauchy--Schwarz inner-product
bound `Preliminaries.closenessOfInnerProduct_left`, the `A^v` self-consistency
input via `addInU_pointMeasurement_snd_selfConsistency`, and the
filtered-tensor contraction `addInU_filtered_sandwiched_tensor_sum_le_one`. -/
theorem addInU_cs_chain_step2_abs_le_sqrt_two_delta
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (delta : ℝ)
    (hssc : strategy.state.BipartiteSSCRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta) :
    |addInUCSChainQ1 params strategy T - addInUCSChainQ2 params strategy T| ≤
      Real.sqrt (2 * delta) := by
  classical
  let Aop : Point params × Point params → Fq params → K →L[ℂ] K :=
    fun uv a => strategy.state.L ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
  let Bop : Point params × Point params → Fq params → K →L[ℂ] K :=
    fun uv a => strategy.state.R ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
  let Cop : Point params × Point params → Fq params → MIPStarRE.LDT.Polynomial params →
      K →L[ℂ] K :=
    fun uv a h =>
      if h uv.2 = a then
        strategy.state.L ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
          strategy.state.opTensor
            ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h) (T.outcome h)
      else 0
  have hcs := Preliminaries.closenessOfInnerProduct_left strategy.state
    (uniformDistribution (Point params × Point params))
    (uniformDistribution_weight_sum_le_one (Point params × Point params))
    Aop Bop Cop (2 * delta)
    (addInU_pointMeasurement_snd_selfConsistency params strategy delta hssc).squaredDistanceBound
    (addInU_step2_C_contraction params strategy T)
  have hmatch_pointwise : ∀ uv : Point params × Point params,
      (∑ a : Fq params, ∑ h : MIPStarRE.LDT.Polynomial params,
          strategy.state.ev (Cop uv a h * Aop uv a)) -
        (∑ a : Fq params, ∑ h : MIPStarRE.LDT.Polynomial params,
          strategy.state.ev (Cop uv a h * Bop uv a)) =
      ∑ h : MIPStarRE.LDT.Polynomial params,
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
        let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
        strategy.state.ev
          (strategy.state.L Av *
            (strategy.state.opTensor Mh (T.outcome h) *
              (strategy.state.L Av - strategy.state.R Av))) := by
    intro uv
    have hCop : ∀ a h, h uv.2 ≠ a → Cop uv a h = 0 := fun _ _ ha => ite_eq_right ha
    rw [addInU_sum_fiber_collapse strategy.state uv.2 (fun a h => Cop uv a h * Aop uv a)
        fun a h ha => by rw [hCop a h ha, zero_mul],
      addInU_sum_fiber_collapse strategy.state uv.2 (fun a h => Cop uv a h * Bop uv a)
        fun a h ha => by rw [hCop a h ha, zero_mul],
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [show Cop uv (h uv.2) h = _ from ite_eq_left rfl, ← strategy.state.ev_sub, ← mul_sub,
      mul_assoc]
    rfl
  rw [abs_sub_comm, addInU_cs_chain_step2_diff_eq params strategy T,
    avgOver_congr _ _ _ fun uv => (hmatch_pointwise uv).symm, avgOver_sub]
  exact hcs

end MIPRE.LIDT.Co.SelfImprovement

end

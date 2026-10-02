/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
SelfImprovement/Theorems/Results/AddInUStep12/Selected.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Results.AddInUStep12.Algebra
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Results.AddInUStep12.Raw

@[expose] public section

/-!
# Selected add-in-u Step 1/2 Cauchy--Schwarz bounds

Selected-family contraction inputs and raw `√(2δ)` estimates for the first two add-in-u moves
in the self-improvement chain: the counterpart of the vendored
`SelfImprovement/Theorems/Results/AddInUStep12/Selected.lean` (under
`MIPRE/Background/LIDT/MIPStarRE/LDT/`) in the port of `planning/c6b-plan.md` (milestone M10,
section "Port conventions"). It is the selected-pair twin of Co `AddInUStep12/Raw`: the sums run
over the selected pairs `(o, h) ∈ S_u` with an arbitrary outcome operator `M^u_o`, in place of
all polynomials `h` with the sandwiched operator.

## Contents

- `addInU_selected_filtered_tensor_sum_le_one`: the selected fibre mass
  `∑_{(o,h) ∈ S_u, h(v) = a} M^u_o ⊗ T_h` is at most `1`.
- `addInU_selected_step1_C_contraction`, `addInU_selected_step2_C_contraction`: the contraction
  side conditions `∑ₐ C_a^* C_a ≤ 1` and `∑ₐ C_a C_a^* ≤ 1` of the weighted Cauchy--Schwarz
  bounds, as inequalities in `K →L[ℂ] K`.
- `addInU_selected_cs_chain_step1_abs_le_sqrt_two_delta`,
  `addInU_selected_cs_chain_step2_abs_le_sqrt_two_delta`: `|Q₀ − Q₁| ≤ √(2δ)` and
  `|Q₁ − Q₂| ≤ √(2δ)` for the selected chain.

Every scalar is `strategy.state.ev` of a joint operator; `leftTensor A`, `rightTensor A` and
`opTensor A B` are `strategy.state.L A`, `strategy.state.R A` and `strategy.state.opTensor A B`,
and `Xᴴ` is `star X`. The vendored `addInU_selected_filtered_tensor_sum_le_one` names no state,
its `opTensor` being the Kronecker product on the carrier; here it takes the model
`(ψ : SymModel 𝔓 K)` as an explicit first argument (`S` is the selection), and its proof is the
keystone's `opTensor_le_one` after summing the fibre into `M^u_{tot} ⊗ T_{tot}`. The vendored
Hermitian facts `(Matrix.nonneg_iff_posSemidef.mp (…outcome_pos _)).isHermitian.eq` and the
`Matrix.conjTranspose_sum`/`conjTranspose_opTensor` computation of `Kᴴ = K` are
`(IsSelfAdjoint.of_nonneg …).star_eq`. The vendored proofs pass `strategy.isNormalized` to
`closenessOfInnerProduct_right`/`_left` (vendored lines 448 and 662); the ported Cauchy--Schwarz
bounds (Co `Preliminaries/SwitchSandwichPrep/InnerProduct`) have no normalization hypothesis, so
it is dropped, and the vendored `rw [hCop_zero, Matrix.mul_zero, ev_zero]` steps are `mul_zero`
(`zero_mul`) with `VecState.ev_zero`. No statement of the vendored file carries a swap, density
or normalization hypothesis.

The contraction proofs reuse Co `Raw`'s `addInU_sum_projection_sandwich_le_one`, which is why this
file imports Co `AddInUStep12/Raw` beside `Algebra`, where the vendored file imports `Algebra`
alone (the vendored `AddInUStep34AndTransfer/Factored` imports both). The two raw bounds share
the new `addInU_selected_sum_fiber_collapse`, the selected form of `Raw`'s
`addInU_sum_fiber_collapse`; the vendored proofs repeat it inline as `hcollapse`.

## Not ported

Every declaration of the vendored file has a counterpart here.

## New here

- `addInU_selected_sum_fiber_collapse`: the collapse of `∑ₐ ∑_{(o,h)}` onto the selected pairs
  with `a = h(v)`, shared by the two raw bounds.

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
open MIPStarRE.LDT.SelfImprovement (AddInUSelection addInUSelectionPairs)
open MIPRE.LIDT.Co.GlobalVariance (pointConditionedOutcomeOperatorAtPolynomial)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The selected fiber tensor mass is a contraction.

For fixed points `u, v` and a value `a`, the selected sum over pairs
`(o,h) ∈ S_u` with `h(v)=a` is bounded by the full product
`M^u_{\mathrm{tot}} ⊗ T_{\mathrm{tot}}`, hence by the identity. -/
theorem addInU_selected_filtered_tensor_sum_le_one
    {Outcome : Type*} [Fintype Outcome]
    (ψ : SymModel 𝔓 K)
    (params : Parameters) [FieldModel params.q]
    (M : IdxSubMeas (Point params) Outcome 𝔓)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (S : AddInUSelection params Outcome)
    (u v : Point params)
    (a : Fq params) :
    ∑ ah ∈ (addInUSelectionPairs params S u).filter (fun ah => ah.2 v = a),
        ψ.opTensor ((M u).outcome ah.1) (T.outcome ah.2) ≤
      (1 : K →L[ℂ] K) :=
  calc
    ∑ ah ∈ (addInUSelectionPairs params S u).filter (fun ah => ah.2 v = a),
        ψ.opTensor ((M u).outcome ah.1) (T.outcome ah.2)
        ≤ ∑ ah : Outcome × MIPStarRE.LDT.Polynomial params,
            ψ.opTensor ((M u).outcome ah.1) (T.outcome ah.2) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun ah _ _ =>
            ψ.opTensor_nonneg ((M u).outcome_pos ah.1) (T.outcome_pos ah.2)
    _ = ψ.opTensor (M u).total T.total := by
          rw [← (M u).sum_eq_total, ← T.sum_eq_total, ψ.opTensor_sum_left_univ]
          exact (Fintype.sum_prod_type' fun o h => ψ.opTensor ((M u).outcome o) (T.outcome h)).trans
            (Finset.sum_congr rfl fun o _ => (ψ.opTensor_sum_right_univ _ _).symm)
    _ ≤ 1 := ψ.opTensor_le_one (M u).total_nonneg (M u).total_le_one T.total_le_one

/-- Cauchy--Schwarz contraction side condition for selected Step 1.

For a fixed `(u, v)`, the selected fiber sum
`K_a = ∑_{(o,h) ∈ S_u, h(v)=a} M^u_o ⊗ T_h` is a contraction.  Sandwiching
by the right-register point projector `A^v_a` and summing over `a` is therefore
bounded by the identity. -/
theorem addInU_selected_step1_C_contraction
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (M : IdxSubMeas (Point params) Outcome 𝔓)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (S : AddInUSelection params Outcome)
    (uv : Point params × Point params) :
    ∑ a : Fq params,
        star (∑ ah ∈ (addInUSelectionPairs params S uv.1).filter
              (fun ah => ah.2 uv.2 = a),
            strategy.state.opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2) *
              strategy.state.R ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)) *
          (∑ ah ∈ (addInUSelectionPairs params S uv.1).filter
              (fun ah => ah.2 uv.2 = a),
            strategy.state.opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2) *
              strategy.state.R ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)) ≤
      (1 : K →L[ℂ] K) := by
  let Kf : Fq params → K →L[ℂ] K := fun a =>
    ∑ ah ∈ (addInUSelectionPairs params S uv.1).filter (fun ah => ah.2 uv.2 = a),
      strategy.state.opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2)
  let P : Fq params → K →L[ℂ] K := fun a =>
    strategy.state.R ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
  have hK0 : ∀ a, 0 ≤ Kf a := fun a => Finset.sum_nonneg fun ah _ =>
    strategy.state.opTensor_nonneg ((M uv.1).outcome_pos ah.1) (T.outcome_pos ah.2)
  have hK1 : ∀ a, Kf a ≤ 1 := fun a =>
    addInU_selected_filtered_tensor_sum_le_one strategy.state params M T S uv.1 uv.2 a
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
  rw [← Finset.sum_mul]
  change star (Kf a * P a) * (Kf a * P a) = P a * (Kf a * Kf a) * P a
  rw [star_mul, (hP a).star_eq, (IsSelfAdjoint.of_nonneg (hK0 a)).star_eq]
  simp only [mul_assoc]

/-- Cauchy--Schwarz contraction side condition for selected Step 2.

This is the left-register analogue of `addInU_selected_step1_C_contraction`:
for each fixed `(u,v)`, the operators
`C_a = A^v_a \otimes I · K_a`, with `K_a` the selected fiber tensor mass,
have `∑_a C_a C_a^* ≤ I`. -/
theorem addInU_selected_step2_C_contraction
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (M : IdxSubMeas (Point params) Outcome 𝔓)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (S : AddInUSelection params Outcome)
    (uv : Point params × Point params) :
    ∑ a : Fq params,
        (∑ ah ∈ (addInUSelectionPairs params S uv.1).filter
              (fun ah => ah.2 uv.2 = a),
            strategy.state.L ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
              strategy.state.opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2)) *
          star (∑ ah ∈ (addInUSelectionPairs params S uv.1).filter
              (fun ah => ah.2 uv.2 = a),
            strategy.state.L ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
              strategy.state.opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2)) ≤
      (1 : K →L[ℂ] K) := by
  let Kf : Fq params → K →L[ℂ] K := fun a =>
    ∑ ah ∈ (addInUSelectionPairs params S uv.1).filter (fun ah => ah.2 uv.2 = a),
      strategy.state.opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2)
  let P : Fq params → K →L[ℂ] K := fun a =>
    strategy.state.L ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
  have hK0 : ∀ a, 0 ≤ Kf a := fun a => Finset.sum_nonneg fun ah _ =>
    strategy.state.opTensor_nonneg ((M uv.1).outcome_pos ah.1) (T.outcome_pos ah.2)
  have hK1 : ∀ a, Kf a ≤ 1 := fun a =>
    addInU_selected_filtered_tensor_sum_le_one strategy.state params M T S uv.1 uv.2 a
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
  rw [← Finset.mul_sum]
  change P a * Kf a * star (P a * Kf a) = P a * (Kf a * Kf a) * P a
  rw [star_mul, (hP a).star_eq, (IsSelfAdjoint.of_nonneg (hK0 a)).star_eq]
  simp only [mul_assoc]

/-- Collapsing a double sum `∑ₐ ∑_{(o,h)} ev(X a (o,h))` onto the selected pairs with
`a = h(v)`, when `X a (o,h)` vanishes unless `(o,h) ∈ s` and `h(v) = a`: the step that turns the
fibre-indexed Cauchy--Schwarz sums of the two selected raw bounds into the single sums over the
selected pairs of the algebraic alignment. -/
theorem addInU_selected_sum_fiber_collapse {Outcome : Type*} [Fintype Outcome]
    {params : Parameters} [FieldModel params.q]
    (V : VecState K) (v : Point params)
    (s : Finset (Outcome × MIPStarRE.LDT.Polynomial params))
    (X : Fq params → Outcome × MIPStarRE.LDT.Polynomial params → K →L[ℂ] K)
    (hX : ∀ a ah, ah ∉ s.filter (fun ah => ah.2 v = a) → X a ah = 0) :
    ∑ a : Fq params, ∑ ah : Outcome × MIPStarRE.LDT.Polynomial params, V.ev (X a ah) =
      ∑ ah ∈ s, V.ev (X (ah.2 v) ah) := by
  rw [Finset.sum_comm, ← Finset.sum_subset (Finset.subset_univ s) fun ah _ hah => ?_]
  · refine Finset.sum_congr rfl fun ah _ => Finset.sum_eq_single (ah.2 v) (fun a _ ha => ?_)
      fun hm => (hm (Finset.mem_univ _)).elim
    rw [hX a ah fun hf => ha (Finset.mem_filter.1 hf).2.symm, V.ev_zero]
  · refine Finset.sum_eq_zero fun a _ => ?_
    rw [hX a ah fun hf => hah (Finset.mem_filter.1 hf).1, V.ev_zero]

/-- Raw selected `|Q₀ - Q₁| ≤ √(2δ)` bound for the first add-in-u move.

This is the selection-parametrized form of
`addInU_cs_chain_step1_abs_le_sqrt_two_delta`.  It applies the weighted
Cauchy--Schwarz estimate to the selected pairs `(o,h) ∈ S_u`; the contraction
side condition is `addInU_selected_step1_C_contraction`. -/
theorem addInU_selected_cs_chain_step1_abs_le_sqrt_two_delta
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (M : IdxSubMeas (Point params) Outcome 𝔓)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (S : AddInUSelection params Outcome)
    (delta : ℝ)
    (hssc : strategy.state.BipartiteSSCRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta) :
    |addInUSelectedCSChainQ0 params strategy M T S -
        addInUSelectedCSChainQ1 params strategy M T S| ≤
      Real.sqrt (2 * delta) := by
  classical
  let Aop : Point params × Point params → Fq params → K →L[ℂ] K :=
    fun uv a => strategy.state.L ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
  let Bop : Point params × Point params → Fq params → K →L[ℂ] K :=
    fun uv a => strategy.state.R ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
  let Cop : Point params × Point params → Fq params →
      Outcome × MIPStarRE.LDT.Polynomial params → K →L[ℂ] K :=
    fun uv a ah =>
      if ah ∈ (addInUSelectionPairs params S uv.1).filter (fun ah => ah.2 uv.2 = a) then
        strategy.state.opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2) *
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
    simp only [Aop, Bop, (IsSelfAdjoint.of_nonneg (strategy.state.leftTensor_nonneg (hpos _))).star_eq,
      (IsSelfAdjoint.of_nonneg (strategy.state.rightTensor_nonneg (hpos _))).star_eq]
    rfl
  have hC : ∀ uv : Point params × Point params,
      (∑ a : Fq params,
          star (∑ ah : Outcome × MIPStarRE.LDT.Polynomial params, Cop uv a ah) *
            (∑ ah : Outcome × MIPStarRE.LDT.Polynomial params, Cop uv a ah)) ≤ 1 := by
    intro uv
    simpa only [Cop, Finset.sum_ite_mem, Finset.univ_inter] using
      addInU_selected_step1_C_contraction params strategy M T S uv
  have hcs := Preliminaries.closenessOfInnerProduct_right strategy.state
    (uniformDistribution (Point params × Point params))
    (uniformDistribution_weight_sum_le_one (Point params × Point params))
    Aop Bop Cop (2 * delta) hAB hC
  have hmatch_pointwise : ∀ uv : Point params × Point params,
      (∑ a : Fq params, ∑ ah : Outcome × MIPStarRE.LDT.Polynomial params,
          strategy.state.ev (Aop uv a * Cop uv a ah)) -
        (∑ a : Fq params, ∑ ah : Outcome × MIPStarRE.LDT.Polynomial params,
          strategy.state.ev (Bop uv a * Cop uv a ah)) =
      ∑ ah ∈ addInUSelectionPairs params S uv.1,
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
        let Moh := (M uv.1).outcome ah.1
        strategy.state.ev
          ((strategy.state.L Av - strategy.state.R Av) *
            (strategy.state.opTensor Moh (T.outcome ah.2) * strategy.state.R Av)) := by
    intro uv
    have hCop : ∀ a ah, ah ∉ (addInUSelectionPairs params S uv.1).filter
        (fun ah => ah.2 uv.2 = a) → Cop uv a ah = 0 := fun _ _ h => ite_eq_right h
    rw [addInU_selected_sum_fiber_collapse strategy.state uv.2 _
        (fun a ah => Aop uv a * Cop uv a ah) fun a ah h => by rw [hCop a ah h, mul_zero],
      addInU_selected_sum_fiber_collapse strategy.state uv.2 _
        (fun a ah => Bop uv a * Cop uv a ah) fun a ah h => by rw [hCop a ah h, mul_zero],
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ah hah => ?_
    have hmem : ah ∈ (addInUSelectionPairs params S uv.1).filter
        (fun bh => bh.2 uv.2 = ah.2 uv.2) := Finset.mem_filter.2 ⟨hah, rfl⟩
    rw [show Cop uv (ah.2 uv.2) ah = _ from ite_eq_left hmem,
      ← strategy.state.ev_sub, ← sub_mul]
    rfl
  rw [abs_sub_comm, addInU_selected_cs_chain_step1_diff_eq params strategy M T S,
    avgOver_congr _ _ _ fun uv => (hmatch_pointwise uv).symm, avgOver_sub]
  exact hcs

/-- Raw selected `|Q₁ - Q₂| ≤ √(2δ)` bound for the second add-in-u move.

This is the selection-parametrized form of
`addInU_cs_chain_step2_abs_le_sqrt_two_delta`.  It uses the left-action
Cauchy--Schwarz estimate with the selected Step 2 contraction side condition. -/
theorem addInU_selected_cs_chain_step2_abs_le_sqrt_two_delta
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (M : IdxSubMeas (Point params) Outcome 𝔓)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (S : AddInUSelection params Outcome)
    (delta : ℝ)
    (hssc : strategy.state.BipartiteSSCRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta) :
    |addInUSelectedCSChainQ1 params strategy M T S -
        addInUSelectedCSChainQ2 params strategy M T S| ≤
      Real.sqrt (2 * delta) := by
  classical
  let Aop : Point params × Point params → Fq params → K →L[ℂ] K :=
    fun uv a => strategy.state.L ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
  let Bop : Point params × Point params → Fq params → K →L[ℂ] K :=
    fun uv a => strategy.state.R ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
  let Cop : Point params × Point params → Fq params →
      Outcome × MIPStarRE.LDT.Polynomial params → K →L[ℂ] K :=
    fun uv a ah =>
      if ah ∈ (addInUSelectionPairs params S uv.1).filter (fun ah => ah.2 uv.2 = a) then
        strategy.state.L ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
          strategy.state.opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2)
      else 0
  have hC : ∀ uv : Point params × Point params,
      (∑ a : Fq params,
          (∑ ah : Outcome × MIPStarRE.LDT.Polynomial params, Cop uv a ah) *
            star (∑ ah : Outcome × MIPStarRE.LDT.Polynomial params, Cop uv a ah)) ≤ 1 := by
    intro uv
    simpa only [Cop, Finset.sum_ite_mem, Finset.univ_inter] using
      addInU_selected_step2_C_contraction params strategy M T S uv
  have hcs := Preliminaries.closenessOfInnerProduct_left strategy.state
    (uniformDistribution (Point params × Point params))
    (uniformDistribution_weight_sum_le_one (Point params × Point params))
    Aop Bop Cop (2 * delta)
    (addInU_pointMeasurement_snd_selfConsistency params strategy delta hssc).squaredDistanceBound
    hC
  have hmatch_pointwise : ∀ uv : Point params × Point params,
      (∑ a : Fq params, ∑ ah : Outcome × MIPStarRE.LDT.Polynomial params,
          strategy.state.ev (Cop uv a ah * Aop uv a)) -
        (∑ a : Fq params, ∑ ah : Outcome × MIPStarRE.LDT.Polynomial params,
          strategy.state.ev (Cop uv a ah * Bop uv a)) =
      ∑ ah ∈ addInUSelectionPairs params S uv.1,
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
        let Moh := (M uv.1).outcome ah.1
        strategy.state.ev
          (strategy.state.L Av *
            (strategy.state.opTensor Moh (T.outcome ah.2) *
              (strategy.state.L Av - strategy.state.R Av))) := by
    intro uv
    have hCop : ∀ a ah, ah ∉ (addInUSelectionPairs params S uv.1).filter
        (fun ah => ah.2 uv.2 = a) → Cop uv a ah = 0 := fun _ _ h => ite_eq_right h
    rw [addInU_selected_sum_fiber_collapse strategy.state uv.2 _
        (fun a ah => Cop uv a ah * Aop uv a) fun a ah h => by rw [hCop a ah h, zero_mul],
      addInU_selected_sum_fiber_collapse strategy.state uv.2 _
        (fun a ah => Cop uv a ah * Bop uv a) fun a ah h => by rw [hCop a ah h, zero_mul],
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ah hah => ?_
    have hmem : ah ∈ (addInUSelectionPairs params S uv.1).filter
        (fun bh => bh.2 uv.2 = ah.2 uv.2) := Finset.mem_filter.2 ⟨hah, rfl⟩
    rw [show Cop uv (ah.2 uv.2) ah = _ from ite_eq_left hmem,
      ← strategy.state.ev_sub, ← mul_sub, mul_assoc]
    rfl
  rw [abs_sub_comm, addInU_selected_cs_chain_step2_diff_eq params strategy M T S,
    avgOver_congr _ _ _ fun uv => (hmatch_pointwise uv).symm, avgOver_sub]
  exact hcs

end MIPRE.LIDT.Co.SelfImprovement

end

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
SelfImprovement/Theorems/Results/HelperCompleteness/FiberBounds.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Basic.SubMeasurementFamilies
public import MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.ParametersFiniteAnswers
public import MIPRE.Background.LIDT.Co.Preliminaries.SelfConsistency.DataProcessing
public import MIPRE.Background.LIDT.MIPStarRE.LDT.SelfImprovement.Theorems.Thresholds.Final
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Statements
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Results.CommonHelpers

@[expose] public section

/-!
# Helper completeness: fiber operators and Cauchy--Schwarz bounds

The fiber operator `T_[h(u)=a]` of the helper-completeness proof, the pointwise operator
inequalities and the averaged Cauchy--Schwarz estimates of its two analytic moves: the
counterpart of the vendored
`SelfImprovement/Theorems/Results/HelperCompleteness/FiberBounds.lean` (under
`MIPRE/Background/LIDT/MIPStarRE/LDT/`) in the port of `planning/c6b-plan.md` (milestone M10,
section "Port conventions").

A strategy is a `SymStrat params 𝔓 K`. The fiber operator and its bounds live in the local
algebra `𝔓`, where their positivity is proved; the joint operators are `strategy.state.L`,
`strategy.state.opTensor` in `K →L[ℂ] K`.

- `helper_second_move_first_factor_operator_le_one` places without a strategy, so it takes the
  model `(S : SymModel 𝔓 K)` as an explicit first argument, as M6's placement lemmas do.
- The vendored `ev_one_of_isNormalized strategy.state strategy.isNormalized` is
  `strategy.state.ev_one_of_isNormalized`, a theorem of the model.
- The vendored entrywise `kronecker_sub_right` steps are `mul_sub` with the keystone's
  `rightTensor_sub` and `rightTensor_one`, and the adjoint computations of the Cauchy--Schwarz
  step are the keystone's `conjTranspose_opTensor`, `opTensor_mul`, `leftTensor_mul_opTensor`
  and `leftTensor_mul_leftTensor`; the `Matrix.PosSemidef` self-adjointness arguments are
  `IsSelfAdjoint.of_nonneg`.

The vendored file imports `Basic/ParametersFiniteAnswers.lean` (for `polynomial_sum_fiberwise`)
and `SelfImprovement/Theorems/Thresholds/Final.lean`, both classical and without a Co file; so
does this one.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/self_improvement.tex` lines 359--394
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.SelfImprovement

open MIPStarRE.LDT (Parameters FieldModel Point Fq avgOver uniformDistribution
  avgOver_congr avgOver_mono avgOver_sub avgOver_uniform_le_const polynomial_sum_fiberwise)
open MIPRE.LIDT.Co.GlobalVariance (pointConditionedOutcomeOperatorAtPolynomial)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The fiber operator `T_[h(u)=a]` in the helper-completeness proof.

It is the sum of all SDP-measurement outcomes indexed by polynomials whose
value at the point `u` is `a`. -/
noncomputable def helperFiberOperator
    (params : Parameters)
    [FieldModel params.q]
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (u : Point params) (a : Fq params) : 𝔓 :=
  ∑ h ∈ Finset.univ.filter (fun h : MIPStarRE.LDT.Polynomial params => h u = a), T.outcome h

/-- The helper fiber operator is positive. -/
theorem helperFiberOperator_nonneg
    (params : Parameters)
    [FieldModel params.q]
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (u : Point params) (a : Fq params) :
    0 ≤ helperFiberOperator params T u a :=
  Finset.sum_nonneg fun h _ => T.outcome_pos h

/-- The helper fiber operator is bounded by the identity. -/
theorem helperFiberOperator_le_one
    (params : Parameters)
    [FieldModel params.q]
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (u : Point params) (a : Fq params) :
    helperFiberOperator params T u a ≤ 1 :=
  calc
    helperFiberOperator params T u a
        ≤ ∑ h : MIPStarRE.LDT.Polynomial params, T.outcome h :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset _ _) (fun h _ _ => T.outcome_pos h)
    _ = T.total := T.sum_eq_total
    _ ≤ 1 := T.total_le_one

omit [StarOrderedRing 𝔓] in
/-- The fiber operators over all values at a fixed point sum to the total SDP
submeasurement operator. -/
theorem helperFiberOperator_sum_eq_total
    (params : Parameters)
    [FieldModel params.q]
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (u : Point params) :
    (∑ a : Fq params, helperFiberOperator params T u a) = T.total :=
  (polynomial_sum_fiberwise params u T.outcome).symm.trans T.sum_eq_total

/-- Pointwise operator form of the identity bound for the first
Cauchy--Schwarz factor in the second helper-completeness move.

At a fixed point `u`, the fiber operators form a submeasurement after grouping
by the value `h(u)`.  Thus `Σ_a T_[h(u)=a]^2 ≤ Σ_a T_[h(u)=a] = T.total ≤ I`. -/
theorem helper_second_move_first_factor_operator_le_one
    (S : SymModel 𝔓 K)
    (params : Parameters)
    [FieldModel params.q]
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (u : Point params) :
    (∑ a : Fq params,
      let Tfiber := helperFiberOperator params T u a
      S.L (Tfiber * Tfiber)) ≤ 1 :=
  calc
    (∑ a : Fq params,
      let Tfiber := helperFiberOperator params T u a
      S.L (Tfiber * Tfiber))
        ≤ ∑ a : Fq params, S.L (helperFiberOperator params T u a) :=
          Finset.sum_le_sum fun a _ => S.leftTensor_mono (sq_le_self
            (helperFiberOperator_nonneg params T u a) (helperFiberOperator_le_one params T u a))
    _ = S.L T.total := by
        rw [S.leftTensor_finset_sum, helperFiberOperator_sum_eq_total]
    _ ≤ 1 := S.leftTensor_le_one T.total_le_one

/-- The first Cauchy--Schwarz factor in the second helper-completeness move is
bounded by one.

This is the Lean form of the paper's assertion, following
`eq:mysterious-case-of-the-disappearing-a`, that
`E_u Σ_a ⟨ψ, T_[h(u)=a]^2 ⊗ I ψ⟩ ≤ 1`. -/
theorem helper_second_move_first_factor_le_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    avgOver (uniformDistribution (Point params)) (fun u =>
      ∑ a : Fq params,
        let Tfiber := helperFiberOperator params T u a
        strategy.state.ev (strategy.state.L (Tfiber * Tfiber))) ≤
      1 := by
  refine avgOver_uniform_le_const _ 1 fun u => ?_
  have hev := strategy.state.ev_mono _ _
    (helper_second_move_first_factor_operator_le_one strategy.state params T u)
  rwa [VecState.ev_sum, VecState.ev_one_of_isNormalized] at hev

/-- Pointwise comparison between the projective residual in the second
Cauchy--Schwarz move and the bipartite strong self-consistency defect.

Projectivity gives `(A^u_a)^2 = A^u_a` and `(I - A^u_a)^2 = I - A^u_a`.
After summing over `a`, the residual is the one-register total mass minus the
diagonal cross-register overlap, and hence is bounded by the `max 0` defining
`qBipartiteSSCDefect`. -/
theorem helper_second_move_second_factor_pointwise_le_qBipartiteSSCDefect
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (u : Point params) :
    (∑ a : Fq params,
      let Au := (strategy.pointMeasurement u).outcome a
      strategy.state.ev (strategy.state.opTensor (Au * Au) ((1 - Au) * (1 - Au)))) ≤
      strategy.state.qBipartiteSSCDefect ((strategy.pointMeasurement u).toSubMeas) := by
  set S := strategy.state
  set P := strategy.pointMeasurement u
  have hterm (a : Fq params) :
      S.ev (S.opTensor (P.outcome a * P.outcome a) ((1 - P.outcome a) * (1 - P.outcome a))) =
        S.ev (S.L (P.outcome a)) - S.ev (S.opTensor (P.outcome a) (P.outcome a)) := by
    have hproj : P.outcome a * P.outcome a = P.outcome a := P.proj a
    have hsq : (1 - P.outcome a) * (1 - P.outcome a) = 1 - P.outcome a := by
      rw [sub_mul, one_mul, mul_sub, mul_one, hproj, sub_self, sub_zero]
    rw [hproj, hsq, ← VecState.ev_sub, SymModel.opTensor, SymModel.opTensor,
      ← S.rightTensor_sub, S.rightTensor_one, mul_sub, mul_one]
  have hresidual :
      (∑ a : Fq params,
        S.ev (S.opTensor (P.outcome a * P.outcome a) ((1 - P.outcome a) * (1 - P.outcome a)))) =
        S.ev (S.L P.toSubMeas.total) -
          ∑ a : Fq params, S.ev (S.opTensor (P.outcome a) (P.outcome a)) := by
    rw [Finset.sum_congr rfl fun a _ => hterm a, Finset.sum_sub_distrib, ← VecState.ev_sum,
      S.leftTensor_finset_sum, P.toSubMeas.sum_eq_total]
  exact hresidual.trans_le (le_max_right 0 _)

/-- The second Cauchy--Schwarz factor in the second helper-completeness move is
bounded by the bipartite strong self-consistency error.

This is the Lean form of the paper's assertion that
`E_u Σ_a ⟨ψ, A^u_a ⊗ (I-A^u_a) ψ⟩ ≤ delta`. -/
theorem helper_second_move_second_factor_le_delta
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (delta : ℝ)
    (hssc : strategy.state.BipartiteSSCRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta) :
    avgOver (uniformDistribution (Point params)) (fun u =>
      ∑ a : Fq params,
        let Au := (strategy.pointMeasurement u).outcome a
        strategy.state.ev (strategy.state.opTensor (Au * Au) ((1 - Au) * (1 - Au)))) ≤
      delta :=
  (avgOver_mono _ _ _ fun u =>
    helper_second_move_second_factor_pointwise_le_qBipartiteSSCDefect params strategy u).trans
    hssc.overlapBound

/-- Pointwise operator form of the identity bound for the second
Cauchy--Schwarz factor in the first helper-completeness move.

For a fixed point `u`, each fiber operator satisfies
`0 ≤ T_[h(u)=a] ≤ I`, hence `T_[h(u)=a]^2 ≤ I`.  Sandwiching by the
projection `A^u_a` gives
`A^u_a T_[h(u)=a]^2 A^u_a ≤ A^u_a`, and the projective measurement
`A^u` sums to the identity. -/
theorem helper_first_move_second_factor_operator_le_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (u : Point params) :
    (∑ a : Fq params,
      let Au := (strategy.pointMeasurement u).outcome a
      let Tfiber := helperFiberOperator params T u a
      strategy.state.L (Au * (Tfiber * Tfiber) * Au)) ≤ 1 := by
  set S := strategy.state
  set P := strategy.pointMeasurement u
  have hterm (a : Fq params) :
      P.outcome a * (helperFiberOperator params T u a * helperFiberOperator params T u a) *
        P.outcome a ≤ P.outcome a := by
    have hT_sq_le_one :
        helperFiberOperator params T u a * helperFiberOperator params T u a ≤ 1 :=
      (sq_le_self (helperFiberOperator_nonneg params T u a)
        (helperFiberOperator_le_one params T u a)).trans
        (helperFiberOperator_le_one params T u a)
    have hAu : IsSelfAdjoint (P.outcome a) := IsSelfAdjoint.of_nonneg (P.outcome_pos a)
    calc
      P.outcome a * (helperFiberOperator params T u a * helperFiberOperator params T u a) *
          P.outcome a
          ≤ P.outcome a * 1 * P.outcome a := hAu.conjugate_le_conjugate hT_sq_le_one
      _ = P.outcome a := by rw [mul_one, P.proj a]
  calc
    (∑ a : Fq params,
      let Au := P.outcome a
      let Tfiber := helperFiberOperator params T u a
      S.L (Au * (Tfiber * Tfiber) * Au))
        ≤ ∑ a : Fq params, S.L (P.outcome a) :=
          Finset.sum_le_sum fun a _ => S.leftTensor_mono (hterm a)
    _ = 1 := by
        rw [S.leftTensor_finset_sum, P.toSubMeas.sum_eq_total, P.total_eq_one, map_one]

/-- The second Cauchy--Schwarz factor in the first helper-completeness move is
bounded by the identity contribution.

This is the Lean form of the paper's assertion, following
`eq:yet-another-move-a`, that
`E_u Σ_a ⟨ψ, (A^u_a T_[h(u)=a]^2 A^u_a) ⊗ I ψ⟩ ≤ 1`. -/
theorem helper_first_move_second_factor_le_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    avgOver (uniformDistribution (Point params)) (fun u =>
      ∑ a : Fq params,
        let Au := (strategy.pointMeasurement u).outcome a
        let Tfiber := helperFiberOperator params T u a
        strategy.state.ev (strategy.state.L (Au * (Tfiber * Tfiber) * Au))) ≤
      1 := by
  refine avgOver_uniform_le_const _ 1 fun u => ?_
  have hev := strategy.state.ev_mono _ _
    (helper_first_move_second_factor_operator_le_one params strategy T u)
  rwa [VecState.ev_sum, VecState.ev_one_of_isNormalized] at hev

/-- The scalar expression after the first Cauchy--Schwarz move in helper
completeness.

This is
`E_u Σ_a ⟨ψ, (T_[h(u)=a] A^u_a) ⊗ A^u_a ψ⟩`, the right-hand side of
`eq:yet-another-move-a` in the paper.  The fiber
`T_[h(u)=a]` is represented by the finite sum over polynomials whose value at
`u` is `a`. -/
noncomputable def helperFirstMovedCompletenessQuantity
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) : ℝ :=
  avgOver (uniformDistribution (Point params)) (fun u =>
    ∑ a : Fq params,
      let Au := (strategy.pointMeasurement u).outcome a
      let Tfiber := helperFiberOperator params T u a
      strategy.state.ev (strategy.state.opTensor (Tfiber * Au) Au))

/-- The scalar expression after removing the remaining point-measurement
operator in helper completeness.

This is
`E_u Σ_h ⟨ψ, (T_h A^u_{h(u)}) ⊗ I ψ⟩`.  Complementary slackness identifies this
quantity with the dual mass `⟨ψ, Z ⊗ I ψ⟩`. -/
noncomputable def helperLinearizedCompletenessQuantity
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) : ℝ :=
  avgOver (uniformDistribution (Point params)) (fun u =>
    ∑ h : MIPStarRE.LDT.Polynomial params,
      strategy.state.ev
        (strategy.state.L
          (T.outcome h *
            pointConditionedOutcomeOperatorAtPolynomial params strategy h u)))

/-- Fiberwise form of the linearized helper-completeness quantity.

The expression
`E_u Σ_h ⟨ψ, (T_h A^u_{h(u)}) ⊗ I ψ⟩` may equivalently be grouped by the value
`a = h(u)`, giving
`E_u Σ_a ⟨ψ, (T_[h(u)=a] A^u_a) ⊗ I ψ⟩`.  This is the algebraic rewrite used
after `eq:mysterious-case-of-the-disappearing-a` in the paper. -/
theorem helper_linearized_completeness_quantity_eq_fiber_sum
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    helperLinearizedCompletenessQuantity params strategy T =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ a : Fq params,
          let Au := (strategy.pointMeasurement u).outcome a
          let Tfiber := helperFiberOperator params T u a
          strategy.state.ev (strategy.state.L (Tfiber * Au))) := by
  unfold helperLinearizedCompletenessQuantity
  refine avgOver_congr _ _ _ fun u => ?_
  rw [polynomial_sum_fiberwise params u]
  refine Finset.sum_congr rfl fun a _ => ?_
  dsimp only
  rw [← VecState.ev_finset_sum, strategy.state.leftTensor_finset_sum, helperFiberOperator,
    Finset.sum_mul]
  refine congrArg (fun X => strategy.state.ev (strategy.state.L X))
    (Finset.sum_congr rfl fun h hh => ?_)
  rw [(Finset.mem_filter.1 hh).2.symm]
  rfl

/-- Pointwise Cauchy--Schwarz estimate for the second helper-completeness move.

For fixed `u` and `a`, this bounds the residual term
`⟨ψ, (T_[h(u)=a] A^u_a) ⊗ (I - A^u_a) ψ⟩` by the product of the two square-root
factors appearing after `eq:mysterious-case-of-the-disappearing-a`. -/
theorem helper_second_move_pointwise_abs_le_sqrt
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (u : Point params) (a : Fq params) :
    |strategy.state.ev (strategy.state.opTensor
      (helperFiberOperator params T u a * (strategy.pointMeasurement u).outcome a)
      (1 - (strategy.pointMeasurement u).outcome a))| ≤
      Real.sqrt (strategy.state.ev (strategy.state.L
        (helperFiberOperator params T u a * helperFiberOperator params T u a))) *
      Real.sqrt (strategy.state.ev (strategy.state.opTensor
        ((strategy.pointMeasurement u).outcome a * (strategy.pointMeasurement u).outcome a)
        ((1 - (strategy.pointMeasurement u).outcome a) *
          (1 - (strategy.pointMeasurement u).outcome a)))) := by
  set S := strategy.state
  set Tf := helperFiberOperator params T u a
  set Au := (strategy.pointMeasurement u).outcome a
  have hTf : star Tf = Tf :=
    (IsSelfAdjoint.of_nonneg (helperFiberOperator_nonneg params T u a)).star_eq
  have hAu : star Au = Au := SubMeas.outcome_hermitian (strategy.pointMeasurement u).toSubMeas a
  have hOneSub : star (1 - Au) = 1 - Au := by rw [star_sub, star_one, hAu]
  have hcs := S.toVecState.ev_abs_mul_le_sqrt (S.L Tf) (S.opTensor Au (1 - Au))
  rwa [S.leftTensor_mul_opTensor, S.leftTensor_conjTranspose, hTf, S.leftTensor_mul_leftTensor,
    S.conjTranspose_opTensor, hAu, hOneSub, S.opTensor_mul] at hcs

/-- The second Cauchy--Schwarz move in the helper-completeness proof.

Assuming bipartite strong self-consistency of the point measurement with error
`delta`, the first-moved helper-completeness expression
`E_u Σ_a ⟨ψ, (T_[h(u)=a] A^u_a) ⊗ A^u_a ψ⟩` differs from the linearized
expression `E_u Σ_a ⟨ψ, (T_[h(u)=a] A^u_a) ⊗ I ψ⟩` by at most `sqrt delta`.
The first factor is bounded by the grouped submeasurement estimate, and the
second is exactly the projective residual controlled by self-consistency. -/
theorem helper_second_move_abs_sub_first_moved_le_sqrt_delta
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (delta : ℝ)
    (hssc : strategy.state.BipartiteSSCRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta) :
    |helperLinearizedCompletenessQuantity params strategy T -
      helperFirstMovedCompletenessQuantity params strategy T| ≤
      Real.sqrt delta := by
  set S := strategy.state
  let t : Point params → Fq params → ℝ := fun u a =>
    S.ev (S.opTensor (helperFiberOperator params T u a * (strategy.pointMeasurement u).outcome a)
      (1 - (strategy.pointMeasurement u).outcome a))
  let x : Point params → Fq params → ℝ := fun u a =>
    S.ev (S.L (helperFiberOperator params T u a * helperFiberOperator params T u a))
  let y : Point params → Fq params → ℝ := fun u a =>
    S.ev (S.opTensor
      ((strategy.pointMeasurement u).outcome a * (strategy.pointMeasurement u).outcome a)
      ((1 - (strategy.pointMeasurement u).outcome a) *
        (1 - (strategy.pointMeasurement u).outcome a)))
  have hx (u : Point params) (a : Fq params) : 0 ≤ x u a :=
    S.ev_nonneg_of_psd _ (S.leftTensor_nonneg
      (IsSelfAdjoint.of_nonneg (helperFiberOperator_nonneg params T u a)).mul_self_nonneg)
  have hy (u : Point params) (a : Fq params) : 0 ≤ y u a := by
    have hAu : IsSelfAdjoint ((strategy.pointMeasurement u).outcome a) :=
      IsSelfAdjoint.of_nonneg ((strategy.pointMeasurement u).outcome_pos a)
    exact S.ev_nonneg_of_psd _ (S.opTensor_nonneg hAu.mul_self_nonneg
      ((IsSelfAdjoint.one 𝔓).sub hAu).mul_self_nonneg)
  have hweighted := MIPStarRE.LDT.Preliminaries.weightedFinsetCauchySchwarz
    (uniformDistribution (Point params)) t x y
    (fun u a => helper_second_move_pointwise_abs_le_sqrt params strategy T u a) hx hy
  have hgap :
      avgOver (uniformDistribution (Point params)) (fun u => ∑ a : Fq params, t u a) =
        helperLinearizedCompletenessQuantity params strategy T -
          helperFirstMovedCompletenessQuantity params strategy T := by
    rw [helper_linearized_completeness_quantity_eq_fiber_sum, helperFirstMovedCompletenessQuantity,
      ← avgOver_sub]
    refine avgOver_congr _ _ _ fun u => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [t]
    rw [← VecState.ev_sub, SymModel.opTensor, SymModel.opTensor, ← S.rightTensor_sub,
      S.rightTensor_one, mul_sub, mul_one]
  have hx_avg : avgOver (uniformDistribution (Point params))
      (fun u => ∑ a : Fq params, x u a) ≤ 1 :=
    helper_second_move_first_factor_le_one params strategy T
  have hy_avg : avgOver (uniformDistribution (Point params))
      (fun u => ∑ a : Fq params, y u a) ≤ delta :=
    helper_second_move_second_factor_le_delta params strategy delta hssc
  rw [← hgap]
  refine hweighted.trans ?_
  calc
    Real.sqrt (avgOver (uniformDistribution (Point params)) (fun u => ∑ a : Fq params, x u a)) *
        Real.sqrt (avgOver (uniformDistribution (Point params)) (fun u => ∑ a : Fq params, y u a))
        ≤ 1 * Real.sqrt delta :=
          mul_le_mul (Real.sqrt_le_one.2 hx_avg) (Real.sqrt_le_sqrt hy_avg)
            (Real.sqrt_nonneg _) zero_le_one
    _ = Real.sqrt delta := one_mul _

end MIPRE.LIDT.Co.SelfImprovement

end

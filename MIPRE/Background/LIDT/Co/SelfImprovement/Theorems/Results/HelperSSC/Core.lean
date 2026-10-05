/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
SelfImprovement/Theorems/Results/HelperSSC/Core.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Results.AddInUStep34AndTransfer.Transfer
public import MIPStarRE.LDT.SelfImprovement.Theorems.Results.HelperSSC.Core

@[expose] public section

/-!
# Helper strong self-consistency bounds: core reductions

Core bound structures, the bare off-diagonal quantity, and the two variance-swap identities used
in the helper strong self-consistency chain: the counterpart of the vendored
`SelfImprovement/Theorems/Results/HelperSSC/Core.lean` (under
`MIPRE/Background/LIDT/MIPStarRE/LDT/`) in the port of `planning/c6b-plan.md` (milestone M10,
section "Port conventions").

## Contents

- `HelperStrongSelfConsistencyBounds`: the four scalar transport bounds along
  `Q₀ → Q₁ → Q₂ → Q₃ → Q₄` and the residual lower bound, and its constructor
  `helper_strong_self_consistency_bounds_of_selfConsistency_localVariance`.
- `helperOffDiagonalBareQuantity` and `helperOffDiagonalBareQuantity_le_one`.
- The selected-chain endpoints `Q₄`, `Q₃`, `Q₂` at the off-diagonal selection, identified with
  the indicator quantities of Co `AddInUDiagonalAndDefs/Residual`, and the two off-diagonal
  variance swaps.

A strategy is a `SymStrat params 𝔓 K`; the polynomial submeasurement `T` and the point projectors
live in `𝔓`, and every scalar is `strategy.state.ev` of a joint operator
`strategy.state.opTensor X Y`. `subMeasMass strategy.state Hhat.liftLeft` is
`strategy.state.subMeasMass (Hhat.liftLeft strategy.state)`, and `BipartiteSSCRel strategy.state`
is the `SymModel` declaration. The vendored `helperOffDiagonalBareQuantity_le_one` used
`strategy.isNormalized` to evaluate `ev 1`; here `S.ev_one_of_isNormalized` takes no hypothesis,
so no statement changed. The conjugation step of `Q₃` uses `star_mul` and the keystone's
`conjTranspose_opTensor` in place of the matrix `conjTranspose` lemmas. The file sets no option,
the vendored file-wide `respectTransparency false` not being needed.

The selection `helperOffDiagonalVarianceSwapSelection` and its pair-sum identity are classical
(a set of polynomial pairs and a scalar sum), so the vendored module is imported for them; its
own import, the vendored `AddInUStep34AndTransfer/Transfer`, is already imported by Co
`Transfer`.

## Not ported

- `helperOffDiagonalVarianceSwapSelection`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/self_improvement.tex`
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.SelfImprovement

open MIPStarRE.LDT (Parameters FieldModel Point avgOver uniformDistribution avgOver_congr
  avgOver_uniform_le_const avgOver_uniform_fst avgOver_uniform_prod avgOver_comm avgOver_sum
  avgOver_finset_sum avgOver_mul_const)
open MIPStarRE.LDT.GlobalVariance (localVarianceOfPointsError)
open MIPStarRE.LDT.SelfImprovement (AddInUSelection addInUSelectionPairs
  selfConsistencyAddInUSelection selfImprovementVarianceError addInUError
  helperOffDiagonalVarianceSwapSelection)
open MIPRE.LIDT.Co.GlobalVariance (pointConditionedOutcomeOperatorAtPolynomial
  localVarianceDeviationAtPolynomial globalVarianceDeviation_sum_le_of_localVarianceDeviation_sum_le)

/-- Upstream keeps this helper `private` since its Lean-module port (`LionSR/MIPStarRE` at `5fc363b`); the port carries its own copy, with upstream's proof. -/
theorem helperOffDiagonalVarianceSwapSelection_pairs_sum
    (params : Parameters) [FieldModel params.q]
    (u : Point params)
    (F : Polynomial params → Polynomial params → ℝ) :
    ∑ hh ∈ addInUSelectionPairs params
        (helperOffDiagonalVarianceSwapSelection params) u,
        F hh.1 hh.2 =
      ∑ h : Polynomial params,
        ∑ h' ∈ (Finset.univ : Finset (Polynomial params)).erase h,
          (if h u = h' u then (1 : ℝ) else 0) * F h' h := by
  classical
  unfold addInUSelectionPairs helperOffDiagonalVarianceSwapSelection
  rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro h _
  rw [← Finset.filter_ne' Finset.univ h, Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro h' _
  by_cases hne : h' ≠ h
  · by_cases heq : h u = h' u
    · rw [ite_eq_left ⟨hne, heq⟩, ite_eq_left hne, ite_eq_left heq, one_mul]
    · rw [ite_eq_left hne, ite_eq_right heq]
      simp only [Set.mem_ofPred_eq, heq, and_false, ite_false]
      ring
  · have hheq : h' = h := not_not.mp hne
    subst h'
    simp only [Set.mem_ofPred_eq, ne_eq, not_true_eq_false, false_and, ite_false]

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Named intermediate bounds for the helper-stage strong self-consistency proof.

Paper origin: `references/ldt-paper/self_improvement.tex:255-603`
(`\label{item:self-improvement-self}` and the subsequent add-in-`u`,
self-consistency, and variance-swap chain).

This is an internal record for the helper-stage strong self-consistency proof.  It is not a
hypothesis of a source-labelled theorem.  Its fields are derived from the add-in-`u`,
self-consistency, and global-variance estimates and are not passed across the public statement
of `lem:self-improvement-helper`.

These fields isolate the paper-side intermediate estimates in the proof of
`item:self-improvement-self` once the reduced helper conclusion is fixed:

1. the four scalar transport bounds along the chain
   `Q₀ \to Q₁ \to Q₂ \to Q₃ \to Q₄`, and
2. the final lower bound on the released right-hand side before the arithmetic
   absorption into `selfImprovementHelperError`. -/
structure HelperStrongSelfConsistencyBounds
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓)
    (Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (eps delta : ℝ) : Prop where
  /-- Paper `eq:move-one`: the `Q₀ \to Q₁` transport bound. -/
  step01Bound :
    |addInUCSChainQ0 params strategy T.toSubMeas -
        addInUCSChainQ1 params strategy T.toSubMeas| ≤
      Real.sqrt (2 * delta)
  /-- Paper `eq:move-another`: the `Q₁ \to Q₂` transport bound. -/
  step12Bound :
    |addInUCSChainQ1 params strategy T.toSubMeas -
        addInUCSChainQ2 params strategy T.toSubMeas| ≤
      Real.sqrt (2 * delta)
  /-- Paper `eq:change-one`: the `Q₂ \to Q₃` variance transport bound. -/
  step23Bound :
    |addInUCSChainQ2 params strategy T.toSubMeas -
        addInUCSChainQ3 params strategy T.toSubMeas| ≤
      Real.sqrt (selfImprovementVarianceError params eps delta)
  /-- Paper `eq:change-another`: the `Q₃ \to Q₄` variance transport bound. -/
  step34Bound :
    |addInUCSChainQ3 params strategy T.toSubMeas -
        addInUCSChainQ4 params strategy T.toSubMeas| ≤
      Real.sqrt (selfImprovementVarianceError params eps delta)
  /-- The released right-hand side is within the paper's pre-absorption helper
  SSC error of the helper mass. -/
  residualLowerBound :
    strategy.state.subMeasMass (Hhat.liftLeft strategy.state) -
        addInURightQuantity params strategy
          (sandwichedPolynomialSubMeasAt params strategy T.toSubMeas)
          T.toSubMeas
          (selfConsistencyAddInUSelection params) ≤
      (11 * Real.sqrt (selfImprovementVarianceError params eps delta) +
          Real.sqrt (2 * delta) +
          ((params.m : ℝ) * (params.d : ℝ) / (params.q : ℝ))) -
        addInUError params eps delta

/-- Construct the helper-stage bounds from the mathematical inputs after the
add-in-`u` chain has been closed.

The point self-consistency hypothesis supplies the two self-consistency moves
`Q₀ → Q₁` and `Q₁ → Q₂`; the local-variance sum bound supplies the two
global-variance moves `Q₂ → Q₃` and `Q₃ → Q₄`. The only additional scalar input
is the residual lower bound for the released right-hand side. -/
theorem helper_strong_self_consistency_bounds_of_selfConsistency_localVariance
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    {T : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    (hssc : strategy.state.BipartiteSSCRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta)
    (hlocal :
      (∑ g : MIPStarRE.LDT.Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state T.toSubMeas g) ≤
        localVarianceOfPointsError params eps delta)
    (hresidual :
      strategy.state.subMeasMass (Hhat.liftLeft strategy.state) -
          addInURightQuantity params strategy
            (sandwichedPolynomialSubMeasAt params strategy T.toSubMeas)
            T.toSubMeas
            (selfConsistencyAddInUSelection params) ≤
        (11 * Real.sqrt (selfImprovementVarianceError params eps delta) +
            Real.sqrt (2 * delta) +
            ((params.m : ℝ) * (params.d : ℝ) / (params.q : ℝ))) -
          addInUError params eps delta) :
    HelperStrongSelfConsistencyBounds params strategy T Hhat eps delta :=
  have hsteps :=
    add_in_u_cs_chain_global_variance_steps_of_local_sum_bound_from_factor_bounds
      params strategy eps delta T.toSubMeas hlocal
  { step01Bound := addInU_cs_chain_step1_abs_le_sqrt_two_delta params strategy T.toSubMeas delta hssc
    step12Bound := addInU_cs_chain_step2_abs_le_sqrt_two_delta params strategy T.toSubMeas delta hssc
    step23Bound := hsteps.1
    step34Bound := hsteps.2
    residualLowerBound := hresidual }

/-- The bare off-diagonal polynomial-pair mass appearing after the released
residual is expanded.

This is the right-hand side of
`helper_mass_sub_release_eq_polynomial_off_diagonal`, stated for an arbitrary
polynomial submeasurement `T`. -/
noncomputable def helperOffDiagonalBareQuantity
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) : ℝ :=
  avgOver (uniformDistribution (Point params)) (fun u =>
    ∑ h : MIPStarRE.LDT.Polynomial params,
      ∑ h' ∈ (Finset.univ : Finset (MIPStarRE.LDT.Polynomial params)).erase h,
        strategy.state.ev
          (strategy.state.opTensor
            ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h')
            (T.outcome h)))

/-- The bare off-diagonal polynomial-pair mass is a contraction.

For each point `u`, the off-diagonal sum is bounded by the full double sum
`Σ_h Σ_{h'} H^u_{h'} ⊗ T_h`, which is `(H^u.total) ⊗ T.total`.  Both factors are
submeasurement totals, so the expectation is at most `1`. -/
theorem helperOffDiagonalBareQuantity_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    helperOffDiagonalBareQuantity params strategy T ≤ 1 := by
  classical
  refine avgOver_uniform_le_const _ 1 fun u => ?_
  let H := sandwichedPolynomialSubMeasAt params strategy T u
  have hnonneg : ∀ h h' : MIPStarRE.LDT.Polynomial params,
      0 ≤ strategy.state.ev (strategy.state.opTensor (H.outcome h') (T.outcome h)) :=
    fun h h' => strategy.state.ev_nonneg_of_psd _ <|
      strategy.state.opTensor_nonneg (H.outcome_pos h') (T.outcome_pos h)
  have hfull :
      (∑ h : MIPStarRE.LDT.Polynomial params, ∑ h' : MIPStarRE.LDT.Polynomial params,
          strategy.state.ev (strategy.state.opTensor (H.outcome h') (T.outcome h))) =
        strategy.state.ev (strategy.state.opTensor H.total T.total) := by
    rw [← H.sum_eq_total, ← T.sum_eq_total, strategy.state.opTensor_sum_right_univ,
      strategy.state.ev_sum]
    exact Finset.sum_congr rfl fun h _ => by
      rw [strategy.state.opTensor_sum_left_univ, strategy.state.ev_sum]
  calc
    _ ≤ ∑ h : MIPStarRE.LDT.Polynomial params, ∑ h' : MIPStarRE.LDT.Polynomial params,
          strategy.state.ev (strategy.state.opTensor (H.outcome h') (T.outcome h)) :=
      Finset.sum_le_sum fun h _ =>
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset h Finset.univ)
          fun h' _ _ => hnonneg h h'
    _ = strategy.state.ev (strategy.state.opTensor H.total T.total) := hfull
    _ ≤ strategy.state.ev 1 :=
      strategy.state.ev_mono _ _ <|
        strategy.state.opTensor_le_one H.total_nonneg H.total_le_one T.total_le_one
    _ = 1 := strategy.state.ev_one_of_isNormalized

/-! ### Off-diagonal variance swaps -/

/-- The selected-chain endpoint `Q₄` is the off-diagonal indicator quantity. -/
theorem helperOffDiagonalSelectedCSChainQ4_eq_indicator
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    addInUSelectedCSChainQ4 params strategy
        (fun _ : Point params => T) T
        (helperOffDiagonalVarianceSwapSelection params) =
      helperOffDiagonalIndicatorQuantity params strategy T := by
  classical
  rw [addInUSelectedCSChainQ4, helperOffDiagonalIndicatorQuantity]
  rw [avgOver_uniform_fst (α := Point params) (β := Point params)
    (f := fun u : Point params =>
      ∑ ah ∈ addInUSelectionPairs params (helperOffDiagonalVarianceSwapSelection params) u,
        let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 u
        strategy.state.ev
          (strategy.state.opTensor (Au * T.outcome ah.1 * Au) (T.outcome ah.2)))]
  refine avgOver_congr (uniformDistribution (Point params)) _ _ fun u => ?_
  rw [helperOffDiagonalVarianceSwapSelection_pairs_sum params u
    (fun h' h =>
      let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
      strategy.state.ev
        (strategy.state.opTensor (Au * T.outcome h' * Au) (T.outcome h)))]
  refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun h' _ => ?_
  by_cases heq : h u = h' u
  · simp [heq, sandwichedPolynomialSubMeasAt, sandwichedPolynomialOutcomeOperatorAt,
      pointConditionedOutcomeOperatorAtPolynomial]
  · simp [heq]

/-- The selected-chain scalar `Q₃` is the one-sided swapped off-diagonal
indicator quantity. -/
theorem helperOffDiagonalSelectedCSChainQ3_eq_oneSidedSwappedIndicator
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    addInUSelectedCSChainQ3 params strategy
        (fun _ : Point params => T) T
        (helperOffDiagonalVarianceSwapSelection params) =
      helperOffDiagonalOneSidedSwappedIndicatorQuantity params strategy T := by
  classical
  rw [addInUSelectedCSChainQ3, helperOffDiagonalOneSidedSwappedIndicatorQuantity]
  refine avgOver_congr (uniformDistribution (Point params × Point params)) _ _ fun uv => ?_
  rw [helperOffDiagonalVarianceSwapSelection_pairs_sum params uv.1
    (fun h' h =>
      strategy.state.ev
        (strategy.state.opTensor
          (pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1 *
            T.outcome h' *
            pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2)
          (T.outcome h)))]
  refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun h' _ => ?_
  congr 1
  rw [← strategy.state.ev_conjTranspose, strategy.state.conjTranspose_opTensor, star_mul,
    star_mul, SubMeas.outcome_hermitian, SubMeas.outcome_hermitian,
    pointConditionedOutcomeOperatorAtPolynomial, pointConditionedOutcomeOperatorAtPolynomial,
    SubMeas.outcome_hermitian, SubMeas.outcome_hermitian, mul_assoc]

/-- The selected-chain scalar `Q₂` is the fully swapped off-diagonal indicator
quantity. -/
theorem helperOffDiagonalSelectedCSChainQ2_eq_swappedIndicator
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    addInUSelectedCSChainQ2 params strategy
        (fun _ : Point params => T) T
        (helperOffDiagonalVarianceSwapSelection params) =
      helperOffDiagonalSwappedIndicatorQuantity params strategy T := by
  classical
  rw [addInUSelectedCSChainQ2, helperOffDiagonalSwappedIndicatorQuantity]
  rw [avgOver_uniform_prod (α := Point params) (β := Point params)
    (f := fun u v =>
      ∑ ah ∈ addInUSelectionPairs params (helperOffDiagonalVarianceSwapSelection params) u,
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 v
        strategy.state.ev
          (strategy.state.opTensor (Av * T.outcome ah.1 * Av) (T.outcome ah.2))),
    avgOver_comm]
  refine avgOver_congr (uniformDistribution (Point params)) _ _ fun v => ?_
  simp only [helperOffDiagonalVarianceSwapSelection_pairs_sum params _
    (fun h' h =>
      let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h v
      strategy.state.ev
        (strategy.state.opTensor (Av * T.outcome h' * Av) (T.outcome h)))]
  rw [avgOver_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [avgOver_finset_sum]
  exact Finset.sum_congr rfl fun h' _ => avgOver_mul_const _ _ _

/-- The first off-diagonal variance swap, corresponding to
`eq:swapped-u-for-v` in the helper SSC residual chain. -/
theorem helperOffDiagonalIndicatorQuantity_abs_sub_oneSidedSwappedIndicator_le_sqrt
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hlocal :
      (∑ g : MIPStarRE.LDT.Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤
        localVarianceOfPointsError params eps delta) :
    |helperOffDiagonalIndicatorQuantity params strategy T -
      helperOffDiagonalOneSidedSwappedIndicatorQuantity params strategy T| ≤
        Real.sqrt (selfImprovementVarianceError params eps delta) := by
  have hsteps :=
    addInU_selected_cs_chain_step34_abs_le_sqrt_of_globalVarianceDeviation_sum_le
      params strategy (fun _ : Point params => T) T
      (helperOffDiagonalVarianceSwapSelection params)
      (globalVarianceDeviation_sum_le_of_localVarianceDeviation_sum_le
        params strategy eps delta T hlocal)
  rw [helperOffDiagonalSelectedCSChainQ4_eq_indicator,
    helperOffDiagonalSelectedCSChainQ3_eq_oneSidedSwappedIndicator] at hsteps
  exact (abs_sub_comm _ _).trans_le hsteps.2

/-- The second off-diagonal variance swap, corresponding to
`eq:swapped-u-for-v-this-time-it's-personal` in the helper SSC residual chain. -/
theorem helperOffDiagonalOneSidedSwappedIndicator_abs_sub_swappedIndicator_le_sqrt
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hlocal :
      (∑ g : MIPStarRE.LDT.Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤
        localVarianceOfPointsError params eps delta) :
    |helperOffDiagonalOneSidedSwappedIndicatorQuantity params strategy T -
      helperOffDiagonalSwappedIndicatorQuantity params strategy T| ≤
        Real.sqrt (selfImprovementVarianceError params eps delta) := by
  have hsteps :=
    addInU_selected_cs_chain_step34_abs_le_sqrt_of_globalVarianceDeviation_sum_le
      params strategy (fun _ : Point params => T) T
      (helperOffDiagonalVarianceSwapSelection params)
      (globalVarianceDeviation_sum_le_of_localVarianceDeviation_sum_le
        params strategy eps delta T hlocal)
  rw [helperOffDiagonalSelectedCSChainQ3_eq_oneSidedSwappedIndicator,
    helperOffDiagonalSelectedCSChainQ2_eq_swappedIndicator] at hsteps
  exact (abs_sub_comm _ _).trans_le hsteps.1

end MIPRE.LIDT.Co.SelfImprovement

end

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
SelfImprovement/Theorems/Results/HelperCompleteness/Linearized.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Results.HelperCompleteness.InputSdp
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Results.HelperCompleteness.FiberBounds

@[expose] public section

/-!
# Helper completeness: the linearized SDP expression

The rewrite of the linearized helper-completeness expression as the dual mass, and the assembly
of the Cauchy--Schwarz estimates with input consistency, the algebraic bridge from the two
analytic moves to the `Hhat`-versus-`Z` lower bound: the counterpart of the vendored
`SelfImprovement/Theorems/Results/HelperCompleteness/Linearized.lean` (under
`MIPRE/Background/LIDT/MIPStarRE/LDT/`) in the port of `planning/c6b-plan.md` (milestone M10,
section "Port conventions").

A strategy is a `SymStrat params 𝔓 K`; `T`, `Hhat` and `Z` are local, in `𝔓`, and the joint
operators are `strategy.state.L`, `strategy.state.R` and `strategy.state.opTensor` in
`K →L[ℂ] K`. The vendored `Hhat.liftLeft` is `Hhat.liftLeft strategy.state`, and
`subMeasMass`/`CompletenessAtLeast` are those of the state.

- `helper_first_move_abs_sub_bracketed_le_two_sqrt_delta` passes `hssc` to M3's
  `twoNotionsOfSelfConsistency`, whose vendored hypothesis `PermInvState ψ ∧ BipartiteSSCRel …`
  is now `BipartiteSSCRel` alone, and calls `closenessOfInnerProduct_right` on
  `strategy.state.toVecState` without the vendored `strategy.isNormalized`. The vendored
  `Matrix.PosSemidef` self-adjointness of the fiber operator is `IsSelfAdjoint.of_nonneg`, and
  the adjoint computations are `map_star strategy.state.L` with the keystone's
  `leftTensor_mul_leftTensor` and `rightTensor_mul_leftTensor_eq_opTensor`.
- The averaging step of
  `helper_linearized_completeness_eq_dual_mass_of_complementary_slackness` is the keystone's
  `ev_leftTensor_averageOperatorOverDistribution` with `Finset.mul_sum`, in place of the vendored
  `ev_opTensor_averageOperatorOverDistribution_left` at `B = 1` and `Matrix.mul_sum`.

The vendored file has no swap or density hypotheses.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/self_improvement.tex` lines 395--414
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.SelfImprovement

open MIPStarRE.LDT (Parameters FieldModel Point Fq avgOver uniformDistribution avgOver_congr
  avgOver_sum uniformDistribution_weight_sum_le_one)
open MIPStarRE.LDT.SelfImprovement (selfImprovementHelperError
  helper_completeness_error_le_selfImprovementHelperError)
open MIPRE.LIDT.Co.GlobalVariance (pointConditionedOutcomeOperatorAtPolynomial)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The final algebraic rewrite in the helper-completeness Cauchy--Schwarz
argument, isolated from the two analytic estimates.

After the two Cauchy--Schwarz moves in
`references/ldt-paper/self_improvement.tex`, lines 360--399, the remaining
linear expression is

`E_u Σ_h ⟨ψ, (T_h A^u_{h(u)}) ⊗ I ψ⟩`.

This theorem reindexes the average to
`Σ_h ⟨ψ, (T_h E_u A^u_{h(u)}) ⊗ I ψ⟩`, applies the complementary-slackness
identity `T_h E_u A^u_{h(u)} = T_h Z`, and finally invokes
`sdp_complementary_slackness_sum_eq_dual_mass` to use `Σ_h T_h = I`.
The statement deliberately keeps complementary slackness as an explicit
hypothesis; it is not a consequence of the reduced `SdpOptimalPair` interface. -/
theorem helper_linearized_completeness_eq_dual_mass_of_complementary_slackness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (Z : 𝔓)
    (hTtotal : T.total = 1)
    (hslack :
      ∀ h : MIPStarRE.LDT.Polynomial params,
        T.outcome h * averagedPointOperator params strategy h =
          T.outcome h * Z) :
    avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : MIPStarRE.LDT.Polynomial params,
          strategy.state.ev
            (strategy.state.L
              (T.outcome h *
                pointConditionedOutcomeOperatorAtPolynomial params strategy h u))) =
      strategy.state.ev (strategy.state.L Z) := by
  set S := strategy.state
  let 𝒟 := uniformDistribution (Point params)
  have hmul_avg (h : MIPStarRE.LDT.Polynomial params) :
      averageOperatorOverDistribution 𝒟
          (fun u => T.outcome h * pointConditionedOutcomeOperatorAtPolynomial params strategy h u) =
        T.outcome h * averagedPointOperator params strategy h := by
    rw [averagedPointOperator, averageOperatorOverDistribution, averageOperatorOverDistribution,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => (mul_smul_comm _ _ _).symm
  rw [avgOver_sum]
  refine (Finset.sum_congr rfl fun h _ => ?_).trans
    (sdp_complementary_slackness_sum_eq_dual_mass params strategy T Z hTtotal
      fun h => (hslack h).symm)
  rw [← hmul_avg, S.ev_leftTensor_averageOperatorOverDistribution]

/-- The named linearized helper-completeness quantity is the SDP dual mass under
complementary slackness. -/
theorem helper_linearized_completeness_quantity_eq_dual_mass_of_complementary_slackness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (Z : 𝔓)
    (hTtotal : T.total = 1)
    (hslack :
      ∀ h : MIPStarRE.LDT.Polynomial params,
        T.outcome h * averagedPointOperator params strategy h =
          T.outcome h * Z) :
    helperLinearizedCompletenessQuantity params strategy T =
      strategy.state.ev (strategy.state.L Z) :=
  helper_linearized_completeness_eq_dual_mass_of_complementary_slackness
    params strategy T Z hTtotal hslack

/-- Complementary-slackness conversion specialized to the SDP witness packaged
inside `SelfImprovementHelperConclusion`. -/
theorem helper_sdp_complementary_slackness_sum_eq_dual_mass
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    {T : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Z : 𝔓}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hcomp :
      ∀ h : MIPStarRE.LDT.Polynomial params,
        sdpComplementarySlacknessEquation params strategy T.toSubMeas Z h) :
    (∑ h : MIPStarRE.LDT.Polynomial params,
        strategy.state.ev
          (strategy.state.L
            (T.toSubMeas.outcome h * averagedPointOperator params strategy h))) =
      strategy.state.ev (strategy.state.L Z) :=
  sdp_complementary_slackness_sum_eq_dual_mass params strategy T.toSubMeas Z
    hhelper.sdpWitness.primalTotalOperator hcomp

/-- The bracketed scalar expression before the first Cauchy--Schwarz move in
helper completeness.

This is the right-hand side of `eq:bracketize-the-expression`:

`E_u Σ_a ⟨ψ, (A^u_a · T_[h(u)=a] · A^u_a) ⊗ I ψ⟩`.

The finite sum
`Σ_{h : h(u)=a} T_h` represents the paper's fiber operator
`T_[h(u)=a]`. -/
noncomputable def helperBracketedCompletenessQuantity
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) : ℝ :=
  avgOver (uniformDistribution (Point params)) (fun u =>
    ∑ a : Fq params,
      let Au := (strategy.pointMeasurement u).outcome a
      let Tfiber := helperFiberOperator params T u a
      strategy.state.ev (strategy.state.L (Au * Tfiber * Au)))

/-- The first Cauchy--Schwarz move in the helper-completeness proof.

Assuming bipartite strong self-consistency of the point measurement with error
`delta`, the bracketed expression
`E_u Σ_a ⟨ψ, (A^u_a T_[h(u)=a] A^u_a) ⊗ I ψ⟩`
differs from
`E_u Σ_a ⟨ψ, (T_[h(u)=a] A^u_a) ⊗ A^u_a ψ⟩`
by at most `2 sqrt delta`.  The proof is the paper's
`eq:yet-another-move-a`: `twoNotionsOfSelfConsistency` supplies the first
square-root factor, while `helper_first_move_second_factor_operator_le_one` supplies
the second. -/
theorem helper_first_move_abs_sub_bracketed_le_two_sqrt_delta
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (delta : ℝ)
    (hssc : strategy.state.BipartiteSSCRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta) :
    |helperFirstMovedCompletenessQuantity params strategy T -
      helperBracketedCompletenessQuantity params strategy T| ≤
      2 * Real.sqrt delta := by
  set S := strategy.state
  let 𝒟 := uniformDistribution (Point params)
  let Aop : Point params → Fq params → K →L[ℂ] K :=
    fun u a => S.L ((strategy.pointMeasurement u).outcome a)
  let Bop : Point params → Fq params → K →L[ℂ] K :=
    fun u a => S.R ((strategy.pointMeasurement u).outcome a)
  let Cop : Point params → Fq params → Unit → K →L[ℂ] K :=
    fun u a _ => S.L (helperFiberOperator params T u a * (strategy.pointMeasurement u).outcome a)
  have hOutcome_herm (u : Point params) (a : Fq params) :
      star ((strategy.pointMeasurement u).outcome a) = (strategy.pointMeasurement u).outcome a :=
    SubMeas.outcome_hermitian (strategy.pointMeasurement u).toSubMeas a
  have hTfiber_herm (u : Point params) (a : Fq params) :
      star (helperFiberOperator params T u a) = helperFiberOperator params T u a :=
    (IsSelfAdjoint.of_nonneg (helperFiberOperator_nonneg params T u a)).star_eq
  have hAB :
      avgOver 𝒟 (fun u =>
        S.qSDDCore (fun a : Fq params => star (Aop u a)) (fun a : Fq params => star (Bop u a))) ≤
        2 * delta := by
    refine le_of_eq_of_le (avgOver_congr _ _ _ fun u => ?_)
      (Preliminaries.twoNotionsOfSelfConsistency S 𝒟
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta hssc).squaredDistanceBound
    have hA : (fun a : Fq params => star (Aop u a)) = Aop u :=
      funext fun a => (map_star S.L _).symm.trans (congrArg S.L (hOutcome_herm u a))
    have hB : (fun a : Fq params => star (Bop u a)) = Bop u :=
      funext fun a => (map_star S.R _).symm.trans (congrArg S.R (hOutcome_herm u a))
    rw [hA, hB]
    rfl
  have hC (u : Point params) :
      (∑ a : Fq params, star (∑ b : Unit, Cop u a b) * (∑ b : Unit, Cop u a b)) ≤ 1 := by
    refine le_of_eq_of_le (Finset.sum_congr rfl fun a _ => ?_)
      (helper_first_move_second_factor_operator_le_one params strategy T u)
    rw [Fintype.sum_unique, ← map_star S.L, S.leftTensor_mul_leftTensor, star_mul,
      hOutcome_herm, hTfiber_herm]
    simp only [mul_assoc]
    rfl
  have hcs := Preliminaries.closenessOfInnerProduct_right S.toVecState 𝒟
    (uniformDistribution_weight_sum_le_one (Point params)) Aop Bop Cop (2 * delta) hAB hC
  have hbracket :
      avgOver 𝒟 (fun u =>
        ∑ a : Fq params, ∑ b : Unit, S.ev (Aop u a * Cop u a b)) =
        helperBracketedCompletenessQuantity params strategy T := by
    refine avgOver_congr _ _ _ fun u => Finset.sum_congr rfl fun a _ => ?_
    dsimp only
    rw [Fintype.sum_unique, S.leftTensor_mul_leftTensor, mul_assoc]
  have hfirst :
      avgOver 𝒟 (fun u =>
        ∑ a : Fq params, ∑ b : Unit, S.ev (Bop u a * Cop u a b)) =
        helperFirstMovedCompletenessQuantity params strategy T := by
    refine avgOver_congr _ _ _ fun u => Finset.sum_congr rfl fun a _ => ?_
    dsimp only
    rw [Fintype.sum_unique, S.rightTensor_mul_leftTensor_eq_opTensor]
  have hsqrt2delta_le : Real.sqrt (2 * delta) ≤ 2 * Real.sqrt delta := by
    rw [Real.sqrt_mul zero_le_two]
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_iff.2 ⟨zero_le_two, by norm_num⟩)
      (Real.sqrt_nonneg _)
  rw [← hbracket, ← hfirst, abs_sub_comm]
  exact hcs.trans hsqrt2delta_le

/-- The recorded `Hhat`-versus-`Z` comparison follows from the two
Cauchy--Schwarz scalar bounds and complementary slackness.

The first hypothesis is the bound for moving the leftmost copy of `A^u_a` across
the bipartition; the second is the bound for removing the remaining copy of
`A^u_a` on the right register.  Together with complementary slackness, these
are precisely the estimates leading to
`eq:gonna-use-this-later-H-versus-Z` in the paper. -/
theorem helper_hhat_vs_z_of_cauchy_schwarz_and_complementary_slackness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    {T : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Z : 𝔓}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hmove_left :
      |helperFirstMovedCompletenessQuantity params strategy T.toSubMeas -
        strategy.state.subMeasMass (Hhat.liftLeft strategy.state)| ≤
        2 * Real.sqrt delta)
    (hremove_right :
      |helperLinearizedCompletenessQuantity params strategy T.toSubMeas -
        helperFirstMovedCompletenessQuantity params strategy T.toSubMeas| ≤
        Real.sqrt delta)
    (hslack :
      ∀ h : MIPStarRE.LDT.Polynomial params,
        T.toSubMeas.outcome h * averagedPointOperator params strategy h =
          T.toSubMeas.outcome h * Z) :
    strategy.state.ev (strategy.state.L Z) - 3 * Real.sqrt delta ≤
      strategy.state.subMeasMass (Hhat.liftLeft strategy.state) := by
  have hmove_left_upper := (abs_le.mp hmove_left).2
  have hremove_right_upper := (abs_le.mp hremove_right).2
  have hlinearized :=
    helper_linearized_completeness_quantity_eq_dual_mass_of_complementary_slackness
      params strategy T.toSubMeas Z hhelper.sdpWitness.primalTotalOperator hslack
  linarith

/-- Helper-stage completeness from the `Hhat`-versus-`Z` comparison and the
dual-mass lower bound.

The paper proves
`subMeasMass ψ Hhat.liftLeft ≥ ⟨ψ, Z ⊗ I, ψ⟩ - 3 √δ` by the two
Cauchy--Schwarz moves in the helper-completeness paragraph.  Once the separate
input-consistency argument gives `1 - ν ≤ ⟨ψ, Z ⊗ I, ψ⟩`, this theorem performs
the scalar assembly and absorbs the loss `3 √δ` into the helper threshold
`ζ̂ = selfImprovementHelperError params eps delta`. -/
theorem helper_completeness_of_dual_mass_lower_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta nu : ℝ)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    {Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Z : 𝔓}
    (hHhat_vs_Z :
      strategy.state.ev (strategy.state.L Z) - 3 * Real.sqrt delta ≤
        strategy.state.subMeasMass (Hhat.liftLeft strategy.state))
    (hdualMass :
      1 - nu ≤ strategy.state.ev (strategy.state.L Z)) :
    strategy.state.CompletenessAtLeast (Hhat.liftLeft strategy.state)
      ((1 - nu) - selfImprovementHelperError params eps delta) := by
  refine ⟨?_⟩
  have herr :=
    helper_completeness_error_le_selfImprovementHelperError params eps delta heps hdelta
  linarith

/-- Helper-stage completeness from input consistency and the
`Hhat`-versus-`Z` comparison.

This is the checked assembly of the final part of the helper-completeness
paragraph in `thm:self-improvement`.  The only analytic input still external is
the paper's Cauchy--Schwarz comparison
`subMeasMass ψ Hhat.liftLeft ≥ ⟨ψ, Z ⊗ I, ψ⟩ - 3 √δ`; the SDP dual-feasibility
fields of `SelfImprovementHelperConclusion` and the input consistency of `G`
produce the dual-mass lower bound internally. -/
theorem helper_completeness_of_input_consistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓)
    (eps delta nu : ℝ)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    {T : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Z : 𝔓}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hHhat_vs_Z :
      strategy.state.ev (strategy.state.L Z) - 3 * Real.sqrt delta ≤
        strategy.state.subMeasMass (Hhat.liftLeft strategy.state))
    (hcons : strategy.state.ConsRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas) nu) :
    strategy.state.CompletenessAtLeast (Hhat.liftLeft strategy.state)
      ((1 - nu) - selfImprovementHelperError params eps delta) :=
  helper_completeness_of_dual_mass_lower_bound params strategy eps delta nu
    heps hdelta hHhat_vs_Z
    (input_consistency_dual_mass_lower_bound params strategy G Z nu
      hhelper.sdpWitness.dualPositive hhelper.sdpWitness.dualFeasible hcons)

/-- Helper-stage completeness from the two Cauchy--Schwarz scalar bounds,
complementary slackness, and input consistency.

This theorem is the completeness paragraph with the `Hhat`-versus-`Z`
comparison assembled internally from its two analytic estimates and the exact
SDP rewrite.  The remaining external hypotheses are therefore the two
Cauchy--Schwarz estimates themselves and the complementary-slackness equation. -/
theorem helper_completeness_of_cauchy_schwarz_input_consistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓)
    (eps delta nu : ℝ)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    {T : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Z : 𝔓}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hmove_left :
      |helperFirstMovedCompletenessQuantity params strategy T.toSubMeas -
        strategy.state.subMeasMass (Hhat.liftLeft strategy.state)| ≤
        2 * Real.sqrt delta)
    (hremove_right :
      |helperLinearizedCompletenessQuantity params strategy T.toSubMeas -
        helperFirstMovedCompletenessQuantity params strategy T.toSubMeas| ≤
        Real.sqrt delta)
    (hslack :
      ∀ h : MIPStarRE.LDT.Polynomial params,
        T.toSubMeas.outcome h * averagedPointOperator params strategy h =
          T.toSubMeas.outcome h * Z)
    (hcons : strategy.state.ConsRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas) nu) :
    strategy.state.CompletenessAtLeast (Hhat.liftLeft strategy.state)
      ((1 - nu) - selfImprovementHelperError params eps delta) :=
  helper_completeness_of_input_consistency params strategy G eps delta nu
    heps hdelta hhelper
    (helper_hhat_vs_z_of_cauchy_schwarz_and_complementary_slackness
      params strategy eps delta hhelper hmove_left hremove_right hslack)
    hcons

end MIPRE.LIDT.Co.SelfImprovement

end

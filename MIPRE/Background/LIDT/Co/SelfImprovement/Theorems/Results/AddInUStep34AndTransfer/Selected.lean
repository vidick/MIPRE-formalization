/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
SelfImprovement/Theorems/Results/AddInUStep34AndTransfer/Selected.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Results.AddInUStep34AndTransfer.Factored
public import MIPRE.Background.LIDT.MIPStarRE.LDT.SelfImprovement.Theorems.Results.AddInUStep34AndTransfer.Selected

@[expose] public section

/-!
# Selected add-in-u Step 3/4 global-variance bounds

Selected-family Cauchy--Schwarz estimates and factor bounds for the `Q₂ → Q₃` and `Q₃ → Q₄`
add-in-u moves: the counterpart of the vendored
`SelfImprovement/Theorems/Results/AddInUStep34AndTransfer/Selected.lean` (under
`MIPRE/Background/LIDT/MIPStarRE/LDT/`) in the port of `planning/c6b-plan.md` (milestone M10,
section "Port conventions"). It is the selected-pair twin of Co `AddInUStep34AndTransfer/Factored`:
the sums run over the selected pairs `(o, h) ∈ S_u`, extended by zero to all pairs, with an
arbitrary outcome operator `M^u_o`.

## Contents

- `addInU_selected_cs_chain_step3_factored_cs`, `addInU_selected_cs_chain_step4_factored_cs`:
  the operator Cauchy--Schwarz bounds, `S.ev_opTensor_sandwich_abs_le_sqrt` (Co
  `Basic/OperatorExpectations`) at each `(u, v, o, h)`, lifted through the imported
  `addInU_selected_weighted_cauchy_schwarz`.
- `addInU_selected_sandwich_tensor_if_sum_le`: `∑_{(o,h) ∈ S_u} (X_h M^u_o X_h) ⊗ T_h ≤
  ∑_h X_h² ⊗ T_h` for self-adjoint `X_h`.
- `addInU_selected_cs_chain_self_energy_factor_le_one_at`: the self-energy factor is at most `1`.
- `addInU_selected_cs_chain_step34_variance_factor_le_globalVarianceDeviation_sum`: the variance
  factor is at most the summed global-variance deviation.
- `addInU_selected_cs_chain_step{3,4}_abs_le_sqrt_globalVarianceDeviation_sum`, their `_of_…_le`
  upgrades and the combined `addInU_selected_cs_chain_step34_abs_le_sqrt_of_…_le`.

Every scalar is `strategy.state.ev` of a joint operator; `opTensor A B` is
`strategy.state.opTensor A B`, `rightTensor A` is `strategy.state.R A`, and `Xᴴ` is `star X`. The
vendored `addInU_selected_sandwich_tensor_if_sum_le` names no state, its `opTensor` being the
Kronecker product on the carrier; here it takes the model `(ψ : SymModel 𝔓 K)` as an explicit
first argument (`S` is the selection), as Co `AddInUStep12/Selected`'s
`addInU_selected_filtered_tensor_sum_le_one` does. Its hypothesis `(X h)ᴴ = X h` is
`star (X h) = X h`, which is `IsSelfAdjoint (X h)` by definition. The vendored Hermitian facts
`SubMeas.outcome_hermitian …` and `rw [Matrix.conjTranspose_sub, hAu_herm, hAv_herm]` are
`(IsSelfAdjoint.of_nonneg …).star_eq` and `IsSelfAdjoint.sub`; the positivity of `X · H · X`
through `star_left_conjugate_nonneg` and `simpa [Matrix.star_eq_conjTranspose]` is
`IsSelfAdjoint.conjugate_nonneg`, with the keystone's `opTensor_nonneg` and `ev_nonneg_of_psd`.
Two private helpers carry what the vendored proofs repeat inline: the self-adjointness of
`A^u_{h(u)}`, and `ev (if c then Z else 0) = if c then ev Z else 0` (the vendored
`by_cases hmem … simp [hmem, ev_zero]`). The vendored `simpa using` conversion between the
selected sum `∑_{(o,h) ∈ S_u}` of the Co `addInU_selected_cs_chain_step{3,4}_diff_eq` and the
zero-extended sum of the classical Cauchy--Schwarz is `Fintype.sum_ite_mem`.

**Global variance.** The summed deviation `∑_g globalVarianceDeviationAtPolynomial params strategy
strategy.state T g` is that of M6 (Co `GlobalVariance/Defs/Families`): the independent-points
variance of the family `u ↦ S.L (A^u_{g(u)}) * S.R √T_g` on `strategy.state` itself, not the
vendored weighted state (M6's departure). The variance factor is identified with it through Co
`weightedPointConditionedOperator_sq`, `star D * D = opTensor (star (A^u − A^v) (A^u − A^v)) T_g`,
exactly where the vendored proof rewrites with its vendored counterpart, so the statement keeps
its vendored text.

**Dropped hypothesis.** The vendored `addInU_selected_cs_chain_self_energy_factor_le_one_at`
closes with `ev_one_of_isNormalized strategy.state strategy.isNormalized` (vendored line 484);
here `strategy.state.ev_one_of_isNormalized` takes no hypothesis. No statement of the vendored
file carries a swap, density or normalization hypothesis, so no statement changed.

## Not ported

- `addInU_selected_weighted_cauchy_schwarz`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/self_improvement.tex` lines 299--340
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.SelfImprovement

open MIPStarRE.LDT (Parameters FieldModel Point avgOver uniformDistribution avgOver_congr
  avgOver_mono avgOver_sum avgOver_uniform_le_const)
open MIPStarRE.LDT.ExpansionHypercubeGraph (avgOver_independentPointPair_eq_uniform_prod)
open MIPStarRE.LDT.SelfImprovement (AddInUSelection addInUSelectionPairs
  addInU_le_sqrt_of_factor_bounds_right addInU_le_sqrt_of_factor_bounds_left
  addInU_selected_weighted_cauchy_schwarz)
open MIPRE.LIDT.Co.GlobalVariance (pointConditionedOutcomeOperatorAtPolynomial
  globalVarianceDeviationAtPolynomial weightedPointConditionedOperator_sq)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The point operators `A^u_{h(u)}` are self-adjoint, being positive. -/
private theorem pointConditionedOutcomeOperatorAtPolynomial_isSelfAdjoint
    (params : Parameters) [FieldModel params.q] (strategy : SymStrat params 𝔓 K)
    (h : MIPStarRE.LDT.Polynomial params) (w : Point params) :
    IsSelfAdjoint (pointConditionedOutcomeOperatorAtPolynomial params strategy h w) :=
  .of_nonneg ((strategy.pointMeasurement w).toSubMeas.outcome_pos (h w))

/-- The expectation of a selected term `if c then Z else 0` is the selected expectation. -/
private theorem ev_ite_zero (V : VecState K) (c : Prop) [Decidable c] (Z : K →L[ℂ] K) :
    V.ev (if c then Z else 0) = if c then V.ev Z else 0 := by
  split_ifs
  · rfl
  · exact V.ev_zero

/-- Selected factored Cauchy--Schwarz bound for the `Q₂ → Q₃` add-in-`u` step.

This is the selection-parametrized analogue of
`add_in_u_cs_chain_q2_q3_factored_cs`.  The summation is over all pairs
`(o,h)`, with the terms outside the selected set `S_u` set to zero; this form is
convenient for the finite Cauchy--Schwarz lemma and is equivalent to the
fiberwise selected sum appearing in the paper. -/
theorem addInU_selected_cs_chain_step3_factored_cs
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (M : IdxSubMeas (Point params) Outcome 𝔓)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (S : AddInUSelection params Outcome) :
    |addInUSelectedCSChainQ2 params strategy M T S -
        addInUSelectedCSChainQ3 params strategy M T S| ≤
      Real.sqrt
        (avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ ah : Outcome × MIPStarRE.LDT.Polynomial params,
            if ah ∈ addInUSelectionPairs params S uv.1 then
              let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
              let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
              let Moh := (M uv.1).outcome ah.1
              strategy.state.ev
                (strategy.state.opTensor ((Av - Au) * Moh * (Av - Au)) (T.outcome ah.2))
            else 0)) *
      Real.sqrt
        (avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ ah : Outcome × MIPStarRE.LDT.Polynomial params,
            if ah ∈ addInUSelectionPairs params S uv.1 then
              let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
              let Moh := (M uv.1).outcome ah.1
              strategy.state.ev (strategy.state.opTensor (Av * Moh * Av) (T.outcome ah.2))
            else 0)) := by
  rw [addInU_selected_cs_chain_step3_diff_eq params strategy M T S]
  have hA := pointConditionedOutcomeOperatorAtPolynomial_isSelfAdjoint params strategy
  have hM := fun (uv : Point params × Point params)
    (ah : Outcome × MIPStarRE.LDT.Polynomial params) => (M uv.1).outcome_pos ah.1
  let A := pointConditionedOutcomeOperatorAtPolynomial params strategy
  refine (le_of_eq (congrArg abs (avgOver_congr _ _ _ fun uv =>
    (Fintype.sum_ite_mem _ _).symm))).trans (addInU_selected_weighted_cauchy_schwarz params S
    (fun uv ah => strategy.state.ev (strategy.state.opTensor
      ((A ah.2 uv.2 - A ah.2 uv.1) * (M uv.1).outcome ah.1 * A ah.2 uv.2) (T.outcome ah.2)))
    _ _ (fun uv ah _ => ?_)
    (fun uv ah _ => strategy.state.ev_nonneg_of_psd _ (strategy.state.opTensor_nonneg
      (((hA ah.2 uv.2).sub (hA ah.2 uv.1)).conjugate_nonneg (hM uv ah)) (T.outcome_pos ah.2)))
    (fun uv ah _ => strategy.state.ev_nonneg_of_psd _ (strategy.state.opTensor_nonneg
      ((hA ah.2 uv.2).conjugate_nonneg (hM uv ah)) (T.outcome_pos ah.2))))
  simpa only [((hA ah.2 uv.2).sub (hA ah.2 uv.1)).star_eq, (hA ah.2 uv.2).star_eq] using
    strategy.state.ev_opTensor_sandwich_abs_le_sqrt
      (pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2 -
        pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1)
      (pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2) _ _
      (hM uv ah) (T.outcome_pos ah.2)

/-- Selected factored Cauchy--Schwarz bound for the `Q₃ → Q₄` add-in-`u` step.

This is the selection-parametrized analogue of
`add_in_u_cs_chain_q3_q4_factored_cs`; as in
`addInU_selected_cs_chain_step3_factored_cs`, terms outside the selected set
are represented by zeros in the finite Cauchy--Schwarz sum. -/
theorem addInU_selected_cs_chain_step4_factored_cs
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (M : IdxSubMeas (Point params) Outcome 𝔓)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (S : AddInUSelection params Outcome) :
    |addInUSelectedCSChainQ3 params strategy M T S -
        addInUSelectedCSChainQ4 params strategy M T S| ≤
      Real.sqrt
        (avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ ah : Outcome × MIPStarRE.LDT.Polynomial params,
            if ah ∈ addInUSelectionPairs params S uv.1 then
              let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
              let Moh := (M uv.1).outcome ah.1
              strategy.state.ev (strategy.state.opTensor (Au * Moh * Au) (T.outcome ah.2))
            else 0)) *
      Real.sqrt
        (avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ ah : Outcome × MIPStarRE.LDT.Polynomial params,
            if ah ∈ addInUSelectionPairs params S uv.1 then
              let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
              let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
              let Moh := (M uv.1).outcome ah.1
              strategy.state.ev
                (strategy.state.opTensor ((Av - Au) * Moh * (Av - Au)) (T.outcome ah.2))
            else 0)) := by
  rw [addInU_selected_cs_chain_step4_diff_eq params strategy M T S]
  have hA := pointConditionedOutcomeOperatorAtPolynomial_isSelfAdjoint params strategy
  have hM := fun (uv : Point params × Point params)
    (ah : Outcome × MIPStarRE.LDT.Polynomial params) => (M uv.1).outcome_pos ah.1
  let A := pointConditionedOutcomeOperatorAtPolynomial params strategy
  refine (le_of_eq (congrArg abs (avgOver_congr _ _ _ fun uv =>
    (Fintype.sum_ite_mem _ _).symm))).trans (addInU_selected_weighted_cauchy_schwarz params S
    (fun uv ah => strategy.state.ev (strategy.state.opTensor
      (A ah.2 uv.1 * (M uv.1).outcome ah.1 * (A ah.2 uv.2 - A ah.2 uv.1)) (T.outcome ah.2)))
    _ _ (fun uv ah _ => ?_)
    (fun uv ah _ => strategy.state.ev_nonneg_of_psd _ (strategy.state.opTensor_nonneg
      ((hA ah.2 uv.1).conjugate_nonneg (hM uv ah)) (T.outcome_pos ah.2)))
    (fun uv ah _ => strategy.state.ev_nonneg_of_psd _ (strategy.state.opTensor_nonneg
      (((hA ah.2 uv.2).sub (hA ah.2 uv.1)).conjugate_nonneg (hM uv ah)) (T.outcome_pos ah.2))))
  simpa only [(hA ah.2 uv.1).star_eq, ((hA ah.2 uv.2).sub (hA ah.2 uv.1)).star_eq] using
    strategy.state.ev_opTensor_sandwich_abs_le_sqrt
      (pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1)
      (pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2 -
        pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1) _ _
      (hM uv ah) (T.outcome_pos ah.2)

/-- A selected sandwich tensor sum is bounded by replacing the selected
submeasurement mass with the identity.

For a fixed point `u`, the selected pairs are a subcollection of
`Outcome × Polynomial params`.  Summing over all pairs, the `Outcome`-mass
collapses to `(M u).total`, and the submeasurement inequality
`(M u).total ≤ I` gives the displayed upper bound. -/
theorem addInU_selected_sandwich_tensor_if_sum_le
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (ψ : SymModel 𝔓 K)
    (params : Parameters) [FieldModel params.q]
    (M : IdxSubMeas (Point params) Outcome 𝔓)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (S : AddInUSelection params Outcome)
    (u : Point params)
    (X : MIPStarRE.LDT.Polynomial params → 𝔓)
    (hX_herm : ∀ h : MIPStarRE.LDT.Polynomial params, star (X h) = X h) :
    (∑ ah : Outcome × MIPStarRE.LDT.Polynomial params,
      if ah ∈ addInUSelectionPairs params S u then
        ψ.opTensor (X ah.2 * (M u).outcome ah.1 * X ah.2) (T.outcome ah.2)
      else 0) ≤
      ∑ h : MIPStarRE.LDT.Polynomial params, ψ.opTensor (X h * X h) (T.outcome h) := by
  have hX : ∀ h, IsSelfAdjoint (X h) := hX_herm
  calc
    (∑ ah : Outcome × MIPStarRE.LDT.Polynomial params,
      if ah ∈ addInUSelectionPairs params S u then
        ψ.opTensor (X ah.2 * (M u).outcome ah.1 * X ah.2) (T.outcome ah.2)
      else 0)
        ≤ ∑ ah : Outcome × MIPStarRE.LDT.Polynomial params,
            ψ.opTensor (X ah.2 * (M u).outcome ah.1 * X ah.2) (T.outcome ah.2) :=
          Finset.sum_le_sum fun ah _ => by
            split_ifs
            · exact le_rfl
            · exact ψ.opTensor_nonneg ((hX ah.2).conjugate_nonneg ((M u).outcome_pos ah.1))
                (T.outcome_pos ah.2)
    _ = ∑ h : MIPStarRE.LDT.Polynomial params,
          ψ.opTensor (X h * (M u).total * X h) (T.outcome h) := by
          rw [Fintype.sum_prod_type, Finset.sum_comm]
          refine Finset.sum_congr rfl fun h _ => ?_
          dsimp only
          rw [← ψ.opTensor_sum_left_univ, ← Finset.sum_mul, ← Finset.mul_sum,
            (M u).sum_eq_total]
    _ ≤ ∑ h : MIPStarRE.LDT.Polynomial params, ψ.opTensor (X h * X h) (T.outcome h) :=
          Finset.sum_le_sum fun h _ => by
            simpa only [mul_one] using ψ.opTensor_mono_left
              ((hX h).conjugate_le_conjugate (M u).total_le_one) (T.outcome_pos h)

/-- The selected self-energy factor is at most `1`.

For each pair of points the selected sandwich `∑_{(o,h) ∈ S_u} (A_h M^u_o A_h) ⊗ T_h`, with
`A_h = A^{p(u,v)}_{h(p(u,v))}`, is dominated by `∑_h A_h ⊗ T_h ≤ 1 ⊗ T_{tot} ≤ 1`, the point
measurement being projective. -/
theorem addInU_selected_cs_chain_self_energy_factor_le_one_at
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (M : IdxSubMeas (Point params) Outcome 𝔓)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (S : AddInUSelection params Outcome)
    (p : Point params × Point params → Point params) :
    avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
      ∑ ah : Outcome × MIPStarRE.LDT.Polynomial params,
        if ah ∈ addInUSelectionPairs params S uv.1 then
          let A := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 (p uv)
          let Moh := (M uv.1).outcome ah.1
          strategy.state.ev (strategy.state.opTensor (A * Moh * A) (T.outcome ah.2))
        else 0) ≤ 1 := by
  refine avgOver_uniform_le_const _ 1 fun uv => ?_
  let X : MIPStarRE.LDT.Polynomial params → 𝔓 :=
    fun h => pointConditionedOutcomeOperatorAtPolynomial params strategy h (p uv)
  have hright :
      ∑ h : MIPStarRE.LDT.Polynomial params,
          strategy.state.opTensor (X h * X h) (T.outcome h) ≤ 1 :=
    calc
      ∑ h : MIPStarRE.LDT.Polynomial params,
          strategy.state.opTensor (X h * X h) (T.outcome h)
          ≤ ∑ h : MIPStarRE.LDT.Polynomial params,
              strategy.state.opTensor 1 (T.outcome h) :=
            Finset.sum_le_sum fun h _ => by
              rw [show X h * X h = X h from (strategy.pointMeasurement (p uv)).proj (h (p uv))]
              exact strategy.state.opTensor_mono_left
                ((strategy.pointMeasurement (p uv)).toSubMeas.outcome_le_one (h (p uv)))
                (T.outcome_pos h)
      _ = strategy.state.opTensor 1 T.total := by
            rw [← T.sum_eq_total, strategy.state.opTensor_sum_right_univ]
      _ ≤ 1 := strategy.state.opTensor_le_one zero_le_one le_rfl T.total_le_one
  calc
    (∑ ah : Outcome × MIPStarRE.LDT.Polynomial params,
      if ah ∈ addInUSelectionPairs params S uv.1 then
        let A := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 (p uv)
        let Moh := (M uv.1).outcome ah.1
        strategy.state.ev (strategy.state.opTensor (A * Moh * A) (T.outcome ah.2))
      else 0)
        = strategy.state.ev
            (∑ ah : Outcome × MIPStarRE.LDT.Polynomial params,
              if ah ∈ addInUSelectionPairs params S uv.1 then
                strategy.state.opTensor (X ah.2 * (M uv.1).outcome ah.1 * X ah.2)
                  (T.outcome ah.2)
              else 0) := by
          rw [strategy.state.ev_finset_sum]
          exact Finset.sum_congr rfl fun ah _ => (ev_ite_zero _ _ _).symm
    _ ≤ strategy.state.ev 1 :=
          strategy.state.ev_mono _ _ ((addInU_selected_sandwich_tensor_if_sum_le strategy.state
            params M T S uv.1 X fun h =>
              (pointConditionedOutcomeOperatorAtPolynomial_isSelfAdjoint params strategy h
                (p uv)).star_eq).trans hright)
    _ = 1 := strategy.state.ev_one_of_isNormalized

/-- The selected Step 3/4 variance factor is bounded by the summed
global-variance deviation.

The selected middle operators form a submeasurement after summing over their
outcome coordinate, so the selected sandwich is dominated by the square of
`A^v_{h(v)} - A^u_{h(u)}`.  Averaging over independent points identifies the
result with the global-variance deviation sum. -/
theorem addInU_selected_cs_chain_step34_variance_factor_le_globalVarianceDeviation_sum
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (M : IdxSubMeas (Point params) Outcome 𝔓)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (S : AddInUSelection params Outcome) :
    avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
      ∑ ah : Outcome × MIPStarRE.LDT.Polynomial params,
        if ah ∈ addInUSelectionPairs params S uv.1 then
          let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
          let Moh := (M uv.1).outcome ah.1
          strategy.state.ev
            (strategy.state.opTensor ((Av - Au) * Moh * (Av - Au)) (T.outcome ah.2))
        else 0) ≤
      ∑ g : MIPStarRE.LDT.Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T g := by
  have hA := pointConditionedOutcomeOperatorAtPolynomial_isSelfAdjoint params strategy
  calc
    _ ≤ avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ g : MIPStarRE.LDT.Polynomial params,
            let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy g uv.1
            let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy g uv.2
            strategy.state.ev
              (strategy.state.opTensor (star (Au - Av) * (Au - Av)) (T.outcome g))) :=
        avgOver_mono _ _ _ fun uv => by
          let X : MIPStarRE.LDT.Polynomial params → 𝔓 := fun h =>
            pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2 -
              pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
          have hX : ∀ h, IsSelfAdjoint (X h) := fun h => (hA h uv.2).sub (hA h uv.1)
          have hsq : ∀ h, X h * X h =
              star (pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1 -
                  pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2) *
                (pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1 -
                  pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2) :=
            fun h => by
              rw [((hA h uv.1).sub (hA h uv.2)).star_eq, ← neg_mul_neg, neg_sub]
          calc
            _ = strategy.state.ev
                  (∑ ah : Outcome × MIPStarRE.LDT.Polynomial params,
                    if ah ∈ addInUSelectionPairs params S uv.1 then
                      strategy.state.opTensor (X ah.2 * (M uv.1).outcome ah.1 * X ah.2)
                        (T.outcome ah.2)
                    else 0) := by
                rw [strategy.state.ev_finset_sum]
                exact Finset.sum_congr rfl fun ah _ => (ev_ite_zero _ _ _).symm
            _ ≤ strategy.state.ev (∑ h : MIPStarRE.LDT.Polynomial params,
                  strategy.state.opTensor (X h * X h) (T.outcome h)) :=
                strategy.state.ev_mono _ _ (addInU_selected_sandwich_tensor_if_sum_le
                  strategy.state params M T S uv.1 X fun h => (hX h).star_eq)
            _ = _ := by
                rw [strategy.state.ev_finset_sum]
                exact Finset.sum_congr rfl fun h _ => by rw [hsq h]
    _ = _ := by
        rw [avgOver_sum]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [globalVarianceDeviationAtPolynomial, avgOver_independentPointPair_eq_uniform_prod]
        exact avgOver_congr _ _ _ fun uv =>
          congrArg strategy.state.ev (weightedPointConditionedOperator_sq params strategy T g
            uv.1 uv.2).symm

/-- Raw selected `Q₂ → Q₃` global-variance Cauchy--Schwarz bound after the
selected variance and self-energy factors have been estimated. -/
theorem addInU_selected_cs_chain_step3_abs_le_sqrt_globalVarianceDeviation_sum
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (M : IdxSubMeas (Point params) Outcome 𝔓)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (S : AddInUSelection params Outcome) :
    |addInUSelectedCSChainQ2 params strategy M T S -
        addInUSelectedCSChainQ3 params strategy M T S| ≤
      Real.sqrt
        (∑ g : MIPStarRE.LDT.Polynomial params,
          globalVarianceDeviationAtPolynomial params strategy strategy.state T g) := by
  classical
  exact addInU_le_sqrt_of_factor_bounds_right
    (addInU_selected_cs_chain_step3_factored_cs params strategy M T S)
    (addInU_selected_cs_chain_step34_variance_factor_le_globalVarianceDeviation_sum
      params strategy M T S)
    (addInU_selected_cs_chain_self_energy_factor_le_one_at
      params strategy M T S (fun uv : Point params × Point params => uv.2))

/-- Raw selected `Q₃ → Q₄` global-variance Cauchy--Schwarz bound after the
selected self-energy and variance factors have been estimated. -/
theorem addInU_selected_cs_chain_step4_abs_le_sqrt_globalVarianceDeviation_sum
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (M : IdxSubMeas (Point params) Outcome 𝔓)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (S : AddInUSelection params Outcome) :
    |addInUSelectedCSChainQ3 params strategy M T S -
        addInUSelectedCSChainQ4 params strategy M T S| ≤
      Real.sqrt
        (∑ g : MIPStarRE.LDT.Polynomial params,
          globalVarianceDeviationAtPolynomial params strategy strategy.state T g) := by
  classical
  exact addInU_le_sqrt_of_factor_bounds_left
    (addInU_selected_cs_chain_step4_factored_cs params strategy M T S)
    (addInU_selected_cs_chain_self_energy_factor_le_one_at
      params strategy M T S (fun uv : Point params × Point params => uv.1))
    (addInU_selected_cs_chain_step34_variance_factor_le_globalVarianceDeviation_sum
      params strategy M T S)

/-- Upgrade the selected `Q₂ → Q₃` raw global-variance bound using an external
bound on the summed global-variance deviation. -/
theorem addInU_selected_cs_chain_step3_abs_le_sqrt_of_globalVarianceDeviation_sum_le
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (M : IdxSubMeas (Point params) Outcome 𝔓)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (S : AddInUSelection params Outcome)
    {ζ : ℝ}
    (hglobal :
      (∑ g : MIPStarRE.LDT.Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤ ζ) :
    |addInUSelectedCSChainQ2 params strategy M T S -
        addInUSelectedCSChainQ3 params strategy M T S| ≤ Real.sqrt ζ :=
  (addInU_selected_cs_chain_step3_abs_le_sqrt_globalVarianceDeviation_sum
    params strategy M T S).trans (Real.sqrt_le_sqrt hglobal)

/-- Upgrade the selected `Q₃ → Q₄` raw global-variance bound using an external
bound on the summed global-variance deviation. -/
theorem addInU_selected_cs_chain_step4_abs_le_sqrt_of_globalVarianceDeviation_sum_le
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (M : IdxSubMeas (Point params) Outcome 𝔓)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (S : AddInUSelection params Outcome)
    {ζ : ℝ}
    (hglobal :
      (∑ g : MIPStarRE.LDT.Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤ ζ) :
    |addInUSelectedCSChainQ3 params strategy M T S -
        addInUSelectedCSChainQ4 params strategy M T S| ≤ Real.sqrt ζ :=
  (addInU_selected_cs_chain_step4_abs_le_sqrt_globalVarianceDeviation_sum
    params strategy M T S).trans (Real.sqrt_le_sqrt hglobal)

/-- Combined selected Step 3/4 global-variance bridge.

The two selected replacement steps use the same summed global-variance
hypothesis.  This closed form supplies the raw selected Cauchy--Schwarz
estimates from the factored Step 3/4 proofs in this file and then applies the
external bound on the global-variance sum to both steps. -/
theorem addInU_selected_cs_chain_step34_abs_le_sqrt_of_globalVarianceDeviation_sum_le
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (M : IdxSubMeas (Point params) Outcome 𝔓)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (S : AddInUSelection params Outcome)
    {ζ : ℝ}
    (hglobal :
      (∑ g : MIPStarRE.LDT.Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤ ζ) :
    |addInUSelectedCSChainQ2 params strategy M T S -
        addInUSelectedCSChainQ3 params strategy M T S| ≤ Real.sqrt ζ ∧
      |addInUSelectedCSChainQ3 params strategy M T S -
        addInUSelectedCSChainQ4 params strategy M T S| ≤ Real.sqrt ζ :=
  ⟨addInU_selected_cs_chain_step3_abs_le_sqrt_of_globalVarianceDeviation_sum_le
      params strategy M T S hglobal,
    addInU_selected_cs_chain_step4_abs_le_sqrt_of_globalVarianceDeviation_sum_le
      params strategy M T S hglobal⟩

end MIPRE.LIDT.Co.SelfImprovement

end

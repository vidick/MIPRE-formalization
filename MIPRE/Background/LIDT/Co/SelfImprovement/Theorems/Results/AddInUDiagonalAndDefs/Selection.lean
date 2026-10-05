/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
SelfImprovement/Theorems/Results/AddInUDiagonalAndDefs/Selection.lean, to the symmetric model
of `planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Basic.SubMeasurementFamilies
public import MIPRE.Background.LIDT.Co.Basic.DistributionAvg
public import MIPRE.Background.LIDT.Co.Preliminaries.PolynomialAgreement
public import MIPRE.Background.LIDT.Co.Preliminaries.SelfConsistency.DataProcessing
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Statements
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Results.CommonHelpers
public import MIPStarRE.LDT.SelfImprovement.Theorems.Thresholds.Final
public import MIPStarRE.LDT.SelfImprovement.Theorems.Results.AddInUDiagonalAndDefs.Selection

@[expose] public section

/-!
# Diagonal add-in-u selection and point-sandwich endpoints

The diagonal selection used in the strong-self-consistency application of the add-in-`u` lemma,
the endpoint identities for its left and right sides, the point-projector insertion identities,
and the Schwartz--Zippel collision endpoints used by the helper strong-self-consistency argument:
the counterpart of the vendored
`SelfImprovement/Theorems/Results/AddInUDiagonalAndDefs/Selection.lean` (under
`MIPRE/Background/LIDT/MIPStarRE/LDT/`) in the port of `planning/c6b-plan.md` (milestone M10, section "Port conventions").

A strategy is a `SymStrat params 𝔓 K`; the helper submeasurements live in `𝔓` and the `add-in-u`
operators are joint operators `K →L[ℂ] K`, built with `strategy.state.opTensor`. The selection
`selfConsistencyAddInUSelection` is classical and imported from the vendored file. The vendored
collision bound passed `hnorm := strategy.isNormalized` to
`Preliminaries.polynomialCollision_sandwichTensor_le_mdq`, whose ported form takes no
normalization hypothesis, and `leftTensor_mul_rightTensor_eq_opTensor` holds by `rfl`. The
state-free `proj_outer_sandwich_eq` holds in any semigroup.

## Not ported

- `selfConsistencyAddInUSelection`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/self_improvement.tex` lines 247--252, 455--468
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.SelfImprovement

open MIPStarRE.LDT (Parameters FieldModel Point Fq avgOver uniformDistribution
  avgOver_congr avgOver_sum avgOver_mono avgOver_nonneg avgOver_uniform_le_const)
open MIPStarRE.LDT.SelfImprovement (addInUSelectionPairs addInUError
  selfConsistencyAddInUSelection)
open MIPRE.LIDT.Co.GlobalVariance (pointConditionedOutcomeOperatorAtPolynomial)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The diagonal selection at a point: the selected pairs `(h, h)` re-indexed by `h`. -/
theorem addInULeftOperatorAtPoint_selfConsistencySelection
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (M : IdxSubMeas (Point params) (MIPStarRE.LDT.Polynomial params) 𝔓)
    (H : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (u : Point params) :
    addInULeftOperatorAtPoint params strategy M H (selfConsistencyAddInUSelection params) u =
      ∑ h : MIPStarRE.LDT.Polynomial params,
        strategy.state.opTensor ((M u).outcome h) (H.outcome h) := by
  classical
  unfold addInULeftOperatorAtPoint selfConsistencyAddInUSelection addInUSelectionPairs
  symm
  refine Finset.sum_bij (fun h _ => (h, h)) ?_ ?_ ?_ ?_
  · intro h _
    simp
  · intro a _ _ _ hab
    exact congrArg Prod.fst hab
  · intro ah hah
    refine ⟨ah.1, Finset.mem_univ _, ?_⟩
    simp at hah
    ext <;> simp [hah]
  · intro h _
    rfl

/-- The right `add-in-u` operator at a point for the diagonal selection, re-indexed by `h`. -/
theorem addInURightOperatorAtPoint_selfConsistencySelection
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (M : IdxSubMeas (Point params) (MIPStarRE.LDT.Polynomial params) 𝔓)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (u : Point params) :
    addInURightOperatorAtPoint params strategy M T (selfConsistencyAddInUSelection params) u =
      ∑ h : MIPStarRE.LDT.Polynomial params,
        let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
        strategy.state.opTensor (Au * (M u).outcome h * Au) (T.outcome h) := by
  classical
  unfold addInURightOperatorAtPoint selfConsistencyAddInUSelection addInUSelectionPairs
  symm
  refine Finset.sum_bij (fun h _ => (h, h)) ?_ ?_ ?_ ?_
  · intro h _
    simp
  · intro a _ _ _ hab
    exact congrArg Prod.fst hab
  · intro ah hah
    refine ⟨ah.1, Finset.mem_univ _, ?_⟩
    simp at hah
    ext <;> simp [hah]
  · intro h _
    rfl

/-- The left side of the diagonal `add-in-u` application in the helper
strong-self-consistency proof is exactly the diagonal bipartite match mass of
`Hhat = E_u H^u`.

This formalizes the paper's identity
`∑_h ⟪H_h, H_h⟫ = E_u ∑_h ⟪H^u_h, H_h⟫` used at
`self_improvement.tex`, lines 455--468. -/
theorem addInULeftQuantity_selfConsistencySelection_eq_matchMass
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    addInULeftQuantity params strategy
        (sandwichedPolynomialSubMeasAt params strategy T)
        (averagedSandwichedPolynomialSubMeas params strategy T)
        (selfConsistencyAddInUSelection params) =
      strategy.state.qBipartiteMatchMass
        (averagedSandwichedPolynomialSubMeas params strategy T)
        (averagedSandwichedPolynomialSubMeas params strategy T) := by
  change avgOver (uniformDistribution (Point params)) (fun u =>
      strategy.state.ev (addInULeftOperatorAtPoint params strategy
        (sandwichedPolynomialSubMeasAt params strategy T)
        (averagedSandwichedPolynomialSubMeas params strategy T)
        (selfConsistencyAddInUSelection params) u)) = _
  simp only [addInULeftOperatorAtPoint_selfConsistencySelection, VecState.ev_sum]
  rw [avgOver_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  exact (strategy.state.ev_opTensor_averageOperatorOverDistribution_left _ _ _).symm

/-- The right side of the diagonal `add-in-u` application is the paper's
"release-the-kraken" expression, with the two copies of
`A^u_{h(u)}` placed around the pointwise helper submeasurement `H^u_h`. -/
theorem addInURightQuantity_selfConsistencySelection_eq_release
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    addInURightQuantity params strategy
        (sandwichedPolynomialSubMeasAt params strategy T)
        T
        (selfConsistencyAddInUSelection params) =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : MIPStarRE.LDT.Polynomial params,
          let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
          strategy.state.ev
            (strategy.state.opTensor
              (Au * (sandwichedPolynomialSubMeasAt params strategy T u).outcome h * Au)
              (T.outcome h))) :=
  avgOver_congr (uniformDistribution (Point params)) _ _ fun u => by
    rw [addInURightOperatorAtPoint_selfConsistencySelection]
    exact strategy.state.ev_sum _

/-- Specialization of the missing full `add-in-u` transfer to the diagonal
selection needed for helper strong self-consistency.

The hypothesis is exactly the scalar transfer inequality supplied by the paper's
`lem:add-in-u` after choosing `M^u = H^u` and
`S_u = {(h,h) : h ∈ \polyfunc{m}{q}{d}}`. The conclusion rewrites that
transfer into the paper's displayed step `eq:release-the-kraken`.  The helper
strong-self-consistency assembly now consumes this transfer internally; it is
not a source-theorem hypothesis. -/
theorem selfConsistencyDiagonalAddInU_of_transfer
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (htransfer :
      |addInULeftQuantity params strategy
          (sandwichedPolynomialSubMeasAt params strategy T)
          (averagedSandwichedPolynomialSubMeas params strategy T)
          (selfConsistencyAddInUSelection params) -
        addInURightQuantity params strategy
          (sandwichedPolynomialSubMeasAt params strategy T)
          T
          (selfConsistencyAddInUSelection params)| ≤ addInUError params eps delta) :
    |strategy.state.qBipartiteMatchMass
        (averagedSandwichedPolynomialSubMeas params strategy T)
        (averagedSandwichedPolynomialSubMeas params strategy T) -
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : MIPStarRE.LDT.Polynomial params,
          let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
          strategy.state.ev
            (strategy.state.opTensor
              (Au * (sandwichedPolynomialSubMeasAt params strategy T u).outcome h * Au)
              (T.outcome h)))| ≤ addInUError params eps delta := by
  rwa [addInULeftQuantity_selfConsistencySelection_eq_matchMass,
    addInURightQuantity_selfConsistencySelection_eq_release] at htransfer

/-- Projective sandwich collapse: if `A * A = A`, then `A * (A * X * A) * A = A * X * A`.

This is the operator-algebra fact used to simplify the diagonal `add-in-u`
right-hand side: the outer `A^u_{h(u)}` factors collapse into the inner
sandwich `A^u_{h(u)} T_h A^u_{h(u)}` because
`(strategy.pointMeasurement u).proj` makes every point-measurement outcome a
projection. It is state-free, and holds in any semigroup (the vendored statement is on
`MIPStarRE.Quantum.Op ι`). -/
theorem proj_outer_sandwich_eq {R : Type*} [Semigroup R]
    (A X : R) (hA : A * A = A) :
    A * (A * X * A) * A = A * X * A := by
  calc A * (A * X * A) * A = (A * A) * X * (A * A) := by simp only [mul_assoc]
    _ = A * X * A := by rw [hA]

/-- Insert the point projector around a sandwiched helper outcome.

For fixed `u`, the operator
`H^u_{h'} = A^u_{h'(u)} T_{h'} A^u_{h'(u)}` survives the outer sandwich by
`A^u_{h(u)}` precisely when the two polynomials agree at `u`.  This is the
operator form of the paper identity labelled `eq:h-blt`. -/
theorem pointConditioned_sandwichedPolynomialOutcome_outer_eq_ite
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (u : Point params) (h h' : MIPStarRE.LDT.Polynomial params) :
    let Ah := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
    Ah * ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h') * Ah =
      if h u = h' u then
        (sandwichedPolynomialSubMeasAt params strategy T u).outcome h'
      else
        0 := by
  intro Ah
  let Ah' := pointConditionedOutcomeOperatorAtPolynomial params strategy h' u
  change Ah * (Ah' * T.outcome h' * Ah') * Ah = if h u = h' u then Ah' * T.outcome h' * Ah' else 0
  by_cases heval : h u = h' u
  · rw [ite_eq_left heval]
    have hAA : Ah' = Ah := by
      simp only [Ah, Ah', pointConditionedOutcomeOperatorAtPolynomial, heval]
    rw [hAA]
    exact proj_outer_sandwich_eq Ah (T.outcome h') ((strategy.pointMeasurement u).proj (h u))
  · rw [ite_eq_right heval]
    have horth : Ah * Ah' = 0 :=
      ProjMeas.outcome_orthogonal (strategy.pointMeasurement u) (h u) (h' u) heval
    calc
      Ah * (Ah' * T.outcome h' * Ah') * Ah = (Ah * Ah') * T.outcome h' * Ah' * Ah := by
        simp only [mul_assoc]
      _ = 0 := by rw [horth, zero_mul, zero_mul, zero_mul]

/-- Expectation form of the point-projector insertion identity.

This is the scalar version of
`pointConditioned_sandwichedPolynomialOutcome_outer_eq_ite`, with the agreement
condition written as the real-valued indicator that appears in the paper's
off-diagonal residual estimate. -/
theorem ev_opTensor_pointConditioned_sandwichedPolynomialOutcome_outer_eq_indicator
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (u : Point params) (h h' : MIPStarRE.LDT.Polynomial params) :
    let Ah := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
    strategy.state.ev
        (strategy.state.opTensor
          (Ah * ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h') * Ah)
          (T.outcome h)) =
      (if h u = h' u then (1 : ℝ) else 0) *
        strategy.state.ev
          (strategy.state.opTensor
            ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h')
            (T.outcome h)) := by
  intro Ah
  rw [pointConditioned_sandwichedPolynomialOutcome_outer_eq_ite]
  by_cases heval : h u = h' u
  · rw [ite_eq_left heval, ite_eq_left heval, one_mul]
  · rw [ite_eq_right heval, ite_eq_right heval, zero_mul, SymModel.opTensor, map_zero, zero_mul,
      VecState.ev_zero]

/-- Averaged off-diagonal form of the paper identity `eq:h-blt`.

The left-hand side is the off-diagonal contribution after inserting the outer
point projector `A^u_{h(u)}`.  The right-hand side removes that outer sandwich
and records the surviving summands by the agreement indicator
`1_{h(u)=h'(u)}`. -/
theorem polynomial_off_diagonal_outer_sandwich_eq_indicator_avg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : MIPStarRE.LDT.Polynomial params,
          ∑ h' ∈ (Finset.univ : Finset (MIPStarRE.LDT.Polynomial params)).erase h,
            let Ah := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
            strategy.state.ev
              (strategy.state.opTensor
                (Ah *
                  ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h') *
                  Ah)
                (T.outcome h))) =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : MIPStarRE.LDT.Polynomial params,
          ∑ h' ∈ (Finset.univ : Finset (MIPStarRE.LDT.Polynomial params)).erase h,
            (if h u = h' u then (1 : ℝ) else 0) *
              strategy.state.ev
                (strategy.state.opTensor
                  ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h')
                  (T.outcome h))) :=
  avgOver_congr (uniformDistribution (Point params)) _ _ fun u =>
    Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun h' _ =>
      ev_opTensor_pointConditioned_sandwichedPolynomialOutcome_outer_eq_indicator
        params strategy T u h h'

/-- Right multiplication form of the point-projector identity.

For a point `u`, multiplying the pointwise helper outcome `H^u_{h'}` on the
right by `A^u_{h(u)}` retains exactly the summands with `h(u)=h'(u)`.  Together
with `pointConditioned_sandwichedPolynomialOutcome_outer_eq_ite`, this is the
operator identity used to pass from the enlarged outer-sandwich expression to
the paper's `eq:delete-an-A` form. -/
theorem sandwichedPolynomialOutcome_mul_pointConditioned_eq_ite
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (u : Point params) (h h' : MIPStarRE.LDT.Polynomial params) :
    let Ah := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
    ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h') * Ah =
      if h u = h' u then
        (sandwichedPolynomialSubMeasAt params strategy T u).outcome h'
      else
        0 := by
  intro Ah
  let Ah' := pointConditionedOutcomeOperatorAtPolynomial params strategy h' u
  change Ah' * T.outcome h' * Ah' * Ah = if h u = h' u then Ah' * T.outcome h' * Ah' else 0
  by_cases heval : h u = h' u
  · rw [ite_eq_left heval]
    have hAA : Ah' = Ah := by
      simp only [Ah, Ah', pointConditionedOutcomeOperatorAtPolynomial, heval]
    rw [hAA, mul_assoc _ Ah Ah]
    exact congrArg (Ah * T.outcome h' * ·) ((strategy.pointMeasurement u).proj (h u))
  · rw [ite_eq_right heval]
    have horth : Ah' * Ah = 0 :=
      ProjMeas.outcome_orthogonal (strategy.pointMeasurement u) (h' u) (h u) (Ne.symm heval)
    rw [mul_assoc _ Ah' Ah, horth, mul_zero]

/-- The full outer point-sandwich equals the one-sided `delete-an-A` form.

This is the operator identity underlying the paper's passage from the enlarged
sum in `eq:threw-in-h-prime` to `eq:delete-an-A`. -/
theorem pointConditioned_sandwichedPolynomialOutcome_outer_eq_right
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (u : Point params) (h h' : MIPStarRE.LDT.Polynomial params) :
    let Ah := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
    Ah * ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h') * Ah =
      ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h') * Ah :=
  (pointConditioned_sandwichedPolynomialOutcome_outer_eq_ite params strategy T u h h').trans
    (sandwichedPolynomialOutcome_mul_pointConditioned_eq_ite params strategy T u h h').symm

/-- Schwartz--Zippel bound for the point-measurement sandwich collision term.

After the two variance swaps in the helper strong self-consistency proof, the
polynomial-agreement indicator is independent of the point `v` at which the
outer point measurement is evaluated.  Averaging over `v`, the tensor-form
Schwartz--Zippel estimate from the preliminaries bounds the whole collision
term by `m d / q` (its vendored hypothesis `hnorm` is a theorem of the model). -/
theorem polynomial_collision_pointMeasurement_sandwichTensor_avg_le_mdq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    avgOver (uniformDistribution (Point params)) (fun v =>
        ∑ gg : MIPStarRE.LDT.Polynomial params × MIPStarRE.LDT.Polynomial params,
          ∑ a : Fq params,
            (if gg.1 = gg.2 then 0 else
              avgOver (uniformDistribution (Point params))
                (fun u => if gg.1 u = gg.2 u then (1 : ℝ) else 0)) *
              strategy.state.ev
                (strategy.state.opTensor
                  ((strategy.pointMeasurement v).outcome a *
                    T.outcome gg.1 *
                    (strategy.pointMeasurement v).outcome a)
                  (T.outcome gg.2))) ≤
      (params.m * params.d : ℝ) / params.q :=
  avgOver_uniform_le_const _ _ fun v =>
    Preliminaries.polynomialCollision_sandwichTensor_le_mdq params strategy.state
      (strategy.pointMeasurement v).toSubMeas T T

/-- Schwartz--Zippel bound for the selected off-diagonal residual endpoint.

This is the endpoint used after the variance swaps in the helper
strong-self-consistency residual estimate.  The selected outer point-measurement
outcome `A^v_{h(v)}` is bounded by the full sum over field outcomes in
`polynomial_collision_pointMeasurement_sandwichTensor_avg_le_mdq`. -/
theorem polynomial_off_diagonal_swapped_indicator_sandwich_avg_le_mdq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    avgOver (uniformDistribution (Point params)) (fun v =>
        ∑ h : MIPStarRE.LDT.Polynomial params,
          ∑ h' ∈ (Finset.univ : Finset (MIPStarRE.LDT.Polynomial params)).erase h,
            avgOver (uniformDistribution (Point params))
                (fun u => if h u = h' u then (1 : ℝ) else 0) *
              strategy.state.ev
                (strategy.state.opTensor
                  (pointConditionedOutcomeOperatorAtPolynomial params strategy h v *
                    T.outcome h' *
                    pointConditionedOutcomeOperatorAtPolynomial params strategy h v)
                  (T.outcome h))) ≤
      (params.m * params.d : ℝ) / params.q := by
  refine (avgOver_mono _ _ _ fun v => ?_).trans
    (polynomial_collision_pointMeasurement_sandwichTensor_avg_le_mdq params strategy T)
  let Outer : SubMeas (Fq params) 𝔓 := (strategy.pointMeasurement v).toSubMeas
  let F : Fq params → MIPStarRE.LDT.Polynomial params → MIPStarRE.LDT.Polynomial params → ℝ :=
    fun a i r =>
      (if i = r then 0 else
        avgOver (uniformDistribution (Point params))
          (fun u => if i u = r u then (1 : ℝ) else 0)) *
        strategy.state.ev
          (strategy.state.opTensor (Outer.outcome a * T.outcome i * Outer.outcome a)
            (T.outcome r))
  have hF_nonneg (a i r) : 0 ≤ F a i r := by
    refine mul_nonneg ?_ (strategy.state.sandwichTensorSummand_nonneg Outer T T a i r)
    split_ifs
    · exact le_rfl
    · exact avgOver_nonneg _ _ fun u => by split_ifs <;> norm_num
  calc
    _ = ∑ h : MIPStarRE.LDT.Polynomial params,
          ∑ h' ∈ (Finset.univ : Finset (MIPStarRE.LDT.Polynomial params)).erase h,
            F (h v) h' h := by
        refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun h' hh' => ?_
        have hne : h' ≠ h := (Finset.mem_erase.mp hh').1
        have hcoef :
            avgOver (uniformDistribution (Point params))
                (fun u => if h u = h' u then (1 : ℝ) else 0) =
              avgOver (uniformDistribution (Point params))
                (fun u => if h' u = h u then (1 : ℝ) else 0) :=
          avgOver_congr _ _ _ fun u => by simp only [eq_comm]
        simp only [F, Outer, hcoef, ite_eq_right hne]
        rfl
    _ ≤ ∑ h : MIPStarRE.LDT.Polynomial params,
          ∑ h' : MIPStarRE.LDT.Polynomial params, F (h v) h' h :=
        Finset.sum_le_sum fun h _ =>
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset h Finset.univ)
            fun h' _ _ => hF_nonneg (h v) h' h
    _ ≤ ∑ h : MIPStarRE.LDT.Polynomial params,
          ∑ h' : MIPStarRE.LDT.Polynomial params, ∑ a : Fq params, F a h' h :=
        Finset.sum_le_sum fun h _ => Finset.sum_le_sum fun h' _ =>
          Finset.single_le_sum (fun a _ => hF_nonneg a h' h) (Finset.mem_univ (h v))
    _ = _ := by
        rw [Finset.sum_comm, Fintype.sum_prod_type]

/-- Projective simplification of the diagonal `add-in-u` right operator at a point.

Combining `addInURightOperatorAtPoint_selfConsistencySelection` with the
projectivity of `strategy.pointMeasurement` (each `A^u_a * A^u_a = A^u_a`),
the at-point operator collapses to the simpler tensor sum
`Σ_h H^u_h ⊗ T_h` where `H^u_h = sandwichedPolynomialSubMeasAt T u h`. -/
theorem addInURightOperatorAtPoint_selfConsistencySelection_proj_eq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (u : Point params) :
    addInURightOperatorAtPoint params strategy
        (sandwichedPolynomialSubMeasAt params strategy T)
        T
        (selfConsistencyAddInUSelection params) u =
      ∑ h : MIPStarRE.LDT.Polynomial params,
        strategy.state.opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
          (T.outcome h) := by
  rw [addInURightOperatorAtPoint_selfConsistencySelection]
  refine Finset.sum_congr rfl fun h _ => congrArg (strategy.state.opTensor · (T.outcome h)) ?_
  exact proj_outer_sandwich_eq _ _ ((strategy.pointMeasurement u).proj (h u))

/-- Projective simplification of the diagonal `add-in-u` right quantity.

This is the projection-collapsed paper expression: the two outer
`A^u_{h(u)}` factors absorb into the inner sandwich `H^u_h = A^u_{h(u)}
T_h A^u_{h(u)}`, leaving the cleaner form
`E_u Σ_h ⟨ψ, H^u_h ⊗ T_h ψ⟩` used in the simplified scalar transfer. -/
theorem addInURightQuantity_selfConsistencySelection_eq_simplified
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    addInURightQuantity params strategy
        (sandwichedPolynomialSubMeasAt params strategy T)
        T
        (selfConsistencyAddInUSelection params) =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : MIPStarRE.LDT.Polynomial params,
          strategy.state.ev
            (strategy.state.opTensor
              ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
              (T.outcome h))) :=
  avgOver_congr (uniformDistribution (Point params)) _ _ fun u => by
    rw [addInURightOperatorAtPoint_selfConsistencySelection_proj_eq]
    exact strategy.state.ev_sum _

end MIPRE.LIDT.Co.SelfImprovement

end

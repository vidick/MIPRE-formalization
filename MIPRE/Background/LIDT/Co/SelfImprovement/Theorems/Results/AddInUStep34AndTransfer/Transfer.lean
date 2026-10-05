/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
SelfImprovement/Theorems/Results/AddInUStep34AndTransfer/Transfer.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Results.AddInUStep34AndTransfer.Selected
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Results.AddInUStep34AndTransfer.Variance
public import MIPStarRE.LDT.SelfImprovement.Theorems.Results.AddInUStep34AndTransfer.Transfer

@[expose] public section

/-!
# Add-in-u scalar transfer and off-diagonal expansion

Assembly of the four add-in-u scalar moves, the arithmetic absorption of the paper, and the
residual off-diagonal expansion used by the helper strong self-consistency argument: the
counterpart of the vendored `SelfImprovement/Theorems/Results/AddInUStep34AndTransfer/Transfer.lean`
(under `MIPRE/Background/LIDT/MIPStarRE/LDT/`) in the port of `planning/c6b-plan.md` (milestone
M10, section "Port conventions").

## Contents

- `add_in_u_simplified_transfer_of_cs_chain`, `add_in_u_selected_transfer_of_cs_chain`: the
  triangle inequality along `Q₀ → Q₁ → Q₂ → Q₃ → Q₄`, for the diagonal and the selected chains.
- `add_in_u_simplified_transfer_of_cs_chain_sqrt_form` and its `_local_variance_form` and
  `_selfConsistency_local_variance_form` closings, which discharge the four step bounds in turn.
- `selfConsistencyDiagonalAddInU_of_simplifiedTransfer`: the projection-simplified transfer gives
  the released one.
- `helper_mass_sub_release_eq_polynomial_off_diagonal`: the helper mass minus the released right
  side is the off-diagonal sum `E_u ∑_h ∑_{h' ≠ h} ⟨ψ, H^u_{h'} ⊗ T_h ψ⟩`.

Every scalar is `strategy.state.ev` of a joint operator; `opTensor A B` is
`strategy.state.opTensor A B`, `leftTensor (ι₂ := ι) A` is `strategy.state.L A`,
`qBipartiteMatchMass strategy.state` and `subMeasMass strategy.state` are the `SymModel`/`VecState`
declarations reached by dot notation, and `A.liftLeft` is `A.liftLeft strategy.state`. The vendored
`try rfl` step `ev (leftTensor X) = ev (opTensor X 1)` is the keystone's `rightTensor_one` under
`mul_one`. No
statement of the vendored file carries a swap, density or normalization hypothesis, so no statement
changed; the file sets no option, the vendored file-wide `respectTransparency false` not being
needed.

The vendored module is imported for its three classical declarations; its imports, the vendored
`AddInUStep34AndTransfer/{Selected,Variance}`, are already imported by Co `Selected` and `Variance`.

## Not ported

- `two_sqrt_two_mul_add_two_sqrt_le_four_sqrt`: classical, imported.
- `two_mul_delta_le_selfImprovementVarianceError`: classical, imported.
- `two_sqrt_two_delta_add_two_sqrt_selfImprovementVarianceError_le_addInUError`: classical,
  imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/self_improvement.tex` lines 341--343
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.SelfImprovement

open MIPStarRE.LDT (Parameters FieldModel Point avgOver uniformDistribution avgOver_congr
  avgOver_sub)
open MIPStarRE.LDT.GlobalVariance (localVarianceOfPointsError)
open MIPStarRE.LDT.SelfImprovement (AddInUSelection selfConsistencyAddInUSelection
  selfImprovementVarianceError addInUError
  two_sqrt_two_delta_add_two_sqrt_selfImprovementVarianceError_le_addInUError)
open MIPRE.LIDT.Co.GlobalVariance (pointConditionedOutcomeOperatorAtPolynomial
  localVarianceDeviationAtPolynomial)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The four-term triangle inequality `|Q₀ − Q₄| ≤ ∑ |Qᵢ − Qᵢ₊₁|` behind both chain assemblies. -/
private theorem abs_sub_le_four_steps (Q0 Q1 Q2 Q3 Q4 : ℝ) :
    |Q0 - Q4| ≤ |Q0 - Q1| + |Q1 - Q2| + |Q2 - Q3| + |Q3 - Q4| := by
  calc
    |Q0 - Q4| = |(Q0 - Q1) + (Q1 - Q2) + (Q2 - Q3) + (Q3 - Q4)| := by ring_nf
    _ ≤ |Q0 - Q1| + |Q1 - Q2| + |Q2 - Q3| + |Q3 - Q4| := by
      have h1 := abs_add_le ((Q0 - Q1) + (Q1 - Q2) + (Q2 - Q3)) (Q3 - Q4)
      have h2 := abs_add_le ((Q0 - Q1) + (Q1 - Q2)) (Q2 - Q3)
      have h3 := abs_add_le (Q0 - Q1) (Q1 - Q2)
      linarith

/-- Assemble the projection-simplified scalar transfer from the four scalar
chain moves. The analytic work remains exactly the four bounds
`Q₀ ≈ Q₁`, `Q₁ ≈ Q₂`, `Q₂ ≈ Q₃`, and `Q₃ ≈ Q₄`, plus the final arithmetic
absorption into `addInUError`. -/
theorem add_in_u_simplified_transfer_of_cs_chain
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (η01 η12 η23 η34 : ℝ)
    (h01 :
      |addInUCSChainQ0 params strategy T - addInUCSChainQ1 params strategy T| ≤ η01)
    (h12 :
      |addInUCSChainQ1 params strategy T - addInUCSChainQ2 params strategy T| ≤ η12)
    (h23 :
      |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤ η23)
    (h34 :
      |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤ η34)
    (hsum : η01 + η12 + η23 + η34 ≤ addInUError params eps delta) :
    |strategy.state.qBipartiteMatchMass
        (averagedSandwichedPolynomialSubMeas params strategy T)
        (averagedSandwichedPolynomialSubMeas params strategy T) -
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : MIPStarRE.LDT.Polynomial params,
          strategy.state.ev
            (strategy.state.opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
              (T.outcome h)))| ≤ addInUError params eps delta := by
  rw [add_in_u_cs_chain_q0_eq_match_mass, ← add_in_u_cs_chain_q4_eq_simplified_rhs]
  have := abs_sub_le_four_steps (addInUCSChainQ0 params strategy T)
    (addInUCSChainQ1 params strategy T) (addInUCSChainQ2 params strategy T)
    (addInUCSChainQ3 params strategy T) (addInUCSChainQ4 params strategy T)
  linarith

/-- Assemble the selected add-in-`u` scalar transfer from the four selected
scalar chain moves.

This is the selection-parametrized counterpart of
`add_in_u_simplified_transfer_of_cs_chain`.  The endpoints are the theorem-side
generic add-in-u quantities rather than the diagonal match-mass and simplified
release quantities. -/
theorem add_in_u_selected_transfer_of_cs_chain
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    (M : IdxSubMeas (Point params) Outcome 𝔓)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (S : AddInUSelection params Outcome)
    (η01 η12 η23 η34 : ℝ)
    (h01 :
      |addInUSelectedCSChainQ0 params strategy M T S -
        addInUSelectedCSChainQ1 params strategy M T S| ≤ η01)
    (h12 :
      |addInUSelectedCSChainQ1 params strategy M T S -
        addInUSelectedCSChainQ2 params strategy M T S| ≤ η12)
    (h23 :
      |addInUSelectedCSChainQ2 params strategy M T S -
        addInUSelectedCSChainQ3 params strategy M T S| ≤ η23)
    (h34 :
      |addInUSelectedCSChainQ3 params strategy M T S -
        addInUSelectedCSChainQ4 params strategy M T S| ≤ η34)
    (hsum : η01 + η12 + η23 + η34 ≤ addInUError params eps delta) :
    |addInULeftQuantity params strategy M
        (averagedSandwichedPolynomialSubMeas params strategy T) S -
      addInURightQuantity params strategy M T S| ≤ addInUError params eps delta := by
  rw [addInUSelectedCSChainQ0_eq_leftQuantity_averagedSandwiched,
    addInUSelectedCSChainQ4_eq_rightQuantity]
  have := abs_sub_le_four_steps (addInUSelectedCSChainQ0 params strategy M T S)
    (addInUSelectedCSChainQ1 params strategy M T S) (addInUSelectedCSChainQ2 params strategy M T S)
    (addInUSelectedCSChainQ3 params strategy M T S) (addInUSelectedCSChainQ4 params strategy M T S)
  linarith

/-- Wrapper composing `add_in_u_simplified_transfer_of_cs_chain` with the
arithmetic absorption: when the four chain step bounds have the paper-faithful
shapes `√(2 δ)`, `√(2 δ)`, `√(ζ_variance)`, `√(ζ_variance)`, the
projection-simplified transfer holds with the displayed
`addInUError = 4 ζ_variance^{1/2}`. -/
theorem add_in_u_simplified_transfer_of_cs_chain_sqrt_form
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (h01 :
      |addInUCSChainQ0 params strategy T - addInUCSChainQ1 params strategy T| ≤
        Real.sqrt (2 * delta))
    (h12 :
      |addInUCSChainQ1 params strategy T - addInUCSChainQ2 params strategy T| ≤
        Real.sqrt (2 * delta))
    (h23 :
      |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
        Real.sqrt (selfImprovementVarianceError params eps delta))
    (h34 :
      |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
        Real.sqrt (selfImprovementVarianceError params eps delta)) :
    |strategy.state.qBipartiteMatchMass
        (averagedSandwichedPolynomialSubMeas params strategy T)
        (averagedSandwichedPolynomialSubMeas params strategy T) -
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : MIPStarRE.LDT.Polynomial params,
          strategy.state.ev
            (strategy.state.opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
              (T.outcome h)))| ≤ addInUError params eps delta :=
  add_in_u_simplified_transfer_of_cs_chain params strategy eps delta T _ _ _ _
    h01 h12 h23 h34 (by
      have := two_sqrt_two_delta_add_two_sqrt_selfImprovementVarianceError_le_addInUError
        params eps delta heps hdelta
      linarith)

/-- Projection-simplified add-in-`u` transfer with the Step 3/4 variance bounds
supplied by the local-variance sum hypothesis.

After the factor estimates of Co `AddInUStep34AndTransfer/Variance`, the remaining scalar
hypotheses are only the two self-consistency moves `Q₀ → Q₁` and `Q₁ → Q₂`, together with the
local-variance sum bound from the GlobalVariance theorem. -/
theorem add_in_u_simplified_transfer_of_cs_chain_local_variance_form
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hlocal :
      (∑ g : MIPStarRE.LDT.Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤
        localVarianceOfPointsError params eps delta)
    (h01 :
      |addInUCSChainQ0 params strategy T - addInUCSChainQ1 params strategy T| ≤
        Real.sqrt (2 * delta))
    (h12 :
      |addInUCSChainQ1 params strategy T - addInUCSChainQ2 params strategy T| ≤
        Real.sqrt (2 * delta)) :
    |strategy.state.qBipartiteMatchMass
        (averagedSandwichedPolynomialSubMeas params strategy T)
        (averagedSandwichedPolynomialSubMeas params strategy T) -
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : MIPStarRE.LDT.Polynomial params,
          strategy.state.ev
            (strategy.state.opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
              (T.outcome h)))| ≤ addInUError params eps delta :=
  have hsteps :=
    add_in_u_cs_chain_global_variance_steps_of_local_sum_bound_from_factor_bounds
      params strategy eps delta T hlocal
  add_in_u_simplified_transfer_of_cs_chain_sqrt_form
    params strategy eps delta heps hdelta T h01 h12 hsteps.1 hsteps.2

/-- Projection-simplified add-in-`u` transfer from point self-consistency and
the local-variance sum bound.

This closes all four scalar moves in the add-in-`u` chain: Step 1 and Step 2
come from point-measurement self-consistency, while Step 3 and Step 4 are
supplied by the local-variance form above. -/
theorem add_in_u_simplified_transfer_of_cs_chain_selfConsistency_local_variance_form
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hssc : strategy.state.BipartiteSSCRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta)
    (hlocal :
      (∑ g : MIPStarRE.LDT.Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤
        localVarianceOfPointsError params eps delta) :
    |strategy.state.qBipartiteMatchMass
        (averagedSandwichedPolynomialSubMeas params strategy T)
        (averagedSandwichedPolynomialSubMeas params strategy T) -
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : MIPStarRE.LDT.Polynomial params,
          strategy.state.ev
            (strategy.state.opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
              (T.outcome h)))| ≤ addInUError params eps delta :=
  add_in_u_simplified_transfer_of_cs_chain_local_variance_form
    params strategy eps delta heps hdelta T hlocal
    (addInU_cs_chain_step1_abs_le_sqrt_two_delta params strategy T delta hssc)
    (addInU_cs_chain_step2_abs_le_sqrt_two_delta params strategy T delta hssc)

/-- Specialization of the diagonal add-in-`u` transfer to the projection-simplified scalar
transfer hypothesis.

The hypothesis is stated against the cleaner right-hand side `E_u Σ_h ⟨ψ, H^u_h ⊗ T_h ψ⟩`
obtained after collapsing the outer projection factors of `eq:release-the-kraken` via
`proj_outer_sandwich_eq`; the conclusion is the released form, with `A^u_{h(u)}` on both sides
of `H^u_h`. Both right-hand sides are `addInURightQuantity` of the self-consistency selection. -/
theorem selfConsistencyDiagonalAddInU_of_simplifiedTransfer
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (htransfer :
      |strategy.state.qBipartiteMatchMass
          (averagedSandwichedPolynomialSubMeas params strategy T)
          (averagedSandwichedPolynomialSubMeas params strategy T) -
        avgOver (uniformDistribution (Point params)) (fun u =>
          ∑ h : MIPStarRE.LDT.Polynomial params,
            strategy.state.ev
              (strategy.state.opTensor
                ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
                (T.outcome h)))| ≤ addInUError params eps delta) :
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
  rwa [← addInURightQuantity_selfConsistencySelection_eq_release,
    addInURightQuantity_selfConsistencySelection_eq_simplified]

/-- Exact residual-side expansion for the helper strong self-consistency proof.

For the averaged helper `Hhat = E_u H^u` produced from the primal measurement
`T`, the difference between the helper left mass and the released diagonal
add-in-`u` right-hand side is precisely the contribution of the off-diagonal
polynomial pairs `(h',h)` with `h' ≠ h`:

`E_u \sum_h \sum_{h'≠h} ⟨ψ, H^u_{h'} ⊗ T_h ψ⟩`.

This is the exact algebraic opening of the residual `helper_left_mass - release-the-kraken`;
the later Cauchy--Schwarz, Schwartz--Zippel, point-consistency, and self-consistency estimates
bound this off-diagonal expression in the proof of `item:self-improvement-self`. It differs from
the paper's intermediate "threw-in-`h'`" expression, where the off-diagonal helper operator is
still sandwiched by `A^u_{h(u)}`. -/
theorem helper_mass_sub_release_eq_polynomial_off_diagonal
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓) :
    strategy.state.subMeasMass
        ((averagedSandwichedPolynomialSubMeas params strategy T.toSubMeas).liftLeft
          strategy.state) -
      addInURightQuantity params strategy
        (sandwichedPolynomialSubMeasAt params strategy T.toSubMeas)
        T.toSubMeas
        (selfConsistencyAddInUSelection params) =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : MIPStarRE.LDT.Polynomial params,
          ∑ h' ∈ (Finset.univ : Finset (MIPStarRE.LDT.Polynomial params)).erase h,
            strategy.state.ev
              (strategy.state.opTensor
                ((sandwichedPolynomialSubMeasAt params strategy T.toSubMeas u).outcome h')
                (T.toSubMeas.outcome h))) := by
  classical
  rw [helper_mass_eq_avg_pointwise_sandwich_sum,
    addInURightQuantity_selfConsistencySelection_eq_simplified, ← avgOver_sub]
  refine avgOver_congr (uniformDistribution (Point params)) _ _ fun u => ?_
  have hmass : ∀ h' : MIPStarRE.LDT.Polynomial params,
      strategy.state.ev
          (strategy.state.L
            (sandwichedPolynomialOutcomeOperatorAt params strategy T.toSubMeas u h')) =
        ∑ h : MIPStarRE.LDT.Polynomial params,
          strategy.state.ev
            (strategy.state.opTensor
              ((sandwichedPolynomialSubMeasAt params strategy T.toSubMeas u).outcome h')
              (T.toSubMeas.outcome h)) := fun h' => by
    rw [← strategy.state.ev_sum, ← strategy.state.opTensor_sum_right_univ,
      T.toSubMeas.sum_eq_total, T.total_eq_one]
    exact congrArg strategy.state.ev
      ((congrArg (strategy.state.L _ * ·) strategy.state.rightTensor_one).trans (mul_one _)).symm
  simp only [hmass]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun h _ =>
    (Finset.sum_erase_eq_sub (s := Finset.univ) (a := h)
      (f := fun h' =>
        strategy.state.ev
          (strategy.state.opTensor
            ((sandwichedPolynomialSubMeasAt params strategy T.toSubMeas u).outcome h')
            (T.toSubMeas.outcome h))) (Finset.mem_univ h)).symm

end MIPRE.LIDT.Co.SelfImprovement

end

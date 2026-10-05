/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
SelfImprovement/Theorems/Results/AddInUStep34AndTransfer/Factored.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Basic.SubMeasurementFamilies
public import MIPRE.Background.LIDT.Co.GlobalVariance.Defs.Families
public import MIPRE.Background.LIDT.Co.Preliminaries.SelfConsistency.DataProcessing
public import MIPStarRE.LDT.SelfImprovement.Theorems.Thresholds.Final
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Statements
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Results.CommonHelpers
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Results.AddInUDiagonalAndDefs.Residual
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Results.AddInUDiagonalAndDefs.ScalarChain
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Results.AddInUStep12.Raw
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Results.AddInUStep12.Selected
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Results.HelperCompleteness.Bracketed
public import MIPStarRE.LDT.SelfImprovement.Theorems.Results.AddInUStep34AndTransfer.Factored

@[expose] public section

/-!
# Add-in-u Step 3/4 factored Cauchy--Schwarz bounds

Real-valued variance-bound conversions and the non-selected factored Cauchy--Schwarz estimates
for the `Q₂ → Q₃` and `Q₃ → Q₄` add-in-u moves: the counterpart of the vendored
`SelfImprovement/Theorems/Results/AddInUStep34AndTransfer/Factored.lean` (under
`MIPRE/Background/LIDT/MIPStarRE/LDT/`) in the port of `planning/c6b-plan.md` (milestone M10,
section "Port conventions").

## Contents

- `add_in_u_cs_chain_q2_q3_le_sqrt_of_factor_bounds`,
  `add_in_u_cs_chain_q3_q4_le_sqrt_of_factor_bounds`: a factored bound `√D₁ · √D₂` with one
  factor at most the summed independent-points deviation and the other at most `1` gives
  `|Q₂ − Q₃|`, resp. `|Q₃ − Q₄|`, at most the square root of that sum.
- `add_in_u_cs_chain_q2_q3_factored_cs`, `add_in_u_cs_chain_q3_q4_factored_cs`: the operator
  Cauchy--Schwarz bounds themselves, `S.ev_opTensor_sandwich_abs_le_sqrt` (Co
  `Basic/OperatorExpectations`) at each `(u, v, h)`, lifted through the imported weighted
  Cauchy--Schwarz `addInU_weighted_cauchy_schwarz`.

Every scalar is `strategy.state.ev` of a joint operator; `opTensor A B` is
`strategy.state.opTensor A B`, and `Xᴴ` is `star X`. The vendored Hermitian facts
`SubMeas.outcome_hermitian …` and `rw [Matrix.conjTranspose_sub, hAu_herm, hAv_herm]` are
`(IsSelfAdjoint.of_nonneg …).star_eq` and `star_sub`; the vendored positivity of
`X · H · X` through `star_left_conjugate_nonneg` and `simpa [Matrix.star_eq_conjTranspose]` is
`IsSelfAdjoint.conjugate_nonneg`, with the keystone's `opTensor_nonneg` and `ev_nonneg_of_psd`.
The vendored file has no swap, density or normalization hypothesis, so no statement changed.

The vendored module is imported for its three classical declarations. It keeps the vendored
`HelperCompleteness/Bracketed`, `SdpMatrixBridge` and `MatrixRealization/` in the import closure,
prebuilt; no Co file names them (they are replaced by M9's summed form, see Co
`HelperCompleteness/Bracketed`).

## Not ported

- `addInU_le_sqrt_of_factor_bounds_right`: classical, imported.
- `addInU_le_sqrt_of_factor_bounds_left`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/self_improvement.tex` lines 299--340
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.SelfImprovement

open MIPStarRE.LDT (Parameters FieldModel Point avgOver uniformDistribution)
open MIPStarRE.LDT.SelfImprovement (addInU_le_sqrt_of_factor_bounds_right
  addInU_le_sqrt_of_factor_bounds_left)
open MIPRE.LIDT.Co.GlobalVariance (pointConditionedOutcomeOperatorAtPolynomial
  globalVarianceDeviationAtPolynomial)

/-- Upstream keeps this helper `private` since its Lean-module port (`LionSR/MIPStarRE` at `5fc363b`); the port carries its own copy, with upstream's proof.

Weighted Cauchy--Schwarz for the non-selected add-in-`u` Step 3/4
summands.

The non-selected Step 3 and Step 4 estimates use the same finite inequality
over independent point pairs and polynomial outcomes.  This helper fixes that
common summation structure, leaving the two applications to supply only their
step-specific summands and pointwise operator Cauchy--Schwarz estimates. -/
theorem addInU_weighted_cauchy_schwarz
    (params : Parameters) [FieldModel params.q]
    (t x y : Point params × Point params → MIPStarRE.LDT.Polynomial params → ℝ)
    (ht : ∀ uv h, |t uv h| ≤ Real.sqrt (x uv h) * Real.sqrt (y uv h))
    (hx : ∀ uv h, 0 ≤ x uv h)
    (hy : ∀ uv h, 0 ≤ y uv h) :
    |avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
      ∑ h : MIPStarRE.LDT.Polynomial params, t uv h)| ≤
      Real.sqrt
        (avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ h : MIPStarRE.LDT.Polynomial params, x uv h)) *
      Real.sqrt
        (avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ h : MIPStarRE.LDT.Polynomial params, y uv h)) := by
  exact
    MIPStarRE.LDT.Preliminaries.weightedFinsetCauchySchwarz
      (Question := Point params × Point params) (Outcome := MIPStarRE.LDT.Polynomial params)
      (uniformDistribution (Point params × Point params))
      (t := t) (x := x) (y := y) ht hx hy

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ### Add-in-u variance-bound conversions

The following two lemmas are conditional real-valued conversions for the `Q₂ → Q₃` and
`Q₃ → Q₄` add-in-u steps. They convert a factored product of square-root bounds into the
absolute-value square-root shape used by the surrounding scalar chain; the hypotheses `hCS` and
`hD*_le*` are where the operator-level Cauchy--Schwarz, submeasurement contraction and
total-mass estimates enter. -/

/-- Convert factored `Q₂ → Q₃` sqrt bounds to the summed-deviation sqrt bound.

This lemma assumes the Cauchy--Schwarz product bound as `hCS`, a bound on the first factor by
the summed independent-points deviation, and a `≤ 1` bound on the second factor. The proof is
purely real-valued; the submeasurement and operator content belongs in the hypotheses. -/
theorem add_in_u_cs_chain_q2_q3_le_sqrt_of_factor_bounds
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (D₁ D₂ : ℝ)
    (hCS :
      |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
        Real.sqrt D₁ * Real.sqrt D₂)
    (hD₁_le :
      D₁ ≤ ∑ g : MIPStarRE.LDT.Polynomial params,
          globalVarianceDeviationAtPolynomial params strategy strategy.state T g)
    (hD₂_le_one : D₂ ≤ 1) :
    |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
      Real.sqrt
        (∑ g : MIPStarRE.LDT.Polynomial params,
          globalVarianceDeviationAtPolynomial params strategy strategy.state T g) :=
  addInU_le_sqrt_of_factor_bounds_right hCS hD₁_le hD₂_le_one

/-- Convert factored `Q₃ → Q₄` sqrt bounds to the summed-deviation sqrt bound.

This lemma assumes the Cauchy--Schwarz product bound as `hCS`, a `≤ 1` bound on the first
factor, and a bound on the second factor by the summed independent-points deviation. The proof
is purely real-valued; the submeasurement and operator content belongs in the hypotheses. -/
theorem add_in_u_cs_chain_q3_q4_le_sqrt_of_factor_bounds
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (D₁ D₂ : ℝ)
    (hCS :
      |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
        Real.sqrt D₁ * Real.sqrt D₂)
    (hD₁_le_one : D₁ ≤ 1)
    (hD₂_le :
      D₂ ≤ ∑ g : MIPStarRE.LDT.Polynomial params,
          globalVarianceDeviationAtPolynomial params strategy strategy.state T g) :
    |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
      Real.sqrt
        (∑ g : MIPStarRE.LDT.Polynomial params,
          globalVarianceDeviationAtPolynomial params strategy strategy.state T g) :=
  addInU_le_sqrt_of_factor_bounds_left hCS hD₁_le_one hD₂_le

/-- Factored operator Cauchy--Schwarz bound for the `Q₂ → Q₃` add-in-`u` step.

Applies the bipartite-tensor sandwich Cauchy--Schwarz primitive
`ev_opTensor_sandwich_abs_le_sqrt` at each `(u, v, h)` and lifts the pointwise estimate through
the avgOver-finset Cauchy--Schwarz inequality. The two factors are the variance term
`(A^v_{h(v)} - A^u_{h(u)}) · H^u_h · (A^v_{h(v)} - A^u_{h(u)})` and the self-energy term
`A^v_{h(v)} · H^u_h · A^v_{h(v)}`, with
`H^u_h = (sandwichedPolynomialSubMeasAt params strategy T u).outcome h` (the paper's middle
operator `M^u_o` after the fiberwise `o`-sum has been reindexed by `o = h(u)`).

This is the operator Cauchy--Schwarz part of `eq:change-one-cauchy-schwarz`; the factor
estimates are fed into `add_in_u_cs_chain_q2_q3_le_sqrt_of_factor_bounds`. -/
theorem add_in_u_cs_chain_q2_q3_factored_cs
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
      Real.sqrt
        (avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ h : MIPStarRE.LDT.Polynomial params,
            let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
            let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
            let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
            strategy.state.ev
              (strategy.state.opTensor ((Av - Au) * Mh * (Av - Au)) (T.outcome h)))) *
      Real.sqrt
        (avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ h : MIPStarRE.LDT.Polynomial params,
            let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
            let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
            strategy.state.ev (strategy.state.opTensor (Av * Mh * Av) (T.outcome h)))) := by
  rw [addInU_cs_chain_step3_diff_eq params strategy T]
  have hA : ∀ (h : MIPStarRE.LDT.Polynomial params) w,
      IsSelfAdjoint (pointConditionedOutcomeOperatorAtPolynomial params strategy h w) :=
    fun h w => .of_nonneg ((strategy.pointMeasurement w).toSubMeas.outcome_pos (h w))
  have hM := fun (uv : Point params × Point params) (h : MIPStarRE.LDT.Polynomial params) =>
    (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome_pos h
  refine addInU_weighted_cauchy_schwarz params _ _ _ (fun uv h => ?_)
    (fun uv h => strategy.state.ev_nonneg_of_psd _ (strategy.state.opTensor_nonneg
      (((hA h uv.2).sub (hA h uv.1)).conjugate_nonneg (hM uv h)) (T.outcome_pos h)))
    (fun uv h => strategy.state.ev_nonneg_of_psd _ (strategy.state.opTensor_nonneg
      ((hA h uv.2).conjugate_nonneg (hM uv h)) (T.outcome_pos h)))
  simpa only [((hA h uv.2).sub (hA h uv.1)).star_eq, (hA h uv.2).star_eq] using
    strategy.state.ev_opTensor_sandwich_abs_le_sqrt
      (pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2 -
        pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1)
      (pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2) _ _
      (hM uv h) (T.outcome_pos h)

/-- Factored operator Cauchy--Schwarz bound for the `Q₃ → Q₄` add-in-`u` step.

Applies the bipartite-tensor sandwich Cauchy--Schwarz primitive
`ev_opTensor_sandwich_abs_le_sqrt` at each `(u, v, h)` and lifts the bound through the
avgOver-finset Cauchy--Schwarz inequality. The expressions `A^u_{h(u)} · H^u_h · A^u_{h(u)}` and
`(A^v_{h(v)} − A^u_{h(u)}) · H^u_h · (A^v_{h(v)} − A^u_{h(u)})` are positive, as conjugates of
the positive `H^u_h` by self-adjoint operators.

This is the operator/real Cauchy--Schwarz fragment of `eq:change-another`. Combined with
submeasurement monotonicity on the first factor (`≤ 1`) and the independent-points
global-variance identification of the second, it feeds
`add_in_u_cs_chain_q3_q4_le_sqrt_of_factor_bounds`. -/
theorem add_in_u_cs_chain_q3_q4_factored_cs
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
      Real.sqrt
        (avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ h : MIPStarRE.LDT.Polynomial params,
            let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
            let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
            strategy.state.ev (strategy.state.opTensor (Au * Mh * Au) (T.outcome h)))) *
      Real.sqrt
        (avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ h : MIPStarRE.LDT.Polynomial params,
            let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
            let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
            let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
            strategy.state.ev
              (strategy.state.opTensor ((Av - Au) * Mh * (Av - Au)) (T.outcome h)))) := by
  rw [addInU_cs_chain_step4_diff_eq params strategy T]
  have hA : ∀ (h : MIPStarRE.LDT.Polynomial params) w,
      IsSelfAdjoint (pointConditionedOutcomeOperatorAtPolynomial params strategy h w) :=
    fun h w => .of_nonneg ((strategy.pointMeasurement w).toSubMeas.outcome_pos (h w))
  have hM := fun (uv : Point params × Point params) (h : MIPStarRE.LDT.Polynomial params) =>
    (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome_pos h
  refine addInU_weighted_cauchy_schwarz params _ _ _ (fun uv h => ?_)
    (fun uv h => strategy.state.ev_nonneg_of_psd _ (strategy.state.opTensor_nonneg
      ((hA h uv.1).conjugate_nonneg (hM uv h)) (T.outcome_pos h)))
    (fun uv h => strategy.state.ev_nonneg_of_psd _ (strategy.state.opTensor_nonneg
      (((hA h uv.2).sub (hA h uv.1)).conjugate_nonneg (hM uv h)) (T.outcome_pos h)))
  simpa only [(hA h uv.1).star_eq, ((hA h uv.2).sub (hA h uv.1)).star_eq] using
    strategy.state.ev_opTensor_sandwich_abs_le_sqrt
      (pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1)
      (pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2 -
        pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1) _ _
      (hM uv h) (T.outcome_pos h)

end MIPRE.LIDT.Co.SelfImprovement

end

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
SelfImprovement/Theorems/Results/AddInUStep34AndTransfer/Variance.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Results.AddInUStep34AndTransfer.Factored
public import MIPStarRE.LDT.SelfImprovement.Theorems.Results.AddInUStep34AndTransfer.Variance

@[expose] public section

/-!
# Unselected add-in-u Step 3/4 global-variance bounds

Unselected self-energy estimates, variance-factor comparisons, and the combined global-variance
bridges for the projection-simplified add-in-u chain: the counterpart of the vendored
`SelfImprovement/Theorems/Results/AddInUStep34AndTransfer/Variance.lean` (under
`MIPRE/Background/LIDT/MIPStarRE/LDT/`) in the port of `planning/c6b-plan.md` (milestone M10,
section "Port conventions").

## Contents

- `add_in_u_cs_chain_q3_q4_self_energy_factor_le_one`,
  `add_in_u_cs_chain_q2_q3_self_energy_factor_le_one`: the self-energy factors of the two factored
  Cauchy--Schwarz bounds of Co `AddInUStep34AndTransfer/Factored` are at most `1`.
- `add_in_u_cs_chain_q2_q3_variance_factor_le_globalVarianceDeviation_sum` and its `q3_q4`
  twin: the variance factor is at most the summed global-variance deviation.
- `add_in_u_cs_chain_q{2_q3,3_q4}_le_sqrt_globalVarianceDeviation_sum`: the raw bounds
  `|Q₂ − Q₃|, |Q₃ − Q₄| ≤ √(∑_g globalVarianceDeviationAtPolynomial …)`.
- The `_of_globalVarianceDeviation_sum_le` upgrades to `√ζ`, their `_from_factor_bounds` closed
  forms, the combined `add_in_u_cs_chain_global_variance_steps_of_sum_bound{,_from_factor_bounds}`,
  and the local-variance forms `…_of_local_sum_bound{,_from_factor_bounds}` and
  `…_of_localVarianceDeviation_sum_le_from_factor_bounds`.

Every scalar is `strategy.state.ev` of a joint operator; `opTensor A B` is
`strategy.state.opTensor A B`, `leftTensor A * rightTensor B` is
`strategy.state.L A * strategy.state.R B`, and `Xᴴ` is `star X`. The vendored Hermitian facts
`SubMeas.outcome_hermitian …` and `rw [Matrix.conjTranspose_sub, …]` are
`IsSelfAdjoint.of_nonneg` and `IsSelfAdjoint.sub`.

**Global variance.** The local and global deviations are M6's (Co `GlobalVariance/Defs/Families`):
the variances of the family `u ↦ S.L (A^u_{g(u)}) * S.R √T_g` on `strategy.state` itself, not on
the vendored weighted state (M6's departure). The variance factor is identified with the global
one through Co `weightedPointConditionedOperator_sq`, exactly where the vendored proof rewrites
with its vendored counterpart, and the local-to-global step is Co
`globalVarianceDeviation_sum_le_of_localVarianceDeviation_sum_le`; so every statement keeps its
vendored text.

**Dropped hypothesis.** The vendored `add_in_u_cs_chain_q3_q4_self_energy_factor_le_one` closes
with `ev_one_of_isNormalized strategy.state strategy.isNormalized` (vendored line 124), and
`add_in_u_cs_chain_q2_q3_self_energy_factor_le_one` applies
`sandwichTensor_residual_sum_le_one strategy.state strategy.isNormalized` (vendored line 207);
here `strategy.state.ev_one_of_isNormalized` and Co `SymModel.sandwichTensor_residual_sum_le_one`
(`Basic/TensorPlacement`) take no normalization hypothesis. No statement of the vendored file
carries a swap, density or normalization hypothesis, so no statement changed.

**Proofs.** The `Q₃ → Q₄` self-energy bound is pointwise in `(u, v)`, through
`avgOver_uniform_le_const`, rather than first collapsing the `v`-average with
`avgOver_uniform_fst` as the vendored proof does; the projection collapse is Co
`proj_outer_sandwich_eq` (`AddInUDiagonalAndDefs/Selection`), and the contraction Co
`SubMeas.opTensor_sum_filter_le_one`, which takes the model as an explicit argument. The file sets
no option; the vendored file-wide `respectTransparency false` is not needed.

The vendored module is imported for its one classical declaration; its only import is the
vendored `AddInUStep34AndTransfer/Factored`, which Co `Factored` imports already.

## Not ported

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/self_improvement.tex` lines 299--340
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.SelfImprovement

open MIPStarRE.LDT (Parameters FieldModel Point Fq avgOver uniformDistribution avgOver_mono
  avgOver_sum avgOver_congr avgOver_uniform_le_const)
open MIPStarRE.LDT.ExpansionHypercubeGraph (avgOver_independentPointPair_eq_uniform_prod)
open MIPStarRE.LDT.GlobalVariance (localVarianceOfPointsError globalVarianceOfPointsError)
open MIPStarRE.LDT.SelfImprovement (selfImprovementVarianceError)
open MIPRE.LIDT.Co.GlobalVariance (pointConditionedOutcomeOperatorAtPolynomial
  localVarianceDeviationAtPolynomial globalVarianceDeviationAtPolynomial
  weightedPointConditionedOperator_sq globalVarianceDeviation_sum_le_of_localVarianceDeviation_sum_le)

/-- Upstream keeps this helper `private` since its Lean-module port (`LionSR/MIPStarRE` at `5fc363b`); the port carries its own copy, with upstream's proof.

Sqrt-monotonicity transit lemma used by the two GlobalVariance endpoint
bridges below: a real bounded by `Real.sqrt s` is bounded by `Real.sqrt ζ`
whenever `s ≤ ζ`. Both `Q₂→Q₃` and `Q₃→Q₄` apply this fact with the same `s`
(the summed `globalVarianceDeviationAtPolynomial`). -/
lemma le_sqrt_of_le_sqrt_of_le {a : ℝ} {s ζ : ℝ}
    (hcs : a ≤ Real.sqrt s) (hsum : s ≤ ζ) : a ≤ Real.sqrt ζ :=
  le_trans hcs (Real.sqrt_le_sqrt hsum)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Self-energy factor `≤ 1` for the `Q₃ → Q₄` factored Cauchy--Schwarz.

The first square-root factor `D₁` produced by `add_in_u_cs_chain_q3_q4_factored_cs`
is bounded by `1`. The proof collapses the outer projection `A^u_{h(u)}` around
the sandwiched submeasurement `H^u_h = A^u_{h(u)} · T_h · A^u_{h(u)}` via
projectivity, then bounds the per-point sum of `opTensor (H^u_h) (T_h)` by
the submeasurement-opTensor-sum lemma, lifts to expectation via `ev`,
and averages over `(u, v)`.

This supplies the `hD₁_le_one` hypothesis required by
`add_in_u_cs_chain_q3_q4_le_sqrt_of_factor_bounds`. -/
theorem add_in_u_cs_chain_q3_q4_self_energy_factor_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
      ∑ h : MIPStarRE.LDT.Polynomial params,
        let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
        let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
        strategy.state.ev (strategy.state.opTensor (Au * Mh * Au) (T.outcome h))) ≤ 1 := by
  refine avgOver_uniform_le_const _ 1 fun uv => ?_
  calc
    _ = strategy.state.ev (∑ h : MIPStarRE.LDT.Polynomial params,
          strategy.state.opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
            (T.outcome h)) := by
        rw [strategy.state.ev_finset_sum]
        exact Finset.sum_congr rfl fun h _ => congrArg
          (fun X => strategy.state.ev (strategy.state.opTensor X (T.outcome h)))
          (proj_outer_sandwich_eq _ (T.outcome h)
            ((strategy.pointMeasurement uv.1).proj (h uv.1)))
    _ ≤ strategy.state.ev 1 := strategy.state.ev_mono _ _ (by
        simpa using SubMeas.opTensor_sum_filter_le_one strategy.state
          (sandwichedPolynomialSubMeasAt params strategy T uv.1) T fun _ => True)
    _ = 1 := strategy.state.ev_one_of_isNormalized

/-- Self-energy factor `≤ 1` for the `Q₂ → Q₃` factored Cauchy--Schwarz.

The second square-root factor produced by `add_in_u_cs_chain_q2_q3_factored_cs`
is bounded by `1`. For fixed `(u,v)`, the diagonal summand is one summand of the
nonnegative residual tensor sum
`Σ_{i,r,o} A^v_o H^u_i A^v_o ⊗ T_r`.  The residual sum is at most `1` by
`sandwichTensor_residual_sum_le_one`, applied to the point measurement at `v`,
the sandwiched polynomial submeasurement at `u`, and the original
submeasurement `T`. -/
theorem add_in_u_cs_chain_q2_q3_self_energy_factor_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
      ∑ h : MIPStarRE.LDT.Polynomial params,
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
        let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
        strategy.state.ev (strategy.state.opTensor (Av * Mh * Av) (T.outcome h))) ≤ 1 := by
  refine avgOver_uniform_le_const _ 1 fun uv => ?_
  let Outer : SubMeas (Fq params) 𝔓 := (strategy.pointMeasurement uv.2).toSubMeas
  let Inner : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓 :=
    sandwichedPolynomialSubMeasAt params strategy T uv.1
  let F : Fq params → MIPStarRE.LDT.Polynomial params → MIPStarRE.LDT.Polynomial params → ℝ :=
    fun o i r => strategy.state.ev
      (strategy.state.L (Outer.outcome o * Inner.outcome i * Outer.outcome o) *
        strategy.state.R (T.outcome r))
  have hF : ∀ o i r, 0 ≤ F o i r := fun o i r =>
    strategy.state.sandwichTensorSummand_nonneg Outer Inner T o i r
  calc
    _ = ∑ h : MIPStarRE.LDT.Polynomial params, F (h uv.2) h h :=
        Finset.sum_congr rfl fun h _ => rfl
    _ ≤ ∑ h : MIPStarRE.LDT.Polynomial params, ∑ r : MIPStarRE.LDT.Polynomial params,
          ∑ o : Fq params, F o h r :=
        Finset.sum_le_sum fun h _ =>
          (Finset.single_le_sum (fun o _ => hF o h h) (Finset.mem_univ (h uv.2))).trans
            (Finset.single_le_sum (f := fun r => ∑ o : Fq params, F o h r)
              (fun r _ => Finset.sum_nonneg fun o _ => hF o h r) (Finset.mem_univ h))
    _ = ∑ ir : MIPStarRE.LDT.Polynomial params × MIPStarRE.LDT.Polynomial params,
          ∑ o : Fq params, F o ir.1 ir.2 :=
        (Fintype.sum_prod_type (fun ir => ∑ o : Fq params, F o ir.1 ir.2)).symm
    _ ≤ 1 := strategy.state.sandwichTensor_residual_sum_le_one Outer Inner T

/-- The variance factor in the `Q₂ → Q₃` factored Cauchy--Schwarz estimate is
bounded by the polynomial sum of the global-variance deviations.

For each polynomial `h`, the sandwiched operator `H^u_h` is bounded by `1`.
Thus the summand
`(A^v_{h(v)} - A^u_{h(u)}) H^u_h (A^v_{h(v)} - A^u_{h(u)}) ⊗ T_h`
is dominated by the squared point-operator difference tensored with `T_h`.
The latter is exactly the integrand defining
`globalVarianceDeviationAtPolynomial`, after expanding the weighted
point-conditioned operator. -/
theorem add_in_u_cs_chain_q2_q3_variance_factor_le_globalVarianceDeviation_sum
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
      ∑ h : MIPStarRE.LDT.Polynomial params,
        let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
        let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
        strategy.state.ev
          (strategy.state.opTensor ((Av - Au) * Mh * (Av - Au)) (T.outcome h))) ≤
      ∑ g : MIPStarRE.LDT.Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T g := by
  have hA : ∀ (h : MIPStarRE.LDT.Polynomial params) w,
      IsSelfAdjoint (pointConditionedOutcomeOperatorAtPolynomial params strategy h w) :=
    fun h w => .of_nonneg ((strategy.pointMeasurement w).toSubMeas.outcome_pos (h w))
  calc
    _ ≤ avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ g : MIPStarRE.LDT.Polynomial params,
            let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy g uv.1
            let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy g uv.2
            strategy.state.ev
              (strategy.state.opTensor (star (Au - Av) * (Au - Av)) (T.outcome g))) :=
        avgOver_mono _ _ _ fun uv => Finset.sum_le_sum fun h _ => by
          refine strategy.state.ev_mono _ _ (strategy.state.opTensor_mono_left ?_ (T.outcome_pos h))
          refine (((hA h uv.2).sub (hA h uv.1)).conjugate_le_conjugate
            ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome_le_one h)).trans_eq ?_
          rw [mul_one, ((hA h uv.1).sub (hA h uv.2)).star_eq, ← neg_mul_neg, neg_sub]
    _ = _ := by
        rw [avgOver_sum]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [globalVarianceDeviationAtPolynomial, avgOver_independentPointPair_eq_uniform_prod]
        exact avgOver_congr _ _ _ fun uv =>
          congrArg strategy.state.ev (weightedPointConditionedOperator_sq params strategy T g
            uv.1 uv.2).symm

/-- The variance factor in the `Q₃ → Q₄` factored Cauchy--Schwarz estimate is
bounded by the polynomial sum of the global-variance deviations.

This is the same variance expression as in the `Q₂ → Q₃` estimate, appearing
as the second square-root factor rather than the first. -/
theorem add_in_u_cs_chain_q3_q4_variance_factor_le_globalVarianceDeviation_sum
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
      ∑ h : MIPStarRE.LDT.Polynomial params,
        let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
        let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
        strategy.state.ev
          (strategy.state.opTensor ((Av - Au) * Mh * (Av - Au)) (T.outcome h))) ≤
      ∑ g : MIPStarRE.LDT.Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T g :=
  add_in_u_cs_chain_q2_q3_variance_factor_le_globalVarianceDeviation_sum
    params strategy T

/-- Raw `Q₂ → Q₃` global-variance Cauchy--Schwarz bound after both factors have
been estimated. -/
theorem add_in_u_cs_chain_q2_q3_le_sqrt_globalVarianceDeviation_sum
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
      Real.sqrt
        (∑ g : MIPStarRE.LDT.Polynomial params,
          globalVarianceDeviationAtPolynomial params strategy strategy.state T g) :=
  add_in_u_cs_chain_q2_q3_le_sqrt_of_factor_bounds params strategy T _ _
    (add_in_u_cs_chain_q2_q3_factored_cs params strategy T)
    (add_in_u_cs_chain_q2_q3_variance_factor_le_globalVarianceDeviation_sum
      params strategy T)
    (add_in_u_cs_chain_q2_q3_self_energy_factor_le_one params strategy T)

/-- Raw `Q₃ → Q₄` global-variance Cauchy--Schwarz bound after both factors have
been estimated. -/
theorem add_in_u_cs_chain_q3_q4_le_sqrt_globalVarianceDeviation_sum
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
      Real.sqrt
        (∑ g : MIPStarRE.LDT.Polynomial params,
          globalVarianceDeviationAtPolynomial params strategy strategy.state T g) :=
  add_in_u_cs_chain_q3_q4_le_sqrt_of_factor_bounds params strategy T _ _
    (add_in_u_cs_chain_q3_q4_factored_cs params strategy T)
    (add_in_u_cs_chain_q3_q4_self_energy_factor_le_one params strategy T)
    (add_in_u_cs_chain_q3_q4_variance_factor_le_globalVarianceDeviation_sum
      params strategy T)

/-- The global-variance sum bound upgrades the raw Cauchy--Schwarz estimate for
the first global-variance replacement step into the displayed `sqrt ζ` bound.

This is the variance-use fragment of `eq:change-one` in
`references/ldt-paper/self_improvement.tex`, lines 299--318. The hypothesis
`hcs` is the Cauchy--Schwarz estimate `eq:change-one-cauchy-schwarz`
(lines 306--311) **after** the second square root has been bounded by `1`
using `(A^v_{h(v)})² ≤ I` and the fact that `T` is a measurement
(lines 312--316, 318); concretely, the right-hand side is the summed
`globalVarianceDeviationAtPolynomial` (the displayed first-square-root
content). This lemma applies only the remaining `≤ ζ_variance` step from
`lem:global-variance-of-points` (line 317) via sqrt-monotonicity. -/
theorem add_in_u_cs_chain_q2_q3_le_sqrt_of_globalVarianceDeviation_sum_le
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    {ζ : ℝ}
    (hglobal :
      (∑ g : MIPStarRE.LDT.Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤ ζ)
    (hcs :
      |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
        Real.sqrt
          (∑ g : MIPStarRE.LDT.Polynomial params,
            globalVarianceDeviationAtPolynomial params strategy strategy.state T g)) :
    |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
      Real.sqrt ζ :=
  le_sqrt_of_le_sqrt_of_le hcs hglobal

/-- The global-variance sum bound upgrades the raw Cauchy--Schwarz estimate for
the second global-variance replacement step into the displayed `sqrt ζ` bound.

This is the variance-use fragment of `eq:change-another` in
`references/ldt-paper/self_improvement.tex`, lines 319--340. The hypothesis
`hcs` is the Cauchy--Schwarz estimate of lines 326--332 **after** the
first square root has been bounded by `1` using `(A^u_{h(u)})² ≤ I` and the
fact that `T` is a measurement (lines 333--338); concretely, the right-hand
side is the summed `globalVarianceDeviationAtPolynomial` (the displayed
second-square-root content, equal to the first-square-root term of
`eq:change-one-cauchy-schwarz` per line 340). This lemma applies only the
remaining `≤ ζ_variance` step (line 340) via sqrt-monotonicity. -/
theorem add_in_u_cs_chain_q3_q4_le_sqrt_of_globalVarianceDeviation_sum_le
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    {ζ : ℝ}
    (hglobal :
      (∑ g : MIPStarRE.LDT.Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤ ζ)
    (hcs :
      |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
        Real.sqrt
          (∑ g : MIPStarRE.LDT.Polynomial params,
            globalVarianceDeviationAtPolynomial params strategy strategy.state T g)) :
    |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
      Real.sqrt ζ :=
  le_sqrt_of_le_sqrt_of_le hcs hglobal

/-- Closed global-variance bridge for the first projection-simplified
Cauchy--Schwarz replacement step.

The factor estimates proved above supply the raw square-root bound, so the only
remaining hypothesis is the summed global-variance estimate. -/
theorem add_in_u_cs_chain_q2_q3_le_sqrt_of_globalVarianceDeviation_sum_le_from_factor_bounds
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    {ζ : ℝ}
    (hglobal :
      (∑ g : MIPStarRE.LDT.Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤ ζ) :
    |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
      Real.sqrt ζ :=
  add_in_u_cs_chain_q2_q3_le_sqrt_of_globalVarianceDeviation_sum_le
    params strategy T hglobal
    (add_in_u_cs_chain_q2_q3_le_sqrt_globalVarianceDeviation_sum params strategy T)

/-- Closed global-variance bridge for the second projection-simplified
Cauchy--Schwarz replacement step.

The factor estimates proved above supply the raw square-root bound, so the only
remaining hypothesis is the summed global-variance estimate. -/
theorem add_in_u_cs_chain_q3_q4_le_sqrt_of_globalVarianceDeviation_sum_le_from_factor_bounds
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    {ζ : ℝ}
    (hglobal :
      (∑ g : MIPStarRE.LDT.Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤ ζ) :
    |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
      Real.sqrt ζ :=
  add_in_u_cs_chain_q3_q4_le_sqrt_of_globalVarianceDeviation_sum_le
    params strategy T hglobal
    (add_in_u_cs_chain_q3_q4_le_sqrt_globalVarianceDeviation_sum params strategy T)

/-- Combined Step 3/4 variance bridge for the projection-simplified add-in-u
Cauchy--Schwarz chain.

Given the two raw Cauchy--Schwarz estimates against the summed
independent-points deviation and a GlobalVariance sum bound, this produces the
two `sqrt ζ` absolute-difference bounds needed by
`add_in_u_simplified_transfer_of_cs_chain`. It deliberately does not assemble
the final transfer, so the remaining self-consistency steps and arithmetic
absorption stay separate. -/
theorem add_in_u_cs_chain_global_variance_steps_of_sum_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    {ζ : ℝ}
    (hglobal :
      (∑ g : MIPStarRE.LDT.Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤ ζ)
    (h23cs :
      |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
        Real.sqrt
          (∑ g : MIPStarRE.LDT.Polynomial params,
            globalVarianceDeviationAtPolynomial params strategy strategy.state T g))
    (h34cs :
      |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
        Real.sqrt
          (∑ g : MIPStarRE.LDT.Polynomial params,
            globalVarianceDeviationAtPolynomial params strategy strategy.state T g)) :
    |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
        Real.sqrt ζ ∧
      |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
        Real.sqrt ζ :=
  ⟨add_in_u_cs_chain_q2_q3_le_sqrt_of_globalVarianceDeviation_sum_le
      params strategy T hglobal h23cs,
    add_in_u_cs_chain_q3_q4_le_sqrt_of_globalVarianceDeviation_sum_le
      params strategy T hglobal h34cs⟩

/-- Combined Step 3/4 variance bridge using the factor estimates proved in this
file.

This is the closed form of
`add_in_u_cs_chain_global_variance_steps_of_sum_bound`: the raw
Cauchy--Schwarz estimates are supplied by
`add_in_u_cs_chain_q2_q3_le_sqrt_globalVarianceDeviation_sum` and
`add_in_u_cs_chain_q3_q4_le_sqrt_globalVarianceDeviation_sum`. -/
theorem add_in_u_cs_chain_global_variance_steps_of_sum_bound_from_factor_bounds
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    {ζ : ℝ}
    (hglobal :
      (∑ g : MIPStarRE.LDT.Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤ ζ) :
    |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
        Real.sqrt ζ ∧
      |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
        Real.sqrt ζ :=
  add_in_u_cs_chain_global_variance_steps_of_sum_bound params strategy T hglobal
    (add_in_u_cs_chain_q2_q3_le_sqrt_globalVarianceDeviation_sum params strategy T)
    (add_in_u_cs_chain_q3_q4_le_sqrt_globalVarianceDeviation_sum params strategy T)

-- This bridge applies the global-variance sum transfer and the two
-- Cauchy--Schwarz factor bounds, all over the polynomial-indexed family.
/-- Local-variance-sum version of the combined Step 3/4 variance bridge.

This consumes the expected output of the local-variance normalization step
(`expansion.tex`, lines 317--321) through
`globalVarianceDeviation_sum_le_of_localVarianceDeviation_sum_le`, then applies
the combined Step 3/4 bridge above.  It remains a named bridge because the
blueprint cites this local-sum interface separately from the closed
factor-bound lemma below. -/
theorem add_in_u_cs_chain_global_variance_steps_of_local_sum_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hlocal :
      (∑ g : MIPStarRE.LDT.Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤
        localVarianceOfPointsError params eps delta)
    (h23cs :
      |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
        Real.sqrt
          (∑ g : MIPStarRE.LDT.Polynomial params,
            globalVarianceDeviationAtPolynomial params strategy strategy.state T g))
    (h34cs :
      |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
        Real.sqrt
          (∑ g : MIPStarRE.LDT.Polynomial params,
            globalVarianceDeviationAtPolynomial params strategy strategy.state T g)) :
    |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
        Real.sqrt (globalVarianceOfPointsError params eps delta) ∧
      |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
        Real.sqrt (globalVarianceOfPointsError params eps delta) :=
  add_in_u_cs_chain_global_variance_steps_of_sum_bound params strategy T
    (globalVarianceDeviation_sum_le_of_localVarianceDeviation_sum_le
      params strategy eps delta T hlocal)
    h23cs h34cs

-- This lemma composes the local-to-global sum transfer with the first
-- projection-simplified Cauchy--Schwarz factor estimate.
/-- Closed local-variance bridge for the first projection-simplified
Cauchy--Schwarz replacement step.

The local-variance sum estimate is first transported to the corresponding
global-variance estimate, and the factor estimates provide the raw
Cauchy--Schwarz bound. -/
theorem add_in_u_cs_chain_q2_q3_le_sqrt_of_localVarianceDeviation_sum_le_from_factor_bounds
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hlocal :
      (∑ g : MIPStarRE.LDT.Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤
        localVarianceOfPointsError params eps delta) :
    |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
      Real.sqrt (globalVarianceOfPointsError params eps delta) :=
  add_in_u_cs_chain_q2_q3_le_sqrt_of_globalVarianceDeviation_sum_le_from_factor_bounds
    params strategy T
    (globalVarianceDeviation_sum_le_of_localVarianceDeviation_sum_le
      params strategy eps delta T hlocal)

-- This lemma composes the local-to-global sum transfer with the second
-- projection-simplified Cauchy--Schwarz factor estimate.
/-- Closed local-variance bridge for the second projection-simplified
Cauchy--Schwarz replacement step.

The local-variance sum estimate is first transported to the corresponding
global-variance estimate, and the factor estimates provide the raw
Cauchy--Schwarz bound. -/
theorem add_in_u_cs_chain_q3_q4_le_sqrt_of_localVarianceDeviation_sum_le_from_factor_bounds
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hlocal :
      (∑ g : MIPStarRE.LDT.Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤
        localVarianceOfPointsError params eps delta) :
    |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
      Real.sqrt (globalVarianceOfPointsError params eps delta) :=
  add_in_u_cs_chain_q3_q4_le_sqrt_of_globalVarianceDeviation_sum_le_from_factor_bounds
    params strategy T
    (globalVarianceDeviation_sum_le_of_localVarianceDeviation_sum_le
      params strategy eps delta T hlocal)

/-- Local-variance-sum version of the combined Step 3/4 variance bridge using
the factor estimates proved in this file.

This is the closed local-sum form of
`add_in_u_cs_chain_global_variance_steps_of_sum_bound_from_factor_bounds`: the
only new input is the local-variance sum hypothesis, which is first transported
to the global-variance sum bound. -/
theorem add_in_u_cs_chain_global_variance_steps_of_local_sum_bound_from_factor_bounds
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hlocal :
      (∑ g : MIPStarRE.LDT.Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤
        localVarianceOfPointsError params eps delta) :
    |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
        Real.sqrt (selfImprovementVarianceError params eps delta) ∧
      |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
        Real.sqrt (selfImprovementVarianceError params eps delta) :=
  add_in_u_cs_chain_global_variance_steps_of_local_sum_bound
    params strategy eps delta T hlocal
    (add_in_u_cs_chain_q2_q3_le_sqrt_globalVarianceDeviation_sum params strategy T)
    (add_in_u_cs_chain_q3_q4_le_sqrt_globalVarianceDeviation_sum params strategy T)

end MIPRE.LIDT.Co.SelfImprovement

end

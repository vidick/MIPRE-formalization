/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
SelfImprovement/Theorems/Results/AddInUDiagonalAndDefs/Residual.lean, to the symmetric model
of `planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Results.AddInUDiagonalAndDefs.Selection

@[expose] public section

/-!
# Off-diagonal residual estimates for the helper SSC argument

The off-diagonal scalar quantities appearing after the projector insertion in the helper
strong-self-consistency proof, their exact decompositions, and the assembly of the two
variance-transport comparisons with the Schwartz--Zippel endpoint: the counterpart of the
vendored `SelfImprovement/Theorems/Results/AddInUDiagonalAndDefs/Residual.lean` (under
`MIPRE/Background/LIDT/MIPStarRE/LDT/`) in the port of `planning/c6b-plan.md` (milestone M10,
section "Port conventions").

A strategy is a `SymStrat params 𝔓 K`; the polynomial submeasurement `T` and the point
projectors live in `𝔓`, and every scalar quantity is `strategy.state.ev` of a joint operator
`strategy.state.opTensor X Y`. The statements are the vendored ones, translated; none of them
has a swap or normalization hypothesis. The error term `selfImprovementVarianceError` is
classical and imported from the vendored `SelfImprovement/Defs.lean`.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/self_improvement.tex` lines 455--468
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.SelfImprovement

open MIPStarRE.LDT (Parameters FieldModel Point avgOver uniformDistribution avgOver_congr
  avgOver_add)
open MIPStarRE.LDT.SelfImprovement (selfImprovementVarianceError selfConsistencyAddInUSelection)
open MIPRE.LIDT.Co.GlobalVariance (pointConditionedOutcomeOperatorAtPolynomial)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ### Off-diagonal residual quantities for the helper SSC estimate -/

/-- The off-diagonal contribution after inserting the outer point projector
`A^u_{h(u)}` around the pointwise helper outcome `H^u_{h'}`.

This is the non-diagonal term added when the diagonal released expression is
enlarged to the full `(h,h')` sum in the proof of helper strong
self-consistency. -/
noncomputable def helperOffDiagonalOuterSandwichQuantity
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) : ℝ :=
  avgOver (uniformDistribution (Point params)) (fun u =>
    ∑ h : MIPStarRE.LDT.Polynomial params,
      ∑ h' ∈ (Finset.univ : Finset (MIPStarRE.LDT.Polynomial params)).erase h,
        let Ah := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
        strategy.state.ev
          (strategy.state.opTensor
            (Ah * ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h') * Ah)
            (T.outcome h)))

/-- The same off-diagonal contribution after using `eq:h-blt`: the outer
projector has been removed from the operator and replaced by the polynomial
agreement indicator `1_{h(u)=h'(u)}`. -/
noncomputable def helperOffDiagonalIndicatorQuantity
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) : ℝ :=
  avgOver (uniformDistribution (Point params)) (fun u =>
    ∑ h : MIPStarRE.LDT.Polynomial params,
      ∑ h' ∈ (Finset.univ : Finset (MIPStarRE.LDT.Polynomial params)).erase h,
        (if h u = h' u then (1 : ℝ) else 0) *
          strategy.state.ev
            (strategy.state.opTensor
              ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h')
              (T.outcome h)))

/-- The intermediate off-diagonal expression after the first variance swap.

The left copy of the point projector has been evaluated at an independent point
`v`, while the right copy is still evaluated at the original point `u`.  This is
the Lean scalar form of the expression in the paper immediately after
`eq:swapped-u-for-v`. -/
noncomputable def helperOffDiagonalOneSidedSwappedIndicatorQuantity
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) : ℝ :=
  avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
    ∑ h : MIPStarRE.LDT.Polynomial params,
      ∑ h' ∈ (Finset.univ : Finset (MIPStarRE.LDT.Polynomial params)).erase h,
        (if h uv.1 = h' uv.1 then (1 : ℝ) else 0) *
          strategy.state.ev
            (strategy.state.opTensor
              (pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2 *
                T.outcome h' *
                pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1)
              (T.outcome h)))

/-- The post-variance-swap endpoint for the off-diagonal contribution.

Here both copies of the point projector have been evaluated at an independent
point `v`, while the agreement indicator has already been averaged over the
original point `u`.  This is the scalar expression to which the
Schwartz--Zippel estimate is applied. -/
noncomputable def helperOffDiagonalSwappedIndicatorQuantity
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) : ℝ :=
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
              (T.outcome h)))

/-- The full enlarged expression after inserting the outer point projector.

This includes both the diagonal and off-diagonal pairs `(h,h')`, and is the
right-hand side of `eq:threw-in-h-prime` before applying `eq:h-blt`. -/
noncomputable def helperFullOuterSandwichQuantity
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) : ℝ :=
  avgOver (uniformDistribution (Point params)) (fun u =>
    ∑ h : MIPStarRE.LDT.Polynomial params,
      ∑ h' : MIPStarRE.LDT.Polynomial params,
        let Ah := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
        strategy.state.ev
          (strategy.state.opTensor
            (Ah * ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h') * Ah)
            (T.outcome h)))

/-- The full inserted expression splits into its released diagonal part and its
off-diagonal remainder.

This is the finite-sum identity underlying the passage from
`eq:release-the-kraken` to `eq:threw-in-h-prime`: for each fixed polynomial
`h`, the sum over all `h'` is the diagonal term `h' = h` plus the sum over
`h' ≠ h`. -/
theorem helperFullOuterSandwichQuantity_eq_release_add_offDiagonalOuterSandwichQuantity
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    helperFullOuterSandwichQuantity params strategy T =
      addInURightQuantity params strategy
        (sandwichedPolynomialSubMeasAt params strategy T)
        T
        (selfConsistencyAddInUSelection params) +
      helperOffDiagonalOuterSandwichQuantity params strategy T := by
  rw [addInURightQuantity_selfConsistencySelection_eq_release,
    helperFullOuterSandwichQuantity, helperOffDiagonalOuterSandwichQuantity, ← avgOver_add]
  refine avgOver_congr (uniformDistribution (Point params)) _ _ fun u => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ h)]

/-- The full enlarged expression after deleting the left copy of the point
projector.

This is the paper's `eq:delete-an-A` scalar quantity. -/
noncomputable def helperDeleteAQuantity
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) : ℝ :=
  avgOver (uniformDistribution (Point params)) (fun u =>
    ∑ h : MIPStarRE.LDT.Polynomial params,
      ∑ h' : MIPStarRE.LDT.Polynomial params,
        let Ah := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
        strategy.state.ev
          (strategy.state.opTensor
            (((sandwichedPolynomialSubMeasAt params strategy T u).outcome h') * Ah)
            (T.outcome h)))

/-- Formal version of the paper's `eq:delete-an-A` identity. -/
theorem helperFullOuterSandwichQuantity_eq_deleteAQuantity
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    helperFullOuterSandwichQuantity params strategy T =
      helperDeleteAQuantity params strategy T :=
  avgOver_congr (uniformDistribution (Point params)) _ _ fun u =>
    Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun h' _ =>
      congrArg (fun X => strategy.state.ev (strategy.state.opTensor X (T.outcome h)))
        (pointConditioned_sandwichedPolynomialOutcome_outer_eq_right params strategy T u h h')

/-- The `delete-an-A` expression after replacing the remaining point projector
by an independent point.

This is the scalar quantity on the right-hand side of the paper's
`eq:swap-u-for-v-attack-of-the-clones`. -/
noncomputable def helperDeleteAClonedQuantity
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) : ℝ :=
  avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
    ∑ h : MIPStarRE.LDT.Polynomial params,
      ∑ h' : MIPStarRE.LDT.Polynomial params,
        strategy.state.ev
          (strategy.state.opTensor
            (((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h') *
              pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2)
            (T.outcome h)))

/-- The expression obtained after moving the remaining point projector to the
right tensor factor.

This is the scalar quantity on the right-hand side of the paper's
`eq:move-over-v`. -/
noncomputable def helperMoveOverVQuantity
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) : ℝ :=
  avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
    ∑ h : MIPStarRE.LDT.Polynomial params,
      ∑ h' : MIPStarRE.LDT.Polynomial params,
        strategy.state.ev
          (strategy.state.opTensor
            ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h')
            (T.outcome h *
              pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2)))

/-- Assemble the post-`delete-an-A` transport estimates.

The first hypothesis is the variance replacement
`A^u_{h(u)} → A^v_{h(v)}` in `eq:swap-u-for-v-attack-of-the-clones`.  The second
hypothesis is the self-consistency move `eq:move-over-v`, which moves the
remaining point projector from Alice's tensor factor to Bob's tensor factor.
This lemma only performs the scalar triangle-inequality assembly; the analytic
proofs of the two displayed hypotheses remain separate. -/
theorem helperDeleteAQuantity_le_moveOverV_of_abs_transports
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hclone :
      |helperDeleteAQuantity params strategy T -
        helperDeleteAClonedQuantity params strategy T| ≤
          Real.sqrt (selfImprovementVarianceError params eps delta))
    (hmove :
      |helperDeleteAClonedQuantity params strategy T -
        helperMoveOverVQuantity params strategy T| ≤
          Real.sqrt (2 * delta)) :
    helperDeleteAQuantity params strategy T ≤
      helperMoveOverVQuantity params strategy T +
        Real.sqrt (selfImprovementVarianceError params eps delta) +
        Real.sqrt (2 * delta) := by
  linarith [(abs_le.mp hclone).2, (abs_le.mp hmove).2]

/-- The reverse scalar direction of the post-`delete-an-A` transport estimates.

This is the direction used when the final `move-over-v` expression is known to
be large and one transfers that lower bound back to the `delete-an-A` expression.
It is again only the triangle-inequality assembly of the two analytic transport
estimates. -/
theorem helperMoveOverVQuantity_le_deleteA_of_abs_transports
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hclone :
      |helperDeleteAQuantity params strategy T -
        helperDeleteAClonedQuantity params strategy T| ≤
          Real.sqrt (selfImprovementVarianceError params eps delta))
    (hmove :
      |helperDeleteAClonedQuantity params strategy T -
        helperMoveOverVQuantity params strategy T| ≤
          Real.sqrt (2 * delta)) :
    helperMoveOverVQuantity params strategy T ≤
      helperDeleteAQuantity params strategy T +
        Real.sqrt (selfImprovementVarianceError params eps delta) +
        Real.sqrt (2 * delta) := by
  linarith [(abs_le.mp hclone).1, (abs_le.mp hmove).1]

/-- Named form of the identity `eq:h-blt` for the off-diagonal helper SSC
quantity. -/
theorem helperOffDiagonalOuterSandwichQuantity_eq_indicator
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    helperOffDiagonalOuterSandwichQuantity params strategy T =
      helperOffDiagonalIndicatorQuantity params strategy T :=
  polynomial_off_diagonal_outer_sandwich_eq_indicator_avg params strategy T

/-- Named Schwartz--Zippel endpoint for the helper SSC off-diagonal term. -/
theorem helperOffDiagonalSwappedIndicatorQuantity_le_mdq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    helperOffDiagonalSwappedIndicatorQuantity params strategy T ≤
      (params.m * params.d : ℝ) / params.q :=
  polynomial_off_diagonal_swapped_indicator_sandwich_avg_le_mdq params strategy T

/-- Assemble the two one-projector variance transports for the off-diagonal
helper residual.

The first hypothesis is the estimate for replacing the left copy of
`A^u_{h(u)}` by `A^v_{h(v)}`.  The second hypothesis is the estimate for
replacing the remaining right copy by the same independent point `v`.  Together
they give the transport inequality used before the Schwartz--Zippel endpoint in
the proof of helper strong self-consistency. -/
theorem helperOffDiagonalIndicatorQuantity_le_swapped_of_abs_transports
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hleft :
      |helperOffDiagonalIndicatorQuantity params strategy T -
        helperOffDiagonalOneSidedSwappedIndicatorQuantity params strategy T| ≤
          Real.sqrt (selfImprovementVarianceError params eps delta))
    (hright :
      |helperOffDiagonalOneSidedSwappedIndicatorQuantity params strategy T -
        helperOffDiagonalSwappedIndicatorQuantity params strategy T| ≤
          Real.sqrt (selfImprovementVarianceError params eps delta)) :
    helperOffDiagonalIndicatorQuantity params strategy T ≤
      helperOffDiagonalSwappedIndicatorQuantity params strategy T +
        2 * Real.sqrt (selfImprovementVarianceError params eps delta) := by
  linarith [(abs_le.mp hleft).2, (abs_le.mp hright).2]

/-- Assemble the off-diagonal projector-insertion bound from the two variance
swaps and the Schwartz--Zippel endpoint.

The hypothesis `htransport` is precisely the analytic content of the two
Cauchy--Schwarz variance moves in the proof of
`item:self-improvement-self`: it transports the indicator form of the
off-diagonal term to the endpoint with both point projectors evaluated at the
independent point `v`.  The conclusion is the corresponding paper estimate
before substituting the concrete value of the transport error. -/
theorem helperOffDiagonalOuterSandwichQuantity_le_of_swapped_transport
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (η : ℝ)
    (htransport :
      helperOffDiagonalIndicatorQuantity params strategy T ≤
        helperOffDiagonalSwappedIndicatorQuantity params strategy T + η) :
    helperOffDiagonalOuterSandwichQuantity params strategy T ≤
      η + (params.m * params.d : ℝ) / params.q := by
  rw [helperOffDiagonalOuterSandwichQuantity_eq_indicator]
  linarith [helperOffDiagonalSwappedIndicatorQuantity_le_mdq params strategy T]

/-- Paper-shaped form of the off-diagonal projector-insertion estimate.

Once the two variance swaps have supplied transport error
`2√ζ_variance`, the inserted off-diagonal contribution is bounded by
`2√ζ_variance + md/q`. -/
theorem helperOffDiagonalOuterSandwichQuantity_le_two_sqrt_variance_add_mdq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (htransport :
      helperOffDiagonalIndicatorQuantity params strategy T ≤
        helperOffDiagonalSwappedIndicatorQuantity params strategy T +
          2 * Real.sqrt (selfImprovementVarianceError params eps delta)) :
    helperOffDiagonalOuterSandwichQuantity params strategy T ≤
      2 * Real.sqrt (selfImprovementVarianceError params eps delta) +
        (params.m * params.d : ℝ) / params.q :=
  helperOffDiagonalOuterSandwichQuantity_le_of_swapped_transport
    params strategy T (2 * Real.sqrt (selfImprovementVarianceError params eps delta))
    htransport

/-- Paper-shaped off-diagonal bound from the two explicit variance transports.

This version exposes the two Cauchy--Schwarz/global-variance moves separately:
first from the indicator form to the one-sided swapped expression, and then from
the one-sided swapped expression to the Schwartz--Zippel endpoint. -/
theorem helperOffDiagonalOuterSandwichQuantity_le_two_sqrt_variance_add_mdq_of_abs_transports
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hleft :
      |helperOffDiagonalIndicatorQuantity params strategy T -
        helperOffDiagonalOneSidedSwappedIndicatorQuantity params strategy T| ≤
          Real.sqrt (selfImprovementVarianceError params eps delta))
    (hright :
      |helperOffDiagonalOneSidedSwappedIndicatorQuantity params strategy T -
        helperOffDiagonalSwappedIndicatorQuantity params strategy T| ≤
          Real.sqrt (selfImprovementVarianceError params eps delta)) :
    helperOffDiagonalOuterSandwichQuantity params strategy T ≤
      2 * Real.sqrt (selfImprovementVarianceError params eps delta) +
        (params.m * params.d : ℝ) / params.q :=
  helperOffDiagonalOuterSandwichQuantity_le_two_sqrt_variance_add_mdq
    params strategy eps delta T
    (helperOffDiagonalIndicatorQuantity_le_swapped_of_abs_transports
      params strategy eps delta T hleft hright)

end MIPRE.LIDT.Co.SelfImprovement

end

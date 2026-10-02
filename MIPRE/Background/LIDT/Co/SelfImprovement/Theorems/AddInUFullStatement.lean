/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
SelfImprovement/Theorems/AddInUFullStatement.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Statements
public import MIPRE.Background.LIDT.Co.Test.StrategyFailures
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Results.AddInUStep34AndTransfer.Transfer
public import MIPRE.Background.LIDT.Co.GlobalVariance.Theorems.MainTheorems

@[expose] public section

/-!
# Section 7 — Selection-dependent transfer inequality for `lem:add-in-u`

The full selection-dependent transfer inequality of `lem:add-in-u`: the counterpart of the
vendored `SelfImprovement/Theorems/AddInUFullStatement.lean` (under
`MIPRE/Background/LIDT/MIPStarRE/LDT/`) in the port of `planning/c6b-plan.md` (milestone M10,
section "Port conventions").

## Contents

- `AddInUFullStatement`: for every auxiliary family `M` and selection `S`, the two indexed
  expectations of `lem:add-in-u` agree to within `addInUError params eps delta`.
- `addInUFullStatement_of_isGood`: it holds for every `(ε, δ, γ)`-good symmetric strategy and every
  polynomial measurement `T`, by the selected Cauchy--Schwarz chain of Co
  `AddInUStep12/Selected` and `AddInUStep34AndTransfer/Selected`, the local-variance transport
  bound and the local-to-global transfer of Co `GlobalVariance`.

The strategy is `strategy : SymStrat params 𝔓 K`, the measurement `T : Measurement (Polynomial
params) 𝔓` and the family `M : IdxSubMeas (Point params) Outcome 𝔓`. The self-consistency
hypothesis is read off `hgood.selfConsistencyTest` as `⟨hgood.selfConsistencyTest⟩`, the vendored
`constructor; simpa [SymStrat.selfConsistencyFailureProbability]`, and the global-variance bound
`∑_g globalVarianceDeviationAtPolynomial … ≤ selfImprovementVarianceError params eps delta` is Co
`globalVarianceDeviation_sum_le_of_localVarianceDeviation_sum_le` as it stands, since
`selfImprovementVarianceError` is `globalVarianceOfPointsError` by definition. No statement of the
vendored file carries a swap, density or normalization hypothesis, so no statement changed.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/self_improvement.tex` lines 238--343
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.SelfImprovement

open MIPStarRE.LDT (Parameters FieldModel Point uniformDistribution)
open MIPStarRE.LDT.GlobalVariance (localVarianceOfPointsError)
open MIPStarRE.LDT.SelfImprovement (AddInUSelection selfImprovementVarianceError addInUError
  two_sqrt_two_delta_add_two_sqrt_selfImprovementVarianceError_le_addInUError)
open MIPRE.LIDT.Co.GlobalVariance (localVarianceDeviationAtPolynomial
  globalVarianceDeviationAtPolynomial localVarianceDeviation_sum_le_localVarianceOfPointsError
  globalVarianceDeviation_sum_le_of_localVarianceDeviation_sum_le)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Paper-faithful full statement of `lem:add-in-u` (`self_improvement.tex` lines 238–246).

For every auxiliary submeasurement family `M = {M^u_o}` indexed by points `u ∈ F_q^m` with
outcomes in some set `O`, and every selection rule `S : Point → Set (O × Polynomial)`, the two
indexed expectations

```
  E_{u} ∑_{(o, h) ∈ S(u)} ⟨ψ| M^u_o ⊗ H_h |ψ⟩
```

and

```
  E_{u} ∑_{(o, h) ∈ S(u)} ⟨ψ| (A^u_{h(u)} M^u_o A^u_{h(u)}) ⊗ T_h |ψ⟩
```

agree to within `4 √ζ_variance = addInUError params eps delta`. Here `H` is the averaged
sandwiched family `H_h = E_u (A^u · T_h · A^u)` derived from the measurement `T`, substituted
directly rather than taken as a parameter. The reduced `AddInUStatement` (Co
`Theorems/Statements`) records only the variance-bound consequence; this structure records the
universally quantified transfer inequality. `T` is a `Measurement`, matching the paper's fixed
SDP-optimal family; the operators depend only on `T.toSubMeas`. -/
structure AddInUFullStatement
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓)
    (eps delta : ℝ) : Prop where
  /-- The selection-dependent transfer inequality from `lem:add-in-u`, with
  the paper's `4 √ζ_variance` bound. Universally quantified over the
  auxiliary outcome set `Outcome`, the auxiliary `M`-family, and the
  selection rule `S`. The averaged family `H` is the canonical
  `averagedSandwichedPolynomialSubMeas params strategy T`. -/
  selectionDependentTransfer :
    ∀ {Outcome : Type*} [Fintype Outcome]
      (M : IdxSubMeas (Point params) Outcome 𝔓)
      (S : AddInUSelection params Outcome),
    |addInULeftQuantity params strategy M
          (averagedSandwichedPolynomialSubMeas params strategy T.toSubMeas) S
        - addInURightQuantity params strategy M T.toSubMeas S|
      ≤ addInUError params eps delta

/-- Proves the selection-dependent transfer inequality of `lem:add-in-u`:
for any auxiliary submeasurement family `M = {M^u_o}` and selection rule
`S : Point → Set (Outcome × Polynomial)`, the two indexed expectations agree
to within `4 √ζ_variance` (the bound `addInUError params eps delta`), given an
`(ε, δ, γ)`-good strategy (`self_improvement.tex` lines 247–343).

The proof is the Cauchy–Schwarz chain through `Q₀, …, Q₄`
(`addInUSelectedCSChainQ0` … `addInUSelectedCSChainQ4`): self-consistency of `A` gives the
`√(2δ)` bounds of the two insertion steps, and the global-variance bound the
`√ζ_variance` bounds of the two averaging steps. `gamma` does not enter the bound, matching the
paper, where `lem:add-in-u` is invoked inside a good-strategy section. -/
theorem addInUFullStatement_of_isGood
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (T : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓) :
    AddInUFullStatement params strategy T eps delta := by
  refine ⟨fun {Outcome} _ M S => ?_⟩
  have heps : 0 ≤ eps := eps_nonneg_of_isGood params strategy hgood
  have hdelta : 0 ≤ delta := delta_nonneg_of_isGood params strategy hgood
  have hssc : strategy.state.BipartiteSSCRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta :=
    ⟨hgood.selfConsistencyTest⟩
  have hlocal :
      (∑ g : MIPStarRE.LDT.Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state T.toSubMeas g) ≤
        localVarianceOfPointsError params eps delta :=
    localVarianceDeviation_sum_le_localVarianceOfPointsError
      params strategy eps delta gamma hgood T.toSubMeas
  have hglobal :
      (∑ g : MIPStarRE.LDT.Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T.toSubMeas g) ≤
        selfImprovementVarianceError params eps delta :=
    globalVarianceDeviation_sum_le_of_localVarianceDeviation_sum_le
      params strategy eps delta T.toSubMeas hlocal
  obtain ⟨h23, h34⟩ :=
    addInU_selected_cs_chain_step34_abs_le_sqrt_of_globalVarianceDeviation_sum_le
      (params := params) (strategy := strategy) (M := M) (T := T.toSubMeas) (S := S) hglobal
  have hsum := two_sqrt_two_delta_add_two_sqrt_selfImprovementVarianceError_le_addInUError
    params eps delta heps hdelta
  exact add_in_u_selected_transfer_of_cs_chain params strategy eps delta M T.toSubMeas S
    _ _ _ _
    (addInU_selected_cs_chain_step1_abs_le_sqrt_two_delta params strategy M T.toSubMeas S
      delta hssc)
    (addInU_selected_cs_chain_step2_abs_le_sqrt_two_delta params strategy M T.toSubMeas S
      delta hssc)
    h23 h34 (by linarith)

end MIPRE.LIDT.Co.SelfImprovement

end

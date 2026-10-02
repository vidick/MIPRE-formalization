/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
MainInductionStep/Theorems/RestrictedProbabilities/Core.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.MainInductionStep.Theorems.RestrictedProbabilities.Axis
public import MIPRE.Background.LIDT.Co.MainInductionStep.Theorems.RestrictedProbabilities.Diagonal

@[expose] public section

/-!
# Section 6 — Restricted probability statement

The axis-parallel, self-consistency and diagonal restricted-probability estimates collected
into the statement used by the main induction step (`lem:restricted-probabilities`): the
counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/MainInductionStep/Theorems/RestrictedProbabilities/Core.lean`
in the port of `planning/c6b-plan.md` (milestone M12, section "Port conventions").

A strategy is a `SymStrat params.next 𝔓 K` (`Co/Test/StrategyCore.lean`), whose state is the
symmetric model `strategy.state : SymModel 𝔓 K`, and errors are real numbers (the vendored
`Error := ℝ`). `restrictedProbabilities` holds for every symmetric model: restriction neither
orthonormalizes nor solves a semidefinite program, so it takes none of the model hypotheses
`hS hA` or `1 ≤ params.d` that the induction threads elsewhere, and the vendored statement has
no swap or normalization hypothesis to drop.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/inductive_step.tex`
- `blueprint/src/chapter/ch10_induction.tex`
-/

namespace MIPRE.LIDT.Co.MainInductionStep

open MIPStarRE.LDT (Parameters FieldModel Fq avgOver avgOver_const_mul uniformDistribution)
open MIPStarRE.LDT.MainInductionStep (sliceTransverseDirectionWeight weighted_bound_to_average)
open MIPRE.LIDT.Co (SymStrat)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Data weighted restricted axis/diagonal bounds into the public
`RestrictedProbabilitiesStatement`. -/
theorem RestrictedProbabilitiesStatement.ofWeightedBounds
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (haxisWeightedBound :
      avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedStrategy params strategy x).axisParallelFailureProbability) ≤ eps)
    (hdiagonalWeightedBound :
      avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedStrategy params strategy x).diagonalFailureProbability) ≤ gamma) :
    RestrictedProbabilitiesStatement params strategy eps delta gamma := by
  let profile : RestrictedFailureProfile params strategy :=
    { axisParallel := fun x =>
        (xRestrictedStrategy params strategy x).axisParallelFailureProbability
      selfConsistency := fun x =>
        (xRestrictedStrategy params strategy x).selfConsistencyFailureProbability
      diagonal := fun x =>
        (xRestrictedStrategy params strategy x).diagonalFailureProbability
      restrictedGood := fun _ => ⟨le_rfl, le_rfl, le_rfl⟩ }
  rw [avgOver_const_mul] at haxisWeightedBound hdiagonalWeightedBound
  refine ⟨profile, weighted_bound_to_average params haxisWeightedBound, ?_,
    weighted_bound_to_average params hdiagonalWeightedBound⟩
  exact (selfConsistencyRestrictedAverage_eq params strategy).trans_le
    hgood.selfConsistencyTest

/-- `lem:restricted-probabilities`: the slice restrictions of an `(ε, δ, γ)`-good strategy in
`m + 1` variables are good on average with `((m + 1)/m) ε`, `δ` and `((m + 1)/m) γ`. -/
theorem restrictedProbabilities
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma) :
    RestrictedProbabilitiesStatement params strategy eps delta gamma :=
  RestrictedProbabilitiesStatement.ofWeightedBounds params strategy eps delta gamma hgood
    (weighted_axisParallel_bound params strategy eps delta gamma hgood)
    (weighted_diagonal_bound params strategy eps delta gamma hgood)

end MIPRE.LIDT.Co.MainInductionStep

end

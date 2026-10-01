/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Basic/
DistributionPMF.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Basic.Distribution
public import MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.DistributionPMF

@[expose] public section

/-!
# PMF expectations of operator-valued averages

This is the counterpart, in the port of the low-individual-degree test to the symmetric model
(`planning/c6b-plan.md`, milestone M0, and its section "Port conventions"), of the operator part
of `MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/DistributionPMF.lean`: the operator average
`averageOperatorOverDistribution` against a probabilistic project distribution is the finite
expectation `PMF.realWeightedSum` against the associated Mathlib probability mass function.

The operators live in any real module `R` (`[AddCommMonoid R] [Module ℝ R]`), as in
`MIPRE/Background/LIDT/Co/Basic/Distribution.lean`.

## Main declarations

* `averageOperatorOverDistribution_eq_toPMF_realWeightedSum`
* `averageOperatorOverDistribution_uniform_eq_pmf_realWeightedSum`

## Not ported

The classical declarations of the vendored file, which this file imports:

- `Distribution.weightedSumLinearMap_eq_toPMF_realWeightedSum`: classical, imported.
- `Distribution.weightedSumLinearMap_eq_toPMF_realWeightedSumLinearMap`: classical, imported.
- `avgOver_eq_toPMF_realWeightedSum`: classical, imported.
- `uniformDistribution_sum_smul_eq_pmf_realWeightedSum`: classical, imported.
- `avgOver_uniform_eq_pmf_realWeightedSum`: classical, imported.
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co

open MIPStarRE.LDT (Distribution uniformDistribution)

/-- Operator-valued averaging against a probabilistic project distribution is
the finite expectation against its associated Mathlib probability mass
function. -/
theorem averageOperatorOverDistribution_eq_toPMF_realWeightedSum {α : Type*}
    [Fintype α]
    (𝒟 : Distribution α) (h𝒟 : 𝒟.IsProbability)
    {R : Type*} [AddCommMonoid R] [Module ℝ R]
    (f : α → R) :
    averageOperatorOverDistribution 𝒟 f =
      PMF.realWeightedSum (𝒟.toPMF h𝒟) f :=
  MIPStarRE.LDT.Distribution.weightedSumLinearMap_eq_toPMF_realWeightedSum 𝒟 h𝒟 f

/-- The uniform operator average is the finite expectation against Mathlib's
uniform probability mass function. -/
theorem averageOperatorOverDistribution_uniform_eq_pmf_realWeightedSum {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    {R : Type*} [AddCommMonoid R] [Module ℝ R]
    (f : α → R) :
    averageOperatorOverDistribution (uniformDistribution α) f =
      PMF.realWeightedSum (PMF.uniformOfFintype α) f :=
  MIPStarRE.LDT.uniformDistribution_sum_smul_eq_pmf_realWeightedSum f

end MIPRE.LIDT.Co

end

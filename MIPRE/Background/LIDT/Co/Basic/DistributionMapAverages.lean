/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Basic/
DistributionMapAverages.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored
file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Basic.DistributionAvg
public import MIPStarRE.LDT.Basic.DistributionMapAverages

@[expose] public section

/-!
# Uniform push-forward operator averages

This is the counterpart, in the port of the low-individual-degree test to the symmetric model
(`planning/c6b-plan.md`, milestone M0, and its section "Port conventions"), of the operator part
of `MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/DistributionMapAverages.lean`: averaging lemmas
for uniformly sampled finite seeds that are pushed forward to a question distribution. The main
use case is a random seed `a : α`, a pushed-forward value `m a : β`, and an observed coordinate
`g (m a)` which is identified with a uniform coordinate by an equivalence.

The operators live in any real module `R` (`[AddCommMonoid R] [Module ℝ R]`), as in
`MIPRE/Background/LIDT/Co/Basic/Distribution.lean`.

## Main declarations

* `averageOperatorOverDistribution_uniform_map_eq_uniform_of_factor_equiv`
* `averageOperatorOverDistribution_uniform_map_eq_uniform_fst_of_factor_equiv`
* `averageOperatorOverDistribution_uniform_map_eq_uniform_snd_of_factor_equiv`

## Not ported

The scalar averaging lemmas of the vendored file, which this file imports:

- `avgOver_uniform_map_eq_uniform_of_factor_equiv`: classical, imported.
- `avgOver_uniform_map_eq_uniform_fst_of_factor_equiv`: classical, imported.
- `avgOver_uniform_map_eq_uniform_snd_of_factor_equiv`: classical, imported.
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co

open MIPStarRE.LDT (uniformDistribution)

/-! ### Project-distribution map averages -/

/-- A uniform push-forward has the uniform operator average induced by an
equivalent observed coordinate.

The map `m` is the finite random seed map, `g` is the observed coordinate on
the pushed-forward value, and `e` records that this observed coordinate is
equivalent to a uniform sample of `γ`. -/
theorem averageOperatorOverDistribution_uniform_map_eq_uniform_of_factor_equiv
    {α β γ : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    (m : α → β) (g : β → γ) (e : α ≃ γ)
    (h : ∀ a, g (m a) = e a)
    {R : Type*} [AddCommMonoid R] [Module ℝ R]
    (A : γ → R) :
    averageOperatorOverDistribution ((uniformDistribution α).map m) (fun b => A (g b)) =
      averageOperatorOverDistribution (uniformDistribution γ) A :=
  MIPStarRE.LDT.uniformDistribution_map_sum_smul_eq_uniform_of_factor_equiv m g e h A

/-- A uniform push-forward has the first-coordinate uniform operator marginal
when the observed coordinate factors through a product equivalence of the seed. -/
theorem averageOperatorOverDistribution_uniform_map_eq_uniform_fst_of_factor_equiv
    {α β γ δ : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    [Finite δ] [Nonempty δ]
    (m : α → β) (g : β → γ) (e : α ≃ γ × δ)
    (h : ∀ a, g (m a) = (e a).1)
    {R : Type*} [AddCommMonoid R] [Module ℝ R]
    (A : γ → R) :
    averageOperatorOverDistribution ((uniformDistribution α).map m) (fun b => A (g b)) =
      averageOperatorOverDistribution (uniformDistribution γ) A :=
  MIPStarRE.LDT.uniformDistribution_map_sum_smul_eq_uniform_fst_of_factor_equiv m g e h A

/-- A uniform push-forward has the second-coordinate uniform operator marginal
when the observed coordinate factors through a product equivalence of the seed. -/
theorem averageOperatorOverDistribution_uniform_map_eq_uniform_snd_of_factor_equiv
    {α β γ δ : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [DecidableEq β]
    [Finite γ] [Nonempty γ]
    [Fintype δ] [DecidableEq δ] [Nonempty δ]
    (m : α → β) (g : β → δ) (e : α ≃ γ × δ)
    (h : ∀ a, g (m a) = (e a).2)
    {R : Type*} [AddCommMonoid R] [Module ℝ R]
    (A : δ → R) :
    averageOperatorOverDistribution ((uniformDistribution α).map m) (fun b => A (g b)) =
      averageOperatorOverDistribution (uniformDistribution δ) A :=
  MIPStarRE.LDT.uniformDistribution_map_sum_smul_eq_uniform_snd_of_factor_equiv m g e h A

end MIPRE.LIDT.Co

end

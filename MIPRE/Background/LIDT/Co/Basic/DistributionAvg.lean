/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Basic/
DistributionAvg.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Basic.Distribution
public import MIPStarRE.LDT.Basic.DistributionAvg

@[expose] public section

/-!
# Average lemmas for operator-valued averages over finite-support distributions

This is the counterpart, in the port of the low-individual-degree test to the symmetric model
(`planning/c6b-plan.md`, milestone M0, and its section "Port conventions"), of the operator part
of `MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/DistributionAvg.lean`: the operator-valued forms
of the module-valued finite-sum rules for uniform distributions, the comparison of operator
averages with Mathlib probability mass functions, and the factoring of fixed left and right
multiplications through an average.

As in `MIPRE/Background/LIDT/Co/Basic/Distribution.lean`, the operators live in any real module
`R`; the multiplication lemma asks for a (not necessarily unital or associative) semiring `𝒜`
(named so because the vendored lemma calls its right factor `R`) whose real scalars commute and
associate with the product (`IsScalarTower ℝ 𝒜 𝒜`, `SMulCommClass ℝ 𝒜 𝒜`), and the bound by
the identity the order structure of `averageOperatorOverDistribution_le_one_of_isProbability`.
The local C*-algebra and `K →L[ℂ] K` have all of these instances.

## Not ported

The scalar averaging lemmas of the vendored file, which this file imports:

- `avgOver_zero`: classical, imported.
- `avgOver_mono`: classical, imported.
- `avgOver_nonneg`: classical, imported.
- `avgOver_add`: classical, imported.
- `avgOver_sub`: classical, imported.
- `avgOver_const_mul`: classical, imported.
- `avgOver_mul_const`: classical, imported.
- `avgOver_sum`: classical, imported.
- `avgOver_finset_sum`: classical, imported.
- `avgOver_comm`: classical, imported.
- `avgOver_congr`: classical, imported.
- `avgOver_congr_on_support`: classical, imported.
- `avgOver_mono_on_support`: classical, imported.
- `avgOver_const`: classical, imported.
- `avgOver_const_of_isProbability`: classical, imported.
- `avgOver_le_of_weight_sum_le_one`: classical, imported.
- `avgOver_eq_toPMF_support_sum`: classical, imported.
- `avgOver_eq_toPMF_sum`: classical, imported.
- `avgOver_eq_toPMF_integral`: classical, imported.
- `Distribution.IsProbability.avgOver_le_of_forall_le_on_support`: classical, imported.
- `totalVariationDistance_eq_sum_max_sub`: classical, imported.
- `avgOver_le_avgOver_add_totalVariationDistance`: classical, imported.
- `avgOver_uniform_const`: classical, imported.
- `avgOver_uniform_eq_pmf_sum`: classical, imported.
- `avgOver_uniformOnFinset_eq_pmf_sum`: classical, imported.
- `avgOver_uniformOnFinset_eq_pmf_integral`: classical, imported.
- `avgOver_uniform_eq_pmf_integral`: classical, imported.
- `avgOver_uniformOnFinset_eq_subtype`: classical, imported.
- `avgOver_uniform_le_of_forall_le_on_support`: classical, imported.
- `avgOver_uniform_le_const`: classical, imported.
- `avgOver_uniform_equiv`: classical, imported.
- `avgOver_uniformOnFinset_equiv`: classical, imported.
- `avgOver_uniformOnFinset_filter_eq_subtype`: classical, imported.
- `avgOver_uniformOnFinset_filter_equiv`: classical, imported.
- `avgOver_uniform_prod`: classical, imported.
- `avgOver_uniform_comm`: classical, imported.
- `avgOver_uniform_prod_swap`: classical, imported.
- `avgOver_uniform_sum_eq_card_mul_prod`: classical, imported.
- `avgOver_uniform_equiv_prod`: classical, imported.
- `avgOver_uniform_equiv_prod_swap`: classical, imported.
- `avgOver_uniform_equiv_fst`: classical, imported.
- `avgOver_uniform_equiv_snd`: classical, imported.
- `avgOver_uniform_fst`: classical, imported.
- `avgOver_uniform_snd`: classical, imported.
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co

open MIPStarRE.LDT (Distribution uniformDistribution uniformDistribution_isProbability)

/-- Fixed left and right multiplications factor through an operator average. -/
theorem averageOperatorOverDistribution_mul_left_right {α : Type*}
    {𝒜 : Type*} [NonUnitalNonAssocSemiring 𝒜] [Module ℝ 𝒜]
    [IsScalarTower ℝ 𝒜 𝒜] [SMulCommClass ℝ 𝒜 𝒜]
    (𝒟 : Distribution α) (L R : 𝒜)
    (A : α → 𝒜) :
    averageOperatorOverDistribution 𝒟 (fun a => L * A a * R) =
      L * averageOperatorOverDistribution 𝒟 A * R := by
  simp only [averageOperatorOverDistribution, Finset.mul_sum, Finset.sum_mul, mul_smul_comm,
    smul_mul_assoc]

/-- Operator-valued averaging against a probabilistic project distribution is
the finite operator sum over the stored support against the associated Mathlib
probability mass function. -/
theorem averageOperatorOverDistribution_eq_toPMF_support_sum {α : Type*}
    (𝒟 : Distribution α) (h𝒟 : 𝒟.IsProbability)
    {R : Type*} [AddCommMonoid R] [Module ℝ R]
    (f : α → R) :
    averageOperatorOverDistribution 𝒟 f =
      ∑ a ∈ 𝒟.support, (𝒟.toPMF h𝒟 a).toReal • f a :=
  MIPStarRE.LDT.Distribution.sum_smul_eq_toPMF_support_sum 𝒟 h𝒟 f

/-- Operator-valued averaging against a probabilistic project distribution is
the finite sum against its associated Mathlib probability mass function. -/
theorem averageOperatorOverDistribution_eq_toPMF_sum {α : Type*}
    [Fintype α]
    (𝒟 : Distribution α) (h𝒟 : 𝒟.IsProbability)
    {R : Type*} [AddCommMonoid R] [Module ℝ R]
    (f : α → R) :
    averageOperatorOverDistribution 𝒟 f =
      ∑ a : α, (𝒟.toPMF h𝒟 a).toReal • f a :=
  MIPStarRE.LDT.Distribution.sum_smul_eq_toPMF_sum 𝒟 h𝒟 f

/-- The uniform operator average is the finite operator sum weighted by
`PMF.uniformOfFintype`. -/
theorem averageOperatorOverDistribution_uniform_eq_pmf_sum {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    {R : Type*} [AddCommMonoid R] [Module ℝ R]
    (f : α → R) :
    averageOperatorOverDistribution (uniformDistribution α) f =
      ∑ a : α, (PMF.uniformOfFintype α a).toReal • f a :=
  MIPStarRE.LDT.uniformDistribution_sum_smul_eq_pmf_sum f

/-- A finite-support uniform operator average is the corresponding Mathlib uniform PMF sum. -/
theorem averageOperatorOverDistribution_uniformOnFinset_eq_pmf_sum
    {α : Type*} (s : Finset α) (hs : s.Nonempty)
    {R : Type*} [AddCommMonoid R] [Module ℝ R]
    (f : α → R) :
    averageOperatorOverDistribution (Distribution.uniformOnFinset s) f =
      ∑ a ∈ s, (PMF.uniformOfFinset s hs a).toReal • f a :=
  MIPStarRE.LDT.uniformOnFinset_sum_smul_eq_pmf_sum s hs f

/-- Reindexing a uniform operator average along an equivalence preserves its value. -/
theorem averageOperatorOverDistribution_uniform_equiv
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    {R : Type*} [AddCommMonoid R] [Module ℝ R]
    (e : α ≃ β) (f : α → R) :
    averageOperatorOverDistribution (uniformDistribution α) f =
      averageOperatorOverDistribution (uniformDistribution β)
        (fun b => f (e.symm b)) :=
  MIPStarRE.LDT.uniformDistribution_sum_smul_equiv e f

/-- A uniform operator average over a finite support is the same as the uniform
operator average over the corresponding finite subtype. -/
theorem averageOperatorOverDistribution_uniformOnFinset_eq_subtype
    {α : Type*} [DecidableEq α] (s : Finset α)
    [Nonempty {a : α // a ∈ s}]
    {R : Type*} [AddCommMonoid R] [Module ℝ R]
    (f : α → R) :
    averageOperatorOverDistribution (Distribution.uniformOnFinset s) f =
      averageOperatorOverDistribution (uniformDistribution {a : α // a ∈ s})
        (fun a => f a.1) :=
  MIPStarRE.LDT.uniformOnFinset_sum_smul_eq_subtype s f

/-- A uniform operator average over a finite support may be reindexed by any
finite type equivalent to that support subtype. -/
theorem averageOperatorOverDistribution_uniformOnFinset_equiv
    {α β : Type*}
    [Fintype β] [DecidableEq β] [Nonempty β]
    (s : Finset α) (e : β ≃ {a : α // a ∈ s})
    {R : Type*} [AddCommMonoid R] [Module ℝ R]
    (f : α → R) :
    averageOperatorOverDistribution (Distribution.uniformOnFinset s) f =
      averageOperatorOverDistribution (uniformDistribution β) (fun b => f (e b).1) :=
  MIPStarRE.LDT.uniformOnFinset_sum_smul_equiv s e f

/-- A uniform operator average over a filtered finite support is the uniform
operator average over the finite subtype satisfying the predicate. -/
theorem averageOperatorOverDistribution_uniformOnFinset_filter_eq_subtype
    {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → Prop) [DecidablePred p] [Nonempty {a : α // p a}]
    {R : Type*} [AddCommMonoid R] [Module ℝ R]
    (f : α → R) :
    averageOperatorOverDistribution
        (Distribution.uniformOnFinset (Finset.univ.filter p)) f =
      averageOperatorOverDistribution (uniformDistribution {a : α // p a})
        (fun a => f a.1) :=
  MIPStarRE.LDT.uniformOnFinset_filter_sum_smul_eq_subtype p f

/-- A uniform operator average over a filtered finite type may be reindexed by
any finite seed type equivalent to the predicate subtype. -/
theorem averageOperatorOverDistribution_uniformOnFinset_filter_equiv
    {α β : Type*} [Fintype α]
    (p : α → Prop) [DecidablePred p]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (e : β ≃ {a : α // p a})
    {R : Type*} [AddCommMonoid R] [Module ℝ R]
    (f : α → R) :
    averageOperatorOverDistribution
        (Distribution.uniformOnFinset (Finset.univ.filter p)) f =
      averageOperatorOverDistribution (uniformDistribution β) (fun b => f (e b).1) :=
  MIPStarRE.LDT.uniformOnFinset_filter_sum_smul_equiv p e f

/-- A uniform average of effects is again bounded above by the identity operator. -/
theorem averageOperatorOverDistribution_uniform_le_one {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    {R : Type*} [AddCommMonoid R] [Module ℝ R] [PartialOrder R] [IsOrderedAddMonoid R]
    [PosSMulMono ℝ R] [SMulPosMono ℝ R] [One R] [ZeroLEOneClass R]
    (f : α → R) (hf : ∀ a, f a ≤ 1) :
    averageOperatorOverDistribution (uniformDistribution α) f ≤ 1 :=
  averageOperatorOverDistribution_le_one_of_isProbability
    (uniformDistribution α) (uniformDistribution_isProbability α) f hf

end MIPRE.LIDT.Co

end

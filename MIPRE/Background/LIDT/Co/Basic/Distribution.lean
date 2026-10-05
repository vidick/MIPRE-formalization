/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Basic/
Distribution.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPStarRE.LDT.Basic.Distribution

@[expose] public section

/-!
# The operator-valued average over a finite-support distribution

This is the counterpart, in the port of the low-individual-degree test to the symmetric model
(`planning/c6b-plan.md`, milestone M0, and its section "Port conventions"), of the operator part
of `MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/Distribution.lean`.

The vendored file defines `averageOperatorOverDistribution 𝒟 f = ∑ a ∈ 𝒟.support, 𝒟.weight a • f a`
for a family `f` of matrices `MIPStarRE.Quantum.Op ι`. The port needs it for two kinds of
operators, the local ones (a C*-algebra `𝔓`) and the joint ones (`K →L[ℂ] K`), so it is defined
here for any real module `R`, and each lemma asks for exactly the structure its proof uses:

* the definition and the linear lemmas (`_map`, `_congr`, `_sum`, `_finset_sum`, `_const`):
  `[AddCommMonoid R] [Module ℝ R]`;
* the order lemmas (`_nonneg`, `_mono`): in addition `[PartialOrder R] [IsOrderedAddMonoid R]
  [PosSMulMono ℝ R]`;
* the bounds by the identity (`_le_one_*`): in addition `[One R] [ZeroLEOneClass R]
  [SMulPosMono ℝ R]`.

Every C*-algebra with its order (`[CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]`), in
particular `K →L[ℂ] K`, has all of these instances, with `Module ℝ` the restriction of scalars of
its complex structure. For `K →L[ℂ] K` this file also declares shortcut instances for the real
scalars (see "Shortcut instances for the joint operators" below), because synthesizing those
classes there is slow; they are `scoped` to `MIPRE.LIDT.Co`, so in force in every port file and
nowhere else.

The classical part of the vendored file (`Distribution`, `avgOver`, the uniform distributions,
the push-forward, `toPMF`, the total variation distance) is not ported: it is imported, and named
through an explicit `open MIPStarRE.LDT (…)` list. The names below resolve, inside
`MIPRE.LIDT.Co`, to the ported declarations, never to the vendored matrix ones.

## Not ported

The classical declarations of the vendored file, which this file imports:

- `Distribution`: classical, imported.
- `Distribution.totalWeight`: classical, imported.
- `Distribution.IsProbability`: classical, imported.
- `Distribution.map`: classical, imported.
- `Distribution.map_support`: classical, imported.
- `Distribution.map_weight`: classical, imported.
- `Distribution.map_totalWeight`: classical, imported.
- `Distribution.map_sum_smul`: classical, imported.
- `Distribution.sum_univ_eq_sum_support`: classical, imported.
- `Distribution.IsProbability.weight_sum_eq_one`: classical, imported.
- `Distribution.IsProbability.weight_sum_univ_eq_one`: classical, imported.
- `Distribution.IsProbability.weight_sum_le_one`: classical, imported.
- `Distribution.IsProbability.map`: classical, imported.
- `Distribution.toPMF`: classical, imported.
- `Distribution.toPMF_apply`: classical, imported.
- `Distribution.toPMF_apply_toReal`: classical, imported.
- `Distribution.toPMF_apply_of_notMem`: classical, imported.
- `Distribution.toPMF_map`: classical, imported.
- `avgOver`: classical, imported.
- `Distribution.weightedSumLinearMap`: classical (generic in the module), imported.
- `Distribution.weightedSumLinearMap_apply`: classical, imported.
- `Distribution.avgOver_eq_weightedSumLinearMap`: classical, imported.
- `Distribution.avgOver_map`: classical, imported.
- `Distribution.uniformOnFinset`: classical, imported.
- `Distribution.uniformOnFinset_support`: classical, imported.
- `Distribution.uniformOnFinset_weight`: classical, imported.
- `Distribution.uniformOnFinset_isProbability`: classical, imported.
- `Distribution.uniformOnFinset_weight_sum_le_one`: classical, imported.
- `Distribution.uniformOnFinset_toPMF`: classical, imported.
- `uniformDistribution`: classical, imported.
- `uniformDistribution_support`: classical, imported.
- `uniformDistribution_weight_sum_eq_one`: classical, imported.
- `uniformDistribution_isProbability`: classical, imported.
- `uniformDistribution_weight_sum_le_one`: classical, imported.
- `uniformDistribution_toPMF`: classical, imported.
- `totalVariationDistance`: classical, imported.
- `totalVariationDistance_eq_univ_sum`: classical, imported.
- `totalVariationDistance_eq_toPMF_sum`: classical, imported.
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co

open MIPStarRE.LDT (Distribution)

/-! ### Shortcut instances for the joint operators

Under the import of all of Mathlib that the vendored classical layer brings, synthesizing the
real ordered-module structure of `K →L[ℂ] K` takes 0.6–1.9 s per class (`PosSMulMono ℝ` through
`Mathlib/Algebra/Order/Star/Basic.lean`'s `IsOrderedModule` instance for star-ordered rings, and
`IsScalarTower ℝ`/`SMulCommClass ℝ` through `Algebra.complexToReal`), paid again at every use of
an order lemma below on joint operators. These shortcuts, found first, cut such a use from about
2 s to 0.3 s. The real scalar structure itself is slow too: `SMulZeroClass ℝ` (reached through
`smul_nonneg`) and `Algebra ℝ` (reached by `simp [smul_mul_assoc]`) take about 0.5 s each, and
`SMul ℝ` 0.1 s at every elaboration of `c • X` with `c : ℝ`; their shortcuts carry data, but each
is `inferInstance`, the instance the search finds anyway, so it is the same term and creates no
diamond. The local C*-algebra `𝔓` does not need any of them (0.1–0.2 s per use).

They are `scoped` instances of `MIPRE.LIDT.Co`: in force in every file of the port (each works
inside that namespace) and in no importer outside it. A new shortcut for the joint operators goes
here. -/

section JointShortcuts

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Shortcut: the real scalar action on `K →L[ℂ] K`. -/
noncomputable scoped instance (priority := high) instSMulRealCLM : SMul ℝ (K →L[ℂ] K) :=
  inferInstance

/-- Shortcut: the real scalar action on `K →L[ℂ] K` fixes zero. -/
noncomputable scoped instance (priority := high) instSMulZeroClassRealCLM :
    SMulZeroClass ℝ (K →L[ℂ] K) :=
  inferInstance

/-- Shortcut: `K →L[ℂ] K` is a real vector space. -/
noncomputable scoped instance (priority := high) instModuleRealCLM : Module ℝ (K →L[ℂ] K) :=
  inferInstance

/-- Shortcut: `K →L[ℂ] K` is a real algebra. -/
noncomputable scoped instance (priority := high) instAlgebraRealCLM : Algebra ℝ (K →L[ℂ] K) :=
  inferInstance

/-- Shortcut: real scalars associate with the product of `K →L[ℂ] K`. -/
scoped instance (priority := high) instIsScalarTowerRealCLM :
    IsScalarTower ℝ (K →L[ℂ] K) (K →L[ℂ] K) :=
  inferInstance

/-- Shortcut: real scalars commute with the product of `K →L[ℂ] K`. -/
scoped instance (priority := high) instSMulCommClassRealCLM :
    SMulCommClass ℝ (K →L[ℂ] K) (K →L[ℂ] K) :=
  inferInstance

/-- Shortcut: real scalars act monotonically on the Loewner order of `K →L[ℂ] K`. -/
scoped instance (priority := high) instPosSMulMonoRealCLM : PosSMulMono ℝ (K →L[ℂ] K) :=
  inferInstance

/-- Shortcut: a nonnegative operator of `K →L[ℂ] K` scales monotonically in a real scalar. -/
scoped instance (priority := high) instSMulPosMonoRealCLM : SMulPosMono ℝ (K →L[ℂ] K) :=
  PosSMulMono.toSMulPosMono

end JointShortcuts

/-- Weighted sum of operators over a distribution's finite support, using the same
`support`/`weight` data as the scalar `avgOver`.

This is a project-local adapter around Mathlib finite sums for the LDT `Distribution`
representation and the real scalar action on an operator space `R` (the local C*-algebra or
`K →L[ℂ] K`), not a replacement for Mathlib's probability theory APIs. -/
noncomputable def averageOperatorOverDistribution {α : Type*}
    {R : Type*} [AddCommMonoid R] [Module ℝ R]
    (𝒟 : Distribution α) (f : α → R) : R :=
  ∑ a ∈ 𝒟.support, 𝒟.weight a • f a

namespace Distribution

/-- Operator averaging is the weighted finite-sum linear map applied to an
operator-valued family. -/
theorem averageOperatorOverDistribution_eq_weightedSumLinearMap {α : Type*}
    (𝒟 : Distribution α)
    {R : Type*} [AddCommMonoid R] [Module ℝ R]
    (f : α → R) :
    averageOperatorOverDistribution 𝒟 f = 𝒟.weightedSumLinearMap R f :=
  rfl

/-- Operator-valued averaging against a pushed-forward distribution is
operator-valued averaging of the pulled-back family against the original
distribution. -/
theorem averageOperatorOverDistribution_map {α β : Type*} [DecidableEq β]
    (𝒟 : Distribution α) (e : α → β)
    {R : Type*} [AddCommMonoid R] [Module ℝ R]
    (f : β → R) :
    averageOperatorOverDistribution (𝒟.map e) f =
      averageOperatorOverDistribution 𝒟 (fun a => f (e a)) :=
  𝒟.map_sum_smul e f

end Distribution

/-- If two operator-valued families agree pointwise, their averages agree. -/
theorem averageOperatorOverDistribution_congr {α : Type*}
    {R : Type*} [AddCommMonoid R] [Module ℝ R]
    (𝒟 : Distribution α) (A B : α → R)
    (h : ∀ a, A a = B a) :
    averageOperatorOverDistribution 𝒟 A = averageOperatorOverDistribution 𝒟 B :=
  Finset.sum_congr rfl fun a _ => by rw [h a]

/-- Pull a finite outcome sum through an operator-valued average. -/
theorem averageOperatorOverDistribution_sum {α β : Type*} [Fintype β]
    (𝒟 : Distribution α)
    {R : Type*} [AddCommMonoid R] [Module ℝ R]
    (f : α → β → R) :
    averageOperatorOverDistribution 𝒟 (fun a => ∑ b : β, f a b) =
      ∑ b : β, averageOperatorOverDistribution 𝒟 (fun a => f a b) := by
  simp only [averageOperatorOverDistribution, Finset.smul_sum]
  exact Finset.sum_comm

/-- Pull a finite-set outcome sum through an operator-valued average. -/
theorem averageOperatorOverDistribution_finset_sum {α β : Type*}
    (𝒟 : Distribution α) (s : Finset β)
    {R : Type*} [AddCommMonoid R] [Module ℝ R]
    (f : α → β → R) :
    averageOperatorOverDistribution 𝒟 (fun a => ∑ b ∈ s, f a b) =
      ∑ b ∈ s, averageOperatorOverDistribution 𝒟 (fun a => f a b) := by
  simp only [averageOperatorOverDistribution, Finset.smul_sum]
  exact Finset.sum_comm

/-- Operator averages preserve positivity. -/
theorem averageOperatorOverDistribution_nonneg {α : Type*}
    {R : Type*} [AddCommMonoid R] [Module ℝ R] [PartialOrder R] [IsOrderedAddMonoid R]
    [PosSMulMono ℝ R]
    (𝒟 : Distribution α) (f : α → R)
    (hf : ∀ a, 0 ≤ f a) :
    0 ≤ averageOperatorOverDistribution 𝒟 f :=
  Finset.sum_nonneg fun a _ => smul_nonneg (𝒟.nonnegative a) (hf a)

/-- Operator averages preserve pointwise order. -/
theorem averageOperatorOverDistribution_mono {α : Type*}
    {R : Type*} [AddCommMonoid R] [Module ℝ R] [PartialOrder R] [IsOrderedAddMonoid R]
    [PosSMulMono ℝ R]
    (𝒟 : Distribution α) (f g : α → R)
    (hfg : ∀ a, f a ≤ g a) :
    averageOperatorOverDistribution 𝒟 f ≤ averageOperatorOverDistribution 𝒟 g :=
  Finset.sum_le_sum fun a _ => smul_le_smul_of_nonneg_left (hfg a) (𝒟.nonnegative a)

/-- The average of a constant operator is the total mass times that operator. -/
theorem averageOperatorOverDistribution_const {α : Type*}
    {R : Type*} [AddCommMonoid R] [Module ℝ R]
    (𝒟 : Distribution α) (A : R) :
    averageOperatorOverDistribution 𝒟 (fun _ : α => A) =
      (∑ a ∈ 𝒟.support, 𝒟.weight a) • A :=
  (Finset.sum_smul ..).symm

/-- The average of a constant operator over a probability distribution is that
operator. -/
theorem averageOperatorOverDistribution_const_of_isProbability {α : Type*}
    {R : Type*} [AddCommMonoid R] [Module ℝ R]
    (𝒟 : Distribution α) (h𝒟 : 𝒟.IsProbability) (A : R) :
    averageOperatorOverDistribution 𝒟 (fun _ : α => A) = A := by
  rw [averageOperatorOverDistribution_const, h𝒟.weight_sum_eq_one, one_smul]

/-- An average of effects against a sub-probability distribution is again bounded
above by the identity operator. -/
theorem averageOperatorOverDistribution_le_one_of_weight_sum_le_one {α : Type*}
    {R : Type*} [AddCommMonoid R] [Module ℝ R] [PartialOrder R] [IsOrderedAddMonoid R]
    [PosSMulMono ℝ R] [SMulPosMono ℝ R] [One R] [ZeroLEOneClass R]
    (𝒟 : Distribution α) (f : α → R)
    (h𝒟 : ∑ a ∈ 𝒟.support, 𝒟.weight a ≤ 1)
    (hf : ∀ a, f a ≤ 1) :
    averageOperatorOverDistribution 𝒟 f ≤ 1 :=
  calc
    averageOperatorOverDistribution 𝒟 f
        ≤ averageOperatorOverDistribution 𝒟 (fun _ : α => 1) :=
          averageOperatorOverDistribution_mono 𝒟 f (fun _ : α => 1) hf
    _ = (∑ a ∈ 𝒟.support, 𝒟.weight a) • (1 : R) :=
          averageOperatorOverDistribution_const 𝒟 1
    _ ≤ (1 : ℝ) • (1 : R) := smul_le_smul_of_nonneg_right h𝒟 zero_le_one
    _ = 1 := one_smul ℝ 1

/-- An average of effects against a probability distribution is again bounded
above by the identity operator. -/
theorem averageOperatorOverDistribution_le_one_of_isProbability {α : Type*}
    {R : Type*} [AddCommMonoid R] [Module ℝ R] [PartialOrder R] [IsOrderedAddMonoid R]
    [PosSMulMono ℝ R] [SMulPosMono ℝ R] [One R] [ZeroLEOneClass R]
    (𝒟 : Distribution α) (h𝒟 : 𝒟.IsProbability)
    (f : α → R) (hf : ∀ a, f a ≤ 1) :
    averageOperatorOverDistribution 𝒟 f ≤ 1 :=
  averageOperatorOverDistribution_le_one_of_weight_sum_le_one 𝒟 f h𝒟.weight_sum_le_one hf

end MIPRE.LIDT.Co

end

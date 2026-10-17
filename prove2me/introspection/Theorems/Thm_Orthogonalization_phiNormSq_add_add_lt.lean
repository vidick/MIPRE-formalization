/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/PhiNorm.lean
-/
/-
# The seminorm `‖·‖_φ` of a positive functional, and its triangle inequality

For a positive linear functional `φ` on `H →L[ℂ] H` the paper
(M. de la Salle, *Orthogonalization of Positive Operator Valued Measures*,
arXiv:2103.14126v2, Section 1) writes `‖b‖_φ = √(φ (b* b))`, and the assembly
step (`PLAN.md` §1, step **F3**) applies its triangle inequality to *tuples*
`(b_i)_{i ∈ ι}`, i.e. to the norm of `PiLp 2` over the GNS space:

`‖(b_i)‖_φ = √(∑ i, φ (b_i* b_i))`.

This file defines the square of that quantity, `phiNormSq φ b`, as a real
number, and proves what the three-term estimate of step **F3** needs:

* `norm_map_star_mul_le` / `sq_norm_map_star_mul_le`: the Cauchy–Schwarz
  inequality for a positive functional, obtained from Mathlib's GNS
  construction (`PositiveLinearMap.PreGNS`), which turns `x, y ↦ φ (x* y)`
  into an honest (semi-definite) inner product;
* `phiNormSq_nonneg`, `phiNormSq_add_le`: the triangle inequality
  `√(phiNormSq φ (b + c)) ≤ √(phiNormSq φ b) + √(phiNormSq φ c)`;
* `phiNormSq_add_add_lt`: the three-term corollary
  `phiNormSq φ b ≤ ε`, `phiNormSq φ c ≤ ε`, `phiNormSq φ d < ε`
  imply `phiNormSq φ (b + c + d) < 9 ε`, which is exactly the shape in which
  the constant `9` of Theorem 1.2 is produced.

Positivity of `φ` is kept as a bare hypothesis
`hφ : ∀ z, 0 ≤ φ (star z * z)` (with the `ComplexOrder` order on `ℂ`) rather
than bundled, so that the lemmas apply verbatim to the functional underlying a
normal state.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Orthonormalization/Orthogonalization/PhiNorm.lean (statement stub of Orthogonalization.phiNormSq_add_add_lt);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Module.PositiveLinearMap
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.NNReal.Star
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.Data.SetLike.Basic
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Hom.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Algebra.Star.Real
import Mathlib.Topology.Algebra.UniformMulAction
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.Defs
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_Positivity
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_PhiNorm

open Orthogonalization
open scoped ComplexOrder BigOperators
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ} {ι : Type*} [Fintype ι]

theorem Orthogonalization.phiNormSq_add_add_lt (hφ : ∀ z : H →L[ℂ] H, 0 ≤ φ (star z * z))
    {b c d : ι → H →L[ℂ] H} {ε : ℝ} (hε : 0 < ε)
    (hb : phiNormSq φ b ≤ ε) (hc : phiNormSq φ c ≤ ε) (hd : phiNormSq φ d < ε) :
    phiNormSq φ (b + c + d) < 9 * ε := by sorry

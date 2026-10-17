/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/FinDim/Isometry.lean
-/
/-
# Isometric completion in finite dimension (Step F2, Lemma 3.2 of the paper)

Given `T : H → K` and a positive self-adjoint `s` on `H` with `T* T = s²`
(so `‖T v‖ = ‖s v‖`), and a subspace `L ≤ K` with `range T ≤ L` and
`dim L = dim H`, there is an isometry `u : H → K` onto `L` with `u ∘ s = T`.
This is the finite-dimensional content of Lemma 3.2 (`lem:polar_decom_finite`):
the polar part `u₀` of `T` (defined on `range s = range |T|`) is completed on
`ker s` by any isometry onto the orthogonal complement of `range T` inside `L`,
which has the right dimension because `dim L = dim H`.

Proof-side; nothing here is a statement of the paper.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Orthonormalization/Orthogonalization/FinDim/Isometry.lean (statement stub of Orthogonalization.FinDim.exists_isometry_completion);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.CStarAlgebra.Module.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Submodule
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.FunLike.IsApply
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Operations
import Mathlib.Data.SetLike.Basic
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Logic.Equiv.Defs
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Notation
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.UniformMulAction
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Defs

open scoped InnerProductSpace ComplexOrder
open Module ContinuousLinearMap
set_option autoImplicit true
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K]

theorem Orthogonalization.FinDim.exists_isometry_completion (T : H →L[ℂ] K) (s : H →L[ℂ] H)
    (hs : IsSelfAdjoint s) (hs0 : 0 ≤ s) (hT : adjoint T ∘L T = s ∘L s)
    (L : Submodule ℂ K) (hTL : LinearMap.range (T : H →ₗ[ℂ] K) ≤ L) (hL : finrank ℂ L = finrank ℂ H) :
    ∃ u : H →L[ℂ] K, adjoint u ∘L u = 1 ∧ u ∘L adjoint u = L.starProjection ∧
      u ∘L s = T := by sorry

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Repetition/TenProofs/QuantumParallelRepetition/Part02.lean (solution of QuantumParallelRepetition.ClassicalInformation.rationalPermutationOutput_disagreement_le_two_mul_finiteTotalVariation);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Opposite
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Opposite
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Action.Pi
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Basic
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Opposites
import Mathlib.Algebra.Order.Archimedean.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.IsBotOne
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.CharZero
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.Unitary
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.CStarAlgebra.Module.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Group.Submodule
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Countable.Defs
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Holder
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Finite.Sum
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.FunLike.IsApply
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.PEquiv
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Init
import Mathlib.Data.PEquiv
import Mathlib.Data.Prod.Basic
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Init
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.CoeSort
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Set.Operations
import Mathlib.Data.Set.Restrict
import Mathlib.Data.SetLike.Basic
import Mathlib.Data.Sigma.Basic
import Mathlib.Data.Subtype
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Embedding.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Function.Defs
import Mathlib.Logic.IsEmpty.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.AEEqFun
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Bounds.Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Defs
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Disjoint
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.AtTopBot.Group
import Mathlib.Order.Filter.Defs
import Mathlib.Order.Filter.Tendsto
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.Lattice
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Max
import Mathlib.Order.MinMax
import Mathlib.Order.Monotone.Defs
import Mathlib.Order.Notation
import Mathlib.Order.RelClasses
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.LinearCombination.Lemmas
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Algebra.Star.Real
import Mathlib.Topology.Algebra.UniformMulAction
import Mathlib.Topology.Closure
import Mathlib.Topology.Constructions
import Mathlib.Topology.Continuous
import Mathlib.Topology.ContinuousMap.ContinuousSqrt
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.EMetricSpace.Defs
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.Hom.Esakia
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Separation.GDelta
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.UniformSpace.Defs
import Mathlib.Topology.UniformSpace.Matrix
import Mathlib.Topology.UniformSpace.Pi
import Mathlib.Topology.UniformSpace.Real
import Definitions.Def_MIPRE_Background_Repetition_TenProofs_QuantumParallelRepetition_Part01
import Definitions.Def_MIPRE_Background_Repetition_TenProofs_QuantumParallelRepetition_Part02
import Theorems.Thm_QuantumParallelRepetition_ClassicalInformation_rationalMarked_markedTotalVariation_eq
import Theorems.Thm_QuantumParallelRepetition_ClassicalSampling_markedFirst_event_card_mul

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace QuantumParallelRepetition.ClassicalSampling
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
set_option autoImplicit true
variable {α : Type*} [Fintype α] [DecidableEq α]
omit [DecidableEq α] in

theorem markedFirst_mem (rank : α ≃ Fin (Fintype.card α))
    (marked : Finset α) (nonempty : marked.Nonempty)
    (permutation : Equiv.Perm α) :
    markedFirst rank marked nonempty permutation ∈ marked := by
  have hmin := (marked.image (fun a => rank (permutation a))).min'_mem
    (nonempty.image (fun a => rank (permutation a)))
  obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp hmin
  simpa [markedFirst, ← heq] using ha
end
end QuantumParallelRepetition.ClassicalSampling

namespace QuantumParallelRepetition.ClassicalSampling
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
set_option autoImplicit true
variable {α : Type*} [Fintype α] [DecidableEq α]
omit [DecidableEq α] in

theorem markedFirst_rank (rank : α ≃ Fin (Fintype.card α))
    (marked : Finset α) (nonempty : marked.Nonempty)
    (permutation : Equiv.Perm α) :
    rank (permutation (markedFirst rank marked nonempty permutation)) =
      (marked.image (fun a => rank (permutation a))).min'
        (nonempty.image (fun a => rank (permutation a))) := by
  simp [markedFirst]
end
end QuantumParallelRepetition.ClassicalSampling

namespace QuantumParallelRepetition.ClassicalSampling
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
set_option autoImplicit true
variable {α : Type*} [Fintype α] [DecidableEq α]
omit [DecidableEq α] in

theorem markedFirst_rank_le (rank : α ≃ Fin (Fintype.card α))
    (marked : Finset α) (nonempty : marked.Nonempty)
    (permutation : Equiv.Perm α) {a : α} (ha : a ∈ marked) :
    rank (permutation (markedFirst rank marked nonempty permutation)) ≤
      rank (permutation a) := by
  rw [markedFirst_rank]
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
end
end QuantumParallelRepetition.ClassicalSampling

namespace QuantumParallelRepetition.ClassicalSampling
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
set_option autoImplicit true
variable {α : Type*} [Fintype α] [DecidableEq α]
omit [DecidableEq α] in

theorem markedFirst_eq_of_mem_of_rank_le
    (rank : α ≃ Fin (Fintype.card α))
    (marked : Finset α) (nonempty : marked.Nonempty)
    (permutation : Equiv.Perm α) {a : α} (ha : a ∈ marked)
    (hle : ∀ b ∈ marked, rank (permutation a) ≤ rank (permutation b)) :
    markedFirst rank marked nonempty permutation = a := by
  apply permutation.injective
  apply rank.injective
  exact le_antisymm
    (markedFirst_rank_le rank marked nonempty permutation ha)
    (hle _ (markedFirst_mem rank marked nonempty permutation))
end
end QuantumParallelRepetition.ClassicalSampling

namespace QuantumParallelRepetition.ClassicalSampling
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
set_option autoImplicit true
variable {α : Type*} [Fintype α] [DecidableEq α]
omit [DecidableEq α] in

theorem markedFirst_subset_eq_of_mem
    (rank : α ≃ Fin (Fintype.card α))
    {small large : Finset α}
    (hsmall : small.Nonempty) (hlarge : large.Nonempty)
    (permutation : Equiv.Perm α)
    (hsub : small ⊆ large)
    (hmem : markedFirst rank large hlarge permutation ∈ small) :
    markedFirst rank small hsmall permutation =
      markedFirst rank large hlarge permutation := by
  apply markedFirst_eq_of_mem_of_rank_le rank small hsmall permutation hmem
  intro a ha
  exact markedFirst_rank_le rank large hlarge permutation (hsub ha)
end
end QuantumParallelRepetition.ClassicalSampling

namespace QuantumParallelRepetition.ClassicalSampling
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
set_option autoImplicit true
variable {α : Type*} [Fintype α] [DecidableEq α]
theorem markedFirst_eq_iff_union_first_mem_inter
    (rank : α ≃ Fin (Fintype.card α))
    (left right : Finset α)
    (hleft : left.Nonempty) (hright : right.Nonempty)
    (permutation : Equiv.Perm α) :
    markedFirst rank left hleft permutation =
        markedFirst rank right hright permutation ↔
      markedFirst rank (left ∪ right) (hleft.mono Finset.subset_union_left)
          permutation ∈ left ∩ right := by
  let hunion : (left ∪ right).Nonempty :=
    hleft.mono Finset.subset_union_left
  constructor
  · intro hagree
    have hfirst :
        markedFirst rank (left ∪ right) hunion permutation =
          markedFirst rank left hleft permutation := by
      apply markedFirst_eq_of_mem_of_rank_le
        rank (left ∪ right) hunion permutation
      · exact Finset.mem_union_left right
          (markedFirst_mem rank left hleft permutation)
      · intro a ha
        rcases Finset.mem_union.mp ha with ha | ha
        · exact markedFirst_rank_le rank left hleft permutation ha
        · rw [hagree]
          exact markedFirst_rank_le rank right hright permutation ha
    apply Finset.mem_inter.mpr
    constructor
    · rw [hfirst]
      exact markedFirst_mem rank left hleft permutation
    · rw [hfirst, hagree]
      exact markedFirst_mem rank right hright permutation
  · intro hcommon
    have hleft' := markedFirst_subset_eq_of_mem
      rank hleft hunion permutation Finset.subset_union_left
      (Finset.mem_inter.mp hcommon).1
    have hright' := markedFirst_subset_eq_of_mem
      rank hright hunion permutation Finset.subset_union_right
      (Finset.mem_inter.mp hcommon).2
    exact hleft'.trans hright'.symm
end
end QuantumParallelRepetition.ClassicalSampling

namespace QuantumParallelRepetition.ClassicalSampling
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
set_option autoImplicit true
variable {α : Type*} [Fintype α] [DecidableEq α]
theorem markedFirst_ne_iff_union_first_mem_symmDiff
    (rank : α ≃ Fin (Fintype.card α))
    (left right : Finset α)
    (hleft : left.Nonempty) (hright : right.Nonempty)
    (permutation : Equiv.Perm α) :
    markedFirst rank left hleft permutation ≠
        markedFirst rank right hright permutation ↔
      markedFirst rank (left ∪ right) (hleft.mono Finset.subset_union_left)
          permutation ∈ (left \ right) ∪ (right \ left) := by
  let hunion : (left ∪ right).Nonempty :=
    hleft.mono Finset.subset_union_left
  let a := markedFirst rank (left ∪ right) hunion permutation
  have ha : a ∈ left ∪ right :=
    markedFirst_mem rank (left ∪ right) hunion permutation
  have hagree := markedFirst_eq_iff_union_first_mem_inter
    rank left right hleft hright permutation
  change markedFirst rank left hleft permutation ≠
      markedFirst rank right hright permutation ↔
    a ∈ (left \ right) ∪ (right \ left)
  constructor
  · intro hne
    have hninter : a ∉ left ∩ right := by
      intro hinter
      exact hne (hagree.mpr hinter)
    rcases Finset.mem_union.mp ha with hla | hra
    · apply Finset.mem_union_left
      exact Finset.mem_sdiff.mpr
        ⟨hla, fun hright' => hninter (Finset.mem_inter.mpr ⟨hla, hright'⟩)⟩
    · apply Finset.mem_union_right
      exact Finset.mem_sdiff.mpr
        ⟨hra, fun hleft' => hninter (Finset.mem_inter.mpr ⟨hleft', hra⟩)⟩
  · intro hdiff heq
    have hinter : a ∈ left ∩ right := hagree.mp heq
    rcases Finset.mem_union.mp hdiff with hdiff | hdiff
    · exact (Finset.mem_sdiff.mp hdiff).2 (Finset.mem_inter.mp hinter).2
    · exact (Finset.mem_sdiff.mp hdiff).2 (Finset.mem_inter.mp hinter).1
end
end QuantumParallelRepetition.ClassicalSampling

namespace QuantumParallelRepetition.ClassicalSampling
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
set_option autoImplicit true
variable {α : Type*} [Fintype α] [DecidableEq α]
theorem sharedPermutation_disagreement_card_mul
    (rank : α ≃ Fin (Fintype.card α))
    (left right : Finset α)
    (hleft : left.Nonempty) (hright : right.Nonempty) :
    (Finset.univ.filter fun permutation : Equiv.Perm α =>
        markedFirst rank left hleft permutation ≠
          markedFirst rank right hright permutation).card *
        (left ∪ right).card =
      ((left \ right) ∪ (right \ left)).card *
        Fintype.card (Equiv.Perm α) := by
  classical
  let hunion : (left ∪ right).Nonempty :=
    hleft.mono Finset.subset_union_left
  have hsubset : (left \ right) ∪ (right \ left) ⊆ left ∪ right := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact Finset.mem_union_left right (Finset.mem_sdiff.mp ha).1
    · exact Finset.mem_union_right left (Finset.mem_sdiff.mp ha).1
  have hfilter :
      (Finset.univ.filter fun permutation : Equiv.Perm α =>
        markedFirst rank left hleft permutation ≠
          markedFirst rank right hright permutation) =
      (Finset.univ.filter fun permutation : Equiv.Perm α =>
        markedFirst rank (left ∪ right) hunion permutation ∈
          (left \ right) ∪ (right \ left)) := by
    ext permutation
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact markedFirst_ne_iff_union_first_mem_symmDiff
      rank left right hleft hright permutation
  rw [hfilter]
  exact markedFirst_event_card_mul rank (left ∪ right) hunion
    ((left \ right) ∪ (right \ left)) hsubset
end
end QuantumParallelRepetition.ClassicalSampling

namespace QuantumParallelRepetition.ClassicalSampling
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
set_option autoImplicit true
variable {α : Type*} [Fintype α] [DecidableEq α]
theorem sharedPermutation_disagreement_probability
    (rank : α ≃ Fin (Fintype.card α))
    (left right : Finset α)
    (hleft : left.Nonempty) (hright : right.Nonempty) :
    uniformPermutationProbability
      (fun permutation : Equiv.Perm α =>
        markedFirst rank left hleft permutation ≠
          markedFirst rank right hright permutation) =
      (((left \ right) ∪ (right \ left)).card : ℝ) /
        (left ∪ right).card := by
  classical
  have hpermutation : 0 < (Fintype.card (Equiv.Perm α) : ℝ) := by
    exact_mod_cast
      (Fintype.card_pos_iff.mpr ⟨Equiv.refl α⟩ :
        0 < Fintype.card (Equiv.Perm α))
  have hunion : 0 < ((left ∪ right).card : ℝ) := by
    exact_mod_cast
      (Finset.card_pos.mpr
        (hleft.mono Finset.subset_union_left) :
        0 < (left ∪ right).card)
  unfold uniformPermutationProbability
  apply (div_eq_div_iff hpermutation.ne' hunion.ne').mpr
  exact_mod_cast
    sharedPermutation_disagreement_card_mul rank left right hleft hright
end
end QuantumParallelRepetition.ClassicalSampling

namespace QuantumParallelRepetition.ClassicalSampling
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
set_option autoImplicit true
variable {α : Type*} [Fintype α] [DecidableEq α]
theorem sharedPermutation_disagreement_probability_le
    (rank : α ≃ Fin (Fintype.card α))
    (left right : Finset α)
    (hleft : left.Nonempty) (hright : right.Nonempty) :
    uniformPermutationProbability
      (fun permutation : Equiv.Perm α =>
        markedFirst rank left hleft permutation ≠
          markedFirst rank right hright permutation) ≤
      (((left \ right) ∪ (right \ left)).card : ℝ) / left.card := by
  rw [sharedPermutation_disagreement_probability
    rank left right hleft hright]
  apply div_le_div_of_nonneg_left
  · positivity
  · exact_mod_cast (Finset.card_pos.mpr hleft : 0 < left.card)
  · exact_mod_cast (Finset.card_le_card Finset.subset_union_left :
      left.card ≤ (left ∪ right).card)
end
end QuantumParallelRepetition.ClassicalSampling

namespace QuantumParallelRepetition.ClassicalSampling
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
set_option autoImplicit true
variable {α : Type*} [Fintype α] [DecidableEq α]
theorem sharedPermutation_disagreement_probability_le_two_mul_tv
    (rank : α ≃ Fin (Fintype.card α))
    (left right : Finset α)
    (hleft : left.Nonempty) (hright : right.Nonempty)
    (_equal_card : left.card = right.card) :
    uniformPermutationProbability
      (fun permutation : Equiv.Perm α =>
        markedFirst rank left hleft permutation ≠
          markedFirst rank right hright permutation) ≤
      2 * markedTotalVariation left right := by
  calc
    uniformPermutationProbability
        (fun permutation : Equiv.Perm α =>
          markedFirst rank left hleft permutation ≠
            markedFirst rank right hright permutation) ≤
        (((left \ right) ∪ (right \ left)).card : ℝ) / left.card :=
      sharedPermutation_disagreement_probability_le
        rank left right hleft hright
    _ = 2 * markedTotalVariation left right := by
      unfold markedTotalVariation
      have hcard : (left.card : ℝ) ≠ 0 := by
        exact_mod_cast (Finset.card_ne_zero.mpr hleft)
      field_simp
end
end QuantumParallelRepetition.ClassicalSampling

namespace QuantumParallelRepetition.ClassicalSampling
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
set_option autoImplicit true
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {β : Type*} [Fintype β] [DecidableEq β]
theorem rationalMarked_fiber_card
    (denominator : ℕ) (numerator : β → ℕ) (letter : β) :
    ((rationalMarked denominator numerator).filter
      fun point => point.1 = letter).card =
        min denominator (numerator letter) := by
  classical
  calc
    ((rationalMarked denominator numerator).filter
      fun point => point.1 = letter).card =
        (Finset.univ.filter fun copy : Fin denominator =>
          copy.val < numerator letter).card := by
      refine Finset.card_bij'
        (fun point _ => point.2)
        (fun copy _ => (letter, copy))
        ?_ ?_ ?_ ?_
      · intro point hpoint
        have hpoint' :
            point.2.val < numerator point.1 ∧ point.1 = letter := by
          simpa [rationalMarked] using hpoint
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, by simpa [hpoint'.2] using hpoint'.1⟩
      · intro copy hcopy
        have hcopy' : copy.val < numerator letter :=
          (Finset.mem_filter.mp hcopy).2
        simp [rationalMarked, hcopy']
      · intro point hpoint
        have hletter : point.1 = letter :=
          (Finset.mem_filter.mp hpoint).2
        apply Prod.ext
        · exact hletter.symm
        · rfl
      · intro copy _
        rfl
    _ = min denominator (numerator letter) := by
      simpa using
        (Fin.card_filter_val_lt (n := denominator)
          (m := numerator letter))
end
end QuantumParallelRepetition.ClassicalSampling

namespace QuantumParallelRepetition.ClassicalSampling
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
set_option autoImplicit true
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {β : Type*} [Fintype β] [DecidableEq β]
omit [DecidableEq β] in

theorem rationalNumerator_le_denominator
    (denominator : ℕ) (numerator : β → ℕ)
    (normalized : (∑ letter, numerator letter) = denominator)
    (letter : β) : numerator letter ≤ denominator := by
  rw [← normalized]
  exact Finset.single_le_sum
    (fun a _ => Nat.zero_le (numerator a)) (Finset.mem_univ letter)
end
end QuantumParallelRepetition.ClassicalSampling

namespace QuantumParallelRepetition.ClassicalSampling
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
set_option autoImplicit true
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {β : Type*} [Fintype β] [DecidableEq β]
theorem rationalMarked_card
    (denominator : ℕ) (numerator : β → ℕ)
    (normalized : (∑ letter, numerator letter) = denominator) :
    (rationalMarked denominator numerator).card = denominator := by
  classical
  calc
    (rationalMarked denominator numerator).card =
        ∑ letter : β,
          ((rationalMarked denominator numerator).filter
            fun point => point.1 = letter).card := by
      simpa using
        (Finset.card_eq_sum_card_fiberwise
          (f := fun point : β × Fin denominator => point.1)
          (s := rationalMarked denominator numerator)
          (t := (Finset.univ : Finset β))
          (fun _ _ => Finset.mem_univ _))
    _ = ∑ letter : β, numerator letter := by
      apply Finset.sum_congr rfl
      intro letter _
      rw [rationalMarked_fiber_card]
      exact min_eq_right
        (rationalNumerator_le_denominator denominator numerator normalized letter)
    _ = denominator := normalized
end
end QuantumParallelRepetition.ClassicalSampling

namespace QuantumParallelRepetition.ClassicalInformation
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalSampling
set_option autoImplicit true
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem uniformPermutationProbability_mono
    {α : Type*} [Fintype α] [DecidableEq α]
    (small large : Equiv.Perm α → Prop)
    (hinclusion : ∀ permutation, small permutation → large permutation) :
    uniformPermutationProbability small ≤
      uniformPermutationProbability large := by
  classical
  unfold uniformPermutationProbability
  apply div_le_div_of_nonneg_right
  · exact_mod_cast Finset.card_le_card (show
      (Finset.univ.filter fun permutation : Equiv.Perm α =>
        small permutation) ⊆
      (Finset.univ.filter fun permutation : Equiv.Perm α =>
        large permutation) from by
        intro permutation hpermutation
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hinclusion permutation
            (Finset.mem_filter.mp hpermutation).2⟩)
  · exact_mod_cast (Nat.zero_le (Fintype.card (Equiv.Perm α)))
end
end QuantumParallelRepetition.ClassicalInformation

namespace QuantumParallelRepetition.ClassicalInformation
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalSampling
set_option autoImplicit true
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem rationalPermutationOutput_disagreement_le_two_mul_tv
    (denominator : ℕ) (left right : ι → ℕ)
    (hleft : (∑ i, left i) = denominator)
    (hright : (∑ i, right i) = denominator)
    (nonempty_left : (rationalMarked denominator left).Nonempty)
    (nonempty_right : (rationalMarked denominator right).Nonempty) :
    uniformPermutationProbability
        (fun permutation : Equiv.Perm (ι × Fin denominator) =>
          rationalPermutationOutput denominator left
            nonempty_left permutation ≠
          rationalPermutationOutput denominator right
            nonempty_right permutation) ≤
      2 * markedTotalVariation
        (rationalMarked denominator left)
        (rationalMarked denominator right) := by
  let rank := Fintype.equivFin (ι × Fin denominator)
  calc
    uniformPermutationProbability
        (fun permutation : Equiv.Perm (ι × Fin denominator) =>
          rationalPermutationOutput denominator left
            nonempty_left permutation ≠
          rationalPermutationOutput denominator right
            nonempty_right permutation) ≤
      uniformPermutationProbability
        (fun permutation : Equiv.Perm (ι × Fin denominator) =>
          markedFirst rank (rationalMarked denominator left)
            nonempty_left permutation ≠
          markedFirst rank (rationalMarked denominator right)
            nonempty_right permutation) := by
        apply uniformPermutationProbability_mono
        intro permutation hdifferent hequal
        apply hdifferent
        exact congrArg Prod.fst hequal
    _ ≤ 2 * markedTotalVariation
        (rationalMarked denominator left)
        (rationalMarked denominator right) := by
      apply sharedPermutation_disagreement_probability_le_two_mul_tv
      calc
        (rationalMarked denominator left).card = denominator :=
          rationalMarked_card denominator left hleft
        _ = (rationalMarked denominator right).card :=
          (rationalMarked_card denominator right hright).symm
end
end QuantumParallelRepetition.ClassicalInformation

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace QuantumParallelRepetition.ClassicalInformation
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalSampling
set_option autoImplicit true
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem _root_.solution
    (denominator : ℕ) (positive : 0 < denominator)
    (left right : ι → ℕ)
    (hleft : (∑ i, left i) = denominator)
    (hright : (∑ i, right i) = denominator)
    (nonempty_left : (rationalMarked denominator left).Nonempty)
    (nonempty_right : (rationalMarked denominator right).Nonempty) :
    uniformPermutationProbability
        (fun permutation : Equiv.Perm (ι × Fin denominator) =>
          rationalPermutationOutput denominator left
            nonempty_left permutation ≠
          rationalPermutationOutput denominator right
            nonempty_right permutation) ≤
      2 * finiteTotalVariation
        (fun i => (left i : ℝ) / denominator)
        (fun i => (right i : ℝ) / denominator) := by
  calc
    uniformPermutationProbability
        (fun permutation : Equiv.Perm (ι × Fin denominator) =>
          rationalPermutationOutput denominator left
            nonempty_left permutation ≠
          rationalPermutationOutput denominator right
            nonempty_right permutation) ≤
      2 * markedTotalVariation
        (rationalMarked denominator left)
        (rationalMarked denominator right) :=
          rationalPermutationOutput_disagreement_le_two_mul_tv
            denominator left right hleft hright
            nonempty_left nonempty_right
    _ = 2 * finiteTotalVariation
        (fun i => (left i : ℝ) / denominator)
        (fun i => (right i : ℝ) / denominator) := by
      rw [rationalMarked_markedTotalVariation_eq
        denominator positive left right hleft hright]
end QuantumParallelRepetition.ClassicalInformation

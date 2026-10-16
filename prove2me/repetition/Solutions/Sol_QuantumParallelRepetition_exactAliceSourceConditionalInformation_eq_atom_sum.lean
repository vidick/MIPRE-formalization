/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Repetition/TenProofs/QuantumParallelRepetition/Part06.lean (solution of QuantumParallelRepetition.exactAliceSourceConditionalInformation_eq_atom_sum);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
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
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Opposite
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Opposite
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Group.Subsemigroup.Defs
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.Group.Units.Equiv
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
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
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
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Algebra.Order.SuccPred
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
import Mathlib.Algebra.Ring.Parity
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
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
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
import Mathlib.Analysis.MeanInequalitiesPow
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
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
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
import Mathlib.Data.Finset.Attach
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
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Embedding
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
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.SuccPred
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
import Mathlib.Logic.Basic
import Mathlib.Logic.Embedding.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Option
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Sum
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Function.Defs
import Mathlib.Logic.IsEmpty.Defs
import Mathlib.Logic.Unique
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
import Mathlib.Order.ConditionallyCompletePartialOrder.Defs
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
import Mathlib.Order.Nat
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
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.Hom.Esakia
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Separation.GDelta
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.Defs
import Mathlib.Topology.UniformSpace.Matrix
import Mathlib.Topology.UniformSpace.Pi
import Mathlib.Topology.UniformSpace.Real
import Definitions.Def_MIPRE_Background_Repetition_TenProofs_QuantumParallelRepetition_Part01
import Definitions.Def_MIPRE_Background_Repetition_TenProofs_QuantumParallelRepetition_Part02
import Definitions.Def_MIPRE_Background_Repetition_TenProofs_QuantumParallelRepetition_Part03
import Definitions.Def_MIPRE_Background_Repetition_TenProofs_QuantumParallelRepetition_Part04
import Definitions.Def_MIPRE_Background_Repetition_TenProofs_QuantumParallelRepetition_Part05
import Definitions.Def_MIPRE_Background_Repetition_TenProofs_QuantumParallelRepetition_Part06
import Theorems.Thm_QuantumParallelRepetition_exactAliceInformationReference_firstMarginal
import Theorems.Thm_QuantumParallelRepetition_exactLocallySampleableLaw_absolute_continuous_JA
import Theorems.Thm_QuantumParallelRepetition_exactLocallySampleableLaw_nonneg
import Theorems.Thm_QuantumParallelRepetition_finiteConditionalHistoryRelativeEntropy_eq
import Theorems.Thm_QuantumParallelRepetition_finiteNestedNextInformation_eq_atom_sum

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace QuantumParallelRepetition.Game
section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix
set_option autoImplicit true
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem marginalX_nonneg (G : Game X Y A B) (x : X) :
    0 ≤ G.marginalX x := by
  unfold marginalX
  exact Finset.sum_nonneg fun y _ => G.weight_nonneg x y
end
end QuantumParallelRepetition.Game

attribute [instance] QuantumParallelRepetition.Strategy.alice_fintype QuantumParallelRepetition.Strategy.bob_fintype QuantumParallelRepetition.Strategy.alice_decidableEq QuantumParallelRepetition.Strategy.bob_decidableEq

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace QuantumParallelRepetition.Game
section
open scoped BigOperators Kronecker
set_option autoImplicit true
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem questionWeight_le_marginalX
    (G : Game X Y A B) (x : X) (y : Y) :
    G.questionWeight x y ≤ G.marginalX x := by
  unfold marginalX
  exact Finset.single_le_sum
    (fun y _ => G.weight_nonneg x y)
    (Finset.mem_univ y)
end
end QuantumParallelRepetition.Game

namespace QuantumParallelRepetition.Game
section
open scoped BigOperators Kronecker
set_option autoImplicit true
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem marginalX_mul_conditionalYGivenX
    (G : Game X Y A B) (x : X) (y : Y) :
    G.marginalX x * G.conditionalYGivenX x y =
      G.questionWeight x y := by
  unfold conditionalYGivenX
  by_cases hx : G.marginalX x = 0
  · have hzero : G.questionWeight x y = 0 := by
      have hle := G.questionWeight_le_marginalX x y
      have hnonneg := G.weight_nonneg x y
      rw [hx] at hle
      linarith
    simp [hx, hzero]
  · field_simp
end
end QuantumParallelRepetition.Game

namespace QuantumParallelRepetition.Game
section
open scoped BigOperators Kronecker
set_option autoImplicit true
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem conditionalYGivenX_sum
    (G : Game X Y A B) (x : X)
    (hx : 0 < G.marginalX x) :
    (∑ y : Y, G.conditionalYGivenX x y) = 1 := by
  unfold conditionalYGivenX
  rw [← Finset.sum_div]
  change G.marginalX x / G.marginalX x = 1
  exact div_self hx.ne'
end
end QuantumParallelRepetition.Game

namespace QuantumParallelRepetition.ClassicalInformation
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalSampling
set_option autoImplicit true
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ]
omit [Fintype ι] [DecidableEq ι] in

theorem jointFirstMarginal_absolute_continuity
    (p q : ι × κ → ℝ)
    (hq : ∀ point, 0 ≤ q point)
    (absolute_continuity : ∀ point, q point = 0 → p point = 0)
    (i : ι) :
    jointFirstMarginal q i = 0 → jointFirstMarginal p i = 0 := by
  intro hzero
  change (∑ j : κ, q (i, j)) = 0 at hzero
  have hcoordinates : ∀ j : κ, q (i, j) = 0 := by
    intro j
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => hq (i, j))).mp hzero j (Finset.mem_univ j)
  change (∑ j : κ, p (i, j)) = 0
  exact Finset.sum_eq_zero
    (fun j _ => absolute_continuity (i, j) (hcoordinates j))
end
end QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
open QuantumParallelRepetition.ClassicalSampling
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem exactAliceLocalMass_nonneg
    {n : ℕ} (D : Finset (Fin n))
    (Q : ExactLocallySampleableTuple X Y A B D → ℝ)
    (nonnegative : ∀ t, 0 ≤ Q t)
    (i : SourceRemainingCoordinate D) (x : X) :
    0 ≤ exactAliceLocalMass D Q i x := by
  unfold exactAliceLocalMass
  exact Finset.sum_nonneg
    (fun r _ => Finset.sum_nonneg (fun y _ => nonnegative (i, x, y, r)))
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
open QuantumParallelRepetition.ClassicalSampling
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem exactAliceLocalConditional_nonneg
    {n : ℕ} (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D)
    (Q : ExactLocallySampleableTuple X Y A B D → ℝ)
    (nonnegative : ∀ t, 0 ≤ Q t)
    (i : SourceRemainingCoordinate D) (x : X)
    (r : ExactHistoryFlag X Y A B D) :
    0 ≤ exactAliceLocalConditional D base Q i x r := by
  unfold exactAliceLocalConditional
  split_ifs with hmass hbase
  · exact zero_le_one
  · exact le_rfl
  · exact div_nonneg
      (Finset.sum_nonneg (fun y _ => nonnegative (i, x, y, r)))
      (exactAliceLocalMass_nonneg D Q nonnegative i x)
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
open QuantumParallelRepetition.ClassicalSampling
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem exactLocallySampleableJA_nonneg
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (t : ExactLocallySampleableTuple X Y A B D) :
    0 ≤ exactLocallySampleableJA G n S D base t := by
  unfold exactLocallySampleableJA
  exact div_nonneg
    (mul_nonneg (G.weight_nonneg t.2.1 t.2.2.1)
      (exactAliceLocalConditional_nonneg D base
        (exactLocallySampleableLaw G n S D)
        (exactLocallySampleableLaw_nonneg G n S D positive)
        t.1 t.2.1 t.2.2.2))
    (Nat.cast_nonneg _)
end
end QuantumParallelRepetition

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
theorem finiteSupportedConditionalHistoryReferenceFirstMarginal_eq
    {I R V : Type*} [Fintype I] [Fintype R] [Fintype V]
    (p q : I × (R × V) → ℝ)
    (q_nonnegative : ∀ point, 0 ≤ q point)
    (absolute_continuity : ∀ point, q point = 0 → p point = 0)
    (reference : I → R → V → ℝ)
    (reference_normalized : ∀ i,
      jointFirstMarginal p i ≠ 0 →
        ∀ r, (∑ v : V, reference i r v) = 1)
    (factor : ∀ i,
      jointFirstMarginal p i ≠ 0 →
        ∀ r v,
          q (i, (r, v)) =
            jointFirstMarginal q i *
              jointFirstMarginal (jointConditional p i) r *
              reference i r v)
    (i : I) (supported : jointFirstMarginal p i ≠ 0) :
    jointFirstMarginal (jointConditional q i) =
      jointFirstMarginal (jointConditional p i) := by
  have hqi : jointFirstMarginal q i ≠ 0 := by
    intro hz
    exact supported
      (jointFirstMarginal_absolute_continuity
        p q q_nonnegative absolute_continuity i hz)
  funext r
  change
    (∑ v : V,
      q (i, (r, v)) / jointFirstMarginal q i) =
      jointFirstMarginal (jointConditional p i) r
  simp_rw [factor i supported r]
  calc
    (∑ v : V,
      (jointFirstMarginal q i *
        jointFirstMarginal (jointConditional p i) r *
        reference i r v) / jointFirstMarginal q i) =
      ∑ v : V,
        jointFirstMarginal (jointConditional p i) r *
          reference i r v := by
        apply Finset.sum_congr rfl
        intro v _
        field_simp [hqi]
    _ = jointFirstMarginal (jointConditional p i) r := by
      rw [← Finset.mul_sum, reference_normalized i supported r]
      ring
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
theorem finiteSupportedConditionalHistoryReferenceConditional_eq
    {I R V : Type*} [Fintype I] [Fintype R] [Fintype V]
    (p q : I × (R × V) → ℝ)
    (q_nonnegative : ∀ point, 0 ≤ q point)
    (absolute_continuity : ∀ point, q point = 0 → p point = 0)
    (reference : I → R → V → ℝ)
    (reference_normalized : ∀ i,
      jointFirstMarginal p i ≠ 0 →
        ∀ r, (∑ v : V, reference i r v) = 1)
    (factor : ∀ i,
      jointFirstMarginal p i ≠ 0 →
        ∀ r v,
          q (i, (r, v)) =
            jointFirstMarginal q i *
              jointFirstMarginal (jointConditional p i) r *
              reference i r v)
    (i : I) (r : R)
    (supported : jointFirstMarginal p i ≠ 0)
    (history_supported :
      jointFirstMarginal (jointConditional p i) r ≠ 0) :
    jointConditional (jointConditional q i) r = reference i r := by
  have hqi : jointFirstMarginal q i ≠ 0 := by
    intro hz
    exact supported
      (jointFirstMarginal_absolute_continuity
        p q q_nonnegative absolute_continuity i hz)
  have hhistory :=
    finiteSupportedConditionalHistoryReferenceFirstMarginal_eq
      p q q_nonnegative absolute_continuity
      reference reference_normalized factor i supported
  funext v
  change
    (q (i, (r, v)) / jointFirstMarginal q i) /
        jointFirstMarginal (jointConditional q i) r =
      reference i r v
  rw [factor i supported r v, congrFun hhistory r]
  field_simp [hqi, history_supported]
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
theorem finiteSupportedConditionalHistoryRelativeEntropy_eq_of_factor
    {I R V : Type*} [Fintype I] [Fintype R] [Fintype V]
    (p q : I × (R × V) → ℝ)
    (p_nonnegative : ∀ point, 0 ≤ p point)
    (q_nonnegative : ∀ point, 0 ≤ q point)
    (absolute_continuity : ∀ point, q point = 0 → p point = 0)
    (reference : I → R → V → ℝ)
    (reference_normalized : ∀ i,
      jointFirstMarginal p i ≠ 0 →
        ∀ r, (∑ v : V, reference i r v) = 1)
    (factor : ∀ i,
      jointFirstMarginal p i ≠ 0 →
        ∀ r v,
          q (i, (r, v)) =
            jointFirstMarginal q i *
              jointFirstMarginal (jointConditional p i) r *
              reference i r v) :
    (∑ i : I,
      jointFirstMarginal p i *
        finiteRelativeEntropy
          (jointConditional p i)
          (jointConditional q i)) =
      ∑ i : I,
        jointFirstMarginal p i *
          (∑ r : R,
            jointFirstMarginal (jointConditional p i) r *
              finiteRelativeEntropy
                (jointConditional (jointConditional p i) r)
                (reference i r)) := by
  apply finiteConditionalHistoryRelativeEntropy_eq
    p q p_nonnegative q_nonnegative absolute_continuity reference
  · intro i hi
    exact
      (finiteSupportedConditionalHistoryReferenceFirstMarginal_eq
        p q q_nonnegative absolute_continuity
        reference reference_normalized factor i hi).symm
  · intro i r hi hr
    exact
      finiteSupportedConditionalHistoryReferenceConditional_eq
        p q q_nonnegative absolute_continuity
        reference reference_normalized factor i r hi hr
end
end QuantumParallelRepetition

attribute [local instance] Classical.propDecidable

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option maxRecDepth 2048
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem exactAliceInformationPosterior_firstMarginal_eq_localMass
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (i : SourceRemainingCoordinate D) (x : X) :
    jointFirstMarginal
        (exactAliceInformationPosterior G n S D) (i, x) =
      exactAliceLocalMass D
        (exactLocallySampleableLaw G n S D) i x := by
  unfold jointFirstMarginal
  rw [Fintype.sum_prod_type]
  rfl
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option maxRecDepth 2048
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem exactAliceSupportedQuestion_marginal_pos
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (i : SourceRemainingCoordinate D) (x : X)
    (supported : jointFirstMarginal
      (exactAliceInformationPosterior G n S D) (i, x) ≠ 0) :
    0 < G.marginalX x := by
  let p := exactAliceInformationPosterior G n S D
  let q := exactAliceInformationReference G n S D base
  have hqnonnegative : ∀ t, 0 ≤ q t := by
    intro t
    exact exactLocallySampleableJA_nonneg
      G n S D positive base
      ((exactAliceInformationEquiv
        (X := X) (Y := Y) (A := A) (B := B) D).symm t)
  have hac : ∀ t, q t = 0 → p t = 0 := by
    intro t hz
    exact exactLocallySampleableLaw_absolute_continuous_JA
      G n S D remaining positive base
      ((exactAliceInformationEquiv
        (X := X) (Y := Y) (A := A) (B := B) D).symm t) hz
  have hqmass : jointFirstMarginal q (i, x) ≠ 0 := by
    intro hz
    exact supported
      (jointFirstMarginal_absolute_continuity
        p q hqnonnegative hac (i, x) hz)
  rw [exactAliceInformationReference_firstMarginal
    G n S D base i x] at hqmass
  have hx : G.marginalX x ≠ 0 := by
    intro hz
    apply hqmass
    change G.marginalX x /
      (Fintype.card (SourceRemainingCoordinate D) : ℝ) = 0
    rw [hz]
    simp
  exact lt_of_le_of_ne (G.marginalX_nonneg x) (Ne.symm hx)
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option maxRecDepth 2048
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem exactAliceInformationPosterior_historyMarginal
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D)
    (i : SourceRemainingCoordinate D) (x : X)
    (supported : jointFirstMarginal
      (exactAliceInformationPosterior G n S D) (i, x) ≠ 0)
    (r : ExactHistoryFlag X Y A B D) :
    jointFirstMarginal
        (jointConditional
          (exactAliceInformationPosterior G n S D) (i, x)) r =
      exactAliceLocalConditional D base
        (exactLocallySampleableLaw G n S D) i x r := by
  have hmass :=
    exactAliceInformationPosterior_firstMarginal_eq_localMass
      G n S D i x
  have hlocal :
      exactAliceLocalMass D
        (exactLocallySampleableLaw G n S D) i x ≠ 0 := by
    rw [← hmass]
    exact supported
  unfold jointFirstMarginal jointConditional
  change
    (∑ y : Y,
      exactLocallySampleableLaw G n S D (i, x, y, r) /
        jointFirstMarginal
          (exactAliceInformationPosterior G n S D) (i, x)) =
      exactAliceLocalConditional D base
        (exactLocallySampleableLaw G n S D) i x r
  rw [← Finset.sum_div, hmass]
  simp [exactAliceLocalConditional, hlocal]
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option maxRecDepth 2048
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem exactAliceInformationReference_supported_factor
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D)
    (i : SourceRemainingCoordinate D) (x : X)
    (supported : jointFirstMarginal
      (exactAliceInformationPosterior G n S D) (i, x) ≠ 0)
    (r : ExactHistoryFlag X Y A B D) (y : Y) :
    exactAliceInformationReference G n S D base
        ((i, x), (r, y)) =
      jointFirstMarginal
          (exactAliceInformationReference G n S D base) (i, x) *
        jointFirstMarginal
          (jointConditional
            (exactAliceInformationPosterior G n S D) (i, x)) r *
        G.conditionalYGivenX x y := by
  rw [exactAliceInformationReference_firstMarginal
    G n S D base i x,
    exactAliceInformationPosterior_historyMarginal
      G n S D base i x supported r]
  change
    G.questionWeight x y *
        exactAliceLocalConditional D base
          (exactLocallySampleableLaw G n S D) i x r /
          (Fintype.card (SourceRemainingCoordinate D) : ℝ) =
      (G.marginalX x /
        (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
        exactAliceLocalConditional D base
          (exactLocallySampleableLaw G n S D) i x r *
        G.conditionalYGivenX x y
  rw [← G.marginalX_mul_conditionalYGivenX x y]
  ring
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option maxRecDepth 2048
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem exactAliceSourceConditionalInformation_eq_question
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D) :
    exactAliceSourceConditionalInformation G n S D base =
      ∑ ix : SourceRemainingCoordinate D × X,
        jointFirstMarginal
          (exactAliceInformationPosterior G n S D) ix *
          (∑ r : ExactHistoryFlag X Y A B D,
            jointFirstMarginal
                (jointConditional
                  (exactAliceInformationPosterior G n S D) ix) r *
              finiteRelativeEntropy
                (jointConditional
                  (jointConditional
                    (exactAliceInformationPosterior G n S D) ix) r)
                (G.conditionalYGivenX ix.2)) := by
  let p := exactAliceInformationPosterior G n S D
  let q := exactAliceInformationReference G n S D base
  have hp : ∀ t, 0 ≤ p t := by
    intro t
    exact exactLocallySampleableLaw_nonneg
      G n S D positive
      ((exactAliceInformationEquiv
        (X := X) (Y := Y) (A := A) (B := B) D).symm t)
  have hq : ∀ t, 0 ≤ q t := by
    intro t
    exact exactLocallySampleableJA_nonneg
      G n S D positive base
      ((exactAliceInformationEquiv
        (X := X) (Y := Y) (A := A) (B := B) D).symm t)
  have hac : ∀ t, q t = 0 → p t = 0 := by
    intro t hz
    exact exactLocallySampleableLaw_absolute_continuous_JA
      G n S D remaining positive base
      ((exactAliceInformationEquiv
        (X := X) (Y := Y) (A := A) (B := B) D).symm t) hz
  unfold exactAliceSourceConditionalInformation
  apply finiteSupportedConditionalHistoryRelativeEntropy_eq_of_factor
    p q hp hq hac
    (fun ix _ => G.conditionalYGivenX ix.2)
  · intro ix hix r
    exact G.conditionalYGivenX_sum ix.2
      (exactAliceSupportedQuestion_marginal_pos
        G n S D remaining positive base ix.1 ix.2 hix)
  · intro ix hix r y
    exact exactAliceInformationReference_supported_factor
      G n S D base ix.1 ix.2 hix r y
end
end QuantumParallelRepetition

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
set_option maxRecDepth 2048
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem _root_.solution
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D) :
    exactAliceSourceConditionalInformation G n S D base =
      ∑ point : (SourceRemainingCoordinate D × X) ×
          (ExactHistoryFlag X Y A B D × Y),
        exactAliceInformationPosterior G n S D point *
          finiteRelativeEntropy
            (jointConditional
              (fun atom :
                ((SourceRemainingCoordinate D × X) ×
                    ExactHistoryFlag X Y A B D) × Y =>
                exactAliceInformationPosterior G n S D
                  (atom.1.1, (atom.1.2, atom.2)))
              (point.1, point.2.1))
            (G.conditionalYGivenX point.1.2) := by
  have hnonnegative :
      ∀ point,
        0 ≤ exactAliceInformationPosterior
          G n S D point := by
    intro point
    exact exactLocallySampleableLaw_nonneg
      G n S D positive
      ((exactAliceInformationEquiv
        (X := X) (Y := Y) (A := A) (B := B) D).symm point)
  calc
    exactAliceSourceConditionalInformation G n S D base =
      ∑ index : SourceRemainingCoordinate D × X,
        jointFirstMarginal
          (exactAliceInformationPosterior G n S D) index *
          (∑ history : ExactHistoryFlag X Y A B D,
            jointFirstMarginal
                (jointConditional
                  (exactAliceInformationPosterior G n S D)
                  index) history *
              finiteRelativeEntropy
                (jointConditional
                  (jointConditional
                    (exactAliceInformationPosterior G n S D)
                    index) history)
                (G.conditionalYGivenX index.2)) :=
      exactAliceSourceConditionalInformation_eq_question
        G n S D remaining positive base
    _ = _ :=
      finiteNestedNextInformation_eq_atom_sum
        (exactAliceInformationPosterior G n S D)
        hnonnegative
        (fun index : SourceRemainingCoordinate D × X =>
          G.conditionalYGivenX index.2)
end QuantumParallelRepetition

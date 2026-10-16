/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Repetition/TenProofs/QuantumParallelRepetition/Part06.lean (solution of QuantumParallelRepetition.exact_source_equation_twenty_three_of_conditioned_reverse_prefix);
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
import Theorems.Thm_QuantumParallelRepetition_exactAliceInformationPosterior_firstMarginal
import Theorems.Thm_QuantumParallelRepetition_exactAliceInformationReference_firstMarginal
import Theorems.Thm_QuantumParallelRepetition_exactBobInformationPosterior_firstMarginal
import Theorems.Thm_QuantumParallelRepetition_exactBobInformationReference_firstMarginal
import Theorems.Thm_QuantumParallelRepetition_exact_source_equation_twenty_four_alice
import Theorems.Thm_QuantumParallelRepetition_exact_source_equation_twenty_four_bob
import Theorems.Thm_QuantumParallelRepetition_repeatedAliceCoordinateInformation_sum_le
import Theorems.Thm_QuantumParallelRepetition_repeatedBobCoordinateInformation_sum_le
import Theorems.Thm_QuantumParallelRepetition_reversePartition_relativeEntropy_budget
import Theorems.Thm_QuantumParallelRepetition_reweightedSeed_source_equation_twenty_six

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

namespace QuantumParallelRepetition.Game
section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix
set_option autoImplicit true
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem marginalY_nonneg (G : Game X Y A B) (y : Y) :
    0 ≤ G.marginalY y := by
  unfold marginalY
  exact Finset.sum_nonneg fun x _ => G.weight_nonneg x y
end
end QuantumParallelRepetition.Game

attribute [instance] QuantumParallelRepetition.Strategy.alice_fintype QuantumParallelRepetition.Strategy.bob_fintype QuantumParallelRepetition.Strategy.alice_decidableEq QuantumParallelRepetition.Strategy.bob_decidableEq

attribute [local instance] Classical.propDecidable

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

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
open QuantumParallelRepetition.ClassicalSampling
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem conditionedEventDistribution_nonneg
    {Ω : Type*} [Fintype Ω]
    (law : FiniteEventLaw Ω) (event : Finset Ω)
    (positive : 0 < law.eventMass event) (ω : Ω) :
    0 ≤ conditionedEventDistribution law event ω := by
  unfold conditionedEventDistribution
  split_ifs
  · exact div_nonneg (law.weight_nonneg ω) positive.le
  · exact le_rfl
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
theorem finiteRelativeEntropy_nonneg
    {Ω : Type*} [Fintype Ω]
    (p q : Ω → ℝ)
    (hp : ∀ ω, 0 ≤ p ω)
    (hq : ∀ ω, 0 ≤ q ω) :
    0 ≤ finiteRelativeEntropy p q := by
  unfold finiteRelativeEntropy
  apply Finset.sum_nonneg
  intro ω _
  exact mul_nonneg (hq ω)
    (InformationTheory.klFun_nonneg (div_nonneg (hp ω) (hq ω)))
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
theorem groupedMass_nonneg
    {Ω κ : Type*} [Fintype Ω] [Fintype κ] [DecidableEq κ]
    (f : Ω → κ) (p : Ω → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (a : κ) :
    0 ≤ groupedMass f p a := by
  unfold groupedMass
  exact Finset.sum_nonneg (fun ω _ => hp ω)
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
theorem groupedMass_comp
    {Ω κ θ : Type*} [Fintype Ω] [Fintype κ] [Fintype θ]
    [DecidableEq κ] [DecidableEq θ]
    (f : Ω → κ) (g : κ → θ) (p : Ω → ℝ) :
    groupedMass g (groupedMass f p) =
      groupedMass (g ∘ f) p := by
  funext a
  unfold groupedMass
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
    Function.comp_apply] using
    (Finset.sum_fiberwise_eq_sum_filter
      (Finset.univ : Finset Ω)
      (Finset.univ.filter fun b : κ => g b = a)
      f p)
end
end QuantumParallelRepetition

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
set_option autoImplicit true
theorem exactRemainingReverse_relativeEntropy_budget
    {n : ℕ} (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (increment :
      (s : Finset (SourceRemainingCoordinate D)) → Fin s.card → ℝ)
    {cost : ℝ} (nonnegative_cost : 0 ≤ cost)
    (budget : ∀ s : Finset (SourceRemainingCoordinate D),
      (∑ k : Fin s.card, increment s k) ≤ cost) :
    (∑ s : Finset (SourceRemainingCoordinate D),
      reversePartitionWeight s *
        ((∑ k : Fin s.card, increment s k) /
          (s.card : ℝ))) ≤
      2 * cost / ((Finset.univ \ D).card : ℝ) := by
  have hcard : 0 < Fintype.card (SourceRemainingCoordinate D) := by
    simpa using remaining
  simpa using
    (reversePartition_relativeEntropy_budget
      hcard increment nonnegative_cost budget)
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
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem exactGroupedMass_decidableEq_irrel
    {Ω κ : Type*} [Fintype Ω]
    (first second : DecidableEq κ)
    (projection : Ω → κ) (mass : Ω → ℝ) :
    @groupedMass Ω _ κ first projection mass =
      @groupedMass Ω _ κ second projection mass := by
  have h : first = second := Subsingleton.elim first second
  subst second
  rfl
end
end QuantumParallelRepetition

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
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem reweightedSeed_reverse_source_prefix_information_budget
    {K V : Type*} [Fintype K] [Fintype V]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (seedLaw : Finset (SourceRemainingCoordinate D) →
      FiniteEventLaw K)
    (Ω : Finset (SourceRemainingCoordinate D) → Type*)
    [∀ side, Fintype (Ω side)]
    (projection : ∀ side : Finset (SourceRemainingCoordinate D),
      K × ExactOutcome X Y A B n →
        Ω side × (Fin side.card → V))
    (default : V) :
    (∑ side : Finset (SourceRemainingCoordinate D),
      reversePartitionWeight side *
        ((∑ k : Fin side.card,
          reweightedSeedPrefixEntropyIncrement
            (seedLaw side) G n S D
            (projection side) default k) /
          (side.card : ℝ))) ≤
      2 * (postselectionLogCost G n S D +
        answerLogCost (A := A) (B := B) D) /
        ((Finset.univ \ D).card : ℝ) := by
  have nonnegative_cost :
      0 ≤ postselectionLogCost G n S D +
        answerLogCost (A := A) (B := B) D := by
    have hempty := reweightedSeed_source_equation_twenty_six
      (seedLaw ∅) G n S D positive (projection ∅) default
    simpa using hempty
  exact exactRemainingReverse_relativeEntropy_budget
    D remaining
    (fun side k => reweightedSeedPrefixEntropyIncrement
      (seedLaw side) G n S D (projection side) default k)
    nonnegative_cost
    (fun side => reweightedSeed_source_equation_twenty_six
      (seedLaw side) G n S D positive (projection side) default)
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
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
theorem finiteCoordinateMarginal_nonneg
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : (ι → V) → ℝ) (hp : ∀ x, 0 ≤ p x)
    (i : ι) (v : V) :
    0 ≤ finiteCoordinateMarginal p i v := by
  classical
  unfold finiteCoordinateMarginal
  exact groupedMass_nonneg (fun x : ι → V => x i) p hp v
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
theorem finiteCoordinateMarginal_groupedMass
    {Ω ι V : Type*} [Fintype Ω] [Fintype ι] [Fintype V]
    (projection : Ω → (ι → V)) (mass : Ω → ℝ)
    (i : ι) (v : V) :
    finiteCoordinateMarginal
        (groupedMass projection mass) i v =
      groupedMass (fun ω : Ω => projection ω i) mass v := by
  classical
  let eval : (ι → V) → V := fun x => x i
  have h := congrFun
    (groupedMass_comp projection eval mass) v
  unfold finiteCoordinateMarginal
  have hleft :
      groupedMass (fun x : ι → V => x i)
          (groupedMass projection mass) v =
        @groupedMass (ι → V) inferInstance V
          (fun a b => Classical.propDecidable (a = b))
          eval (groupedMass projection mass) v := by
    exact congrFun
      (exactGroupedMass_decidableEq_irrel _ _
        eval (groupedMass projection mass)) v
  have hright :
      @groupedMass Ω inferInstance V
          (fun a b => Classical.propDecidable (a = b))
          (eval ∘ projection) mass v =
        groupedMass (fun ω : Ω => projection ω i) mass v := by
    exact congrFun
      (exactGroupedMass_decidableEq_irrel _ _
        (fun ω : Ω => projection ω i) mass) v
  exact hleft.trans (h.trans hright)
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
theorem finiteUniformCoordinate_relativeEntropy
    {ι V : Type*} [Fintype ι] [Fintype V]
    (positive : 0 < Fintype.card ι)
    (posterior : ι → V → ℝ) (prior : V → ℝ) :
    finiteRelativeEntropy
        (fun t : ι × V =>
          (1 / (Fintype.card ι : ℝ)) * posterior t.1 t.2)
        (fun t : ι × V =>
          (1 / (Fintype.card ι : ℝ)) * prior t.2) =
      (1 / (Fintype.card ι : ℝ)) *
        ∑ i : ι, finiteRelativeEntropy (posterior i) prior := by
  classical
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt positive)
  have huniform : (1 / (Fintype.card ι : ℝ)) ≠ 0 :=
    one_div_ne_zero hcard
  unfold finiteRelativeEntropy
  rw [Fintype.sum_prod_type]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [mul_div_mul_left _ _ huniform]
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
theorem repeatedAlicePostselectedQuestionLaw_nonneg
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (xs : Fin n → X) :
    0 ≤ repeatedAlicePostselectedQuestionLaw G n S D xs := by
  classical
  unfold repeatedAlicePostselectedQuestionLaw
  apply groupedMass_nonneg
  intro ω
  exact conditionedEventDistribution_nonneg
    (strategyEventLaw (G.repeat n) S)
    (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)
    positive ω
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
theorem repeatedBobPostselectedQuestionLaw_nonneg
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (ys : Fin n → Y) :
    0 ≤ repeatedBobPostselectedQuestionLaw G n S D ys := by
  classical
  unfold repeatedBobPostselectedQuestionLaw
  apply groupedMass_nonneg
  intro ω
  exact conditionedEventDistribution_nonneg
    (strategyEventLaw (G.repeat n) S)
    (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)
    positive ω
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
theorem repeatedAlicePostselectedCoordinateMarginal
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (j : Fin n) (x : X) :
    finiteCoordinateMarginal
        (repeatedAlicePostselectedQuestionLaw G n S D) j x =
      groupedMass
        (fun ω : ExactOutcome X Y A B n => ω.1 j)
        (repeatedConditionedOutcomeLaw G n S D) x := by
  classical
  let projection :=
    fun ω : ExactOutcome X Y A B n => ω.1
  let posterior := repeatedConditionedOutcomeLaw G n S D
  have hlaw :
      repeatedAlicePostselectedQuestionLaw G n S D =
        groupedMass projection posterior := by
    unfold repeatedAlicePostselectedQuestionLaw
    exact exactGroupedMass_decidableEq_irrel _ _ _ _
  rw [hlaw]
  exact finiteCoordinateMarginal_groupedMass
    projection posterior j x
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
theorem repeatedBobPostselectedCoordinateMarginal
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (j : Fin n) (y : Y) :
    finiteCoordinateMarginal
        (repeatedBobPostselectedQuestionLaw G n S D) j y =
      groupedMass
        (fun ω : ExactOutcome X Y A B n => ω.2.1 j)
        (repeatedConditionedOutcomeLaw G n S D) y := by
  classical
  let projection :=
    fun ω : ExactOutcome X Y A B n => ω.2.1
  let posterior := repeatedConditionedOutcomeLaw G n S D
  have hlaw :
      repeatedBobPostselectedQuestionLaw G n S D =
        groupedMass projection posterior := by
    unfold repeatedBobPostselectedQuestionLaw
    exact exactGroupedMass_decidableEq_irrel _ _ _ _
  rw [hlaw]
  exact finiteCoordinateMarginal_groupedMass
    projection posterior j y
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
theorem exactAliceSourceMarginalInformation_eq
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (base : ExactHistoryFlag X Y A B D) :
    exactAliceSourceMarginalInformation G n S D base =
      (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
        ∑ i : SourceRemainingCoordinate D,
          finiteRelativeEntropy
            (finiteCoordinateMarginal
              (repeatedAlicePostselectedQuestionLaw G n S D)
              i.val)
            G.marginalX := by
  classical
  let posterior := repeatedAlicePostselectedQuestionLaw G n S D
  have hposterior :
      jointFirstMarginal
          (exactAliceInformationPosterior G n S D) =
        (fun t : SourceRemainingCoordinate D × X =>
          (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
            finiteCoordinateMarginal posterior t.1.val t.2) := by
    funext t
    rcases t with ⟨i, x⟩
    rw [exactAliceInformationPosterior_firstMarginal]
    congr 1
    exact (repeatedAlicePostselectedCoordinateMarginal
      G n S D i.val x).symm
  have hreference :
      jointFirstMarginal
          (exactAliceInformationReference G n S D base) =
        (fun t : SourceRemainingCoordinate D × X =>
          (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
            G.marginalX t.2) := by
    funext t
    rcases t with ⟨i, x⟩
    rw [exactAliceInformationReference_firstMarginal]
    change G.marginalX x /
      (Fintype.card (SourceRemainingCoordinate D) : ℝ) = _
    ring
  unfold exactAliceSourceMarginalInformation
  rw [hposterior, hreference]
  exact finiteUniformCoordinate_relativeEntropy
    (exactRemainingCoordinate_card_pos D remaining)
    (fun i : SourceRemainingCoordinate D =>
      finiteCoordinateMarginal posterior i.val)
    G.marginalX
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
theorem exactBobSourceMarginalInformation_eq
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (base : ExactHistoryFlag X Y A B D) :
    exactBobSourceMarginalInformation G n S D base =
      (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
        ∑ i : SourceRemainingCoordinate D,
          finiteRelativeEntropy
            (finiteCoordinateMarginal
              (repeatedBobPostselectedQuestionLaw G n S D)
              i.val)
            G.marginalY := by
  classical
  let posterior := repeatedBobPostselectedQuestionLaw G n S D
  have hposterior :
      jointFirstMarginal
          (exactBobInformationPosterior G n S D) =
        (fun t : SourceRemainingCoordinate D × Y =>
          (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
            finiteCoordinateMarginal posterior t.1.val t.2) := by
    funext t
    rcases t with ⟨i, y⟩
    rw [exactBobInformationPosterior_firstMarginal]
    congr 1
    exact (repeatedBobPostselectedCoordinateMarginal
      G n S D i.val y).symm
  have hreference :
      jointFirstMarginal
          (exactBobInformationReference G n S D base) =
        (fun t : SourceRemainingCoordinate D × Y =>
          (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
            G.marginalY t.2) := by
    funext t
    rcases t with ⟨i, y⟩
    rw [exactBobInformationReference_firstMarginal]
    change G.marginalY y /
      (Fintype.card (SourceRemainingCoordinate D) : ℝ) = _
    ring
  unfold exactBobSourceMarginalInformation
  rw [hposterior, hreference]
  exact finiteUniformCoordinate_relativeEntropy
    (exactRemainingCoordinate_card_pos D remaining)
    (fun i : SourceRemainingCoordinate D =>
      finiteCoordinateMarginal posterior i.val)
    G.marginalY
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
theorem sourceRemaining_nonnegative_sum_le
    {n : ℕ} (D : Finset (Fin n)) (f : Fin n → ℝ)
    (nonnegative : ∀ j, 0 ≤ f j) :
    (∑ i : SourceRemainingCoordinate D, f i.val) ≤
      ∑ j : Fin n, f j := by
  classical
  change
    (∑ i ∈ (Finset.univ \ D).attach, f i.val) ≤
      ∑ j : Fin n, f j
  rw [Finset.sum_attach]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ (Finset.univ \ D))
    (fun j _ _ => nonnegative j)
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
theorem exactAliceSourceMarginalInformation_le
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D) :
    exactAliceSourceMarginalInformation G n S D base ≤
      postselectionLogCost G n S D /
        ((Finset.univ \ D).card : ℝ) := by
  classical
  let posterior := repeatedAlicePostselectedQuestionLaw G n S D
  let coordinateInfo : Fin n → ℝ := fun j =>
    finiteRelativeEntropy
      (finiteCoordinateMarginal posterior j) G.marginalX
  have hnonnegative (j : Fin n) : 0 ≤ coordinateInfo j := by
    exact finiteRelativeEntropy_nonneg
      (finiteCoordinateMarginal posterior j) G.marginalX
      (fun x => finiteCoordinateMarginal_nonneg
        posterior
        (repeatedAlicePostselectedQuestionLaw_nonneg
          G n S D positive) j x)
      G.marginalX_nonneg
  have hremaining :
      (∑ i : SourceRemainingCoordinate D, coordinateInfo i.val) ≤
        postselectionLogCost G n S D := by
    exact
      (sourceRemaining_nonnegative_sum_le
        D coordinateInfo hnonnegative).trans
      (repeatedAliceCoordinateInformation_sum_le
        G n S D positive)
  have hcard :
      Fintype.card (SourceRemainingCoordinate D) =
        (Finset.univ \ D).card := by
    simp
  calc
    exactAliceSourceMarginalInformation G n S D base =
      (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
        ∑ i : SourceRemainingCoordinate D, coordinateInfo i.val :=
      exactAliceSourceMarginalInformation_eq
        G n S D remaining base
    _ ≤ (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
        postselectionLogCost G n S D := by
      exact mul_le_mul_of_nonneg_left hremaining
        (one_div_nonneg.mpr (Nat.cast_nonneg _))
    _ = postselectionLogCost G n S D /
        ((Finset.univ \ D).card : ℝ) := by
      rw [hcard]
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
theorem exactBobSourceMarginalInformation_le
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D) :
    exactBobSourceMarginalInformation G n S D base ≤
      postselectionLogCost G n S D /
        ((Finset.univ \ D).card : ℝ) := by
  classical
  let posterior := repeatedBobPostselectedQuestionLaw G n S D
  let coordinateInfo : Fin n → ℝ := fun j =>
    finiteRelativeEntropy
      (finiteCoordinateMarginal posterior j) G.marginalY
  have hnonnegative (j : Fin n) : 0 ≤ coordinateInfo j := by
    exact finiteRelativeEntropy_nonneg
      (finiteCoordinateMarginal posterior j) G.marginalY
      (fun y => finiteCoordinateMarginal_nonneg
        posterior
        (repeatedBobPostselectedQuestionLaw_nonneg
          G n S D positive) j y)
      G.marginalY_nonneg
  have hremaining :
      (∑ i : SourceRemainingCoordinate D, coordinateInfo i.val) ≤
        postselectionLogCost G n S D := by
    exact
      (sourceRemaining_nonnegative_sum_le
        D coordinateInfo hnonnegative).trans
      (repeatedBobCoordinateInformation_sum_le
        G n S D positive)
  have hcard :
      Fintype.card (SourceRemainingCoordinate D) =
        (Finset.univ \ D).card := by
    simp
  calc
    exactBobSourceMarginalInformation G n S D base =
      (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
        ∑ i : SourceRemainingCoordinate D, coordinateInfo i.val :=
      exactBobSourceMarginalInformation_eq
        G n S D remaining base
    _ ≤ (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
        postselectionLogCost G n S D := by
      exact mul_le_mul_of_nonneg_left hremaining
        (one_div_nonneg.mpr (Nat.cast_nonneg _))
    _ = postselectionLogCost G n S D /
        ((Finset.univ \ D).card : ℝ) := by
      rw [hcard]
      ring
end
end QuantumParallelRepetition

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
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem _root_.solution
    {KA KB : Type*} [Fintype KA] [Fintype KB]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (seedLawA : Finset (SourceRemainingCoordinate D) →
      FiniteEventLaw KA)
    (seedLawB : Finset (SourceRemainingCoordinate D) →
      FiniteEventLaw KB)
    (ΩA ΩB : Finset (SourceRemainingCoordinate D) → Type*)
    [∀ side, Fintype (ΩA side)]
    [∀ side, Fintype (ΩB side)]
    (projectionA : ∀ side : Finset (SourceRemainingCoordinate D),
      KA × ExactOutcome X Y A B n →
        ΩA side × (Fin side.card → Y))
    (projectionB : ∀ side : Finset (SourceRemainingCoordinate D),
      KB × ExactOutcome X Y A B n →
        ΩB side × (Fin side.card → X))
    (defaultY : Y) (defaultX : X)
    (aliceConditionedReverseIdentification :
      exactAliceSourceConditionalInformation G n S D base =
        ∑ side : Finset (SourceRemainingCoordinate D),
          reversePartitionWeight side *
            ((∑ k : Fin side.card,
              reweightedSeedPrefixEntropyIncrement
                (seedLawA side) G n S D
                (projectionA side) defaultY k) /
              (side.card : ℝ)))
    (bobConditionedReverseIdentification :
      exactBobSourceConditionalInformation G n S D base =
        ∑ side : Finset (SourceRemainingCoordinate D),
          reversePartitionWeight side *
            ((∑ k : Fin side.card,
              reweightedSeedPrefixEntropyIncrement
                (seedLawB side) G n S D
                (projectionB side) defaultX k) /
              (side.card : ℝ))) :
    ExactSourceClassicalInformationBound G n S D base := by
  constructor
  · rw [exact_source_equation_twenty_four_alice
      G n S D remaining positive base]
    change
      exactAliceSourceMarginalInformation G n S D base +
          exactAliceSourceConditionalInformation G n S D base ≤
        exactSourceClassicalInformationRate G n S D
    calc
      exactAliceSourceMarginalInformation G n S D base +
          exactAliceSourceConditionalInformation G n S D base ≤
        postselectionLogCost G n S D /
            ((Finset.univ \ D).card : ℝ) +
          2 * (postselectionLogCost G n S D +
            answerLogCost (A := A) (B := B) D) /
              ((Finset.univ \ D).card : ℝ) := by
            apply add_le_add
            · exact exactAliceSourceMarginalInformation_le
                G n S D remaining positive base
            · rw [aliceConditionedReverseIdentification]
              exact
                reweightedSeed_reverse_source_prefix_information_budget
                  G n S D remaining positive
                  seedLawA ΩA projectionA defaultY
      _ = exactSourceClassicalInformationRate G n S D := by
        unfold exactSourceClassicalInformationRate
        ring
  · rw [exact_source_equation_twenty_four_bob
      G n S D remaining positive base]
    change
      exactBobSourceMarginalInformation G n S D base +
          exactBobSourceConditionalInformation G n S D base ≤
        exactSourceClassicalInformationRate G n S D
    calc
      exactBobSourceMarginalInformation G n S D base +
          exactBobSourceConditionalInformation G n S D base ≤
        postselectionLogCost G n S D /
            ((Finset.univ \ D).card : ℝ) +
          2 * (postselectionLogCost G n S D +
            answerLogCost (A := A) (B := B) D) /
              ((Finset.univ \ D).card : ℝ) := by
            apply add_le_add
            · exact exactBobSourceMarginalInformation_le
                G n S D remaining positive base
            · rw [bobConditionedReverseIdentification]
              exact
                reweightedSeed_reverse_source_prefix_information_budget
                  G n S D remaining positive
                  seedLawB ΩB projectionB defaultX
      _ = exactSourceClassicalInformationRate G n S D := by
        unfold exactSourceClassicalInformationRate
        ring
end QuantumParallelRepetition

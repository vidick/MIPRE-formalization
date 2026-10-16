/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Repetition/TenProofs/QuantumParallelRepetition/Part04.lean (definition bundle: declarations the uploaded statements rest on);
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
import Mathlib.Algebra.Order.Archimedean.Basic
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
import Mathlib.Topology.UniformSpace.Defs
import Mathlib.Topology.UniformSpace.Matrix
import Mathlib.Topology.UniformSpace.Pi
import Mathlib.Topology.UniformSpace.Real
import Definitions.Def_MIPRE_Background_Repetition_TenProofs_QuantumParallelRepetition_Part01
import Definitions.Def_MIPRE_Background_Repetition_TenProofs_QuantumParallelRepetition_Part02
import Definitions.Def_MIPRE_Background_Repetition_TenProofs_QuantumParallelRepetition_Part03
import Theorems.Thm_QuantumParallelRepetition_exactForwardSeed_sum
import Theorems.Thm_QuantumParallelRepetition_exactLeft_coordinate_not_mem
import Theorems.Thm_QuantumParallelRepetition_exactPaddedDefault_norm
import Theorems.Thm_QuantumParallelRepetition_exactRight_coordinate_not_mem
import Theorems.Thm_QuantumParallelRepetition_exactSeedWeight_nonneg
import Theorems.Thm_QuantumParallelRepetition_exactSeedWeight_sum
import Theorems.Thm_QuantumParallelRepetition_reversePartitionWeight_nonneg
import Theorems.Thm_QuantumParallelRepetition_reversePartitionWeight_pos_iff
import Theorems.Thm_QuantumParallelRepetition_taggedTensorVector_norm

set_option autoImplicit true

namespace QuantumParallelRepetition

open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
open QuantumParallelRepetition.ClassicalSampling

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

abbrev ExactLocallySampleableTuple
    (X Y A B : Type*)
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {n : ℕ} (D : Finset (Fin n)) :=
  SourceRemainingCoordinate D ×
    (X × (Y × ExactHistoryFlag X Y A B D))

def exactHistoryCode
    {n : ℕ} (D : Finset (Fin n))
    (q : ExactJointOutcome X Y A B D) :
    ExactHistoryFlag X Y A B D where
  seed := q.1
  history := exactRevealCode D q.1 (q.2.1, q.2.2.1)
  aliceAnswer := fun j => q.2.2.2.1 j.val
  bobAnswer := fun j => q.2.2.2.2 j.val

def exactLocallySampleableCode
    {n : ℕ} (D : Finset (Fin n))
    (q : ExactJointOutcome X Y A B D) :
    ExactLocallySampleableTuple X Y A B D :=
  (q.1.coordinate,
    q.2.1 q.1.coordinate.val,
    q.2.2.1 q.1.coordinate.val,
    exactHistoryCode D q)

def exactLocallySampleableLaw
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) :
    ExactLocallySampleableTuple X Y A B D → ℝ :=
  exactSourcePushforward G n S D
    (exactLocallySampleableCode D)

def exactAliceLocalMass
    {n : ℕ} (D : Finset (Fin n))
    (Q : ExactLocallySampleableTuple X Y A B D → ℝ)
    (i : SourceRemainingCoordinate D) (x : X) : ℝ :=
  ∑ r : ExactHistoryFlag X Y A B D,
    ∑ y : Y, Q (i, x, y, r)

def exactBobLocalMass
    {n : ℕ} (D : Finset (Fin n))
    (Q : ExactLocallySampleableTuple X Y A B D → ℝ)
    (i : SourceRemainingCoordinate D) (y : Y) : ℝ :=
  ∑ r : ExactHistoryFlag X Y A B D,
    ∑ x : X, Q (i, x, y, r)

def exactAliceLocalConditional
    {n : ℕ} (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D)
    (Q : ExactLocallySampleableTuple X Y A B D → ℝ)
    (i : SourceRemainingCoordinate D) (x : X)
    (r : ExactHistoryFlag X Y A B D) : ℝ :=
  if exactAliceLocalMass D Q i x = 0 then
    if r = base then 1 else 0
  else
    (∑ y : Y, Q (i, x, y, r)) /
      exactAliceLocalMass D Q i x

def exactBobLocalConditional
    {n : ℕ} (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D)
    (Q : ExactLocallySampleableTuple X Y A B D → ℝ)
    (i : SourceRemainingCoordinate D) (y : Y)
    (r : ExactHistoryFlag X Y A B D) : ℝ :=
  if exactBobLocalMass D Q i y = 0 then
    if r = base then 1 else 0
  else
    (∑ x : X, Q (i, x, y, r)) /
      exactBobLocalMass D Q i y

def exactLocallySampleableJA
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D)
    (t : ExactLocallySampleableTuple X Y A B D) : ℝ :=
  G.questionWeight t.2.1 t.2.2.1 *
    exactAliceLocalConditional D base
      (exactLocallySampleableLaw G n S D)
      t.1 t.2.1 t.2.2.2 /
    (Fintype.card (SourceRemainingCoordinate D) : ℝ)

def exactLocallySampleableJB
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D)
    (t : ExactLocallySampleableTuple X Y A B D) : ℝ :=
  G.questionWeight t.2.1 t.2.2.1 *
    exactBobLocalConditional D base
      (exactLocallySampleableLaw G n S D)
      t.1 t.2.2.1 t.2.2.2 /
    (Fintype.card (SourceRemainingCoordinate D) : ℝ)

theorem exactRemainingCoordinate_card_pos
    {n : ℕ} (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card) :
    0 < Fintype.card (SourceRemainingCoordinate D) := by
  simpa using remaining

abbrev ExactLocalSamplerIndex
    (X Y : Type*) [Fintype X] [Fintype Y]
    {n : ℕ} (D : Finset (Fin n)) :=
  (SourceRemainingCoordinate D × X) ⊕
    (SourceRemainingCoordinate D × Y)

def exactLocalConditionalFamily
    {n : ℕ} (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D)
    (Q : ExactLocallySampleableTuple X Y A B D → ℝ)
    (k : ExactLocalSamplerIndex X Y D)
    (r : ExactHistoryFlag X Y A B D) : ℝ :=
  match k with
  | .inl (i, x) => exactAliceLocalConditional D base Q i x r
  | .inr (i, y) => exactBobLocalConditional D base Q i y r

end

noncomputable section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def exactConditionalQuestionWeight
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y)
    (xs : Fin n → X) (ys : Fin n → Y) : ℝ :=
  exactFiberQuestionWeight
      G n D seed history x y xs ys /
    exactFiberQuestionMass G n D seed history x y

def exactJointAliceQuestionFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (x : X) (y : Y) : Matrix S.Alice S.Alice ℂ :=
  ∑ xs : Fin n → X,
    (exactFiberAliceMarginal
      G n D seed history x y xs /
      exactFiberQuestionMass G n D seed history x y) •
    conditionedAliceEffect G n S D answer xs

def exactJointBobQuestionFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (x : X) (y : Y) : Matrix S.Bob S.Bob ℂ :=
  ∑ ys : Fin n → Y,
    (exactFiberBobMarginal
      G n D seed history x y ys /
      exactFiberQuestionMass G n D seed history x y) •
    conditionedBobEffect G n S D answer ys

def exactJointAliceCoordinateFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (x : X) (y : Y) (a : A) : Matrix S.Alice S.Alice ℂ :=
  ∑ xs : Fin n → X,
    (exactFiberAliceMarginal
      G n D seed history x y xs /
      exactFiberQuestionMass G n D seed history x y) •
    conditionedAliceCoordinateEffect
      G n S D answer xs seed.coordinate.val a

def exactJointBobCoordinateFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (x : X) (y : Y) (b : B) : Matrix S.Bob S.Bob ℂ :=
  ∑ ys : Fin n → Y,
    (exactFiberBobMarginal
      G n D seed history x y ys /
      exactFiberQuestionMass G n D seed history x y) •
    conditionedBobCoordinateEffect
      G n S D answer ys seed.coordinate.val b

def exactJointConditionalWinningMass
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (aliceAnswer : {j : Fin n // j ∈ D} → A)
    (bobAnswer : {j : Fin n // j ∈ D} → B)
    (x : X) (y : Y) : ℝ :=
  ∑ a : A, ∑ b : B,
    if G.predicate x y a b = true then
      bornTracePairing S.state.matrix
        (exactJointAliceCoordinateFilter
          G n S D seed history aliceAnswer x y a)
        (exactJointBobCoordinateFilter
          G n S D seed history bobAnswer x y b)
    else 0

end

noncomputable section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def exactFixedBobQuestionMass
    (G : Game X Y A B) (n : ℕ)
    (fixed : Finset (Fin n))
    (xs : Fin n → X) (known : Fin n → Y) : ℝ :=
  ∑ ys : Fin n → Y,
    if ∀ j : Fin n, j ∈ fixed → ys j = known j then
      (G.repeat n).questionWeight xs ys
    else 0

def exactFixedAliceQuestionMass
    (G : Game X Y A B) (n : ℕ)
    (fixed : Finset (Fin n))
    (known : Fin n → X) (ys : Fin n → Y) : ℝ :=
  ∑ xs : Fin n → X,
    if ∀ j : Fin n, j ∈ fixed → xs j = known j then
      (G.repeat n).questionWeight xs ys
    else 0

end

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

def exactReverseLeftSide
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) : Finset M :=
  insert seed.coordinate
    (exactLeft seed.coordinate seed.partition)

def exactReverseRightSide
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) : Finset M :=
  insert seed.coordinate
    (exactRight seed.coordinate seed.partition)

@[simp] theorem exactReverseLeftSide_coordinate_mem
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    seed.coordinate ∈ exactReverseLeftSide seed := by
  simp [exactReverseLeftSide]

@[simp] theorem exactReverseRightSide_coordinate_mem
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    seed.coordinate ∈ exactReverseRightSide seed := by
  simp [exactReverseRightSide]

theorem exactReverseLeftSide_card
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    (exactReverseLeftSide seed).card =
      (exactLeft seed.coordinate seed.partition).card + 1 := by
  simp [exactReverseLeftSide,
    exactLeft_coordinate_not_mem, Nat.add_comm]

theorem exactReverseRightSide_card
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    (exactReverseRightSide seed).card =
      (exactRight seed.coordinate seed.partition).card + 1 := by
  simp [exactReverseRightSide,
    exactRight_coordinate_not_mem, Nat.add_comm]

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048

open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

def exactReverseLeftSeedWeight
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) : ℝ :=
  (1 / (2 : ℝ)) *
    reverseMarkedPartitionWeight
      (exactReverseLeftSide seed) seed.coordinate *
    (1 / (Fintype.card
      (Equiv.Perm
        {j : M // j ∈ exactReverseLeftSide seed}) : ℝ)) *
    (1 / (Fintype.card
      (Equiv.Perm
        {j : M // j ∈
          exactRight seed.coordinate seed.partition}) : ℝ)) *
    (1 /
      ((exactRight
        seed.coordinate seed.partition).card + 1 : ℝ))

def exactReverseRightSeedWeight
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) : ℝ :=
  (1 / (2 : ℝ)) *
    reverseMarkedPartitionWeight
      (exactReverseRightSide seed) seed.coordinate *
    (1 / (Fintype.card
      (Equiv.Perm
        {j : M // j ∈ exactReverseRightSide seed}) : ℝ)) *
    (1 / (Fintype.card
      (Equiv.Perm
        {j : M // j ∈
          exactLeft seed.coordinate seed.partition}) : ℝ)) *
    (1 /
      ((exactLeft
        seed.coordinate seed.partition).card + 1 : ℝ))

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def exactHistoryAccepted
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) : Prop :=
  ∀ j : {j : Fin n // j ∈ D},
    G.predicate
      (r.history.aliceConditioned j)
      (r.history.bobConditioned j)
      (r.aliceAnswer j)
      (r.bobAnswer j) = true

end

noncomputable section

open scoped BigOperators Kronecker ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

abbrev ExactGlobalHistoryLocalIndex
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) :=
  PUnit.{1} ⊕
    (Σ r : ExactHistoryFlag X Y A B D,
      ExactPaddedLocalIndex G n S D r)

def exactGlobalHistoryVector
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (z : EuclideanSpace ℂ
      (ExactPaddedLocalIndex G n S D r ×
        ExactPaddedLocalIndex G n S D r)) :
    EuclideanSpace ℂ
      (ExactGlobalHistoryLocalIndex G n S D ×
        ExactGlobalHistoryLocalIndex G n S D) :=
  taggedTensorVector r z

theorem exactGlobalHistoryVector_norm
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (z : EuclideanSpace ℂ
      (ExactPaddedLocalIndex G n S D r ×
        ExactPaddedLocalIndex G n S D r)) :
    ‖exactGlobalHistoryVector G n S D r z‖ = ‖z‖ :=
  taggedTensorVector_norm r z

def exactGlobalHistoryFinReindex
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) :
    EuclideanSpace ℂ
      (ExactGlobalHistoryLocalIndex G n S D ×
        ExactGlobalHistoryLocalIndex G n S D) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ
        (Fin (Fintype.card
          (ExactGlobalHistoryLocalIndex G n S D)) ×
         Fin (Fintype.card
          (ExactGlobalHistoryLocalIndex G n S D))) := by
  classical
  exact LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (Equiv.prodCongr
      (Fintype.equivFin (ExactGlobalHistoryLocalIndex G n S D))
      (Fintype.equivFin (ExactGlobalHistoryLocalIndex G n S D)))

def exactGlobalHistoryFinGamma
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) (x : X) :
    BipartiteUnitVector
      (Fintype.card (ExactGlobalHistoryLocalIndex G n S D)) :=
  ⟨exactGlobalHistoryFinReindex G n S D
      (exactGlobalHistoryVector G n S D r
        (exactGamma G n S D r x)), by
      rw [LinearIsometryEquiv.norm_map,
        exactGlobalHistoryVector_norm]
      exact normalizeOrDefault_norm _ _
        (exactPaddedDefault_norm G n S D r)⟩

def exactGlobalHistoryFinPhi
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) (y : Y) :
    BipartiteUnitVector
      (Fintype.card (ExactGlobalHistoryLocalIndex G n S D)) :=
  ⟨exactGlobalHistoryFinReindex G n S D
      (exactGlobalHistoryVector G n S D r
        (exactPhi G n S D r y)), by
      rw [LinearIsometryEquiv.norm_map,
        exactGlobalHistoryVector_norm]
      exact normalizeOrDefault_norm _ _
        (exactPaddedDefault_norm G n S D r)⟩

def exactGlobalHistoryFinPsi
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y) :
    BipartiteUnitVector
      (Fintype.card (ExactGlobalHistoryLocalIndex G n S D)) :=
  ⟨exactGlobalHistoryFinReindex G n S D
      (exactGlobalHistoryVector G n S D r
        (exactPsi G n S D r x y)), by
      rw [LinearIsometryEquiv.norm_map,
        exactGlobalHistoryVector_norm]
      exact normalizeOrDefault_norm _ _
        (exactPaddedDefault_norm G n S D r)⟩

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

abbrev ExactSourceGlobalState
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) :=
  EuclideanSpace ℂ
    (Fin (Fintype.card (ExactGlobalHistoryLocalIndex G n S D)) ×
      Fin (Fintype.card (ExactGlobalHistoryLocalIndex G n S D)))

def exactSourceTuplePsi
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (t : ExactLocallySampleableTuple X Y A B D) :
    ExactSourceGlobalState G n S D :=
  (exactGlobalHistoryFinPsi
    G n S D t.2.2.2 t.2.1 t.2.2.1).val

def exactSourceTupleGamma
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (t : ExactLocallySampleableTuple X Y A B D) :
    ExactSourceGlobalState G n S D :=
  (exactGlobalHistoryFinGamma
    G n S D t.2.2.2 t.2.1).val

def exactSourceTuplePhi
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (t : ExactLocallySampleableTuple X Y A B D) :
    ExactSourceGlobalState G n S D :=
  (exactGlobalHistoryFinPhi
    G n S D t.2.2.2 t.2.2.1).val

def ExactSourceStateDistanceBound
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (η : ℝ) : Prop :=
  (∑ t : ExactLocallySampleableTuple X Y A B D,
    exactLocallySampleableLaw G n S D t *
      ‖exactSourceTupleGamma G n S D t -
        exactSourceTuplePsi G n S D t‖ ^ 2) ≤ 8 * η ∧
  (∑ t : ExactLocallySampleableTuple X Y A B D,
    exactLocallySampleableLaw G n S D t *
      ‖exactSourceTuplePsi G n S D t -
        exactSourceTuplePhi G n S D t‖ ^ 2) ≤ 8 * η

end

noncomputable section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def exactFairAliceQuestionEntropyIncrement
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) (y : Y) : ℝ :=
  bornTracePairing S.state.matrix
    ((∑ x : X, G.conditionalXGivenY y x •
      cfc (fun z : ℝ => z * Real.log z)
        (exactAliceQuestionFilter
          G n S D r.seed r.history r.aliceAnswer x)) -
      cfc (fun z : ℝ => z * Real.log z)
        (exactAliceMeanFilter
          G n S D r.seed r.history r.aliceAnswer y))
    (exactBobQuestionFilter
      G n S D r.seed r.history r.bobAnswer y)

def exactFairBobQuestionEntropyIncrement
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) (x : X) : ℝ :=
  bornTracePairing S.state.matrix
    (exactAliceQuestionFilter
      G n S D r.seed r.history r.aliceAnswer x)
    ((∑ y : Y, G.conditionalYGivenX x y •
      cfc (fun z : ℝ => z * Real.log z)
        (exactBobQuestionFilter
          G n S D r.seed r.history r.bobAnswer y)) -
      cfc (fun z : ℝ => z * Real.log z)
        (exactBobMeanFilter
          G n S D r.seed r.history r.bobAnswer x))

def exactFairAliceHistoryVariation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) : ℝ :=
  ∑ y : Y, ∑ x : X, G.questionWeight x y *
    ‖exactUnnormalizedPsi G n S D r x y -
      exactUnnormalizedPhi G n S D r y‖ ^ 2

def exactFairBobHistoryVariation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) : ℝ :=
  ∑ x : X, ∑ y : Y, G.questionWeight x y *
    ‖exactUnnormalizedPsi G n S D r x y -
      exactUnnormalizedGamma G n S D r x‖ ^ 2

def exactFairAliceHistoryEntropyIncrement
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) : ℝ :=
  ∑ y : Y, G.marginalY y *
    exactFairAliceQuestionEntropyIncrement G n S D r y

def exactFairBobHistoryEntropyIncrement
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) : ℝ :=
  ∑ x : X, G.marginalX x *
    exactFairBobQuestionEntropyIncrement G n S D r x

def exactFairHistoryPriorWeight
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) : ℝ :=
  exactSeedWeight r.seed *
    exactRevealMass G n D r.seed r.history

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def exactSourceClassicalInformationRate
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) : ℝ :=
  (3 * postselectionLogCost G n S D +
      2 * answerLogCost (A := A) (B := B) D) /
    ((Finset.univ \ D).card : ℝ)

def ExactSourceClassicalInformationBound
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D) : Prop :=
  finiteRelativeEntropy
      (exactLocallySampleableLaw G n S D)
      (exactLocallySampleableJA G n S D base) ≤
        exactSourceClassicalInformationRate G n S D ∧
    finiteRelativeEntropy
      (exactLocallySampleableLaw G n S D)
      (exactLocallySampleableJB G n S D base) ≤
        exactSourceClassicalInformationRate G n S D

def exactAliceInformationEquiv
    {n : ℕ} (D : Finset (Fin n)) :
    ExactLocallySampleableTuple X Y A B D ≃
      (SourceRemainingCoordinate D × X) ×
        (ExactHistoryFlag X Y A B D × Y) where
  toFun t := ((t.1, t.2.1), (t.2.2.2, t.2.2.1))
  invFun t := (t.1.1, t.1.2, t.2.2, t.2.1)
  left_inv t := by
    rcases t with ⟨i, x, y, r⟩
    rfl
  right_inv t := by
    rcases t with ⟨⟨i, x⟩, ⟨r, y⟩⟩
    rfl

def exactBobInformationEquiv
    {n : ℕ} (D : Finset (Fin n)) :
    ExactLocallySampleableTuple X Y A B D ≃
      (SourceRemainingCoordinate D × Y) ×
        (ExactHistoryFlag X Y A B D × X) where
  toFun t := ((t.1, t.2.2.1), (t.2.2.2, t.2.1))
  invFun t := (t.1.1, t.2.2, t.1.2, t.2.1)
  left_inv t := by
    rcases t with ⟨i, x, y, r⟩
    rfl
  right_inv t := by
    rcases t with ⟨⟨i, y⟩, ⟨r, x⟩⟩
    rfl

def exactAliceInformationPosterior
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) :
    (SourceRemainingCoordinate D × X) ×
      (ExactHistoryFlag X Y A B D × Y) → ℝ :=
  fun t => exactLocallySampleableLaw G n S D
    ((exactAliceInformationEquiv
      (X := X) (Y := Y) (A := A) (B := B) D).symm t)

def exactAliceInformationReference
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D) :
    (SourceRemainingCoordinate D × X) ×
      (ExactHistoryFlag X Y A B D × Y) → ℝ :=
  fun t => exactLocallySampleableJA G n S D base
    ((exactAliceInformationEquiv
      (X := X) (Y := Y) (A := A) (B := B) D).symm t)

def exactBobInformationPosterior
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) :
    (SourceRemainingCoordinate D × Y) ×
      (ExactHistoryFlag X Y A B D × X) → ℝ :=
  fun t => exactLocallySampleableLaw G n S D
    ((exactBobInformationEquiv
      (X := X) (Y := Y) (A := A) (B := B) D).symm t)

def exactBobInformationReference
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D) :
    (SourceRemainingCoordinate D × Y) ×
      (ExactHistoryFlag X Y A B D × X) → ℝ :=
  fun t => exactLocallySampleableJB G n S D base
    ((exactBobInformationEquiv
      (X := X) (Y := Y) (A := A) (B := B) D).symm t)

def exactSourcePinskerRate
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) : ℝ :=
  Real.sqrt (exactSourceClassicalInformationRate G n S D / 2)

end

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1600000

attribute [local instance] Classical.propDecidable

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def exactSourcePrefixFlagEquiv
    {Ω V Z : Type*} {h : ℕ} :
    ((Ω × (Fin h → V)) × Z) ≃
      ((Ω × Z) × (Fin h → V)) where
  toFun t := ((t.1.1, t.2), t.1.2)
  invFun t := ((t.1.1, t.2), t.1.2)
  left_inv t := by
    rcases t with ⟨⟨u, values⟩, z⟩
    rfl
  right_inv t := by
    rcases t with ⟨⟨u, z⟩, values⟩
    rfl

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def exactAliceQuestionPriorMarginal
    (G : Game X Y A B) (x : X) : ℝ :=
  ∑ y : Y, G.questionWeight x y

def exactBobQuestionPriorMarginal
    (G : Game X Y A B) (y : Y) : ℝ :=
  ∑ x : X, G.questionWeight x y

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def exactAliceSourceMarginalInformation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D) : ℝ :=
  finiteRelativeEntropy
    (jointFirstMarginal
      (exactAliceInformationPosterior G n S D))
    (jointFirstMarginal
      (exactAliceInformationReference G n S D base))

def exactBobSourceMarginalInformation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D) : ℝ :=
  finiteRelativeEntropy
    (jointFirstMarginal
      (exactBobInformationPosterior G n S D))
    (jointFirstMarginal
      (exactBobInformationReference G n S D base))

def exactAliceSourceConditionalInformation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D) : ℝ :=
  ∑ ix : SourceRemainingCoordinate D × X,
    jointFirstMarginal
        (exactAliceInformationPosterior G n S D) ix *
      finiteRelativeEntropy
        (jointConditional
          (exactAliceInformationPosterior G n S D) ix)
        (jointConditional
          (exactAliceInformationReference G n S D base) ix)

def exactBobSourceConditionalInformation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D) : ℝ :=
  ∑ iy : SourceRemainingCoordinate D × Y,
    jointFirstMarginal
        (exactBobInformationPosterior G n S D) iy *
      finiteRelativeEntropy
        (jointConditional
          (exactBobInformationPosterior G n S D) iy)
        (jointConditional
          (exactBobInformationReference G n S D base) iy)

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048

attribute [local instance] Classical.propDecidable

def exactInsertedRank
    {M : Type*} [DecidableEq M]
    (i : M) (side : Finset M) (not_mem : i ∉ side)
    (rank : {j : M // j ∈ side} ≃ Fin side.card)
    (cut : Fin (side.card + 1)) :
    {j : M // j ∈ insert i side} ≃ Fin (side.card + 1) :=
  (Finset.subtypeInsertEquivOption not_mem).trans
    ((Equiv.optionCongr rank).trans (finSuccEquiv' cut).symm)

@[simp] theorem exactInsertedRank_marker
    {M : Type*} [DecidableEq M]
    (i : M) (side : Finset M) (not_mem : i ∉ side)
    (rank : {j : M // j ∈ side} ≃ Fin side.card)
    (cut : Fin (side.card + 1)) :
    exactInsertedRank i side not_mem rank cut
      ⟨i, Finset.mem_insert_self i side⟩ = cut := by
  simp [exactInsertedRank,
    Finset.subtypeInsertEquivOption]

theorem exactInsertedRank_old
    {M : Type*} [DecidableEq M]
    (i : M) (side : Finset M) (not_mem : i ∉ side)
    (rank : {j : M // j ∈ side} ≃ Fin side.card)
    (cut : Fin (side.card + 1))
    (j : {j : M // j ∈ side}) :
    exactInsertedRank i side not_mem rank cut
      ⟨j.val, Finset.mem_insert_of_mem j.property⟩ =
      cut.succAbove (rank j) := by
  have hne : j.val ≠ i := by
    intro h
    exact not_mem (h ▸ j.property)
  simp [exactInsertedRank,
    Finset.subtypeInsertEquivOption, hne]

def exactReverseLeftRank
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    {j : M // j ∈ exactReverseLeftSide seed} ≃
      Fin ((exactLeft seed.coordinate seed.partition).card + 1) :=
  exactInsertedRank seed.coordinate
    (exactLeft seed.coordinate seed.partition)
    (exactLeft_coordinate_not_mem seed.coordinate seed.partition)
    (exactLeftRank seed) seed.leftCut

def exactReverseRightRank
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    {j : M // j ∈ exactReverseRightSide seed} ≃
      Fin ((exactRight seed.coordinate seed.partition).card + 1) :=
  exactInsertedRank seed.coordinate
    (exactRight seed.coordinate seed.partition)
    (exactRight_coordinate_not_mem seed.coordinate seed.partition)
    (exactRightRank seed) seed.rightCut

@[simp] theorem exactReverseLeftRank_coordinate
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    exactReverseLeftRank seed
      ⟨seed.coordinate,
        exactReverseLeftSide_coordinate_mem seed⟩ =
      seed.leftCut := by
  exact exactInsertedRank_marker
    seed.coordinate
    (exactLeft seed.coordinate seed.partition)
    (exactLeft_coordinate_not_mem
      seed.coordinate seed.partition)
    (exactLeftRank seed) seed.leftCut

@[simp] theorem exactReverseRightRank_coordinate
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    exactReverseRightRank seed
      ⟨seed.coordinate,
        exactReverseRightSide_coordinate_mem seed⟩ =
      seed.rightCut := by
  exact exactInsertedRank_marker
    seed.coordinate
    (exactRight seed.coordinate seed.partition)
    (exactRight_coordinate_not_mem
      seed.coordinate seed.partition)
    (exactRightRank seed) seed.rightCut

theorem exactReverseLeftRank_old
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M)
    (j : {j : M //
      j ∈ exactLeft seed.coordinate seed.partition}) :
    exactReverseLeftRank seed
      ⟨j.val, Finset.mem_insert_of_mem j.property⟩ =
      seed.leftCut.succAbove (exactLeftRank seed j) := by
  exact exactInsertedRank_old
    seed.coordinate
    (exactLeft seed.coordinate seed.partition)
    (exactLeft_coordinate_not_mem
      seed.coordinate seed.partition)
    (exactLeftRank seed) seed.leftCut j

theorem exactReverseRightRank_old
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M)
    (j : {j : M //
      j ∈ exactRight seed.coordinate seed.partition}) :
    exactReverseRightRank seed
      ⟨j.val, Finset.mem_insert_of_mem j.property⟩ =
      seed.rightCut.succAbove (exactRightRank seed j) := by
  exact exactInsertedRank_old
    seed.coordinate
    (exactRight seed.coordinate seed.partition)
    (exactRight_coordinate_not_mem
      seed.coordinate seed.partition)
    (exactRightRank seed) seed.rightCut j

def exactInsertedPrefixBefore
    {M : Type*} [Fintype M] [DecidableEq M]
    (i : M) (side : Finset M) (not_mem : i ∉ side)
    (rank : {j : M // j ∈ side} ≃ Fin side.card)
    (cut : Fin (side.card + 1)) : Finset M :=
  (Finset.univ.filter
    (fun j : {j : M // j ∈ insert i side} =>
      (exactInsertedRank i side not_mem rank cut j).val <
        cut.val)).image Subtype.val

def exactReverseLeftPrefixBeforeMarked
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) : Finset M :=
  exactInsertedPrefixBefore seed.coordinate
    (exactLeft seed.coordinate seed.partition)
    (exactLeft_coordinate_not_mem
      seed.coordinate seed.partition)
    (exactLeftRank seed) seed.leftCut

def exactReverseRightPrefixBeforeMarked
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) : Finset M :=
  exactInsertedPrefixBefore seed.coordinate
    (exactRight seed.coordinate seed.partition)
    (exactRight_coordinate_not_mem
      seed.coordinate seed.partition)
    (exactRightRank seed) seed.rightCut

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048

attribute [local instance] Classical.propDecidable

def exactOrderedSidePrefix
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (rank : {j : M // j ∈ side} ≃ Fin side.card)
    (cut : Fin (side.card + 1)) : Finset M :=
  (Finset.univ.filter
    (fun j : {j : M // j ∈ side} =>
      (rank j).val < cut.val)).image Subtype.val

structure ExactReverseSideContext
    (M : Type*) [Fintype M] [DecidableEq M]
    (side : Finset M) where
  otherSide : Finset M
  sideRank : {j : M // j ∈ side} ≃ Fin side.card
  otherRank : {j : M // j ∈ otherSide} ≃ Fin otherSide.card
  otherCut : Fin (otherSide.card + 1)
  ignoredBit : Bool
  otherSide_eq_complement : otherSide = Finset.univ \ side
  deriving Fintype

def exactReverseContextOtherPrefix
    {M : Type*} [Fintype M] [DecidableEq M]
    {side : Finset M}
    (context : ExactReverseSideContext M side) : Finset M :=
  exactOrderedSidePrefix
    context.otherSide context.otherRank context.otherCut

theorem exactReverseLeftSide_complement
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    exactRight seed.coordinate seed.partition =
      Finset.univ \ exactReverseLeftSide seed := by
  ext j
  by_cases hcoordinate : j = seed.coordinate
  · subst j
    simp [exactRight, exactReverseLeftSide]
  · cases hbit : seed.partition j <;>
      simp [exactRight, exactLeft,
        exactReverseLeftSide, hcoordinate, hbit]

theorem exactReverseRightSide_complement
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    exactLeft seed.coordinate seed.partition =
      Finset.univ \ exactReverseRightSide seed := by
  ext j
  by_cases hcoordinate : j = seed.coordinate
  · subst j
    simp [exactLeft, exactReverseRightSide]
  · cases hbit : seed.partition j <;>
      simp [exactRight, exactLeft,
        exactReverseRightSide, hcoordinate, hbit]

def exactReverseAliceContext
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    ExactReverseSideContext M
      (exactReverseLeftSide seed) where
  otherSide := exactRight seed.coordinate seed.partition
  sideRank := (exactReverseLeftRank seed).trans
    (finCongr (exactReverseLeftSide_card seed).symm)
  otherRank := exactRightRank seed
  otherCut := seed.rightCut
  ignoredBit := seed.partition seed.coordinate
  otherSide_eq_complement := exactReverseLeftSide_complement seed

def exactReverseBobContext
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    ExactReverseSideContext M
      (exactReverseRightSide seed) where
  otherSide := exactLeft seed.coordinate seed.partition
  sideRank := (exactReverseRightRank seed).trans
    (finCongr (exactReverseRightSide_card seed).symm)
  otherRank := exactLeftRank seed
  otherCut := seed.leftCut
  ignoredBit := seed.partition seed.coordinate
  otherSide_eq_complement := exactReverseRightSide_complement seed

def exactDefaultReverseSideContext
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) : ExactReverseSideContext M side where
  otherSide := Finset.univ \ side
  sideRank := Finset.equivFin side
  otherRank := Finset.equivFin (Finset.univ \ side)
  otherCut := 0
  ignoredBit := false
  otherSide_eq_complement := rfl

def exactReverseAliceContextAt
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (seed : ExactForwardSeed M) :
    ExactReverseSideContext M side :=
  if h : exactReverseLeftSide seed = side then
    h ▸ exactReverseAliceContext seed
  else
    exactDefaultReverseSideContext side

def exactReverseBobContextAt
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (seed : ExactForwardSeed M) :
    ExactReverseSideContext M side :=
  if h : exactReverseRightSide seed = side then
    h ▸ exactReverseBobContext seed
  else
    exactDefaultReverseSideContext side

@[simp] theorem exactReverseAliceContextAt_actual
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    exactReverseAliceContextAt
        (exactReverseLeftSide seed) seed =
      exactReverseAliceContext seed := by
  simp [exactReverseAliceContextAt]

@[simp] theorem exactReverseBobContextAt_actual
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    exactReverseBobContextAt
        (exactReverseRightSide seed) seed =
      exactReverseBobContext seed := by
  simp [exactReverseBobContextAt]

@[simp] theorem exactReverseAliceContext_otherPrefix
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    exactReverseContextOtherPrefix
        (exactReverseAliceContext seed) =
      exactRightPrefix seed := by
  rfl

@[simp] theorem exactReverseBobContext_otherPrefix
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    exactReverseContextOtherPrefix
        (exactReverseBobContext seed) =
      exactLeftPrefix seed := by
  rfl

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

abbrev ExactReverseAliceFixedInformation
    (X Y : Type*) [Fintype X] [Fintype Y]
    {n : ℕ} (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D)) :=
  Σ context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side,
    ({j : Fin n // j ∈ D} → X) ×
    ({j : Fin n // j ∈ D} → Y) ×
    ({j : SourceRemainingCoordinate D // j ∈ side} → X) ×
    ({j : SourceRemainingCoordinate D // j ∈ context.otherSide} → Y) ×
    ({j : SourceRemainingCoordinate D //
        j ∈ exactReverseContextOtherPrefix context} → X)

abbrev ExactReverseBobFixedInformation
    (X Y : Type*) [Fintype X] [Fintype Y]
    {n : ℕ} (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D)) :=
  Σ context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side,
    ({j : Fin n // j ∈ D} → X) ×
    ({j : Fin n // j ∈ D} → Y) ×
    ({j : SourceRemainingCoordinate D // j ∈ side} → Y) ×
    ({j : SourceRemainingCoordinate D // j ∈ context.otherSide} → X) ×
    ({j : SourceRemainingCoordinate D //
        j ∈ exactReverseContextOtherPrefix context} → Y)

def exactReverseAliceSourceProjection
    {n : ℕ} (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D)) :
    ExactJointOutcome X Y A B D →
      ExactReverseAliceFixedInformation X Y D side ×
        (Fin side.card → Y) :=
  fun q =>
    let context := exactReverseAliceContextAt side q.1
    (⟨context,
       (fun j => q.2.1 j.val),
       (fun j => q.2.2.1 j.val),
       (fun j => q.2.1 j.val.val),
       (fun j => q.2.2.1 j.val.val),
       (fun j => q.2.1 j.val.val)⟩,
      fun k => q.2.2.1 (context.sideRank.symm k).val.val)

def exactReverseBobSourceProjection
    {n : ℕ} (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D)) :
    ExactJointOutcome X Y A B D →
      ExactReverseBobFixedInformation X Y D side ×
        (Fin side.card → X) :=
  fun q =>
    let context := exactReverseBobContextAt side q.1
    (⟨context,
       (fun j => q.2.1 j.val),
       (fun j => q.2.2.1 j.val),
       (fun j => q.2.2.1 j.val.val),
       (fun j => q.2.1 j.val.val),
       (fun j => q.2.2.1 j.val.val)⟩,
      fun k => q.2.1 (context.sideRank.symm k).val.val)

@[simp] theorem exactReverseAliceContext_marked_rank
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    ((exactReverseAliceContext seed).sideRank
      ⟨seed.coordinate,
        exactReverseLeftSide_coordinate_mem seed⟩).val =
      seed.leftCut.val := by
  simp [exactReverseAliceContext,
    Equiv.trans_apply,
    exactReverseLeftRank_coordinate]

@[simp] theorem exactReverseBobContext_marked_rank
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    ((exactReverseBobContext seed).sideRank
      ⟨seed.coordinate,
        exactReverseRightSide_coordinate_mem seed⟩).val =
      seed.rightCut.val := by
  simp [exactReverseBobContext,
    Equiv.trans_apply,
    exactReverseRightRank_coordinate]

def exactReverseContextPrefixBefore
    {M : Type*} [Fintype M] [DecidableEq M]
    {side : Finset M}
    (context : ExactReverseSideContext M side)
    (position : Fin side.card) : Finset M :=
  exactOrderedSidePrefix
    side context.sideRank position.castSucc

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

def exactPrefixNextCode
    {Ω V : Type*} {h : ℕ}
    (default : V) (k : Fin h) :
    (Ω × (Fin h → V)) → ((Ω × (Fin h → V)) × V) :=
  fun t => (finitePrefixMask default k.castSucc t, t.2 k)

def exactPrefixNextDecode
    {Ω V : Type*} {h : ℕ}
    (k : Fin h) :
    ((Ω × (Fin h → V)) × V) → (Ω × (Fin h → V)) :=
  fun t => (t.1.1, Function.update t.1.2 k t.2)

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048

open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

def exactReverseAliceCanonicalPartition
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M) (ignored : Bool) : M → Bool :=
  fun j => if j = coordinate then ignored
    else if j ∈ side then false else true

theorem exactReverseAliceCanonicalPartition_side
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (member : coordinate ∈ side) (ignored : Bool) :
    insert coordinate
        (exactLeft coordinate
          (exactReverseAliceCanonicalPartition
            side coordinate ignored)) = side := by
  ext j
  by_cases hj : j = coordinate
  · subst j
    simp [member]
  · by_cases hs : j ∈ side <;>
      simp [exactLeft,
        exactReverseAliceCanonicalPartition,
        hj, hs]

theorem exactReverseAliceCanonicalPartition_unique
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (partition : M → Bool)
    (fiber : insert coordinate
      (exactLeft coordinate partition) = side) :
    partition = exactReverseAliceCanonicalPartition
      side coordinate (partition coordinate) := by
  funext j
  by_cases hj : j = coordinate
  · subst j
    simp [exactReverseAliceCanonicalPartition]
  · cases hb : partition j
    · have hs : j ∈ side := by
        rw [← fiber]
        simp [exactLeft, hj, hb]
      simp [exactReverseAliceCanonicalPartition,
        hj, hs]
    · have hs : j ∉ side := by
        rw [← fiber]
        simp [exactLeft, hj, hb]
      simp [exactReverseAliceCanonicalPartition,
        hj, hs]

def exactReverseAlicePartitionFiberEquiv
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (member : coordinate ∈ side) :
    {partition : M → Bool //
      insert coordinate (exactLeft coordinate partition) = side} ≃
        Bool where
  toFun partition := partition.val coordinate
  invFun ignored :=
    ⟨exactReverseAliceCanonicalPartition side coordinate ignored,
      exactReverseAliceCanonicalPartition_side
        side coordinate member ignored⟩
  left_inv partition := by
    apply Subtype.ext
    exact (exactReverseAliceCanonicalPartition_unique
      side coordinate partition.val partition.property).symm
  right_inv ignored := by
    simp [exactReverseAliceCanonicalPartition]

def exactReverseBobCanonicalPartition
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M) (ignored : Bool) : M → Bool :=
  fun j => if j = coordinate then ignored
    else if j ∈ side then true else false

theorem exactReverseBobCanonicalPartition_side
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (member : coordinate ∈ side) (ignored : Bool) :
    insert coordinate
        (exactRight coordinate
          (exactReverseBobCanonicalPartition
            side coordinate ignored)) = side := by
  ext j
  by_cases hj : j = coordinate
  · subst j
    simp [member]
  · by_cases hs : j ∈ side <;>
      simp [exactRight,
        exactReverseBobCanonicalPartition,
        hj, hs]

theorem exactReverseBobCanonicalPartition_unique
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (partition : M → Bool)
    (fiber : insert coordinate
      (exactRight coordinate partition) = side) :
    partition = exactReverseBobCanonicalPartition
      side coordinate (partition coordinate) := by
  funext j
  by_cases hj : j = coordinate
  · subst j
    simp [exactReverseBobCanonicalPartition]
  · cases hb : partition j
    · have hs : j ∉ side := by
        rw [← fiber]
        simp [exactRight, hj, hb]
      simp [exactReverseBobCanonicalPartition,
        hj, hs]
    · have hs : j ∈ side := by
        rw [← fiber]
        simp [exactRight, hj, hb]
      simp [exactReverseBobCanonicalPartition,
        hj, hs]

def exactReverseBobPartitionFiberEquiv
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (member : coordinate ∈ side) :
    {partition : M → Bool //
      insert coordinate (exactRight coordinate partition) = side} ≃
        Bool where
  toFun partition := partition.val coordinate
  invFun ignored :=
    ⟨exactReverseBobCanonicalPartition side coordinate ignored,
      exactReverseBobCanonicalPartition_side
        side coordinate member ignored⟩
  left_inv partition := by
    apply Subtype.ext
    exact (exactReverseBobCanonicalPartition_unique
      side coordinate partition.val partition.property).symm
  right_inv ignored := by
    simp [exactReverseBobCanonicalPartition]

theorem exactReverseAlicePartitionFiber_card
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (member : coordinate ∈ side) :
    Fintype.card
      {partition : M → Bool //
        insert coordinate
          (exactLeft coordinate partition) = side} = 2 := by
  simpa using Fintype.card_congr
    (exactReverseAlicePartitionFiberEquiv
      side coordinate member)

theorem exactReverseBobPartitionFiber_card
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (member : coordinate ∈ side) :
    Fintype.card
      {partition : M → Bool //
        insert coordinate
          (exactRight coordinate partition) = side} = 2 := by
  simpa using Fintype.card_congr
    (exactReverseBobPartitionFiberEquiv
      side coordinate member)

theorem exactFiniteIndicator_sum
    {T : Type*} [Fintype T]
    (predicate : T → Prop) [DecidablePred predicate]
    (weight : ℝ) :
    (∑ t : T, if predicate t then weight else 0) =
      (Fintype.card {t : T // predicate t} : ℝ) * weight := by
  classical
  calc
    (∑ t : T, if predicate t then weight else 0) =
        (∑ t : T, if predicate t then (1 : ℝ) else 0) * weight := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro t _
          split_ifs <;> simp
    _ = (Fintype.card {t : T // predicate t} : ℝ) * weight := by
      simp [Fintype.card_subtype]

theorem exactReverseAlicePartitionFiber_sum
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (member : coordinate ∈ side) (weight : ℝ) :
    (∑ partition : M → Bool,
      if insert coordinate
          (exactLeft coordinate partition) = side
      then weight else 0) = 2 * weight := by
  rw [exactFiniteIndicator_sum]
  rw [exactReverseAlicePartitionFiber_card
    side coordinate member]
  norm_num

theorem exactReverseBobPartitionFiber_sum
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (member : coordinate ∈ side) (weight : ℝ) :
    (∑ partition : M → Bool,
      if insert coordinate
          (exactRight coordinate partition) = side
      then weight else 0) = 2 * weight := by
  rw [exactFiniteIndicator_sum]
  rw [exactReverseBobPartitionFiber_card
    side coordinate member]
  norm_num

theorem exactReversePartition_orderCut_sum
    {M : Type*} [Fintype M] [DecidableEq M]
    (coordinate : M) (partition : M → Bool) :
    (∑ leftOrder : Equiv.Perm
        {j : M // j ∈ exactLeft coordinate partition},
      ∑ rightOrder : Equiv.Perm
        {j : M // j ∈ exactRight coordinate partition},
      ∑ leftCut : Fin
        ((exactLeft coordinate partition).card + 1),
      ∑ rightCut : Fin
        ((exactRight coordinate partition).card + 1),
        exactSeedWeight
          ⟨coordinate, partition,
            leftOrder, rightOrder, leftCut, rightCut⟩) =
      (1 / (Fintype.card M : ℝ)) *
        (1 / (Fintype.card (M → Bool) : ℝ)) := by
  simp only [exactSeedWeight,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_perm, Fintype.card_coe,
    Fintype.card_fin, Nat.cast_add, Nat.cast_one]
  have hleft :
      (0 : ℝ) < ((exactLeft coordinate partition).card + 1) := by
    exact_mod_cast Nat.zero_lt_succ _
  have hright :
      (0 : ℝ) < ((exactRight coordinate partition).card + 1) := by
    exact_mod_cast Nat.zero_lt_succ _
  have hleft_factorial :
      (0 : ℝ) <
        ((exactLeft coordinate partition).card.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have hright_factorial :
      (0 : ℝ) <
        ((exactRight coordinate partition).card.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  field_simp [hleft.ne', hright.ne',
    hleft_factorial.ne', hright_factorial.ne']

theorem exactReverseAlicePartition_orderCut_fiber_sum
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M) (partition : M → Bool) :
    (∑ leftOrder : Equiv.Perm
        {j : M // j ∈ exactLeft coordinate partition},
      ∑ rightOrder : Equiv.Perm
        {j : M // j ∈ exactRight coordinate partition},
      ∑ leftCut : Fin
        ((exactLeft coordinate partition).card + 1),
      ∑ rightCut : Fin
        ((exactRight coordinate partition).card + 1),
        if exactReverseLeftSide
              (⟨coordinate, partition,
                leftOrder, rightOrder, leftCut, rightCut⟩ :
                  ExactForwardSeed M) = side
        then exactSeedWeight
          ⟨coordinate, partition,
            leftOrder, rightOrder, leftCut, rightCut⟩
        else 0) =
      if insert coordinate
          (exactLeft coordinate partition) = side
      then (1 / (Fintype.card M : ℝ)) *
        (1 / (Fintype.card (M → Bool) : ℝ))
      else 0 := by
  by_cases hside :
      insert coordinate
        (exactLeft coordinate partition) = side
  · simpa [exactReverseLeftSide, hside] using
      exactReversePartition_orderCut_sum coordinate partition
  · simp [exactReverseLeftSide, hside]

theorem exactReverseBobPartition_orderCut_fiber_sum
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M) (partition : M → Bool) :
    (∑ leftOrder : Equiv.Perm
        {j : M // j ∈ exactLeft coordinate partition},
      ∑ rightOrder : Equiv.Perm
        {j : M // j ∈ exactRight coordinate partition},
      ∑ leftCut : Fin
        ((exactLeft coordinate partition).card + 1),
      ∑ rightCut : Fin
        ((exactRight coordinate partition).card + 1),
        if exactReverseRightSide
              (⟨coordinate, partition,
                leftOrder, rightOrder, leftCut, rightCut⟩ :
                  ExactForwardSeed M) = side
        then exactSeedWeight
          ⟨coordinate, partition,
            leftOrder, rightOrder, leftCut, rightCut⟩
        else 0) =
      if insert coordinate
          (exactRight coordinate partition) = side
      then (1 / (Fintype.card M : ℝ)) *
        (1 / (Fintype.card (M → Bool) : ℝ))
      else 0 := by
  by_cases hside :
      insert coordinate
        (exactRight coordinate partition) = side
  · simpa [exactReverseRightSide, hside] using
      exactReversePartition_orderCut_sum coordinate partition
  · simp [exactReverseRightSide, hside]

theorem exactReverseAliceSide_marginal
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) :
    groupedMass exactReverseLeftSide
        exactSeedWeight side =
      reversePartitionWeight side := by
  classical
  unfold groupedMass
  rw [Finset.sum_filter, exactForwardSeed_sum]
  simp_rw [exactReverseAlicePartition_orderCut_fiber_sum]
  have hcoordinate (coordinate : M) :
      (∑ partition : M → Bool,
        if insert coordinate
            (exactLeft coordinate partition) = side
        then (1 / (Fintype.card M : ℝ)) *
          (1 / (Fintype.card (M → Bool) : ℝ))
        else 0) =
      if coordinate ∈ side
      then 2 * ((1 / (Fintype.card M : ℝ)) *
        (1 / (Fintype.card (M → Bool) : ℝ)))
      else 0 := by
    by_cases hmember : coordinate ∈ side
    · simp only [hmember, ↓reduceIte]
      exact exactReverseAlicePartitionFiber_sum
        side coordinate hmember
        ((1 / (Fintype.card M : ℝ)) *
          (1 / (Fintype.card (M → Bool) : ℝ)))
    · simp only [hmember, ↓reduceIte]
      apply Finset.sum_eq_zero
      intro partition _
      have hnot :
          insert coordinate
            (exactLeft coordinate partition) ≠ side := by
        intro h
        apply hmember
        rw [← h]
        exact Finset.mem_insert_self _ _
      simp [hnot]
  simp_rw [hcoordinate]
  rw [exactFiniteIndicator_sum]
  simp only [Fintype.card_coe, Fintype.card_fun,
    Fintype.card_bool, reversePartitionWeight,
    fairPartitionWeight, Nat.cast_pow]
  ring

theorem exactReverseBobSide_marginal
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) :
    groupedMass exactReverseRightSide
        exactSeedWeight side =
      reversePartitionWeight side := by
  classical
  unfold groupedMass
  rw [Finset.sum_filter, exactForwardSeed_sum]
  simp_rw [exactReverseBobPartition_orderCut_fiber_sum]
  have hcoordinate (coordinate : M) :
      (∑ partition : M → Bool,
        if insert coordinate
            (exactRight coordinate partition) = side
        then (1 / (Fintype.card M : ℝ)) *
          (1 / (Fintype.card (M → Bool) : ℝ))
        else 0) =
      if coordinate ∈ side
      then 2 * ((1 / (Fintype.card M : ℝ)) *
        (1 / (Fintype.card (M → Bool) : ℝ)))
      else 0 := by
    by_cases hmember : coordinate ∈ side
    · simp only [hmember, ↓reduceIte]
      exact exactReverseBobPartitionFiber_sum
        side coordinate hmember
        ((1 / (Fintype.card M : ℝ)) *
          (1 / (Fintype.card (M → Bool) : ℝ)))
    · simp only [hmember, ↓reduceIte]
      apply Finset.sum_eq_zero
      intro partition _
      have hnot :
          insert coordinate
            (exactRight coordinate partition) ≠ side := by
        intro h
        apply hmember
        rw [← h]
        exact Finset.mem_insert_self _ _
      simp [hnot]
  simp_rw [hcoordinate]
  rw [exactFiniteIndicator_sum]
  simp only [Fintype.card_coe, Fintype.card_fun,
    Fintype.card_bool, reversePartitionWeight,
    fairPartitionWeight, Nat.cast_pow]
  ring

def exactReverseAliceConditionalSeedWeight
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (seed : ExactForwardSeed M) : ℝ :=
  if exactReverseLeftSide seed = side then
    exactSeedWeight seed / reversePartitionWeight side
  else 0

def exactReverseBobConditionalSeedWeight
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (seed : ExactForwardSeed M) : ℝ :=
  if exactReverseRightSide seed = side then
    exactSeedWeight seed / reversePartitionWeight side
  else 0

theorem exactReverseAliceConditionalSeedWeight_nonneg
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (seed : ExactForwardSeed M) :
    0 ≤ exactReverseAliceConditionalSeedWeight side seed := by
  unfold exactReverseAliceConditionalSeedWeight
  split_ifs
  · exact div_nonneg (exactSeedWeight_nonneg seed)
      (reversePartitionWeight_nonneg side)
  · exact le_rfl

theorem exactReverseBobConditionalSeedWeight_nonneg
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (seed : ExactForwardSeed M) :
    0 ≤ exactReverseBobConditionalSeedWeight side seed := by
  unfold exactReverseBobConditionalSeedWeight
  split_ifs
  · exact div_nonneg (exactSeedWeight_nonneg seed)
      (reversePartitionWeight_nonneg side)
  · exact le_rfl

theorem exactReverseAliceConditionalSeedWeight_sum
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (nonempty : side.Nonempty) :
    (∑ seed : ExactForwardSeed M,
      exactReverseAliceConditionalSeedWeight side seed) = 1 := by
  have hM : 0 < Fintype.card M :=
    Fintype.card_pos_iff.mpr ⟨nonempty.choose⟩
  have hside : 0 < reversePartitionWeight side :=
    (reversePartitionWeight_pos_iff hM side).mpr nonempty
  calc
    (∑ seed : ExactForwardSeed M,
        exactReverseAliceConditionalSeedWeight side seed) =
      (∑ seed : ExactForwardSeed M,
        if exactReverseLeftSide seed = side
        then exactSeedWeight seed else 0) /
          reversePartitionWeight side := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro seed _
            unfold exactReverseAliceConditionalSeedWeight
            split_ifs <;> simp
    _ = groupedMass exactReverseLeftSide
        exactSeedWeight side /
          reversePartitionWeight side := by
            unfold groupedMass
            rw [Finset.sum_filter]
    _ = 1 := by
      rw [exactReverseAliceSide_marginal]
      exact div_self hside.ne'

theorem exactReverseBobConditionalSeedWeight_sum
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (nonempty : side.Nonempty) :
    (∑ seed : ExactForwardSeed M,
      exactReverseBobConditionalSeedWeight side seed) = 1 := by
  have hM : 0 < Fintype.card M :=
    Fintype.card_pos_iff.mpr ⟨nonempty.choose⟩
  have hside : 0 < reversePartitionWeight side :=
    (reversePartitionWeight_pos_iff hM side).mpr nonempty
  calc
    (∑ seed : ExactForwardSeed M,
        exactReverseBobConditionalSeedWeight side seed) =
      (∑ seed : ExactForwardSeed M,
        if exactReverseRightSide seed = side
        then exactSeedWeight seed else 0) /
          reversePartitionWeight side := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro seed _
            unfold exactReverseBobConditionalSeedWeight
            split_ifs <;> simp
    _ = groupedMass exactReverseRightSide
        exactSeedWeight side /
          reversePartitionWeight side := by
            unfold groupedMass
            rw [Finset.sum_filter]
    _ = 1 := by
      rw [exactReverseBobSide_marginal]
      exact div_self hside.ne'

def exactForwardSeedLaw
    {M : Type*} [Fintype M] [DecidableEq M]
    (nonempty : 0 < Fintype.card M) :
    FiniteEventLaw (ExactForwardSeed M) where
  weight := exactSeedWeight
  weight_nonneg := exactSeedWeight_nonneg
  weight_sum := exactSeedWeight_sum nonempty

def exactReverseAliceConditionalSeedLaw
    {M : Type*} [Fintype M] [DecidableEq M]
    (nonempty : 0 < Fintype.card M)
    (side : Finset M) :
    FiniteEventLaw (ExactForwardSeed M) :=
  if hside : side.Nonempty then
    { weight := exactReverseAliceConditionalSeedWeight side
      weight_nonneg :=
        exactReverseAliceConditionalSeedWeight_nonneg side
      weight_sum :=
        exactReverseAliceConditionalSeedWeight_sum side hside }
  else exactForwardSeedLaw nonempty

def exactReverseBobConditionalSeedLaw
    {M : Type*} [Fintype M] [DecidableEq M]
    (nonempty : 0 < Fintype.card M)
    (side : Finset M) :
    FiniteEventLaw (ExactForwardSeed M) :=
  if hside : side.Nonempty then
    { weight := exactReverseBobConditionalSeedWeight side
      weight_nonneg :=
        exactReverseBobConditionalSeedWeight_nonneg side
      weight_sum :=
        exactReverseBobConditionalSeedWeight_sum side hside }
  else exactForwardSeedLaw nonempty

@[simp] theorem exactReverseAliceConditionalSeedLaw_weight
    {M : Type*} [Fintype M] [DecidableEq M]
    (nonempty : 0 < Fintype.card M)
    (side : Finset M) (hside : side.Nonempty)
    (seed : ExactForwardSeed M) :
    (exactReverseAliceConditionalSeedLaw
      nonempty side).weight seed =
      exactReverseAliceConditionalSeedWeight side seed := by
  simp [exactReverseAliceConditionalSeedLaw, hside]

@[simp] theorem exactReverseBobConditionalSeedLaw_weight
    {M : Type*} [Fintype M] [DecidableEq M]
    (nonempty : 0 < Fintype.card M)
    (side : Finset M) (hside : side.Nonempty)
    (seed : ExactForwardSeed M) :
    (exactReverseBobConditionalSeedLaw
      nonempty side).weight seed =
      exactReverseBobConditionalSeedWeight side seed := by
  simp [exactReverseBobConditionalSeedLaw, hside]

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def reweightedSeedPriorEventLaw
    {K : Type*} [Fintype K]
    (seedLaw : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n)) :
    FiniteEventLaw (K × ExactOutcome X Y A B n) where
  weight q := seedLaw.weight q.1 *
    (strategyEventLaw (G.repeat n) S).weight q.2
  weight_nonneg q := mul_nonneg
    (seedLaw.weight_nonneg q.1)
    ((strategyEventLaw (G.repeat n) S).weight_nonneg q.2)
  weight_sum := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum,
      (strategyEventLaw (G.repeat n) S).weight_sum, mul_one]
    exact seedLaw.weight_sum

def reweightedSeedWinEvent
    {K : Type*} [Fintype K]
    (G : Game X Y A B) (n : ℕ) (D : Finset (Fin n)) :
    Finset (K × ExactOutcome X Y A B n) :=
  Finset.univ.filter
    (fun q : K × ExactOutcome X Y A B n =>
      q.2 ∈ FiniteEventLaw.winEvent
        (repeatedCoordinateWin G n) D)

def reweightedSeedPosterior
    {K : Type*} [Fintype K]
    (seedLaw : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) :
    K × ExactOutcome X Y A B n → ℝ :=
  conditionedEventDistribution
    (reweightedSeedPriorEventLaw seedLaw G n S)
    (reweightedSeedWinEvent (K := K) G n D)

def reweightedSeedFlaggedProjectionLaw
    {K U Z : Type*} [Fintype K] [Fintype U] [Fintype Z]
    (seedLaw : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (projection : K × ExactOutcome X Y A B n → U)
    (flag : K × ExactOutcome X Y A B n → Z) :
    U × Z → ℝ :=
  groupedMass (fun q => (projection q, flag q))
    (reweightedSeedPosterior seedLaw G n S D)

def reweightedSeedPrefixJoint
    {K Ω V : Type*} [Fintype K] [Fintype Ω] [Fintype V]
    {h : ℕ} (seedLaw : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (projection : K × ExactOutcome X Y A B n →
      Ω × (Fin h → V)) :
    ((Ω × ConditionedAnswerFlag A B D) ×
      (Fin h → V)) → ℝ :=
  fun t => reweightedSeedFlaggedProjectionLaw
    seedLaw G n S D projection
    (fun q => repeatedConditionedAnswerFlag G n S D q.2)
    ((exactSourcePrefixFlagEquiv
      (Ω := Ω) (V := V)
      (Z := ConditionedAnswerFlag A B D)).symm t)

def reweightedSeedPrefixPrior
    {K Ω V : Type*} [Fintype K] [Fintype Ω] [Fintype V]
    {h : ℕ} (seedLaw : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (projection : K × ExactOutcome X Y A B n →
      Ω × (Fin h → V)) :
    ((Ω × ConditionedAnswerFlag A B D) ×
      (Fin h → V)) → ℝ :=
  fun t => uniformFlagReference
    (Z := ConditionedAnswerFlag A B D)
    (groupedMass projection
      (reweightedSeedPriorEventLaw seedLaw G n S).weight)
    ((exactSourcePrefixFlagEquiv
      (Ω := Ω) (V := V)
      (Z := ConditionedAnswerFlag A B D)).symm t)

def reweightedSeedPrefixEntropyIncrement
    {K Ω V : Type*} [Fintype K] [Fintype Ω] [Fintype V]
    {h : ℕ} (seedLaw : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (projection : K × ExactOutcome X Y A B n →
      Ω × (Fin h → V))
    (default : V) (k : Fin h) : ℝ :=
  finitePrefixRelativeEntropy
      (reweightedSeedPrefixJoint
        seedLaw G n S D projection)
      (reweightedSeedPrefixPrior
        seedLaw G n S D projection)
      default k.succ -
    finitePrefixRelativeEntropy
      (reweightedSeedPrefixJoint
        seedLaw G n S D projection)
      (reweightedSeedPrefixPrior
        seedLaw G n S D projection)
      default k.castSucc

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

def exactReverseSideContextWeight
    {M : Type*} [Fintype M] [DecidableEq M]
    {side : Finset M}
    (context : ExactReverseSideContext M side) : ℝ :=
  (1 / (2 : ℝ)) *
    (1 / (Fintype.card
      (Equiv.Perm {j : M // j ∈ side}) : ℝ)) *
    (1 / (Fintype.card
      (Equiv.Perm {j : M // j ∈ context.otherSide}) : ℝ)) *
    (1 / (context.otherSide.card + 1 : ℝ))

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

def exactReverseAliceMarkerCode
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    Σ side : Finset M,
      ExactReverseSideContext M side × Fin side.card :=
  ⟨exactReverseLeftSide seed,
    exactReverseAliceContext seed,
    (exactReverseAliceContext seed).sideRank
      ⟨seed.coordinate,
        exactReverseLeftSide_coordinate_mem seed⟩⟩

def exactReverseBobMarkerCode
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    Σ side : Finset M,
      ExactReverseSideContext M side × Fin side.card :=
  ⟨exactReverseRightSide seed,
    exactReverseBobContext seed,
    (exactReverseBobContext seed).sideRank
      ⟨seed.coordinate,
        exactReverseRightSide_coordinate_mem seed⟩⟩

@[simp] theorem exactReverseAliceMarkerCode_coordinate
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    (((exactReverseAliceMarkerCode seed).2.1.sideRank).symm
      (exactReverseAliceMarkerCode seed).2.2).val =
      seed.coordinate := by
  simp [exactReverseAliceMarkerCode]

@[simp] theorem exactReverseBobMarkerCode_coordinate
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    (((exactReverseBobMarkerCode seed).2.1.sideRank).symm
      (exactReverseBobMarkerCode seed).2.2).val =
      seed.coordinate := by
  simp [exactReverseBobMarkerCode]

theorem exactReverseAliceMarkerCode_coordinate_injective
    {M : Type*} [Fintype M] [DecidableEq M]
    {a b : ExactForwardSeed M}
    (same : exactReverseAliceMarkerCode a =
      exactReverseAliceMarkerCode b) :
    a.coordinate = b.coordinate := by
  have h := congrArg
    (fun t : Σ side : Finset M,
      ExactReverseSideContext M side × Fin side.card =>
      (t.2.1.sideRank.symm t.2.2).val) same
  simpa only [exactReverseAliceMarkerCode_coordinate] using h

theorem exactReverseBobMarkerCode_coordinate_injective
    {M : Type*} [Fintype M] [DecidableEq M]
    {a b : ExactForwardSeed M}
    (same : exactReverseBobMarkerCode a =
      exactReverseBobMarkerCode b) :
    a.coordinate = b.coordinate := by
  have h := congrArg
    (fun t : Σ side : Finset M,
      ExactReverseSideContext M side × Fin side.card =>
      (t.2.1.sideRank.symm t.2.2).val) same
  simpa only [exactReverseBobMarkerCode_coordinate] using h

theorem exactReverseAliceMarkerCode_partition_injective
    {M : Type*} [Fintype M] [DecidableEq M]
    {a b : ExactForwardSeed M}
    (same : exactReverseAliceMarkerCode a =
      exactReverseAliceMarkerCode b) :
    a.partition = b.partition := by
  have hcoordinate :=
    exactReverseAliceMarkerCode_coordinate_injective same
  have hside :
      exactReverseLeftSide a =
        exactReverseLeftSide b :=
    congrArg Sigma.fst same
  have hbit : a.partition a.coordinate = b.partition b.coordinate := by
    have h := congrArg
      (fun t : Σ side : Finset M,
        ExactReverseSideContext M side × Fin side.card =>
        t.2.1.ignoredBit) same
    exact h
  funext j
  by_cases hj : j = a.coordinate
  · subst j
    simpa [hcoordinate] using hbit
  · have hbj : j ≠ b.coordinate := by
      simpa [hcoordinate] using hj
    have hm :
        (a.partition j = false) ↔ (b.partition j = false) := by
      have := Finset.ext_iff.mp hside j
      simpa [exactReverseLeftSide, exactLeft,
        hj, hbj] using this
    cases ha : a.partition j <;>
      cases hb : b.partition j <;>
      simp_all

theorem exactReverseBobMarkerCode_partition_injective
    {M : Type*} [Fintype M] [DecidableEq M]
    {a b : ExactForwardSeed M}
    (same : exactReverseBobMarkerCode a =
      exactReverseBobMarkerCode b) :
    a.partition = b.partition := by
  have hcoordinate :=
    exactReverseBobMarkerCode_coordinate_injective same
  have hside :
      exactReverseRightSide a =
        exactReverseRightSide b :=
    congrArg Sigma.fst same
  have hbit : a.partition a.coordinate = b.partition b.coordinate := by
    have h := congrArg
      (fun t : Σ side : Finset M,
        ExactReverseSideContext M side × Fin side.card =>
        t.2.1.ignoredBit) same
    exact h
  funext j
  by_cases hj : j = a.coordinate
  · subst j
    simpa [hcoordinate] using hbit
  · have hbj : j ≠ b.coordinate := by
      simpa [hcoordinate] using hj
    have hm :
        (a.partition j = true) ↔ (b.partition j = true) := by
      have := Finset.ext_iff.mp hside j
      simpa [exactReverseRightSide, exactRight,
        hj, hbj] using this
    cases ha : a.partition j <;>
      cases hb : b.partition j <;>
      simp_all

theorem exactReverseAliceMarkerCode_injective
    {M : Type*} [Fintype M] [DecidableEq M] :
    Function.Injective (exactReverseAliceMarkerCode (M := M)) := by
  intro a b same
  have hcoordinate :=
    exactReverseAliceMarkerCode_coordinate_injective same
  have hpartition :=
    exactReverseAliceMarkerCode_partition_injective same
  rcases a with ⟨i, p, l, r, lc, rc⟩
  rcases b with ⟨j, q, l', r', lc', rc'⟩
  dsimp at hcoordinate hpartition
  subst j
  subst q
  simp only [exactReverseAliceMarkerCode, Sigma.mk.inj_iff] at same
  have hpair := eq_of_heq same.2
  have hctx := congrArg Prod.fst hpair
  have hmarked := congrArg Prod.snd hpair
  have hleftCut : lc = lc' := by
    apply Fin.ext
    have hv := congrArg Fin.val hmarked
    exact
      (exactReverseAliceContext_marked_rank
        ({ coordinate := i, partition := p, leftOrder := l,
           rightOrder := r, leftCut := lc, rightCut := rc } :
          ExactForwardSeed M)).symm.trans
        (hv.trans
          (exactReverseAliceContext_marked_rank
            ({ coordinate := i, partition := p, leftOrder := l',
               rightOrder := r', leftCut := lc', rightCut := rc' } :
              ExactForwardSeed M)))
  have hrightCut : rc = rc' := by
    apply Fin.ext
    have hv := congrArg
      (fun c : ExactReverseSideContext M
        (exactReverseLeftSide
          ({ coordinate := i, partition := p, leftOrder := l,
             rightOrder := r, leftCut := lc, rightCut := rc } :
            ExactForwardSeed M)) => c.otherCut.val) hctx
    exact hv
  subst lc'
  subst rc'
  change
    exactReverseAliceContext
        ({ coordinate := i, partition := p, leftOrder := l,
           rightOrder := r, leftCut := lc, rightCut := rc } :
          ExactForwardSeed M) =
      exactReverseAliceContext
        ({ coordinate := i, partition := p, leftOrder := l',
           rightOrder := r', leftCut := lc, rightCut := rc } :
          ExactForwardSeed M) at hctx
  have hsideRank := congrArg
    (fun c : ExactReverseSideContext M
      (exactReverseLeftSide
        ({ coordinate := i, partition := p, leftOrder := l,
           rightOrder := r, leftCut := lc, rightCut := rc } :
          ExactForwardSeed M)) => c.sideRank) hctx
  have hotherRankSigma := congrArg
    (fun c : ExactReverseSideContext M
      (exactReverseLeftSide
        ({ coordinate := i, partition := p, leftOrder := l,
           rightOrder := r, leftCut := lc, rightCut := rc } :
          ExactForwardSeed M)) =>
      (⟨c.otherSide, c.otherRank⟩ :
        Σ other : Finset M,
          ({j : M // j ∈ other} ≃ Fin other.card))) hctx
  simp only [exactReverseAliceContext,
    Sigma.mk.inj_iff] at hotherRankSigma
  have hotherRank := eq_of_heq hotherRankSigma.2
  have hrightSymm : r.symm = r'.symm := by
    have h := congrArg
      (fun e :
        ({j : M // j ∈ exactRight i p} ≃
          Fin (exactRight i p).card) =>
        e.trans (Finset.equivFin (exactRight i p)).symm)
      hotherRank
    simpa [exactRightRank, Equiv.trans_assoc] using h
  have hright : r = r' := Equiv.symm_bijective.injective hrightSymm
  subst r'
  have hreverseLeftRank :
      exactReverseLeftRank
          ({ coordinate := i, partition := p, leftOrder := l,
             rightOrder := r, leftCut := lc, rightCut := rc } :
            ExactForwardSeed M) =
        exactReverseLeftRank
          ({ coordinate := i, partition := p, leftOrder := l',
             rightOrder := r, leftCut := lc, rightCut := rc } :
            ExactForwardSeed M) := by
    apply Equiv.ext
    intro j
    apply Fin.ext
    have hsideVal
        (seed : ExactForwardSeed M)
        (k : {k : M // k ∈ exactReverseLeftSide seed}) :
        ((exactReverseAliceContext seed).sideRank k).val =
          (exactReverseLeftRank seed k).val := by
      simp only [exactReverseAliceContext, Equiv.trans_apply,
        finCongr_apply, Fin.val_cast]
    have h := congrArg
      (fun e => (e j).val) hsideRank
    exact
      (hsideVal
        ({ coordinate := i, partition := p, leftOrder := l,
           rightOrder := r, leftCut := lc, rightCut := rc } :
          ExactForwardSeed M) j).symm.trans
        (h.trans
          (hsideVal
            ({ coordinate := i, partition := p, leftOrder := l',
               rightOrder := r, leftCut := lc, rightCut := rc } :
              ExactForwardSeed M) j))
  have hleftRank :
      exactLeftRank
          ({ coordinate := i, partition := p, leftOrder := l,
             rightOrder := r, leftCut := lc, rightCut := rc } :
            ExactForwardSeed M) =
        exactLeftRank
          ({ coordinate := i, partition := p, leftOrder := l',
             rightOrder := r, leftCut := lc, rightCut := rc } :
            ExactForwardSeed M) := by
    apply Equiv.ext
    intro j
    let j' :
        {j : M //
          j ∈ exactLeft i p} := ⟨j.val, j.property⟩
    have h := congrArg
      (fun e => e
        ⟨j.val, Finset.mem_insert_of_mem j.property⟩)
      hreverseLeftRank
    apply Fin.succAbove_right_injective
    exact
      (exactReverseLeftRank_old
        ({ coordinate := i, partition := p, leftOrder := l,
           rightOrder := r, leftCut := lc, rightCut := rc } :
          ExactForwardSeed M) j).symm.trans
        (h.trans
          (exactReverseLeftRank_old
            ({ coordinate := i, partition := p, leftOrder := l',
               rightOrder := r, leftCut := lc, rightCut := rc } :
              ExactForwardSeed M) j'))
  have hleftSymm : l.symm = l'.symm := by
    have h := congrArg
      (fun e :
        ({j : M // j ∈ exactLeft i p} ≃
          Fin (exactLeft i p).card) =>
        e.trans (Finset.equivFin (exactLeft i p)).symm)
      hleftRank
    simpa [exactLeftRank, Equiv.trans_assoc] using h
  have hleft : l = l' := Equiv.symm_bijective.injective hleftSymm
  subst l'
  rfl

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

theorem exactReverseBobMarkerCode_injective
    {M : Type*} [Fintype M] [DecidableEq M] :
    Function.Injective (exactReverseBobMarkerCode (M := M)) := by
  intro a b same
  have hcoordinate :=
    exactReverseBobMarkerCode_coordinate_injective same
  have hpartition :=
    exactReverseBobMarkerCode_partition_injective same
  rcases a with ⟨i, p, l, r, lc, rc⟩
  rcases b with ⟨j, q, l', r', lc', rc'⟩
  dsimp at hcoordinate hpartition
  subst j
  subst q
  simp only [exactReverseBobMarkerCode, Sigma.mk.inj_iff] at same
  have hpair := eq_of_heq same.2
  have hctx := congrArg Prod.fst hpair
  have hmarked := congrArg Prod.snd hpair
  have hrightCut : rc = rc' := by
    apply Fin.ext
    have hv := congrArg Fin.val hmarked
    exact
      (exactReverseBobContext_marked_rank
        ({ coordinate := i, partition := p, leftOrder := l,
           rightOrder := r, leftCut := lc, rightCut := rc } :
          ExactForwardSeed M)).symm.trans
        (hv.trans
          (exactReverseBobContext_marked_rank
            ({ coordinate := i, partition := p, leftOrder := l',
               rightOrder := r', leftCut := lc', rightCut := rc' } :
              ExactForwardSeed M)))
  have hleftCut : lc = lc' := by
    apply Fin.ext
    have hv := congrArg
      (fun c : ExactReverseSideContext M
        (exactReverseRightSide
          ({ coordinate := i, partition := p, leftOrder := l,
             rightOrder := r, leftCut := lc, rightCut := rc } :
            ExactForwardSeed M)) => c.otherCut.val) hctx
    exact hv
  subst rc'
  subst lc'
  change
    exactReverseBobContext
        ({ coordinate := i, partition := p, leftOrder := l,
           rightOrder := r, leftCut := lc, rightCut := rc } :
          ExactForwardSeed M) =
      exactReverseBobContext
        ({ coordinate := i, partition := p, leftOrder := l',
           rightOrder := r', leftCut := lc, rightCut := rc } :
          ExactForwardSeed M) at hctx
  have hsideRank := congrArg
    (fun c : ExactReverseSideContext M
      (exactReverseRightSide
        ({ coordinate := i, partition := p, leftOrder := l,
           rightOrder := r, leftCut := lc, rightCut := rc } :
          ExactForwardSeed M)) => c.sideRank) hctx
  have hotherRankSigma := congrArg
    (fun c : ExactReverseSideContext M
      (exactReverseRightSide
        ({ coordinate := i, partition := p, leftOrder := l,
           rightOrder := r, leftCut := lc, rightCut := rc } :
          ExactForwardSeed M)) =>
      (⟨c.otherSide, c.otherRank⟩ :
        Σ other : Finset M,
          ({j : M // j ∈ other} ≃ Fin other.card))) hctx
  simp only [exactReverseBobContext,
    Sigma.mk.inj_iff] at hotherRankSigma
  have hotherRank := eq_of_heq hotherRankSigma.2
  have hleftSymm : l.symm = l'.symm := by
    have h := congrArg
      (fun e :
        ({j : M // j ∈ exactLeft i p} ≃
          Fin (exactLeft i p).card) =>
        e.trans (Finset.equivFin (exactLeft i p)).symm)
      hotherRank
    simpa [exactLeftRank, Equiv.trans_assoc] using h
  have hleft : l = l' := Equiv.symm_bijective.injective hleftSymm
  subst l'
  have hreverseRightRank :
      exactReverseRightRank
          ({ coordinate := i, partition := p, leftOrder := l,
             rightOrder := r, leftCut := lc, rightCut := rc } :
            ExactForwardSeed M) =
        exactReverseRightRank
          ({ coordinate := i, partition := p, leftOrder := l,
             rightOrder := r', leftCut := lc, rightCut := rc } :
            ExactForwardSeed M) := by
    apply Equiv.ext
    intro j
    apply Fin.ext
    have hsideVal
        (seed : ExactForwardSeed M)
        (k : {k : M // k ∈ exactReverseRightSide seed}) :
        ((exactReverseBobContext seed).sideRank k).val =
          (exactReverseRightRank seed k).val := by
      simp only [exactReverseBobContext, Equiv.trans_apply,
        finCongr_apply, Fin.val_cast]
    have h := congrArg
      (fun e => (e j).val) hsideRank
    exact
      (hsideVal
        ({ coordinate := i, partition := p, leftOrder := l,
           rightOrder := r, leftCut := lc, rightCut := rc } :
          ExactForwardSeed M) j).symm.trans
        (h.trans
          (hsideVal
            ({ coordinate := i, partition := p, leftOrder := l,
               rightOrder := r', leftCut := lc, rightCut := rc } :
              ExactForwardSeed M) j))
  have hrightRank :
      exactRightRank
          ({ coordinate := i, partition := p, leftOrder := l,
             rightOrder := r, leftCut := lc, rightCut := rc } :
            ExactForwardSeed M) =
        exactRightRank
          ({ coordinate := i, partition := p, leftOrder := l,
             rightOrder := r', leftCut := lc, rightCut := rc } :
            ExactForwardSeed M) := by
    apply Equiv.ext
    intro j
    let j' :
        {j : M //
          j ∈ exactRight i p} := ⟨j.val, j.property⟩
    have h := congrArg
      (fun e => e
        ⟨j.val, Finset.mem_insert_of_mem j.property⟩)
      hreverseRightRank
    apply Fin.succAbove_right_injective
    exact
      (exactReverseRightRank_old
        ({ coordinate := i, partition := p, leftOrder := l,
           rightOrder := r, leftCut := lc, rightCut := rc } :
          ExactForwardSeed M) j).symm.trans
        (h.trans
          (exactReverseRightRank_old
            ({ coordinate := i, partition := p, leftOrder := l,
               rightOrder := r', leftCut := lc, rightCut := rc } :
              ExactForwardSeed M) j'))
  have hrightSymm : r.symm = r'.symm := by
    have h := congrArg
      (fun e :
        ({j : M // j ∈ exactRight i p} ≃
          Fin (exactRight i p).card) =>
        e.trans (Finset.equivFin (exactRight i p)).symm)
      hrightRank
    simpa [exactRightRank, Equiv.trans_assoc] using h
  have hright : r = r' := Equiv.symm_bijective.injective hrightSymm
  subst r'
  rfl

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

def exactInsertedOldSubtypeEquiv
    {M : Type*} [DecidableEq M]
    (i : M) (side : Finset M) (not_mem : i ∉ side) :
    {j : M // j ∈ side} ≃
      {j : {j : M // j ∈ insert i side} // j.val ≠ i} where
  toFun j :=
    ⟨⟨j.val, Finset.mem_insert_of_mem j.property⟩,
      fun same => not_mem (same ▸ j.property)⟩
  invFun j :=
    ⟨j.val.val, (Finset.mem_insert.mp j.val.property).resolve_left
      j.property⟩
  left_inv j := by
    apply Subtype.ext
    rfl
  right_inv j := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

def exactDeleteMarkedRank
    {M : Type*} [DecidableEq M]
    (i : M) (side : Finset M) (not_mem : i ∉ side)
    (rank : {j : M // j ∈ insert i side} ≃
      Fin (side.card + 1))
    (cut : Fin (side.card + 1))
    (marked :
      rank ⟨i, Finset.mem_insert_self i side⟩ = cut) :
    {j : M // j ∈ side} ≃ Fin side.card :=
  (exactInsertedOldSubtypeEquiv i side not_mem).trans
    ((rank.subtypeEquiv (p := fun j => j.val ≠ i)
      (q := fun k => k ≠ cut)
      (by
        intro j
        constructor
        · intro distinct same
          apply distinct
          have hrank :
              rank j =
                rank ⟨i, Finset.mem_insert_self i side⟩ := by
            rw [marked]
            exact same
          exact congrArg Subtype.val (rank.injective hrank)
        · intro distinct same
          apply distinct
          have hj : j = ⟨i, Finset.mem_insert_self i side⟩ :=
            Subtype.ext same
          rw [hj, marked])).trans (finSuccAboveEquiv cut).symm)

theorem exactInsertedRank_deleteMarked
    {M : Type*} [DecidableEq M]
    (i : M) (side : Finset M) (not_mem : i ∉ side)
    (rank : {j : M // j ∈ insert i side} ≃
      Fin (side.card + 1))
    (cut : Fin (side.card + 1))
    (marked :
      rank ⟨i, Finset.mem_insert_self i side⟩ = cut) :
    exactInsertedRank i side not_mem
        (exactDeleteMarkedRank
          i side not_mem rank cut marked) cut = rank := by
  apply Equiv.ext
  intro j
  by_cases is_marker : j.val = i
  · have hj : j = ⟨i, Finset.mem_insert_self i side⟩ :=
      Subtype.ext is_marker
    rw [hj, exactInsertedRank_marker, marked]
  · have old_member : j.val ∈ side :=
      (Finset.mem_insert.mp j.property).resolve_left is_marker
    let old : {j : M // j ∈ side} := ⟨j.val, old_member⟩
    have hj :
        (⟨old.val, Finset.mem_insert_of_mem old.property⟩ :
          {j : M // j ∈ insert i side}) = j := by
      apply Subtype.ext
      rfl
    rw [← hj, exactInsertedRank_old]
    have distinct :
        rank ⟨old.val, Finset.mem_insert_of_mem old.property⟩ ≠ cut := by
      intro same
      apply is_marker
      have hrank :
          rank ⟨old.val, Finset.mem_insert_of_mem old.property⟩ =
            rank ⟨i, Finset.mem_insert_self i side⟩ := by
        rw [marked]
        exact same
      exact congrArg Subtype.val (rank.injective hrank)
    let deleted : {k : Fin (side.card + 1) // k ≠ cut} :=
      ⟨rank ⟨old.val, Finset.mem_insert_of_mem old.property⟩,
        distinct⟩
    have hdelete :
        exactDeleteMarkedRank
            i side not_mem rank cut marked old =
          (finSuccAboveEquiv cut).symm deleted := by
      rfl
    rw [hdelete]
    have h := (finSuccAboveEquiv cut).apply_symm_apply deleted
    exact congrArg Subtype.val h

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4200000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

def exactPermutationOfSideRank
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (rank : {j : M // j ∈ side} ≃ Fin side.card) :
    Equiv.Perm {j : M // j ∈ side} :=
  (rank.trans (Finset.equivFin side).symm).symm

theorem exactPermutationOfSideRank_rank
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (rank : {j : M // j ∈ side} ≃ Fin side.card) :
    (exactPermutationOfSideRank side rank).symm.trans
      (Finset.equivFin side) = rank := by
  apply Equiv.ext
  intro j
  simp [exactPermutationOfSideRank, Equiv.trans_apply]

theorem exactReverseAliceCanonicalPartition_otherSide
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (member : coordinate ∈ side) (ignored : Bool) :
    exactRight coordinate
        (exactReverseAliceCanonicalPartition
          side coordinate ignored) =
      Finset.univ \ side := by
  ext j
  by_cases marked : j = coordinate
  · subst j
    simp [exactRight, member]
  · by_cases belongs : j ∈ side <;>
      simp [exactRight,
        exactReverseAliceCanonicalPartition,
        marked, belongs]

theorem exactReverseBobCanonicalPartition_otherSide
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (member : coordinate ∈ side) (ignored : Bool) :
    exactLeft coordinate
        (exactReverseBobCanonicalPartition
          side coordinate ignored) =
      Finset.univ \ side := by
  ext j
  by_cases marked : j = coordinate
  · subst j
    simp [exactLeft, member]
  · by_cases belongs : j ∈ side <;>
      simp [exactLeft,
        exactReverseBobCanonicalPartition,
        marked, belongs]

theorem exactReverseAliceCanonicalPartition_card
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (member : coordinate ∈ side) (ignored : Bool) :
    (exactLeft coordinate
      (exactReverseAliceCanonicalPartition
        side coordinate ignored)).card + 1 = side.card := by
  have h := congrArg Finset.card
    (exactReverseAliceCanonicalPartition_side
      side coordinate member ignored)
  simpa [exactLeft_coordinate_not_mem] using h

theorem exactReverseBobCanonicalPartition_card
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (member : coordinate ∈ side) (ignored : Bool) :
    (exactRight coordinate
      (exactReverseBobCanonicalPartition
        side coordinate ignored)).card + 1 = side.card := by
  have h := congrArg Finset.card
    (exactReverseBobCanonicalPartition_side
      side coordinate member ignored)
  simpa [exactRight_coordinate_not_mem] using h

def exactReverseAliceMarkerDecode
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    ExactForwardSeed M := by
  classical
  let coordinate : M := (context.sideRank.symm marker).val
  have member : coordinate ∈ side :=
    (context.sideRank.symm marker).property
  let partition : M → Bool :=
    exactReverseAliceCanonicalPartition
      side coordinate context.ignoredBit
  have hside :
      insert coordinate (exactLeft coordinate partition) = side :=
    exactReverseAliceCanonicalPartition_side
      side coordinate member context.ignoredBit
  have hcard :
      (exactLeft coordinate partition).card + 1 = side.card :=
    exactReverseAliceCanonicalPartition_card
      side coordinate member context.ignoredBit
  let transportedSide :
      {j : M //
        j ∈ insert coordinate (exactLeft coordinate partition)} ≃
      {j : M // j ∈ side} :=
    Equiv.subtypeEquivRight (fun j => by rw [hside])
  let insertedRank :
      {j : M //
        j ∈ insert coordinate (exactLeft coordinate partition)} ≃
      Fin ((exactLeft coordinate partition).card + 1) :=
    transportedSide.trans
      (context.sideRank.trans (finCongr hcard.symm))
  let leftCut : Fin ((exactLeft coordinate partition).card + 1) :=
    (finCongr hcard.symm) marker
  have marked :
      insertedRank
          ⟨coordinate, Finset.mem_insert_self coordinate
            (exactLeft coordinate partition)⟩ = leftCut := by
    have transported :
        transportedSide
            ⟨coordinate, Finset.mem_insert_self coordinate
              (exactLeft coordinate partition)⟩ =
          context.sideRank.symm marker := by
      apply Subtype.ext
      rfl
    change
      (finCongr hcard.symm)
          (context.sideRank
            (transportedSide
              ⟨coordinate, Finset.mem_insert_self coordinate
                (exactLeft coordinate partition)⟩)) =
        (finCongr hcard.symm) marker
    rw [transported, Equiv.apply_symm_apply]
  let leftRank :
      {j : M // j ∈ exactLeft coordinate partition} ≃
        Fin (exactLeft coordinate partition).card :=
    exactDeleteMarkedRank coordinate
      (exactLeft coordinate partition)
      (exactLeft_coordinate_not_mem coordinate partition)
      insertedRank leftCut marked
  have hother :
      exactRight coordinate partition = context.otherSide := by
    calc
      exactRight coordinate partition =
          Finset.univ \ side :=
        exactReverseAliceCanonicalPartition_otherSide
          side coordinate member context.ignoredBit
      _ = context.otherSide := context.otherSide_eq_complement.symm
  let transportedOther :
      {j : M // j ∈ exactRight coordinate partition} ≃
        {j : M // j ∈ context.otherSide} :=
    Equiv.subtypeEquivRight (fun j => by rw [hother])
  let rightRank :
      {j : M // j ∈ exactRight coordinate partition} ≃
        Fin (exactRight coordinate partition).card :=
    transportedOther.trans
      (context.otherRank.trans
        (finCongr (congrArg Finset.card hother).symm))
  exact
    { coordinate := coordinate
      partition := partition
      leftOrder := exactPermutationOfSideRank
        (exactLeft coordinate partition) leftRank
      rightOrder := exactPermutationOfSideRank
        (exactRight coordinate partition) rightRank
      leftCut := leftCut
      rightCut :=
        (finCongr
          (congrArg (fun s : Finset M => s.card + 1) hother).symm)
          context.otherCut }

def exactReverseBobMarkerDecode
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    ExactForwardSeed M := by
  classical
  let coordinate : M := (context.sideRank.symm marker).val
  have member : coordinate ∈ side :=
    (context.sideRank.symm marker).property
  let partition : M → Bool :=
    exactReverseBobCanonicalPartition
      side coordinate context.ignoredBit
  have hside :
      insert coordinate (exactRight coordinate partition) = side :=
    exactReverseBobCanonicalPartition_side
      side coordinate member context.ignoredBit
  have hcard :
      (exactRight coordinate partition).card + 1 = side.card :=
    exactReverseBobCanonicalPartition_card
      side coordinate member context.ignoredBit
  let transportedSide :
      {j : M //
        j ∈ insert coordinate (exactRight coordinate partition)} ≃
      {j : M // j ∈ side} :=
    Equiv.subtypeEquivRight (fun j => by rw [hside])
  let insertedRank :
      {j : M //
        j ∈ insert coordinate (exactRight coordinate partition)} ≃
      Fin ((exactRight coordinate partition).card + 1) :=
    transportedSide.trans
      (context.sideRank.trans (finCongr hcard.symm))
  let rightCut : Fin ((exactRight coordinate partition).card + 1) :=
    (finCongr hcard.symm) marker
  have marked :
      insertedRank
          ⟨coordinate, Finset.mem_insert_self coordinate
            (exactRight coordinate partition)⟩ = rightCut := by
    have transported :
        transportedSide
            ⟨coordinate, Finset.mem_insert_self coordinate
              (exactRight coordinate partition)⟩ =
          context.sideRank.symm marker := by
      apply Subtype.ext
      rfl
    change
      (finCongr hcard.symm)
          (context.sideRank
            (transportedSide
              ⟨coordinate, Finset.mem_insert_self coordinate
                (exactRight coordinate partition)⟩)) =
        (finCongr hcard.symm) marker
    rw [transported, Equiv.apply_symm_apply]
  let rightRank :
      {j : M // j ∈ exactRight coordinate partition} ≃
        Fin (exactRight coordinate partition).card :=
    exactDeleteMarkedRank coordinate
      (exactRight coordinate partition)
      (exactRight_coordinate_not_mem coordinate partition)
      insertedRank rightCut marked
  have hother :
      exactLeft coordinate partition = context.otherSide := by
    calc
      exactLeft coordinate partition =
          Finset.univ \ side :=
        exactReverseBobCanonicalPartition_otherSide
          side coordinate member context.ignoredBit
      _ = context.otherSide := context.otherSide_eq_complement.symm
  let transportedOther :
      {j : M // j ∈ exactLeft coordinate partition} ≃
        {j : M // j ∈ context.otherSide} :=
    Equiv.subtypeEquivRight (fun j => by rw [hother])
  let leftRank :
      {j : M // j ∈ exactLeft coordinate partition} ≃
        Fin (exactLeft coordinate partition).card :=
    transportedOther.trans
      (context.otherRank.trans
        (finCongr (congrArg Finset.card hother).symm))
  exact
    { coordinate := coordinate
      partition := partition
      leftOrder := exactPermutationOfSideRank
        (exactLeft coordinate partition) leftRank
      rightOrder := exactPermutationOfSideRank
        (exactRight coordinate partition) rightRank
      leftCut :=
        (finCongr
          (congrArg (fun s : Finset M => s.card + 1) hother).symm)
          context.otherCut
      rightCut := rightCut }

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

@[simp] theorem exactReverseAliceMarkerDecode_coordinate
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    (exactReverseAliceMarkerDecode
      side context marker).coordinate =
      (context.sideRank.symm marker).val := by
  rfl

@[simp] theorem exactReverseBobMarkerDecode_coordinate
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    (exactReverseBobMarkerDecode
      side context marker).coordinate =
      (context.sideRank.symm marker).val := by
  rfl

@[simp] theorem exactReverseAliceMarkerDecode_side
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    exactReverseLeftSide
        (exactReverseAliceMarkerDecode
          side context marker) = side := by
  change
    insert (context.sideRank.symm marker).val
      (exactLeft (context.sideRank.symm marker).val
        (exactReverseAliceCanonicalPartition
          side (context.sideRank.symm marker).val
          context.ignoredBit)) = side
  exact exactReverseAliceCanonicalPartition_side
    side (context.sideRank.symm marker).val
    (context.sideRank.symm marker).property context.ignoredBit

@[simp] theorem exactReverseBobMarkerDecode_side
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    exactReverseRightSide
        (exactReverseBobMarkerDecode
          side context marker) = side := by
  change
    insert (context.sideRank.symm marker).val
      (exactRight (context.sideRank.symm marker).val
        (exactReverseBobCanonicalPartition
          side (context.sideRank.symm marker).val
          context.ignoredBit)) = side
  exact exactReverseBobCanonicalPartition_side
    side (context.sideRank.symm marker).val
    (context.sideRank.symm marker).property context.ignoredBit

@[simp] theorem exactReverseAliceMarkerDecode_ignoredBit
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    (exactReverseAliceMarkerDecode
      side context marker).partition
      (exactReverseAliceMarkerDecode
        side context marker).coordinate = context.ignoredBit := by
  simp [exactReverseAliceMarkerDecode,
    exactReverseAliceCanonicalPartition]

@[simp] theorem exactReverseBobMarkerDecode_ignoredBit
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    (exactReverseBobMarkerDecode
      side context marker).partition
      (exactReverseBobMarkerDecode
        side context marker).coordinate = context.ignoredBit := by
  simp [exactReverseBobMarkerDecode,
    exactReverseBobCanonicalPartition]

theorem exactSigmaFinCutTransport
    {M : Type*} [DecidableEq M]
    (source target : Finset M) (same : source = target)
    (cut : Fin (target.card + 1)) :
    (⟨source,
        (finCongr
          (congrArg (fun side : Finset M => side.card + 1) same).symm)
          cut⟩ : Σ side : Finset M, Fin (side.card + 1)) =
      ⟨target, cut⟩ := by
  subst target
  simp

theorem exactSigmaSideRankTransport
    {M : Type*} [DecidableEq M]
    (source target : Finset M) (same : source = target)
    (rank : {j : M // j ∈ target} ≃ Fin target.card) :
    (⟨source,
        (Equiv.subtypeEquivRight (fun j => by rw [same])).trans
          (rank.trans (finCongr (congrArg Finset.card same).symm))⟩ :
        Σ side : Finset M, ({j : M // j ∈ side} ≃ Fin side.card)) =
      ⟨target, rank⟩ := by
  subst target
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Equiv.ext
    intro j
    simp [Equiv.trans_apply]
    apply Subtype.ext
    rfl

theorem exactReverseAliceMarkerDecode_otherRank
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    (⟨exactRight
        (exactReverseAliceMarkerDecode
          side context marker).coordinate
        (exactReverseAliceMarkerDecode
          side context marker).partition,
      exactRightRank
        (exactReverseAliceMarkerDecode
          side context marker)⟩ :
        Σ other : Finset M,
          ({j : M // j ∈ other} ≃ Fin other.card)) =
      ⟨context.otherSide, context.otherRank⟩ := by
  classical
  let coordinate := (context.sideRank.symm marker).val
  let partition :=
    exactReverseAliceCanonicalPartition
      side coordinate context.ignoredBit
  have other : exactRight coordinate partition =
      context.otherSide := by
    exact (exactReverseAliceCanonicalPartition_otherSide
      side coordinate (context.sideRank.symm marker).property
      context.ignoredBit).trans
        context.otherSide_eq_complement.symm
  have transported := exactSigmaSideRankTransport
    (exactRight coordinate partition)
    context.otherSide other context.otherRank
  simpa only [exactReverseAliceMarkerDecode,
    exactRightRank,
    exactPermutationOfSideRank_rank] using transported

theorem exactReverseAliceMarkerDecode_otherCut
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    (⟨exactRight
        (exactReverseAliceMarkerDecode
          side context marker).coordinate
        (exactReverseAliceMarkerDecode
          side context marker).partition,
      (exactReverseAliceMarkerDecode
        side context marker).rightCut⟩ :
        Σ other : Finset M, Fin (other.card + 1)) =
      ⟨context.otherSide, context.otherCut⟩ := by
  classical
  let coordinate := (context.sideRank.symm marker).val
  let partition :=
    exactReverseAliceCanonicalPartition
      side coordinate context.ignoredBit
  have other : exactRight coordinate partition =
      context.otherSide := by
    exact (exactReverseAliceCanonicalPartition_otherSide
      side coordinate (context.sideRank.symm marker).property
      context.ignoredBit).trans
        context.otherSide_eq_complement.symm
  have transported := exactSigmaFinCutTransport
    (exactRight coordinate partition)
    context.otherSide other context.otherCut
  simpa only [exactReverseAliceMarkerDecode] using transported

theorem exactReverseAliceMarkerDecode_sideRank
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    (⟨exactReverseLeftSide
        (exactReverseAliceMarkerDecode
          side context marker),
      (exactReverseAliceContext
        (exactReverseAliceMarkerDecode
          side context marker)).sideRank⟩ :
        Σ actualSide : Finset M,
          ({j : M // j ∈ actualSide} ≃ Fin actualSide.card)) =
      ⟨side, context.sideRank⟩ := by
  classical
  let coordinate := (context.sideRank.symm marker).val
  let partition :=
    exactReverseAliceCanonicalPartition
      side coordinate context.ignoredBit
  have actual : insert coordinate
      (exactLeft coordinate partition) = side :=
    exactReverseAliceCanonicalPartition_side
      side coordinate (context.sideRank.symm marker).property
      context.ignoredBit
  let transportedRank :
      {j : M //
        j ∈ insert coordinate (exactLeft coordinate partition)} ≃
        Fin (insert coordinate (exactLeft coordinate partition)).card :=
    (Equiv.subtypeEquivRight (fun j => by rw [actual])).trans
      (context.sideRank.trans
        (finCongr (congrArg Finset.card actual).symm))
  have transported :
      (⟨insert coordinate (exactLeft coordinate partition),
        transportedRank⟩ :
          Σ actualSide : Finset M,
            ({j : M // j ∈ actualSide} ≃ Fin actualSide.card)) =
        ⟨side, context.sideRank⟩ :=
    exactSigmaSideRankTransport
      (insert coordinate (exactLeft coordinate partition))
      side actual context.sideRank
  calc
    (⟨exactReverseLeftSide
        (exactReverseAliceMarkerDecode side context marker),
      (exactReverseAliceContext
        (exactReverseAliceMarkerDecode
          side context marker)).sideRank⟩ :
        Σ actualSide : Finset M,
          ({j : M // j ∈ actualSide} ≃ Fin actualSide.card)) =
        ⟨insert coordinate (exactLeft coordinate partition),
          transportedRank⟩ := by
            apply Sigma.ext
            · change
                insert (context.sideRank.symm marker).val
                    (exactLeft (context.sideRank.symm marker).val
                      (exactReverseAliceCanonicalPartition
                        side (context.sideRank.symm marker).val
                        context.ignoredBit)) =
                  insert coordinate (exactLeft coordinate partition)
              rfl
            · apply heq_of_eq
              apply Equiv.ext
              intro j
              apply Fin.ext
              simp [coordinate, partition, transportedRank,
                exactReverseAliceMarkerDecode,
                exactReverseAliceContext,
                exactReverseLeftSide,
                exactReverseLeftRank,
                exactLeftRank,
                exactPermutationOfSideRank_rank,
                exactInsertedRank_deleteMarked,
                Equiv.trans_assoc, Equiv.trans_apply,
                finCongr_apply, Fin.val_cast]
    _ = ⟨side, context.sideRank⟩ := transported

theorem exactReverseAliceMarkerDecode_rightInverse
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    exactReverseAliceMarkerCode
        (exactReverseAliceMarkerDecode
          side context marker) =
      ⟨side, context, marker⟩ := by
  classical
  generalize decoded :
    exactReverseAliceMarkerDecode side context marker = seed
  have sameSide : exactReverseLeftSide seed = side := by
    rw [← decoded]
    exact exactReverseAliceMarkerDecode_side
      side context marker
  subst side
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    change
      (exactReverseAliceContext seed,
        (exactReverseAliceContext seed).sideRank
          ⟨seed.coordinate,
            exactReverseLeftSide_coordinate_mem seed⟩) =
        (context, marker)
    have sameContext : exactReverseAliceContext seed = context := by
      cases context with
      | mk otherSide sideRank otherRank otherCut ignored complement =>
        simp only [exactReverseAliceContext,
          ExactReverseSideContext.mk.injEq]
        let reverseContext : ExactReverseSideContext M
            (exactReverseLeftSide seed) :=
          { otherSide := otherSide
            sideRank := sideRank
            otherRank := otherRank
            otherCut := otherCut
            ignoredBit := ignored
            otherSide_eq_complement := complement }
        have exactSideRank :=
          exactReverseAliceMarkerDecode_sideRank
            (exactReverseLeftSide seed)
            reverseContext marker
        have exactOtherRank :=
          exactReverseAliceMarkerDecode_otherRank
            (exactReverseLeftSide seed)
            reverseContext marker
        have exactOtherCut :=
          exactReverseAliceMarkerDecode_otherCut
            (exactReverseLeftSide seed)
            reverseContext marker
        change
          exactReverseAliceMarkerDecode
              (exactReverseLeftSide seed)
              reverseContext marker = seed at decoded
        rw [decoded] at exactSideRank exactOtherRank exactOtherCut
        refine ⟨(exactReverseLeftSide_complement seed).trans
            complement.symm, ?_, ?_, ?_, ?_⟩
        · exact eq_of_heq (Sigma.mk.inj exactSideRank).2
        · exact (Sigma.mk.inj exactOtherRank).2
        · exact (Sigma.mk.inj exactOtherCut).2
        · have exactIgnored := congrArg
            (fun original : ExactForwardSeed M =>
              original.partition original.coordinate) decoded
          simpa only
            [exactReverseAliceMarkerDecode_ignoredBit]
              using exactIgnored.symm
    apply Prod.ext
    · exact sameContext
    · rw [sameContext]
      apply context.sideRank.symm.injective
      change
        context.sideRank.symm
            (context.sideRank ⟨seed.coordinate, _⟩) =
          context.sideRank.symm marker
      rw [Equiv.symm_apply_apply]
      apply Subtype.ext
      have coordinate := congrArg
        (fun original : ExactForwardSeed M => original.coordinate)
        decoded
      simpa only [exactReverseAliceMarkerDecode_coordinate]
        using coordinate.symm

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

theorem exactReverseBobMarkerDecode_otherRank
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    (⟨exactLeft
        (exactReverseBobMarkerDecode
          side context marker).coordinate
        (exactReverseBobMarkerDecode
          side context marker).partition,
      exactLeftRank
        (exactReverseBobMarkerDecode
          side context marker)⟩ :
        Σ other : Finset M,
          ({j : M // j ∈ other} ≃ Fin other.card)) =
      ⟨context.otherSide, context.otherRank⟩ := by
  classical
  let coordinate := (context.sideRank.symm marker).val
  let partition :=
    exactReverseBobCanonicalPartition
      side coordinate context.ignoredBit
  have other : exactLeft coordinate partition =
      context.otherSide := by
    exact (exactReverseBobCanonicalPartition_otherSide
      side coordinate (context.sideRank.symm marker).property
      context.ignoredBit).trans
        context.otherSide_eq_complement.symm
  have transported := exactSigmaSideRankTransport
    (exactLeft coordinate partition)
    context.otherSide other context.otherRank
  simpa only [exactReverseBobMarkerDecode,
    exactLeftRank,
    exactPermutationOfSideRank_rank] using transported

theorem exactReverseBobMarkerDecode_otherCut
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    (⟨exactLeft
        (exactReverseBobMarkerDecode
          side context marker).coordinate
        (exactReverseBobMarkerDecode
          side context marker).partition,
      (exactReverseBobMarkerDecode
        side context marker).leftCut⟩ :
        Σ other : Finset M, Fin (other.card + 1)) =
      ⟨context.otherSide, context.otherCut⟩ := by
  classical
  let coordinate := (context.sideRank.symm marker).val
  let partition :=
    exactReverseBobCanonicalPartition
      side coordinate context.ignoredBit
  have other : exactLeft coordinate partition =
      context.otherSide := by
    exact (exactReverseBobCanonicalPartition_otherSide
      side coordinate (context.sideRank.symm marker).property
      context.ignoredBit).trans
        context.otherSide_eq_complement.symm
  have transported := exactSigmaFinCutTransport
    (exactLeft coordinate partition)
    context.otherSide other context.otherCut
  simpa only [exactReverseBobMarkerDecode] using transported

theorem exactReverseBobMarkerDecode_sideRank
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    (⟨exactReverseRightSide
        (exactReverseBobMarkerDecode
          side context marker),
      (exactReverseBobContext
        (exactReverseBobMarkerDecode
          side context marker)).sideRank⟩ :
        Σ actualSide : Finset M,
          ({j : M // j ∈ actualSide} ≃ Fin actualSide.card)) =
      ⟨side, context.sideRank⟩ := by
  classical
  let coordinate := (context.sideRank.symm marker).val
  let partition :=
    exactReverseBobCanonicalPartition
      side coordinate context.ignoredBit
  have actual : insert coordinate
      (exactRight coordinate partition) = side :=
    exactReverseBobCanonicalPartition_side
      side coordinate (context.sideRank.symm marker).property
      context.ignoredBit
  let transportedRank :
      {j : M //
        j ∈ insert coordinate (exactRight coordinate partition)} ≃
        Fin (insert coordinate (exactRight coordinate partition)).card :=
    (Equiv.subtypeEquivRight (fun j => by rw [actual])).trans
      (context.sideRank.trans
        (finCongr (congrArg Finset.card actual).symm))
  have transported :
      (⟨insert coordinate (exactRight coordinate partition),
        transportedRank⟩ :
          Σ actualSide : Finset M,
            ({j : M // j ∈ actualSide} ≃ Fin actualSide.card)) =
        ⟨side, context.sideRank⟩ :=
    exactSigmaSideRankTransport
      (insert coordinate (exactRight coordinate partition))
      side actual context.sideRank
  calc
    (⟨exactReverseRightSide
        (exactReverseBobMarkerDecode side context marker),
      (exactReverseBobContext
        (exactReverseBobMarkerDecode
          side context marker)).sideRank⟩ :
        Σ actualSide : Finset M,
          ({j : M // j ∈ actualSide} ≃ Fin actualSide.card)) =
        ⟨insert coordinate (exactRight coordinate partition),
          transportedRank⟩ := by
            apply Sigma.ext
            · change
                insert (context.sideRank.symm marker).val
                    (exactRight (context.sideRank.symm marker).val
                      (exactReverseBobCanonicalPartition
                        side (context.sideRank.symm marker).val
                        context.ignoredBit)) =
                  insert coordinate (exactRight coordinate partition)
              rfl
            · apply heq_of_eq
              apply Equiv.ext
              intro j
              apply Fin.ext
              simp [coordinate, partition, transportedRank,
                exactReverseBobMarkerDecode,
                exactReverseBobContext,
                exactReverseRightSide,
                exactReverseRightRank,
                exactRightRank,
                exactPermutationOfSideRank_rank,
                exactInsertedRank_deleteMarked,
                Equiv.trans_assoc, Equiv.trans_apply,
                finCongr_apply, Fin.val_cast]
    _ = ⟨side, context.sideRank⟩ := transported

theorem exactReverseBobMarkerDecode_rightInverse
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    exactReverseBobMarkerCode
        (exactReverseBobMarkerDecode
          side context marker) =
      ⟨side, context, marker⟩ := by
  classical
  generalize decoded :
    exactReverseBobMarkerDecode side context marker = seed
  have sameSide : exactReverseRightSide seed = side := by
    rw [← decoded]
    exact exactReverseBobMarkerDecode_side
      side context marker
  subst side
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    change
      (exactReverseBobContext seed,
        (exactReverseBobContext seed).sideRank
          ⟨seed.coordinate,
            exactReverseRightSide_coordinate_mem seed⟩) =
        (context, marker)
    have sameContext : exactReverseBobContext seed = context := by
      cases context with
      | mk otherSide sideRank otherRank otherCut ignored complement =>
        simp only [exactReverseBobContext,
          ExactReverseSideContext.mk.injEq]
        let reverseContext : ExactReverseSideContext M
            (exactReverseRightSide seed) :=
          { otherSide := otherSide
            sideRank := sideRank
            otherRank := otherRank
            otherCut := otherCut
            ignoredBit := ignored
            otherSide_eq_complement := complement }
        have exactSideRank :=
          exactReverseBobMarkerDecode_sideRank
            (exactReverseRightSide seed)
            reverseContext marker
        have exactOtherRank :=
          exactReverseBobMarkerDecode_otherRank
            (exactReverseRightSide seed)
            reverseContext marker
        have exactOtherCut :=
          exactReverseBobMarkerDecode_otherCut
            (exactReverseRightSide seed)
            reverseContext marker
        change
          exactReverseBobMarkerDecode
              (exactReverseRightSide seed)
              reverseContext marker = seed at decoded
        rw [decoded] at exactSideRank exactOtherRank exactOtherCut
        refine ⟨(exactReverseRightSide_complement seed).trans
            complement.symm, ?_, ?_, ?_, ?_⟩
        · exact eq_of_heq (Sigma.mk.inj exactSideRank).2
        · exact (Sigma.mk.inj exactOtherRank).2
        · exact (Sigma.mk.inj exactOtherCut).2
        · have exactIgnored := congrArg
            (fun original : ExactForwardSeed M =>
              original.partition original.coordinate) decoded
          simpa only
            [exactReverseBobMarkerDecode_ignoredBit]
              using exactIgnored.symm
    apply Prod.ext
    · exact sameContext
    · rw [sameContext]
      apply context.sideRank.symm.injective
      change
        context.sideRank.symm
            (context.sideRank ⟨seed.coordinate, _⟩) =
          context.sideRank.symm marker
      rw [Equiv.symm_apply_apply]
      apply Subtype.ext
      have coordinate := congrArg
        (fun original : ExactForwardSeed M => original.coordinate)
        decoded
      simpa only [exactReverseBobMarkerDecode_coordinate]
        using coordinate.symm

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

def exactReverseAliceWeightedMarkerEquiv
    {M : Type*} [Fintype M] [DecidableEq M] :
    ExactForwardSeed M ≃
      (Σ side : Finset M,
        ExactReverseSideContext M side × Fin side.card) where
  toFun := exactReverseAliceMarkerCode
  invFun marker :=
    exactReverseAliceMarkerDecode
      marker.1 marker.2.1 marker.2.2
  left_inv seed := by
    apply exactReverseAliceMarkerCode_injective
    exact exactReverseAliceMarkerDecode_rightInverse
      (exactReverseAliceMarkerCode seed).1
      (exactReverseAliceMarkerCode seed).2.1
      (exactReverseAliceMarkerCode seed).2.2
  right_inv marker := by
    rcases marker with ⟨side, context, position⟩
    exact exactReverseAliceMarkerDecode_rightInverse
      side context position

def exactReverseBobWeightedMarkerEquiv
    {M : Type*} [Fintype M] [DecidableEq M] :
    ExactForwardSeed M ≃
      (Σ side : Finset M,
        ExactReverseSideContext M side × Fin side.card) where
  toFun := exactReverseBobMarkerCode
  invFun marker :=
    exactReverseBobMarkerDecode
      marker.1 marker.2.1 marker.2.2
  left_inv seed := by
    apply exactReverseBobMarkerCode_injective
    exact exactReverseBobMarkerDecode_rightInverse
      (exactReverseBobMarkerCode seed).1
      (exactReverseBobMarkerCode seed).2.1
      (exactReverseBobMarkerCode seed).2.2
  right_inv marker := by
    rcases marker with ⟨side, context, position⟩
    exact exactReverseBobMarkerDecode_rightInverse
      side context position

end

noncomputable section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
set_option maxRecDepth 2048

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def exactReverseAliceFilterOperatorMarkerEntropy
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) : ℝ :=
  let seed := exactReverseBobMarkerDecode side context marker
  ∑ history : ExactRevealHistory X Y D seed,
  ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
  ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
    if exactHistoryAccepted G n D
        ⟨seed, history, aliceAnswer, bobAnswer⟩ then
      exactRevealMass G n D seed history *
        exactFairAliceHistoryEntropyIncrement G n S D
          ⟨seed, history, aliceAnswer, bobAnswer⟩
    else 0

def exactReverseBobFilterOperatorMarkerEntropy
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) : ℝ :=
  let seed := exactReverseAliceMarkerDecode side context marker
  ∑ history : ExactRevealHistory X Y D seed,
  ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
  ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
    if exactHistoryAccepted G n D
        ⟨seed, history, aliceAnswer, bobAnswer⟩ then
      exactRevealMass G n D seed history *
        exactFairBobHistoryEntropyIncrement G n S D
          ⟨seed, history, aliceAnswer, bobAnswer⟩
    else 0

end

noncomputable section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option maxRecDepth 2048

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def exactFairAliceHistoryHighOperatorPotential
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) : ℝ :=
  ∑ y : Y, G.marginalY y *
    bornTracePairing S.state.matrix
      (∑ x : X, G.conditionalXGivenY y x •
        cfc (fun z : ℝ => z * Real.log z)
          (exactAliceQuestionFilter
            G n S D r.seed r.history r.aliceAnswer x))
      (exactBobQuestionFilter
        G n S D r.seed r.history r.bobAnswer y)

def exactFairAliceHistoryLowOperatorPotential
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) : ℝ :=
  ∑ y : Y, G.marginalY y *
    bornTracePairing S.state.matrix
      (cfc (fun z : ℝ => z * Real.log z)
        (exactAliceMeanFilter
          G n S D r.seed r.history r.aliceAnswer y))
      (exactBobQuestionFilter
        G n S D r.seed r.history r.bobAnswer y)

def exactFairBobHistoryHighOperatorPotential
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) : ℝ :=
  ∑ x : X, G.marginalX x *
    bornTracePairing S.state.matrix
      (exactAliceQuestionFilter
        G n S D r.seed r.history r.aliceAnswer x)
      (∑ y : Y, G.conditionalYGivenX x y •
        cfc (fun z : ℝ => z * Real.log z)
          (exactBobQuestionFilter
            G n S D r.seed r.history r.bobAnswer y))

def exactFairBobHistoryLowOperatorPotential
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) : ℝ :=
  ∑ x : X, G.marginalX x *
    bornTracePairing S.state.matrix
      (exactAliceQuestionFilter
        G n S D r.seed r.history r.aliceAnswer x)
      (cfc (fun z : ℝ => z * Real.log z)
        (exactBobMeanFilter
          G n S D r.seed r.history r.bobAnswer x))

def exactReverseAliceFilterHighOperatorPotential
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) : ℝ :=
  let seed := exactReverseBobMarkerDecode side context marker
  ∑ history : ExactRevealHistory X Y D seed,
  ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
  ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
    if exactHistoryAccepted G n D
        ⟨seed, history, aliceAnswer, bobAnswer⟩ then
      exactRevealMass G n D seed history *
        exactFairAliceHistoryHighOperatorPotential G n S D
          ⟨seed, history, aliceAnswer, bobAnswer⟩
    else 0

def exactReverseAliceFilterLowOperatorPotential
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) : ℝ :=
  let seed := exactReverseBobMarkerDecode side context marker
  ∑ history : ExactRevealHistory X Y D seed,
  ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
  ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
    if exactHistoryAccepted G n D
        ⟨seed, history, aliceAnswer, bobAnswer⟩ then
      exactRevealMass G n D seed history *
        exactFairAliceHistoryLowOperatorPotential G n S D
          ⟨seed, history, aliceAnswer, bobAnswer⟩
    else 0

def exactReverseBobFilterHighOperatorPotential
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) : ℝ :=
  let seed := exactReverseAliceMarkerDecode side context marker
  ∑ history : ExactRevealHistory X Y D seed,
  ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
  ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
    if exactHistoryAccepted G n D
        ⟨seed, history, aliceAnswer, bobAnswer⟩ then
      exactRevealMass G n D seed history *
        exactFairBobHistoryHighOperatorPotential G n S D
          ⟨seed, history, aliceAnswer, bobAnswer⟩
    else 0

def exactReverseBobFilterLowOperatorPotential
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) : ℝ :=
  let seed := exactReverseAliceMarkerDecode side context marker
  ∑ history : ExactRevealHistory X Y D seed,
  ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
  ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
    if exactHistoryAccepted G n D
        ⟨seed, history, aliceAnswer, bobAnswer⟩ then
      exactRevealMass G n D seed history *
        exactFairBobHistoryLowOperatorPotential G n S D
          ⟨seed, history, aliceAnswer, bobAnswer⟩
    else 0

end

noncomputable section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
set_option maxRecDepth 2048

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def exactFairQuestionTailWeight
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y) : ℝ :=
  ∑ tailX : {j : Fin n // j ≠ seed.coordinate.val} → X,
  ∑ tailY : {j : Fin n // j ≠ seed.coordinate.val} → Y,
    if exactRevealCode D seed
       ((Equiv.funSplitAt seed.coordinate.val X).symm (x, tailX),
        (Equiv.funSplitAt seed.coordinate.val Y).symm (y, tailY)) =
          history
    then ∏ j : {j : Fin n // j ≠ seed.coordinate.val},
      G.questionWeight (tailX j) (tailY j)
    else 0

end

noncomputable section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def exactFairConditionedAnswerBornMass
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y) : ℝ :=
  ∑ xs : Fin n → X, ∑ ys : Fin n → Y,
    exactFiberQuestionWeight
      G n D r.seed r.history x y xs ys *
      bornTracePairing S.state.matrix
        (conditionedAliceEffect G n S D r.aliceAnswer xs)
        (conditionedBobEffect G n S D r.bobAnswer ys)

end

noncomputable section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option maxRecDepth 2048

open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def exactFairFullOutcomeBornMass
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y) : ℝ :=
  ∑ o : ExactOutcome X Y A B n,
    if exactLocallySampleableCode D (r.seed, o) =
      (r.seed.coordinate, x, y, r)
    then (strategyEventLaw (G.repeat n) S).weight o
    else 0

end

end QuantumParallelRepetition

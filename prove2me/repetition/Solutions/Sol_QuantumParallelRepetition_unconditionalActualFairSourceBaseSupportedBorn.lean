/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Repetition/TenProofs/QuantumParallelRepetition/Part08.lean (solution of QuantumParallelRepetition.unconditionalActualFairSourceBaseSupportedBorn);
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
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
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
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.NoZeroSMulDivisors.Basic
import Mathlib.Algebra.NoZeroSMulDivisors.Defs
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
import Mathlib.Algebra.Ring.Rat
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
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Countable.Defs
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Holder
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.FinEnum
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
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.AtTopBot.Group
import Mathlib.Order.Filter.Basic
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
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Monoid
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
import Mathlib.Topology.Instances.Rat
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
import Definitions.Def_MIPRE_Background_Repetition_TenProofs_QuantumParallelRepetition_Part07
import Definitions.Def_MIPRE_Background_Repetition_TenProofs_QuantumParallelRepetition_Part08
import Theorems.Thm_QuantumParallelRepetition_directDSVActualReindexedWinningEffect_quadratic
import Theorems.Thm_QuantumParallelRepetition_exactAliceConditionalMatrix_eq_joint
import Theorems.Thm_QuantumParallelRepetition_exactBobConditionalMatrix_eq_joint
import Theorems.Thm_QuantumParallelRepetition_exactFairConditionedAnswerBornMass_eq_fiber_norm
import Theorems.Thm_QuantumParallelRepetition_exactFairFullOutcomeBornMass_eq_conditioned
import Theorems.Thm_QuantumParallelRepetition_exactFairWinningOutcomeBornMass_eq_fiber_conditional
import Theorems.Thm_QuantumParallelRepetition_exactFiberQuestionMass_eq_jointQuestionMass
import Theorems.Thm_QuantumParallelRepetition_exactJointQuestionMass_eq_reveal_mul_question
import Theorems.Thm_QuantumParallelRepetition_exactLocallySampleableLaw_coordinate_eq_of_ne_zero
import Theorems.Thm_QuantumParallelRepetition_exactLocallySampleableLaw_eq_fair_born
import Theorems.Thm_QuantumParallelRepetition_exactLocallySampleableLaw_fiber_ne_zero_of_ne_zero
import Theorems.Thm_QuantumParallelRepetition_exactLocallySampleableLaw_psi_ne_zero_of_ne_zero
import Theorems.Thm_QuantumParallelRepetition_exactLocallySampleableLaw_zero_of_not_accepted
import Theorems.Thm_QuantumParallelRepetition_exactSourceAcceptedCoordinateMass_eq_seeded_fair_born
import Theorems.Thm_QuantumParallelRepetition_exactSourceGlobalCatalystWinningEffect_tensor_quadratic
import Theorems.Thm_QuantumParallelRepetition_matrixQuadraticExpectation_injective
import Theorems.Thm_QuantumParallelRepetition_rectangular_matrix_mulVec_norm_sq
import Theorems.Thm_QuantumParallelRepetition_rectangular_matrix_quadratic_compression
import Theorems.Thm_QuantumParallelRepetition_strategyPurificationVector_quadratic

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
attribute [instance] QuantumParallelRepetition.Strategy.alice_fintype QuantumParallelRepetition.Strategy.bob_fintype QuantumParallelRepetition.Strategy.alice_decidableEq QuantumParallelRepetition.Strategy.bob_decidableEq

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace QuantumParallelRepetition
section
open scoped BigOperators ComplexOrder MatrixOrder
set_option autoImplicit true
theorem spectralSupportProjection_isHermitian
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    (spectralSupportProjection F hF).IsHermitian :=
  spectralSupportFunctional_isHermitian F hF _
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped BigOperators ComplexOrder MatrixOrder
set_option autoImplicit true
theorem spectralSupportInverse_mul
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    spectralSupportInverse F hF * F =
      spectralSupportProjection F hF := by
  change spectralSupportFunctional F hF (fun x => x⁻¹) * F =
    spectralSupportFunctional F hF (fun x => if x = 0 then 0 else 1)
  calc
    spectralSupportFunctional F hF (fun x => x⁻¹) * F =
        spectralSupportFunctional F hF (fun x => x⁻¹) *
          spectralSupportFunctional F hF (fun x => x) := by
            rw [spectralSupportFunctional_id]
    _ = spectralSupportFunctional F hF (fun x => x⁻¹ * x) :=
      spectralSupportFunctional_mul F hF _ _
    _ = _ := spectralSupportFunctional_congr F hF (by
      intro i
      by_cases hi : hF.isHermitian.eigenvalues i = 0
      · simp [hi]
      · simp [hi])
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped BigOperators ComplexOrder MatrixOrder
set_option autoImplicit true
theorem mul_spectralSupportInverse
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    F * spectralSupportInverse F hF =
      spectralSupportProjection F hF := by
  change F * spectralSupportFunctional F hF (fun x => x⁻¹) =
    spectralSupportFunctional F hF (fun x => if x = 0 then 0 else 1)
  calc
    F * spectralSupportFunctional F hF (fun x => x⁻¹) =
        spectralSupportFunctional F hF (fun x => x) *
          spectralSupportFunctional F hF (fun x => x⁻¹) := by
            rw [spectralSupportFunctional_id]
    _ = spectralSupportFunctional F hF (fun x => x * x⁻¹) :=
      spectralSupportFunctional_mul F hF _ _
    _ = _ := spectralSupportFunctional_congr F hF (by
      intro i
      by_cases hi : hF.isHermitian.eigenvalues i = 0
      · simp [hi]
      · simp [hi])
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped BigOperators ComplexOrder MatrixOrder
set_option autoImplicit true
theorem spectralSupportProjection_mul
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    spectralSupportProjection F hF * F = F := by
  change spectralSupportFunctional F hF
      (fun x => if x = 0 then 0 else 1) * F = F
  calc
    spectralSupportFunctional F hF
        (fun x => if x = 0 then 0 else 1) * F =
      spectralSupportFunctional F hF
        (fun x => if x = 0 then 0 else 1) *
          spectralSupportFunctional F hF (fun x => x) := by
            rw [spectralSupportFunctional_id]
    _ = spectralSupportFunctional F hF
          (fun x => (if x = 0 then 0 else 1) * x) :=
      spectralSupportFunctional_mul F hF _ _
    _ = spectralSupportFunctional F hF (fun x => x) :=
      spectralSupportFunctional_congr F hF (by
        intro i
        by_cases hi : hF.isHermitian.eigenvalues i = 0 <;> simp [hi])
    _ = F := spectralSupportFunctional_id F hF
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
set_option autoImplicit true
theorem mul_spectralSupportProjection
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    F * spectralSupportProjection F hF = F := by
  have h := congrArg Matrix.conjTranspose
    (spectralSupportProjection_mul F hF)
  simpa [Matrix.conjTranspose_mul,
    (spectralSupportProjection_isHermitian F hF).eq,
    hF.isHermitian.eq] using h
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
set_option autoImplicit true
theorem posSemidef_kernel_of_sub_posSemidef
    {d : Type*} [Fintype d] [DecidableEq d]
    {F A : Matrix d d ℂ}
    (hA : A.PosSemidef) (hsub : (F - A).PosSemidef)
    {x : d → ℂ} (hx : F *ᵥ x = 0) :
    A *ᵥ x = 0 := by
  apply (hA.dotProduct_mulVec_zero_iff x).mp
  have hA_nonneg : 0 ≤ star x ⬝ᵥ (A *ᵥ x) :=
    hA.dotProduct_mulVec_nonneg x
  have hsub_nonneg : 0 ≤ star x ⬝ᵥ ((F - A) *ᵥ x) :=
    hsub.dotProduct_mulVec_nonneg x
  have hzero :
      star x ⬝ᵥ (A *ᵥ x) +
        star x ⬝ᵥ ((F - A) *ᵥ x) = 0 := by
    calc
      star x ⬝ᵥ (A *ᵥ x) +
          star x ⬝ᵥ ((F - A) *ᵥ x) =
        star x ⬝ᵥ ((A + (F - A)) *ᵥ x) := by
          rw [Matrix.add_mulVec, dotProduct_add]
      _ = star x ⬝ᵥ (F *ᵥ x) := by
        have hsum : A + (F - A) = F := by abel
        rw [hsum]
      _ = 0 := by rw [hx]; simp
  exact (add_eq_zero_iff_of_nonneg hA_nonneg hsub_nonneg).mp hzero |>.1
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
set_option autoImplicit true
theorem posSemidef_mul_spectralSupportProjection
    {d : Type*} [Fintype d] [DecidableEq d]
    {F A : Matrix d d ℂ}
    (hF : F.PosSemidef) (hA : A.PosSemidef)
    (hsub : (F - A).PosSemidef) :
    A * spectralSupportProjection F hF = A := by
  let P := spectralSupportProjection F hF
  have hFP : F * P = F := mul_spectralSupportProjection F hF
  have hkernel : F * (1 - P) = 0 := by
    rw [mul_sub, mul_one, hFP, sub_self]
  have hAzero : A * (1 - P) = 0 := by
    apply Matrix.ext_of_mulVec_single
    intro i
    have hxi : F *ᵥ ((1 - P) *ᵥ Pi.single i 1) = 0 := by
      have h := congrArg
        (fun M : Matrix d d ℂ => M *ᵥ Pi.single i 1) hkernel
      simpa only [Matrix.mulVec_mulVec, Matrix.zero_mulVec] using h
    have hAi := posSemidef_kernel_of_sub_posSemidef hA hsub hxi
    simpa only [Matrix.mulVec_mulVec, Matrix.zero_mulVec] using hAi
  have hdiff : A - A * P = 0 := by
    simpa [mul_sub] using hAzero
  exact (sub_eq_zero.mp hdiff).symm
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
set_option autoImplicit true
theorem spectralSupportProjection_mul_posSemidef
    {d : Type*} [Fintype d] [DecidableEq d]
    {F A : Matrix d d ℂ}
    (hF : F.PosSemidef) (hA : A.PosSemidef)
    (hsub : (F - A).PosSemidef) :
    spectralSupportProjection F hF * A = A := by
  have h := congrArg Matrix.conjTranspose
    (posSemidef_mul_spectralSupportProjection hF hA hsub)
  simpa [Matrix.conjTranspose_mul,
    (spectralSupportProjection_isHermitian F hF).eq,
    hA.isHermitian.eq] using h
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
set_option autoImplicit true
theorem refinement_complement_posSemidef
    {ι d : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype d] [DecidableEq d]
    (effect : ι → Matrix d d ℂ)
    (hpositive : ∀ a, (effect a).PosSemidef)
    (a : ι) :
    ((∑ b : ι, effect b) - effect a).PosSemidef := by
  have herase : (∑ b ∈ Finset.univ.erase a, effect b).PosSemidef := by
    apply Matrix.posSemidef_sum (Finset.univ.erase a)
    intro c _
    exact hpositive c
  have hsum : effect a +
      (∑ b ∈ Finset.univ.erase a, effect b) =
      ∑ b : ι, effect b := by
    simp
  rw [← hsum, add_sub_cancel_left]
  exact herase
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
set_option autoImplicit true
set_option maxHeartbeats 400000
theorem purificationRangeProjection_compression
    {d e : Type*} [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (hΓ : Matrix.conjTranspose Γ * Γ = F) :
    Matrix.conjTranspose Γ * purificationRangeProjection F hF Γ * Γ = F := by
  unfold purificationRangeProjection
  calc
    Matrix.conjTranspose Γ *
        (Γ * spectralSupportInverse F hF * Matrix.conjTranspose Γ) * Γ =
      (Matrix.conjTranspose Γ * Γ) * spectralSupportInverse F hF *
        (Matrix.conjTranspose Γ * Γ) := by
          simp only [Matrix.mul_assoc]
    _ = F * spectralSupportInverse F hF * F := by rw [hΓ]
    _ = spectralSupportProjection F hF * F := by
      rw [mul_spectralSupportInverse]
    _ = F := spectralSupportProjection_mul F hF
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
set_option autoImplicit true
set_option maxHeartbeats 400000
theorem purificationRangeProjection_complement_compression
    {d e : Type*} [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (hΓ : Matrix.conjTranspose Γ * Γ = F) :
    Matrix.conjTranspose Γ *
        (1 - purificationRangeProjection F hF Γ) * Γ = 0 := by
  calc
    Matrix.conjTranspose Γ *
        (1 - purificationRangeProjection F hF Γ) * Γ =
      Matrix.conjTranspose Γ * Γ -
        Matrix.conjTranspose Γ * purificationRangeProjection F hF Γ * Γ := by
          rw [Matrix.mul_sub, Matrix.sub_mul]
          simp
    _ = F - F := by
      rw [hΓ, purificationRangeProjection_compression F hF Γ hΓ]
    _ = 0 := sub_self F
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
set_option autoImplicit true
set_option maxHeartbeats 400000
theorem purifiedRefinementCore_compression
    {ι d e : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (hΓ : Matrix.conjTranspose Γ * Γ = F)
    (effect : ι → Matrix d d ℂ)
    (hpositive : ∀ a, (effect a).PosSemidef)
    (hsum : (∑ a : ι, effect a) = F)
    (a : ι) :
    Matrix.conjTranspose Γ *
        purifiedRefinementCore F hF Γ effect a * Γ = effect a := by
  have hsub : (F - effect a).PosSemidef := by
    rw [← hsum]
    exact refinement_complement_posSemidef effect hpositive a
  unfold purifiedRefinementCore
  calc
    Matrix.conjTranspose Γ *
        (Γ * spectralSupportInverse F hF * effect a *
          spectralSupportInverse F hF * Matrix.conjTranspose Γ) * Γ =
      (Matrix.conjTranspose Γ * Γ) * spectralSupportInverse F hF *
        effect a * spectralSupportInverse F hF *
          (Matrix.conjTranspose Γ * Γ) := by
            simp only [Matrix.mul_assoc]
    _ = F * spectralSupportInverse F hF * effect a *
          spectralSupportInverse F hF * F := by
            rw [hΓ]
    _ = (F * spectralSupportInverse F hF) * effect a *
          (spectralSupportInverse F hF * F) := by
            simp only [Matrix.mul_assoc]
    _ = spectralSupportProjection F hF * effect a *
          spectralSupportProjection F hF := by
            rw [mul_spectralSupportInverse, spectralSupportInverse_mul]
    _ = effect a := by
      rw [spectralSupportProjection_mul_posSemidef hF
        (hpositive a) hsub]
      exact posSemidef_mul_spectralSupportProjection hF
        (hpositive a) hsub
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
set_option autoImplicit true
set_option maxHeartbeats 400000
theorem purifiedRefinedEffect_compression
    {ι d e : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (hΓ : Matrix.conjTranspose Γ * Γ = F)
    (effect : ι → Matrix d d ℂ)
    (hpositive : ∀ a, (effect a).PosSemidef)
    (hsum : (∑ a : ι, effect a) = F)
    (a₀ a : ι) :
    Matrix.conjTranspose Γ *
        purifiedRefinedEffect F hF Γ effect a₀ a * Γ = effect a := by
  have hdefect : Matrix.conjTranspose Γ *
      (if a = a₀ then 1 - purificationRangeProjection F hF Γ else 0) *
        Γ = 0 := by
    split
    · exact purificationRangeProjection_complement_compression F hF Γ hΓ
    · simp
  change Matrix.conjTranspose Γ *
      (purifiedRefinementCore F hF Γ effect a +
        if a = a₀ then 1 - purificationRangeProjection F hF Γ else 0) *
        Γ = effect a
  rw [Matrix.mul_add, Matrix.add_mul]
  rw [purifiedRefinementCore_compression F hF Γ hΓ
    effect hpositive hsum a, hdefect, add_zero]
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
set_option autoImplicit true
set_option maxHeartbeats 400000
theorem purifiedRefinedPOVM_compression
    {ι d e : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (hΓ : Matrix.conjTranspose Γ * Γ = F)
    (effect : ι → Matrix d d ℂ)
    (hpositive : ∀ a, (effect a).PosSemidef)
    (hsum : (∑ a : ι, effect a) = F)
    (a₀ a : ι) :
    Matrix.conjTranspose Γ *
      (purifiedRefinedPOVM F hF Γ hΓ effect hpositive hsum a₀).effect a *
        Γ = effect a :=
  purifiedRefinedEffect_compression F hF Γ hΓ effect
    hpositive hsum a₀ a
end
end QuantumParallelRepetition

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option autoImplicit true
theorem finiteLocalPurificationJointMatrix_gram
    {X Y A B eA eB : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype eA] [Fintype eB]
    {G : Game X Y A B} (S : Strategy G)
    (KA : Matrix eA S.Alice ℂ) (KB : Matrix eB S.Bob ℂ) :
    (finiteLocalPurificationJointMatrix S KA KB).conjTranspose *
        finiteLocalPurificationJointMatrix S KA KB =
      ((KA.conjTranspose * KA) ⊗ₖ
        (1 : Matrix (S.Alice × S.Bob) (S.Alice × S.Bob) ℂ)) ⊗ₖ
        (KB.conjTranspose * KB) := by
  unfold finiteLocalPurificationJointMatrix
  rw [Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul,
    Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul]
  simp
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option autoImplicit true
theorem finiteLocalPurificationVector_norm_sq
    {X Y A B eA eB : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype eA] [Fintype eB]
    {G : Game X Y A B} (S : Strategy G)
    (KA : Matrix eA S.Alice ℂ) (KB : Matrix eB S.Bob ℂ) :
    ‖finiteLocalPurificationVector S KA KB‖ ^ 2 =
      (Matrix.trace
        (S.state.matrix *
          ((KA.conjTranspose * KA) ⊗ₖ
            (KB.conjTranspose * KB)))).re := by
  unfold finiteLocalPurificationVector
  rw [rectangular_matrix_mulVec_norm_sq,
    finiteLocalPurificationJointMatrix_gram]
  exact strategyPurificationVector_quadratic S
    (KA.conjTranspose * KA) (KB.conjTranspose * KB)
end
end QuantumParallelRepetition

attribute [local instance] Classical.propDecidable

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

attribute [local instance] Classical.propDecidable

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option autoImplicit true
theorem finiteLocalPurificationJointMatrix_compression
    {X Y A B eA eB : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype eA] [Fintype eB]
    [DecidableEq eA] [DecidableEq eB]
    {G : Game X Y A B} (S : Strategy G)
    (KA : Matrix eA S.Alice ℂ) (KB : Matrix eB S.Bob ℂ)
    (EA : Matrix eA eA ℂ) (EB : Matrix eB eB ℂ) :
    (finiteLocalPurificationJointMatrix S KA KB).conjTranspose *
        (((EA ⊗ₖ
            (1 : Matrix (S.Alice × S.Bob)
              (S.Alice × S.Bob) ℂ)) ⊗ₖ EB)) *
        finiteLocalPurificationJointMatrix S KA KB =
      (((KA.conjTranspose * EA * KA) ⊗ₖ
          (1 : Matrix (S.Alice × S.Bob)
            (S.Alice × S.Bob) ℂ)) ⊗ₖ
        (KB.conjTranspose * EB * KB)) := by
  unfold finiteLocalPurificationJointMatrix
  rw [Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul,
    Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul]
  simp
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option autoImplicit true
theorem finiteLocalPurificationVector_quadratic
    {X Y A B eA eB : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype eA] [Fintype eB]
    [DecidableEq eA] [DecidableEq eB]
    {G : Game X Y A B} (S : Strategy G)
    (KA : Matrix eA S.Alice ℂ) (KB : Matrix eB S.Bob ℂ)
    (EA : Matrix eA eA ℂ) (EB : Matrix eB eB ℂ) :
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := (eA × (S.Alice × S.Bob)) × eB) (𝕜 := ℂ)
        (((EA ⊗ₖ
          (1 : Matrix (S.Alice × S.Bob)
            (S.Alice × S.Bob) ℂ)) ⊗ₖ EB)))
      (finiteLocalPurificationVector S KA KB) =
      bornTracePairing S.state.matrix
        (KA.conjTranspose * EA * KA)
        (KB.conjTranspose * EB * KB) := by
  unfold finiteLocalPurificationVector
  rw [rectangular_matrix_quadratic_compression,
    finiteLocalPurificationJointMatrix_compression]
  exact strategyPurificationVector_quadratic S
    (KA.conjTranspose * EA * KA)
    (KB.conjTranspose * EB * KB)
end
end QuantumParallelRepetition

attribute [local instance] Classical.propDecidable

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem exactUnnormalizedPsi_norm_sq
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y) :
    ‖exactUnnormalizedPsi G n S D r x y‖ ^ 2 =
      bornTracePairing S.state.matrix
        (exactAliceQuestionFilter
          G n S D r.seed r.history r.aliceAnswer x)
        (exactBobQuestionFilter
          G n S D r.seed r.history r.bobAnswer y) := by
  unfold exactUnnormalizedPsi
  rw [finiteLocalPurificationVector_norm_sq,
    exactAlicePurificationMatrix_gram,
    exactBobPurificationMatrix_gram]
  rfl
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem exactAliceRefinedPOVM_compression
    [DecidableEq A]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (x : X) (a : A) :
    (exactAlicePurificationMatrix
      G n S D r.seed r.history r.aliceAnswer (.inl x)).conjTranspose *
      (exactAliceRefinedPOVM G n S D r a₀ x).effect a *
      exactAlicePurificationMatrix
        G n S D r.seed r.history r.aliceAnswer (.inl x) =
      exactAliceCoordinateFilter
        G n S D r.seed r.history r.aliceAnswer x a := by
  exact purifiedRefinedPOVM_compression
    (exactAliceQuestionFilter
      G n S D r.seed r.history r.aliceAnswer x)
    (exactAliceQuestionFilter_posSemidef
      G n S D r.seed r.history r.aliceAnswer x)
    (exactAlicePurificationMatrix
      G n S D r.seed r.history r.aliceAnswer (.inl x))
    (exactAliceQuestionPurificationMatrix_gram G n S D r x)
    (exactAliceCoordinateFilter
      G n S D r.seed r.history r.aliceAnswer x)
    (exactAliceCoordinateFilter_posSemidef
      G n S D r.seed r.history r.aliceAnswer x)
    (exactAliceCoordinateFilter_sum
      G n S D r.seed r.history r.aliceAnswer x)
    a₀ a
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem exactBobRefinedPOVM_compression
    [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (b₀ : B) (y : Y) (b : B) :
    (exactBobPurificationMatrix
      G n S D r.seed r.history r.bobAnswer (.inl y)).conjTranspose *
      (exactBobRefinedPOVM G n S D r b₀ y).effect b *
      exactBobPurificationMatrix
        G n S D r.seed r.history r.bobAnswer (.inl y) =
      exactBobCoordinateFilter
        G n S D r.seed r.history r.bobAnswer y b := by
  exact purifiedRefinedPOVM_compression
    (exactBobQuestionFilter
      G n S D r.seed r.history r.bobAnswer y)
    (exactBobQuestionFilter_posSemidef
      G n S D r.seed r.history r.bobAnswer y)
    (exactBobPurificationMatrix
      G n S D r.seed r.history r.bobAnswer (.inl y))
    (exactBobQuestionPurificationMatrix_gram G n S D r y)
    (exactBobCoordinateFilter
      G n S D r.seed r.history r.bobAnswer y)
    (exactBobCoordinateFilter_posSemidef
      G n S D r.seed r.history r.bobAnswer y)
    (exactBobCoordinateFilter_sum
      G n S D r.seed r.history r.bobAnswer y)
    b₀ b
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem exactRefinedPOVM_quadratic
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (b₀ : B) (x : X) (y : Y) (a : A) (b : B) :
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := ExactAliceLocalIndex G n S D r ×
          ExactBobLocalIndex G n S D r)
        (𝕜 := ℂ)
        (((exactAliceRefinedPOVM
          G n S D r a₀ x).effect a ⊗ₖ
          (1 : Matrix (S.Alice × S.Bob)
            (S.Alice × S.Bob) ℂ)) ⊗ₖ
          (exactBobRefinedPOVM
            G n S D r b₀ y).effect b))
      (exactUnnormalizedPsi G n S D r x y) =
      bornTracePairing S.state.matrix
        (exactAliceCoordinateFilter
          G n S D r.seed r.history r.aliceAnswer x a)
        (exactBobCoordinateFilter
          G n S D r.seed r.history r.bobAnswer y b) := by
  unfold exactUnnormalizedPsi
  rw [finiteLocalPurificationVector_quadratic,
    exactAliceRefinedPOVM_compression,
    exactBobRefinedPOVM_compression]
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem exactPaddedVector_norm
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (z : EuclideanSpace ℂ
      (ExactAliceLocalIndex G n S D r ×
        ExactBobLocalIndex G n S D r)) :
    ‖exactPaddedVector G n S D r z‖ = ‖z‖ := by
  classical
  have hsquare :
      ‖exactPaddedVector G n S D r z‖ ^ 2 = ‖z‖ ^ 2 := by
    simp [EuclideanSpace.norm_sq_eq, exactPaddedVector,
      Fintype.sum_prod_type, Fintype.sum_sum_type]
  nlinarith [norm_nonneg (exactPaddedVector G n S D r z),
    norm_nonneg z]
end
end QuantumParallelRepetition

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexConjugate ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option autoImplicit true
theorem quadraticExpectation_normalizedPureVector
    {d : Type*} [Fintype d]
    (W : EuclideanSpace ℂ d →L[ℂ] EuclideanSpace ℂ d)
    (z : EuclideanSpace ℂ d) :
    quadraticExpectation W (normalizedPureVector z) =
      quadraticExpectation W z / ‖z‖ ^ 2 := by
  unfold quadraticExpectation normalizedPureVector
  rw [map_smul, inner_smul_left, inner_smul_right]
  simp [Complex.mul_re, div_eq_mul_inv, pow_two]
  by_cases hz : ‖z‖ = 0
  · simp [hz]
  · field_simp
end
end QuantumParallelRepetition

attribute [local instance] Classical.propDecidable

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem sourceHistoryQuadraticExpectation_matrix_sum
    {I d : Type*} [Fintype I] [Fintype d] [DecidableEq d]
    (M : I → Matrix d d ℂ) (z : EuclideanSpace ℂ d) :
    quadraticExpectation
      (Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ) (∑ i : I, M i)) z =
      ∑ i : I,
        quadraticExpectation
          (Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ) (M i)) z := by
  simp [quadraticExpectation]
end
end QuantumParallelRepetition

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem exactAliceCoordinateFilter_eq_joint
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (x : X) (y : Y) (a : A)
    (nonzero : exactFiberQuestionMass
      G n D seed history x y ≠ 0) :
    exactAliceCoordinateFilter
        G n S D seed history answer x a =
      exactJointAliceCoordinateFilter
        G n S D seed history answer x y a := by
  exact exactAliceConditionalMatrix_eq_joint
    G n D seed history x y nonzero
    (fun xs => conditionedAliceCoordinateEffect
      G n S D answer xs seed.coordinate.val a)
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem exactBobCoordinateFilter_eq_joint
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (x : X) (y : Y) (b : B)
    (nonzero : exactFiberQuestionMass
      G n D seed history x y ≠ 0) :
    exactBobCoordinateFilter
        G n S D seed history answer y b =
      exactJointBobCoordinateFilter
        G n S D seed history answer x y b := by
  exact exactBobConditionalMatrix_eq_joint
    G n D seed history x y nonzero
    (fun ys => conditionedBobCoordinateEffect
      G n S D answer ys seed.coordinate.val b)
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

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

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
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem exactFairConditionedAnswerBornMass_eq_reveal_question_norm
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y) :
    exactFairConditionedAnswerBornMass G n S D r x y =
      exactRevealMass G n D r.seed r.history *
        G.questionWeight x y *
        ‖exactUnnormalizedPsi G n S D r x y‖ ^ 2 := by
  rw [exactFairConditionedAnswerBornMass_eq_fiber_norm,
    exactFiberQuestionMass_eq_jointQuestionMass,
    exactJointQuestionMass_eq_reveal_mul_question]
end
end QuantumParallelRepetition

attribute [local instance] Classical.propDecidable

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.ClassicalInformation
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option maxRecDepth 2048
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem exactFairFullOutcomeBornMass_eq_reveal_question_norm
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y) :
    exactFairFullOutcomeBornMass G n S D r x y =
      exactRevealMass G n D r.seed r.history *
        G.questionWeight x y *
        ‖exactUnnormalizedPsi G n S D r x y‖ ^ 2 := by
  rw [exactFairFullOutcomeBornMass_eq_conditioned,
    exactFairConditionedAnswerBornMass_eq_reveal_question_norm]
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

attribute [local instance] Classical.propDecidable

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
open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem exactSourceJointEffect_quadratic
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (b₀ : B) (x : X) (y : Y) (a : A) (b : B) :
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := ExactAliceLocalIndex G n S D r ×
          ExactBobLocalIndex G n S D r) (𝕜 := ℂ)
        (exactSourceJointEffect G n S D r a₀ b₀ x y a b))
      (exactUnnormalizedPsi G n S D r x y) =
      bornTracePairing S.state.matrix
        (exactAliceCoordinateFilter
          G n S D r.seed r.history r.aliceAnswer x a)
        (exactBobCoordinateFilter
          G n S D r.seed r.history r.bobAnswer y b) := by
  classical
  simpa [exactSourceJointEffect,
    exactSourceAliceRefinedPOVM,
    exactSourceBobRefinedPOVM, purificationAlicePOVM] using
    (exactRefinedPOVM_quadratic
      G n S D r a₀ b₀ x y a b)
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem exactSourceWinningEffect_quadratic
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (b₀ : B) (x : X) (y : Y) :
    quadraticExpectation
      (exactSourceWinningEffectCLM
        G n S D r a₀ b₀ x y)
      (exactUnnormalizedPsi G n S D r x y) =
      ∑ a : A, ∑ b : B,
        if G.predicate x y a b = true then
          bornTracePairing S.state.matrix
            (exactAliceCoordinateFilter
              G n S D r.seed r.history r.aliceAnswer x a)
            (exactBobCoordinateFilter
              G n S D r.seed r.history r.bobAnswer y b)
        else 0 := by
  classical
  unfold exactSourceWinningEffectCLM
    exactSourceWinningEffect
  rw [sourceHistoryQuadraticExpectation_matrix_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [sourceHistoryQuadraticExpectation_matrix_sum]
  apply Finset.sum_congr rfl
  intro b _
  split_ifs
  · exact exactSourceJointEffect_quadratic
      G n S D r a₀ b₀ x y a b
  · simp [quadraticExpectation]
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem exactSourceWinningEffect_quadratic_eq_conditional
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (b₀ : B) (x : X) (y : Y)
    (supported : exactFiberQuestionMass
      G n D r.seed r.history x y ≠ 0) :
    quadraticExpectation
      (exactSourceWinningEffectCLM
        G n S D r a₀ b₀ x y)
      (exactUnnormalizedPsi G n S D r x y) =
      exactJointConditionalWinningMass
        G n S D r.seed r.history r.aliceAnswer r.bobAnswer x y := by
  rw [exactSourceWinningEffect_quadratic]
  unfold exactJointConditionalWinningMass
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs
  · rw [exactAliceCoordinateFilter_eq_joint
      G n S D r.seed r.history r.aliceAnswer x y a supported,
      exactBobCoordinateFilter_eq_joint
        G n S D r.seed r.history r.bobAnswer x y b supported]
  · rfl
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem exactSourceNormalizedWinningEffect_eq_conditional
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (b₀ : B) (x : X) (y : Y)
    (supported : exactFiberQuestionMass
      G n D r.seed r.history x y ≠ 0) :
    quadraticExpectation
      (exactSourceWinningEffectCLM
        G n S D r a₀ b₀ x y)
      (normalizedPureVector
        (exactUnnormalizedPsi G n S D r x y)) =
      exactJointConditionalWinningMass
        G n S D r.seed r.history r.aliceAnswer r.bobAnswer x y /
        bornTracePairing S.state.matrix
          (exactAliceQuestionFilter
            G n S D r.seed r.history r.aliceAnswer x)
          (exactBobQuestionFilter
            G n S D r.seed r.history r.bobAnswer y) := by
  rw [quadraticExpectation_normalizedPureVector,
    exactSourceWinningEffect_quadratic_eq_conditional
      G n S D r a₀ b₀ x y supported,
    exactUnnormalizedPsi_norm_sq]
end
end QuantumParallelRepetition

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.ClassicalInformation
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem exactSourceConditionalWinningProbability_eq_fine_born_ratio
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (history : ExactHistoryFlag X Y A B D)
    (accepted : exactHistoryAccepted G n D history)
    (x : X) (y : Y) :
    exactSourceConditionalWinningProbability G n S D
        (history.seed.coordinate, x, y, history) =
      exactFairWinningOutcomeBornMass G n S D history x y /
        exactFairFullOutcomeBornMass G n S D history x y := by
  have seed_positive : 0 < exactSeedWeight history.seed := by
    unfold exactSeedWeight
    have coordinate_positive :
        0 < Fintype.card (SourceRemainingCoordinate D) :=
      Fintype.card_pos_iff.mpr ⟨history.seed.coordinate⟩
    positivity
  have posterior :
      exactLocallySampleableLaw G n S D
        (history.seed.coordinate, x, y, history) =
        (exactSeedWeight history.seed *
          exactFairFullOutcomeBornMass
            G n S D history x y) /
          repeatedPostselectionMass G n S D := by
    rw [exactLocallySampleableLaw_eq_fair_born,
      if_pos accepted,
      exactFairFullOutcomeBornMass_eq_reveal_question_norm]
    ring
  unfold exactSourceConditionalWinningProbability
  rw [exactSourceAcceptedCoordinateMass_eq_seeded_fair_born
    G n S D positive history x y, if_pos accepted, posterior]
  by_cases mass_zero :
      exactFairFullOutcomeBornMass G n S D history x y = 0
  · simp [mass_zero]
  · field_simp [positive.ne', seed_positive.ne', mass_zero]
end
end QuantumParallelRepetition

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem exactSourceConditionalWinningProbability_eq_normalized_verifier
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (history : ExactHistoryFlag X Y A B D)
    (accepted : exactHistoryAccepted G n D history)
    (a₀ : A) (b₀ : B) (x : X) (y : Y)
    (supported : exactFiberQuestionMass
      G n D history.seed history.history x y ≠ 0) :
    exactSourceConditionalWinningProbability G n S D
        (history.seed.coordinate, x, y, history) =
      quadraticExpectation
        (exactSourceWinningEffectCLM
          G n S D history a₀ b₀ x y)
        (normalizedPureVector
          (exactUnnormalizedPsi G n S D history x y)) := by
  rw [exactSourceConditionalWinningProbability_eq_fine_born_ratio
    G n S D positive history accepted x y,
    exactFairWinningOutcomeBornMass_eq_fiber_conditional
      G n S D history x y supported,
    exactFairFullOutcomeBornMass_eq_conditioned,
    exactFairConditionedAnswerBornMass_eq_fiber_norm,
    exactSourceNormalizedWinningEffect_eq_conditional
      G n S D history a₀ b₀ x y supported,
    exactUnnormalizedPsi_norm_sq]
  exact mul_div_mul_left _ _ supported
end
end QuantumParallelRepetition

attribute [local instance] Classical.propDecidable

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
open QuantumParallelRepetition.ClassicalSampling
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem exactLocallySampleableLaw_accepted_of_ne_zero
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (t : ExactLocallySampleableTuple X Y A B D)
    (supported : exactLocallySampleableLaw G n S D t ≠ 0) :
    exactHistoryAccepted G n D t.2.2.2 := by
  classical
  by_contra rejected
  exact supported
    (exactLocallySampleableLaw_zero_of_not_accepted
      G n S D t.1 t.2.1 t.2.2.1 t.2.2.2 rejected)
end
end QuantumParallelRepetition

attribute [local instance] Classical.propDecidable

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem matrixQuadraticExpectation_expand
    {d : Type*} [Fintype d] [DecidableEq d]
    (M : Matrix d d ℂ) (z : EuclideanSpace ℂ d) :
    quadraticExpectation
      (Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ) M) z =
      (∑ i : d, (∑ j : d, M i j * z j) * star (z i)).re := by
  simp [quadraticExpectation, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.mulVec, dotProduct]
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem exactSourceGlobalJointBasis_injective
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) :
    Function.Injective (exactSourceGlobalJointBasis G n S D r) := by
  intro i j same
  rcases i with ⟨ia, ib⟩
  rcases j with ⟨ja, jb⟩
  have alice := congrArg Prod.fst same
  have bob := congrArg Prod.snd same
  change
    (Sum.inr ⟨r, .inr (.inl ia)⟩ :
      ExactGlobalHistoryLocalIndex G n S D) =
      Sum.inr ⟨r, .inr (.inl ja)⟩ at alice
  change
    (Sum.inr ⟨r, .inr (.inr ib)⟩ :
      ExactGlobalHistoryLocalIndex G n S D) =
      Sum.inr ⟨r, .inr (.inr jb)⟩ at bob
  have alice_block :
      (Sum.inr (.inl ia) : ExactPaddedLocalIndex G n S D r) =
        Sum.inr (.inl ja) :=
    eq_of_heq (Sigma.mk.inj (Sum.inr.inj alice)).2
  have bob_block :
      (Sum.inr (.inr ib) : ExactPaddedLocalIndex G n S D r) =
        Sum.inr (.inr jb) :=
    eq_of_heq (Sigma.mk.inj (Sum.inr.inj bob)).2
  have alice' : ia = ja :=
    Sum.inl.inj (Sum.inr.inj alice_block)
  have bob' : ib = jb :=
    Sum.inr.inj (Sum.inr.inj bob_block)
  exact Prod.ext alice' bob'
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem exactSourceGlobalJointBasis_vector
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (z : EuclideanSpace ℂ
      (ExactAliceLocalIndex G n S D r ×
        ExactBobLocalIndex G n S D r))
    (i : ExactAliceLocalIndex G n S D r ×
      ExactBobLocalIndex G n S D r) :
    exactGlobalHistoryVector G n S D r
        (exactPaddedVector G n S D r z)
        (exactSourceGlobalJointBasis G n S D r i) =
      z i := by
  rcases i with ⟨ia, ib⟩
  change
    (if ha : r = r then
      if hb : r = r then
        exactPaddedVector G n S D r z
          (ha ▸ Sum.inr (Sum.inl ia),
            hb ▸ Sum.inr (Sum.inr ib))
      else 0
    else 0) = z (ia, ib)
  simp only [exactPaddedVector, dite_true]
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem exactSourceGlobalJointBasis_support
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (z : EuclideanSpace ℂ
      (ExactAliceLocalIndex G n S D r ×
        ExactBobLocalIndex G n S D r))
    (j : ExactGlobalHistoryLocalIndex G n S D ×
      ExactGlobalHistoryLocalIndex G n S D)
    (outside : ∀ i, exactSourceGlobalJointBasis
      G n S D r i ≠ j) :
    exactGlobalHistoryVector G n S D r
      (exactPaddedVector G n S D r z) j = 0 := by
  classical
  rcases j with ⟨u, v⟩
  rcases u with u | ⟨ru, u⟩
  · rfl
  rcases v with v | ⟨rv, v⟩
  · rfl
  change
    (if ha : ru = r then
      if hb : rv = r then
        exactPaddedVector G n S D r z
          (ha ▸ u, hb ▸ v)
      else 0
    else 0) = 0
  by_cases hu : ru = r
  · subst ru
    by_cases hv : rv = r
    · subst rv
      simp only [dite_true]
      rcases u with u | (u | u)
      · rfl
      · rcases v with v | (v | v)
        · rfl
        · rfl
        · exact False.elim
            (outside (u, v)
              (by rfl))
      · rfl
    · simp only [dif_neg hv, dite_true]
  · simp only [dif_neg hu]
end
end QuantumParallelRepetition

attribute [local instance] Classical.propDecidable

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.ClassicalSampling
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem exactSourceGlobalWinningEffect_compression
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (b₀ : B) (x : X) (y : Y)
    (i j : ExactAliceLocalIndex G n S D r ×
      ExactBobLocalIndex G n S D r) :
    exactSourceGlobalWinningEffect G n S D a₀ b₀ x y
      (exactSourceGlobalJointBasis G n S D r i)
      (exactSourceGlobalJointBasis G n S D r j) =
      exactSourceWinningEffect G n S D r a₀ b₀ x y i j := by
  classical
  rcases i with ⟨ia, ib⟩
  rcases j with ⟨ja, jb⟩
  simp only [exactSourceGlobalWinningEffect,
    exactSourceWinningEffect, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs
  · simp only [exactSourceGlobalJointBasis,
      exactSourceJointEffect, Matrix.kroneckerMap_apply,
      exactSourceGlobalAlicePOVM_effect,
      exactSourceGlobalBobPOVM_effect]
  · rfl
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.ClassicalSampling
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem exactSourceGlobalWinningEffect_quadratic
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (b₀ : B) (x : X) (y : Y)
    (z : EuclideanSpace ℂ
      (ExactAliceLocalIndex G n S D r ×
        ExactBobLocalIndex G n S D r)) :
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := ExactGlobalHistoryLocalIndex G n S D ×
          ExactGlobalHistoryLocalIndex G n S D)
        (𝕜 := ℂ)
        (exactSourceGlobalWinningEffect G n S D a₀ b₀ x y))
      (exactGlobalHistoryVector G n S D r
        (exactPaddedVector G n S D r z)) =
      quadraticExpectation
        (exactSourceWinningEffectCLM G n S D r a₀ b₀ x y)
        z := by
  classical
  unfold exactSourceWinningEffectCLM
  apply matrixQuadraticExpectation_injective
    (exactSourceGlobalJointBasis G n S D r)
    (exactSourceGlobalJointBasis_injective G n S D r)
  · exact exactSourceGlobalJointBasis_vector G n S D r z
  · exact exactSourceGlobalJointBasis_support G n S D r z
  · exact exactSourceGlobalWinningEffect_compression
      G n S D r a₀ b₀ x y
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
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.ClassicalSampling
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem exactPsi_eq_padded_normalizedPureVector_of_ne_zero
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y)
    (nonzero : exactUnnormalizedPsi G n S D r x y ≠ 0) :
    exactPsi G n S D r x y =
      exactPaddedVector G n S D r
        (normalizedPureVector
          (exactUnnormalizedPsi G n S D r x y)) := by
  classical
  let raw := exactUnnormalizedPsi G n S D r x y
  have padded_nonzero :
      exactPaddedVector G n S D r raw ≠ 0 := by
    intro zero
    apply nonzero
    apply norm_eq_zero.mp
    rw [← exactPaddedVector_norm G n S D r raw, zero]
    exact norm_zero
  unfold exactPsi normalizeOrDefault
  rw [if_neg padded_nonzero, NormedSpace.normalize,
    exactPaddedVector_norm]
  ext q
  rcases q with ⟨i, j⟩
  rcases i with i | (i | i) <;>
    rcases j with j | (j | j) <;>
    simp [exactPaddedVector, normalizedPureVector,
      smul_eq_mul]
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.ClassicalSampling
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem exactSourceGlobalCatalystWinningEffect_law_supported_verifier
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (e : ℕ) (residual_positive : 0 < e)
    (a₀ : A) (b₀ : B)
    (t : ExactLocallySampleableTuple X Y A B D)
    (supported : exactLocallySampleableLaw G n S D t ≠ 0) :
    exactSourceConditionalWinningProbability G n S D t =
      quadraticExpectation
        (Matrix.toEuclideanCLM
          (n :=
            Fin (Fintype.card
              (ExactGlobalHistoryLocalIndex G n S D) * e) ×
            Fin (Fintype.card
              (ExactGlobalHistoryLocalIndex G n S D) * e))
          (𝕜 := ℂ)
          (exactSourceGlobalCatalystWinningEffect
            G n S D e a₀ b₀ t.2.1 t.2.2.1))
        (tensorEmbezzlementTarget (n := e)
          (exactGlobalHistoryFinPsi G n S D t.2.2.2
            t.2.1 t.2.2.1)) := by
  classical
  have coordinate :=
    exactLocallySampleableLaw_coordinate_eq_of_ne_zero
      G n S D t supported
  have accepted :=
    exactLocallySampleableLaw_accepted_of_ne_zero
      G n S D t supported
  have fiber :=
    exactLocallySampleableLaw_fiber_ne_zero_of_ne_zero
      G n S D t supported
  have raw_nonzero :=
    exactLocallySampleableLaw_psi_ne_zero_of_ne_zero
      G n S D t supported
  rw [exactSourceGlobalCatalystWinningEffect_tensor_quadratic
    G n S D t.2.2.2 e residual_positive a₀ b₀ t.2.1 t.2.2.1]
  rw [exactPsi_eq_padded_normalizedPureVector_of_ne_zero
    G n S D t.2.2.2 t.2.1 t.2.2.1 raw_nonzero]
  rw [exactSourceGlobalWinningEffect_quadratic
    G n S D t.2.2.2 a₀ b₀ t.2.1 t.2.2.1]
  have tuple :
      t = (t.2.2.2.seed.coordinate,
        t.2.1, t.2.2.1, t.2.2.2) := by
    rcases t with ⟨i, x, y, r⟩
    simpa using coordinate
  conv_lhs => rw [tuple]
  exact
    exactSourceConditionalWinningProbability_eq_normalized_verifier
      G n S D positive t.2.2.2 accepted a₀ b₀
      t.2.1 t.2.2.1 fiber
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option autoImplicit true
theorem unconditionalConjugatePureVector_transpose_quadratic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (z : EuclideanSpace ℂ ι) :
    quadraticExpectation
        (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M.transpose)
        (unconditionalConjugatePureVector z) =
      quadraticExpectation
        (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M) z := by
  classical
  rw [matrixQuadraticExpectation_expand,
    matrixQuadraticExpectation_expand]
  congr 1
  simp only [Matrix.transpose_apply,
    unconditionalConjugatePureVector_apply, star_star]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option autoImplicit true
theorem unconditionalConjugatePOVM_jointEffect
    {A B ι κ : Type*} [Fintype A] [Fintype B]
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : POVM A ι) (Q : POVM B κ) (a : A) (b : B) :
    (unconditionalConjugatePOVM P).effect a ⊗ₖ
        (unconditionalConjugatePOVM Q).effect b =
      (P.effect a ⊗ₖ Q.effect b).transpose := by
  exact Matrix.kroneckerMap_transpose (fun x y : ℂ => x * y)
    (P.effect a) (Q.effect b)
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option autoImplicit true
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem
    unconditionalConjugateSourceGlobalCatalystWinningEffect_eq_transpose
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (e : ℕ)
    (a₀ : A) (b₀ : B) (x : X) (y : Y) :
    unconditionalConjugateSourceGlobalCatalystWinningEffect
        G n S D e a₀ b₀ x y =
      (exactSourceGlobalCatalystWinningEffect
        G n S D e a₀ b₀ x y).transpose := by
  classical
  unfold unconditionalConjugateSourceGlobalCatalystWinningEffect
    exactSourceGlobalCatalystWinningEffect
  rw [Matrix.transpose_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Matrix.transpose_sum]
  apply Finset.sum_congr rfl
  intro b _
  split_ifs
  · exact unconditionalConjugatePOVM_jointEffect
      (exactSourceGlobalCatalystAlicePOVM G n S D e a₀ x)
      (exactSourceGlobalCatalystBobPOVM G n S D e b₀ y)
      a b
  · exact Matrix.transpose_zero.symm
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option autoImplicit true
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem unconditionalConjugateSourceGlobalCatalystWinningEffect_quadratic
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (e : ℕ)
    (a₀ : A) (b₀ : B) (x : X) (y : Y)
    (z : EuclideanSpace ℂ
      (Fin (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) * e) ×
       Fin (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) * e))) :
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n :=
          Fin (Fintype.card
            (ExactGlobalHistoryLocalIndex G n S D) * e) ×
          Fin (Fintype.card
            (ExactGlobalHistoryLocalIndex G n S D) * e))
        (𝕜 := ℂ)
        (unconditionalConjugateSourceGlobalCatalystWinningEffect
          G n S D e a₀ b₀ x y))
      (unconditionalConjugatePureVector z) =
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n :=
          Fin (Fintype.card
            (ExactGlobalHistoryLocalIndex G n S D) * e) ×
          Fin (Fintype.card
            (ExactGlobalHistoryLocalIndex G n S D) * e))
        (𝕜 := ℂ)
        (exactSourceGlobalCatalystWinningEffect
          G n S D e a₀ b₀ x y)) z := by
  calc
    _ = quadraticExpectation
        (Matrix.toEuclideanCLM
          (n :=
            Fin (Fintype.card
              (ExactGlobalHistoryLocalIndex G n S D) * e) ×
            Fin (Fintype.card
              (ExactGlobalHistoryLocalIndex G n S D) * e))
          (𝕜 := ℂ)
          (exactSourceGlobalCatalystWinningEffect
            G n S D e a₀ b₀ x y).transpose)
        (unconditionalConjugatePureVector z) := by
          exact congrArg
            (fun M =>
              quadraticExpectation
                (Matrix.toEuclideanCLM
                  (n :=
                    Fin (Fintype.card
                      (ExactGlobalHistoryLocalIndex G n S D) * e) ×
                    Fin (Fintype.card
                      (ExactGlobalHistoryLocalIndex G n S D) * e))
                  (𝕜 := ℂ) M)
                (unconditionalConjugatePureVector z))
            (unconditionalConjugateSourceGlobalCatalystWinningEffect_eq_transpose
              G n S D e a₀ b₀ x y)
    _ = _ := unconditionalConjugatePureVector_transpose_quadratic
      (exactSourceGlobalCatalystWinningEffect
        G n S D e a₀ b₀ x y) z
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option autoImplicit true
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem
    unconditionalConjugateSourceGlobalCatalystWinningEffect_law_supported
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (e : ℕ) (residual_positive : 0 < e)
    (a₀ : A) (b₀ : B)
    (u : ExactLocallySampleableTuple X Y A B D)
    (supported : exactLocallySampleableLaw G n S D u ≠ 0) :
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n :=
          Fin (Fintype.card
            (ExactGlobalHistoryLocalIndex G n S D) * e) ×
          Fin (Fintype.card
            (ExactGlobalHistoryLocalIndex G n S D) * e))
        (𝕜 := ℂ)
        (unconditionalConjugateSourceGlobalCatalystWinningEffect
          G n S D e a₀ b₀ u.2.1 u.2.2.1))
      (unconditionalConjugatePureVector
        (tensorEmbezzlementTarget (n := e)
          (exactGlobalHistoryFinPsi G n S D u.2.2.2
            u.2.1 u.2.2.1))) =
    exactSourceConditionalWinningProbability G n S D u := by
  rw [unconditionalConjugateSourceGlobalCatalystWinningEffect_quadratic]
  exact
    (exactSourceGlobalCatalystWinningEffect_law_supported_verifier
      G n S D positive e residual_positive a₀ b₀ u supported).symm
end
end QuantumParallelRepetition

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option autoImplicit true
theorem unconditionalActualFairSourceEmbezzlementOne_apply :
    embezzlementState 1 (0, 0) = 1 := by
  simp [embezzlementState, rawEmbezzlementState,
    EuclideanSpace.norm_eq, Fintype.sum_prod_type]
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option autoImplicit true
theorem unconditionalActualFairSourceTensorEmbezzlementOne_reindex
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (Equiv.prodCongr
          (finCongr (Nat.mul_one d))
          (finCongr (Nat.mul_one d)))
        (tensorEmbezzlementTarget (n := 1) ξ) = ξ.val := by
  classical
  ext ⟨i, j⟩
  have first :
      (((finCongr (Nat.mul_one d)).symm i).divNat : Fin d) = i := by
    apply Fin.ext
    change i.val / 1 = i.val
    simp
  have second :
      (((finCongr (Nat.mul_one d)).symm j).divNat : Fin d) = j := by
    apply Fin.ext
    change j.val / 1 = j.val
    simp
  have first_work :
      (((finCongr (Nat.mul_one d)).symm i).modNat : Fin 1) = 0 :=
    Subsingleton.elim _ _
  have second_work :
      (((finCongr (Nat.mul_one d)).symm j).modNat : Fin 1) = 0 :=
    Subsingleton.elim _ _
  change
    ξ.val
        ((((finCongr (Nat.mul_one d)).symm i).divNat : Fin d),
         (((finCongr (Nat.mul_one d)).symm j).divNat : Fin d)) *
      embezzlementState 1
        ((((finCongr (Nat.mul_one d)).symm i).modNat : Fin 1),
         (((finCongr (Nat.mul_one d)).symm j).modNat : Fin 1)) =
      ξ.val (i, j)
  rw [first, second, first_work, second_work,
    unconditionalActualFairSourceEmbezzlementOne_apply, mul_one]
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option autoImplicit true
theorem
    unconditionalActualFairSourceConjugateTensorEmbezzlementOne_inverse_reindex
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (Equiv.prodCongr
          (finCongr (Nat.mul_one d)).symm
          (finCongr (Nat.mul_one d)).symm)
        (unconditionalConjugatePureVector ξ.val) =
      unconditionalConjugatePureVector
        (tensorEmbezzlementTarget (n := 1) ξ) := by
  classical
  ext ⟨i, j⟩
  change
    star (ξ.val
      ((finCongr (Nat.mul_one d)) i,
       (finCongr (Nat.mul_one d)) j)) =
      star (tensorEmbezzlementTarget (n := 1) ξ (i, j))
  congr 1
  have recovered := congrArg
    (fun z : EuclideanSpace ℂ (Fin d × Fin d) =>
      z ((finCongr (Nat.mul_one d)) i,
         (finCongr (Nat.mul_one d)) j))
    (unconditionalActualFairSourceTensorEmbezzlementOne_reindex ξ)
  simpa [LinearIsometryEquiv.piLpCongrLeft_apply] using recovered.symm
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option autoImplicit true
theorem unconditionalActualFairSourceWinningEffect_reindex
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [decA : DecidableEq A] [decB : DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (a₀ : A) (b₀ : B)
    (x : X) (y : Y) :
    directDSVActualLocalPOVMWinningEffect G
        (integratorActualC485SourceAlicePOVM G n S D a₀ x)
        (integratorActualC485SourceBobPOVM G n S D b₀ y)
        x y =
      Matrix.reindex
        (Equiv.prodCongr
          (finCongr
            (Nat.mul_one
              (Fintype.card
                (ExactGlobalHistoryLocalIndex G n S D))))
          (finCongr
            (Nat.mul_one
              (Fintype.card
                (ExactGlobalHistoryLocalIndex G n S D)))))
        (Equiv.prodCongr
          (finCongr
            (Nat.mul_one
              (Fintype.card
                (ExactGlobalHistoryLocalIndex G n S D))))
          (finCongr
            (Nat.mul_one
              (Fintype.card
                (ExactGlobalHistoryLocalIndex G n S D)))))
        (unconditionalConjugateSourceGlobalCatalystWinningEffect
          G n S D 1 a₀ b₀ x y) := by
  classical
  have alice_instance : decA = Classical.decEq A :=
    Subsingleton.elim _ _
  have bob_instance : decB = Classical.decEq B :=
    Subsingleton.elim _ _
  cases alice_instance
  cases bob_instance
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [directDSVActualLocalPOVMWinningEffect,
    integratorActualC485SourceAlicePOVM,
    integratorActualC485SourceBobPOVM,
    unconditionalConjugateSourceGlobalCatalystWinningEffect,
    reindexedPOVM, Matrix.reindex_apply,
    Matrix.sum_apply, Matrix.ite_apply, Matrix.zero_apply,
    Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map]
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option autoImplicit true
theorem unconditionalActualFairSourceEOneReindexedGlobalWinningBorn
    {d : ℕ}
    (winning :
      Matrix (Fin (d * 1) × Fin (d * 1))
        (Fin (d * 1) × Fin (d * 1)) ℂ)
    (ξ : BipartiteUnitVector d) :
    quadraticExpectation
      (Matrix.toEuclideanCLM (n := Fin d × Fin d) (𝕜 := ℂ)
        (Matrix.reindex
          (Equiv.prodCongr
            (finCongr (Nat.mul_one d))
            (finCongr (Nat.mul_one d)))
          (Equiv.prodCongr
            (finCongr (Nat.mul_one d))
            (finCongr (Nat.mul_one d))) winning))
      (unconditionalConjugatePureVector ξ.val) =
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := Fin (d * 1) × Fin (d * 1)) (𝕜 := ℂ) winning)
      (unconditionalConjugatePureVector
        (tensorEmbezzlementTarget (n := 1) ξ)) := by
  classical
  let e : (Fin (d * 1) × Fin (d * 1)) ≃ (Fin d × Fin d) :=
    Equiv.prodCongr (finCongr (Nat.mul_one d))
      (finCongr (Nat.mul_one d))
  calc
    _ = quadraticExpectation
        (Matrix.toEuclideanCLM
          (n := Fin (d * 1) × Fin (d * 1)) (𝕜 := ℂ) winning)
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e.symm
          (unconditionalConjugatePureVector ξ.val)) := by
          exact directDSVActualReindexedWinningEffect_quadratic
            e.symm winning
            (unconditionalConjugatePureVector ξ.val)
    _ = _ := by
          congr 1
          exact
            unconditionalActualFairSourceConjugateTensorEmbezzlementOne_inverse_reindex
              ξ
end
end QuantumParallelRepetition

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option autoImplicit true
theorem _root_.solution
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (a₀ : A) (b₀ : B)
    (h : ExactLocallySampleableTuple X Y A B D)
    (supported : exactLocallySampleableLaw G n S D h ≠ 0) :
    quadraticExpectation
      (unconditionalActualFairSourceBaseWinningCLM
        G n S D a₀ b₀ h.2.1 h.2.2.1)
      (unconditionalConjugatePureVector
        (exactSourceTuplePsi G n S D h)) =
      exactSourceConditionalWinningProbability G n S D h := by
  classical
  unfold unconditionalActualFairSourceBaseWinningCLM
  calc
    _ = quadraticExpectation
          (Matrix.toEuclideanCLM
            (n :=
              Fin (Fintype.card
                (ExactGlobalHistoryLocalIndex G n S D)) ×
              Fin (Fintype.card
                (ExactGlobalHistoryLocalIndex G n S D)))
            (𝕜 := ℂ)
            (Matrix.reindex
              (Equiv.prodCongr
                (finCongr (Nat.mul_one
                  (Fintype.card
                    (ExactGlobalHistoryLocalIndex G n S D))))
                (finCongr (Nat.mul_one
                  (Fintype.card
                    (ExactGlobalHistoryLocalIndex G n S D)))))
              (Equiv.prodCongr
                (finCongr (Nat.mul_one
                  (Fintype.card
                    (ExactGlobalHistoryLocalIndex G n S D))))
                (finCongr (Nat.mul_one
                  (Fintype.card
                    (ExactGlobalHistoryLocalIndex G n S D)))))
              (unconditionalConjugateSourceGlobalCatalystWinningEffect
                G n S D 1 a₀ b₀ h.2.1 h.2.2.1)))
          (unconditionalConjugatePureVector
            (exactSourceTuplePsi G n S D h)) := by
              congr 2
              exact unconditionalActualFairSourceWinningEffect_reindex
                G n S D a₀ b₀ h.2.1 h.2.2.1
    _ = quadraticExpectation
          (Matrix.toEuclideanCLM
            (n :=
              Fin (Fintype.card
                (ExactGlobalHistoryLocalIndex G n S D) * 1) ×
              Fin (Fintype.card
                (ExactGlobalHistoryLocalIndex G n S D) * 1))
            (𝕜 := ℂ)
            (unconditionalConjugateSourceGlobalCatalystWinningEffect
              G n S D 1 a₀ b₀ h.2.1 h.2.2.1))
          (unconditionalConjugatePureVector
            (tensorEmbezzlementTarget (n := 1)
              (exactGlobalHistoryFinPsi
                G n S D h.2.2.2 h.2.1 h.2.2.1))) := by
              exact unconditionalActualFairSourceEOneReindexedGlobalWinningBorn
                (unconditionalConjugateSourceGlobalCatalystWinningEffect
                  G n S D 1 a₀ b₀ h.2.1 h.2.2.1)
                (exactGlobalHistoryFinPsi
                  G n S D h.2.2.2 h.2.1 h.2.2.1)
    _ = _ :=
      unconditionalConjugateSourceGlobalCatalystWinningEffect_law_supported
        G n S D positive 1 (by norm_num) a₀ b₀ h supported
end QuantumParallelRepetition

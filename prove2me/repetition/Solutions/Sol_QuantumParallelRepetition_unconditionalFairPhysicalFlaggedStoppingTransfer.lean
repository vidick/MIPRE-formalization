/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Repetition/TenProofs/QuantumParallelRepetition/Part08.lean (solution of QuantumParallelRepetition.unconditionalFairPhysicalFlaggedStoppingTransfer);
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
import Theorems.Thm_QuantumParallelRepetition_actualStoppingGlobalBorn_eq_sum
import Theorems.Thm_QuantumParallelRepetition_actualStoppingQuestionLocalWinningEffect_quadratic
import Theorems.Thm_QuantumParallelRepetition_convexMixtureStrategy_winProbability
import Theorems.Thm_QuantumParallelRepetition_exactLocallySampleableLaw_absolute_continuous_roundedJA
import Theorems.Thm_QuantumParallelRepetition_exactLocallySampleableLaw_nonneg
import Theorems.Thm_QuantumParallelRepetition_exactLocallySampleableLaw_sum
import Theorems.Thm_QuantumParallelRepetition_exactSeedWeight_nonneg
import Theorems.Thm_QuantumParallelRepetition_exactSourceAcceptedCoordinateMass_le_law
import Theorems.Thm_QuantumParallelRepetition_exactSourceAcceptedCoordinateMass_sum_eq_remaining_average
import Theorems.Thm_QuantumParallelRepetition_exactSourceAliceSampleTuple_expectation
import Theorems.Thm_QuantumParallelRepetition_exactSourceConditionalWinningProbability_bounds
import Theorems.Thm_QuantumParallelRepetition_finiteGroupedExpectation_eq_atom_sum
import Theorems.Thm_QuantumParallelRepetition_finiteTotalVariation_comm
import Theorems.Thm_QuantumParallelRepetition_matched_payoff_discard_le
import Theorems.Thm_QuantumParallelRepetition_pureDensityMatrix_trace_mul
import Theorems.Thm_QuantumParallelRepetition_sourceHistoryAcceptedMass_eq_remaining_average
import Theorems.Thm_QuantumParallelRepetition_sourceHistoryAcceptedMass_gt_of_greedy
import Theorems.Thm_QuantumParallelRepetition_unconditionalWeightedClippedMatchedVerifierAndMassLoss

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
attribute [instance] QuantumParallelRepetition.Strategy.alice_fintype QuantumParallelRepetition.Strategy.bob_fintype QuantumParallelRepetition.Strategy.alice_decidableEq QuantumParallelRepetition.Strategy.bob_decidableEq

namespace QuantumParallelRepetition
section
open scoped BigOperators ComplexConjugate InnerProductSpace
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
attribute [instance] QuantumParallelRepetition.Strategy.alice_fintype QuantumParallelRepetition.Strategy.bob_fintype QuantumParallelRepetition.Strategy.alice_decidableEq QuantumParallelRepetition.Strategy.bob_decidableEq
theorem positive_quadraticExpectation_nonneg
    (W : H →L[ℂ] H) (hW : W.IsPositive) (z : H) :
    0 ≤ quadraticExpectation W z := by
  exact hW.re_inner_nonneg_right z
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
set_option autoImplicit true
attribute [instance] QuantumParallelRepetition.Strategy.alice_fintype QuantumParallelRepetition.Strategy.bob_fintype QuantumParallelRepetition.Strategy.alice_decidableEq QuantumParallelRepetition.Strategy.bob_decidableEq
theorem matrixEffectCLM_isPositive
    {d : Type*} [Fintype d] [DecidableEq d]
    (E : Matrix d d ℂ) (hE : E.PosSemidef) :
    (Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ) E).IsPositive := by
  apply (ContinuousLinearMap.isPositive_toLinearMap_iff _).mp
  exact Matrix.isPositive_toEuclideanLin_iff.mpr hE
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition.Strategy
section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
set_option autoImplicit true
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {G : Game X Y A B}
attribute [instance] QuantumParallelRepetition.Strategy.alice_fintype QuantumParallelRepetition.Strategy.bob_fintype QuantumParallelRepetition.Strategy.alice_decidableEq QuantumParallelRepetition.Strategy.bob_decidableEq
theorem winningEffect_born
    (S : Strategy G) (x : X) (y : Y) :
    (Matrix.trace (S.state.matrix * S.winningEffect x y)).re =
      ∑ a : A, ∑ b : B,
        if G.predicate x y a b = true then
          S.outcomeProbability x y a b else 0 := by
  classical
  simp [winningEffect, outcomeProbability, Matrix.mul_sum,
    Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split <;> simp
end
end QuantumParallelRepetition.Strategy

namespace QuantumParallelRepetition.Strategy
section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
set_option autoImplicit true
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {G : Game X Y A B}
attribute [instance] QuantumParallelRepetition.Strategy.alice_fintype QuantumParallelRepetition.Strategy.bob_fintype QuantumParallelRepetition.Strategy.alice_decidableEq QuantumParallelRepetition.Strategy.bob_decidableEq
theorem winProbability_eq_winningEffect_born
    (S : Strategy G) :
    S.winProbability =
      ∑ x : X, ∑ y : Y,
        G.questionWeight x y *
          (Matrix.trace (S.state.matrix * S.winningEffect x y)).re := by
  simp_rw [S.winningEffect_born]
  rfl
end
end QuantumParallelRepetition.Strategy

namespace QuantumParallelRepetition
section
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option autoImplicit true
attribute [instance] QuantumParallelRepetition.Strategy.alice_fintype QuantumParallelRepetition.Strategy.bob_fintype QuantumParallelRepetition.Strategy.alice_decidableEq QuantumParallelRepetition.Strategy.bob_decidableEq
theorem pureFlaggedStrategy_winProbability
    {X Y A B : Type*} {dA dB J : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype dA] [Fintype dB] [DecidableEq dA] [DecidableEq dB]
    [Fintype J] [DecidableEq J]
    (G : Game X Y A B)
    (p : J → ℝ) (hp : ∀ j, 0 ≤ p j)
    (h_normalized : (∑ j : J, p j) = 1)
    (z : J → EuclideanSpace ℂ (dA × dB))
    (hz : ∀ j, ‖z j‖ = 1)
    (PA : J → X → POVM A dA)
    (PB : J → Y → POVM B dB) :
    (pureFlaggedStrategy G p hp h_normalized z hz PA PB).winProbability =
      ∑ j : J, p j *
        (pureVectorStrategy G (z j) (hz j) (PA j) (PB j)).winProbability := by
  exact convexMixtureStrategy_winProbability p hp h_normalized
    (fun j => pureVectorStrategy G (z j) (hz j) (PA j) (PB j))
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
open QuantumParallelRepetition.Pinsker
set_option autoImplicit true
theorem sum_positive_difference_eq_totalVariation
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ)
    (hp : (∑ i, p i) = 1)
    (hq : (∑ i, q i) = 1) :
    (∑ i, max (p i - q i) 0) = finiteTotalVariation p q := by
  classical
  have hpoint (x : ℝ) : max x 0 = (|x| + x) / 2 := by
    by_cases hx : 0 ≤ x
    · rw [max_eq_left hx, abs_of_nonneg hx]
      ring
    · have hxneg : x < 0 := lt_of_not_ge hx
      rw [max_eq_right hxneg.le, abs_of_neg hxneg]
      ring
  have hzero : (∑ i, (p i - q i)) = 0 := by
    rw [Finset.sum_sub_distrib, hp, hq, sub_self]
  unfold finiteTotalVariation
  simp_rw [hpoint]
  rw [← Finset.sum_div, Finset.sum_add_distrib, hzero, add_zero]
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
open QuantumParallelRepetition.Pinsker
set_option autoImplicit true
theorem expectation_le_add_totalVariation
    {ι : Type*} [Fintype ι]
    (p q f : ι → ℝ)
    (hp : (∑ i, p i) = 1)
    (hq : (∑ i, q i) = 1)
    (U : ℝ)
    (hfzero : ∀ i, 0 ≤ f i)
    (hfupper : ∀ i, f i ≤ U) :
    (∑ i, p i * f i) ≤
      (∑ i, q i * f i) + U * finiteTotalVariation p q := by
  classical
  have hterm (i : ι) :
      (p i - q i) * f i ≤ U * max (p i - q i) 0 := by
    by_cases hi : 0 ≤ p i - q i
    · rw [max_eq_left hi]
      nlinarith [mul_nonneg hi (sub_nonneg.mpr (hfupper i))]
    · have hineg : p i - q i < 0 := lt_of_not_ge hi
      rw [max_eq_right hineg.le]
      simp only [mul_zero]
      exact mul_nonpos_of_nonpos_of_nonneg hineg.le (hfzero i)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
  have hpositive := sum_positive_difference_eq_totalVariation p q hp hq
  calc
    (∑ i, p i * f i) =
        (∑ i, q i * f i) + ∑ i, (p i - q i) * f i := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ ≤ (∑ i, q i * f i) +
          ∑ i, U * max (p i - q i) 0 := by
      linarith
    _ = (∑ i, q i * f i) +
          U * finiteTotalVariation p q := by
      rw [← Finset.mul_sum, hpositive]
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
open QuantumParallelRepetition.Pinsker
set_option autoImplicit true
theorem winning_expectation_transfer
    {ι : Type*} [Fintype ι]
    (p q win : ι → ℝ)
    (hp : (∑ i, p i) = 1)
    (hq : (∑ i, q i) = 1)
    (hzero : ∀ i, 0 ≤ win i)
    (hone : ∀ i, win i ≤ 1) :
    (∑ i, q i * win i) - finiteTotalVariation p q ≤
      ∑ i, p i * win i := by
  have h := expectation_le_add_totalVariation
    q p win hq hp (1 : ℝ) hzero hone
  rw [← finiteTotalVariation_comm p q] at h
  norm_num at h ⊢
  linarith
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option autoImplicit true
variable {X Y A B dA dB J : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype dA] [Fintype dB] [DecidableEq dA] [DecidableEq dB]
variable [Fintype J] [DecidableEq J]
theorem pureVectorWinningProbability_eq
    (G : Game X Y A B)
    (z : EuclideanSpace ℂ (dA × dB)) (hz : ‖z‖ = 1)
    (PA : X → POVM A dA) (PB : Y → POVM B dB) :
    (pureVectorStrategy G z hz PA PB).winProbability =
      ∑ x : X, ∑ y : Y, G.questionWeight x y *
        quadraticExpectation
          (Matrix.toEuclideanCLM (n := dA × dB) (𝕜 := ℂ)
            (pureVerifierEffect G z hz PA PB x y)) z := by
  classical
  rw [(pureVectorStrategy G z hz PA PB).winProbability_eq_winningEffect_born]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  exact pureDensityMatrix_trace_mul z hz
    (pureVerifierEffect G z hz PA PB x y)
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option autoImplicit true
variable {X Y A B dA dB J : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype dA] [Fintype dB] [DecidableEq dA] [DecidableEq dB]
variable [Fintype J] [DecidableEq J]
omit [Fintype J] [DecidableEq J] in

theorem flaggedQuestionWeight_nonneg
    (G : Game X Y A B) (flagWeight : J → ℝ)
    (nonnegative : ∀ j, 0 ≤ flagWeight j)
    (ω : J × (X × Y)) :
    0 ≤ flaggedQuestionWeight G flagWeight ω :=
  mul_nonneg (nonnegative ω.1)
    (G.weight_nonneg ω.2.1 ω.2.2)
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option autoImplicit true
variable {X Y A B dA dB J : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype dA] [Fintype dB] [DecidableEq dA] [DecidableEq dB]
variable [Fintype J] [DecidableEq J]
omit [DecidableEq J] in

theorem flaggedQuestionWeight_sum
    (G : Game X Y A B) (flagWeight : J → ℝ)
    (normalized : (∑ j, flagWeight j) = 1) :
    (∑ ω : J × (X × Y),
      flaggedQuestionWeight G flagWeight ω) = 1 := by
  classical
  simp [flaggedQuestionWeight, Fintype.sum_prod_type,
    ← Finset.mul_sum, G.weight_normalized, normalized]
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
attribute [local instance] Classical.propDecidable
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
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
attribute [local instance] Classical.propDecidable
theorem exactPostselectedJointLaw_nonneg
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (q : ExactJointOutcome X Y A B D) :
    0 ≤ exactPostselectedJointLaw G n S D q := by
  apply mul_nonneg (exactSeedWeight_nonneg q.1)
  exact conditionedEventDistribution_nonneg
    (strategyEventLaw (G.repeat n) S)
    (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)
    positive q.2
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalSampling
open QuantumParallelRepetition.ClassicalInformation
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
attribute [local instance] Classical.propDecidable
theorem exactSourceAliceSampleTuple_groupedMass
    (G : Game X Y A B) (n : ℕ) (D : Finset (Fin n))
    (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (normalized : ∀ k, (∑ r, numerator k r) = denominator)
    (nonempty : ∀ k,
      (rationalMarked denominator (numerator k)).Nonempty)
    (history : ExactLocallySampleableTuple X Y A B D) :
    groupedMass
      (exactSourceAliceSampleTuple
        D denominator numerator nonempty)
      (flaggedQuestionWeight G
        (exactSourceSharedFlagWeight D denominator)) history =
      exactLocallySampleableJARounded
        G n D denominator numerator history := by
  classical
  have expectation := exactSourceAliceSampleTuple_expectation
    G n D denominator numerator normalized nonempty
    (fun candidate => if candidate = history then (1 : ℝ) else 0)
  simpa [groupedMass, Finset.sum_filter, mul_ite] using expectation
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
variable {Ω T : Type*} [Fintype Ω] [Fintype T] [DecidableEq T]
attribute [local instance] Classical.propDecidable
omit [Fintype T] in

theorem exactFiniteFiberLift_groupedMass
    (projection : Ω → T) (original : Ω → ℝ) (target : T → ℝ)
    (supported : ∀ point,
      groupedMass projection original point = 0 → target point = 0)
    (point : T) :
    groupedMass projection
      (exactFiniteFiberLift projection original target) point =
        target point := by
  classical
  change
    (∑ outcome ∈
      (Finset.univ.filter fun outcome : Ω =>
        projection outcome = point),
      exactFiniteFiberLift projection original target outcome) =
        target point
  calc
    (∑ outcome ∈
      (Finset.univ.filter fun outcome : Ω =>
        projection outcome = point),
      exactFiniteFiberLift projection original target outcome) =
      ∑ outcome ∈
        (Finset.univ.filter fun outcome : Ω =>
          projection outcome = point),
        target point * original outcome /
          groupedMass projection original point := by
          apply Finset.sum_congr rfl
          intro outcome member
          have same : projection outcome = point :=
            (Finset.mem_filter.mp member).2
          simp [exactFiniteFiberLift, same]
    _ = target point * groupedMass projection original point /
          groupedMass projection original point := by
          rw [← Finset.sum_div, ← Finset.mul_sum]
          rfl
    _ = target point := by
          by_cases empty : groupedMass projection original point = 0
          · simp [empty, supported point empty]
          · field_simp
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
variable {Ω T : Type*} [Fintype Ω] [Fintype T] [DecidableEq T]
attribute [local instance] Classical.propDecidable
theorem exactFiniteFiberLift_expectation
    (projection : Ω → T) (original : Ω → ℝ) (target : T → ℝ)
    (supported : ∀ point,
      groupedMass projection original point = 0 → target point = 0)
    (value : T → ℝ) :
    (∑ outcome : Ω,
      exactFiniteFiberLift projection original target outcome *
        value (projection outcome)) =
      ∑ point : T, target point * value point := by
  calc
    (∑ outcome : Ω,
      exactFiniteFiberLift projection original target outcome *
        value (projection outcome)) =
      ∑ point : T,
        groupedMass projection
          (exactFiniteFiberLift projection original target) point *
            value point :=
      (finiteGroupedExpectation_eq_atom_sum projection
        (exactFiniteFiberLift projection original target)
        value).symm
    _ = ∑ point : T, target point * value point := by
      simp_rw [exactFiniteFiberLift_groupedMass
        projection original target supported]
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.ClassicalInformation
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
attribute [local instance] Classical.propDecidable
theorem exactSourceAcceptedCoordinateMass_nonneg
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (t : ExactLocallySampleableTuple X Y A B D) :
    0 ≤ exactSourceAcceptedCoordinateMass G n S D t := by
  unfold exactSourceAcceptedCoordinateMass
  apply Finset.sum_nonneg
  intro q _
  split
  · exact exactPostselectedJointLaw_nonneg
      G n S D positive q
  · exact le_rfl
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.ClassicalInformation
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
attribute [local instance] Classical.propDecidable
theorem exactSourceConditionalWinningProbability_mul_law
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (t : ExactLocallySampleableTuple X Y A B D) :
    exactLocallySampleableLaw G n S D t *
        exactSourceConditionalWinningProbability G n S D t =
      exactSourceAcceptedCoordinateMass G n S D t := by
  by_cases zero : exactLocallySampleableLaw G n S D t = 0
  · have nonnegative := exactSourceAcceptedCoordinateMass_nonneg
      G n S D positive t
    have bounded := exactSourceAcceptedCoordinateMass_le_law
      G n S D positive t
    rw [zero] at bounded
    have accepted_zero :
        exactSourceAcceptedCoordinateMass G n S D t = 0 := by
      linarith
    simp [zero, accepted_zero]
  · unfold exactSourceConditionalWinningProbability
    field_simp [zero]
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.ClassicalInformation
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
attribute [local instance] Classical.propDecidable
theorem exactSourceAcceptedCoordinateMass_sum
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) :
    (∑ t : ExactLocallySampleableTuple X Y A B D,
      exactSourceAcceptedCoordinateMass G n S D t) =
      ∑ q : ExactJointOutcome X Y A B D,
        if repeatedCoordinateWin G n q.1.coordinate.val q.2 = true
        then exactPostselectedJointLaw G n S D q
        else 0 := by
  classical
  unfold exactSourceAcceptedCoordinateMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  by_cases winning :
      repeatedCoordinateWin G n q.1.coordinate.val q.2 = true
  · simp [winning]
  · simp [winning]
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.ClassicalInformation
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
attribute [local instance] Classical.propDecidable
theorem exactSourceConditionalWinningProbability_expectation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D) :
    (∑ t : ExactLocallySampleableTuple X Y A B D,
      exactLocallySampleableLaw G n S D t *
        exactSourceConditionalWinningProbability G n S D t) =
      ∑ q : ExactJointOutcome X Y A B D,
        if repeatedCoordinateWin G n q.1.coordinate.val q.2 = true
        then exactPostselectedJointLaw G n S D q
        else 0 := by
  simp_rw [exactSourceConditionalWinningProbability_mul_law
    G n S D positive]
  exact exactSourceAcceptedCoordinateMass_sum G n S D
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.ClassicalInformation
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
attribute [local instance] Classical.propDecidable
theorem exactSourceConditionalWinningProbability_eq_accepted_average
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D) :
    (∑ t : ExactLocallySampleableTuple X Y A B D,
      exactLocallySampleableLaw G n S D t *
        exactSourceConditionalWinningProbability G n S D t) =
      sourceHistoryAcceptedMass G n S D /
        repeatedPostselectionMass G n S D := by
  rw [exactSourceConditionalWinningProbability_expectation
    G n S D positive,
    ← exactSourceAcceptedCoordinateMass_sum,
    exactSourceAcceptedCoordinateMass_sum_eq_remaining_average,
    sourceHistoryAcceptedMass_eq_remaining_average]
  have cardinality :
      Fintype.card (SourceRemainingCoordinate D) =
        (Finset.univ \ D).card := by
    simpa only [Fintype.card_fin] using Fintype.card_congr
      (Finset.equivFin (Finset.univ \ D))
  push_cast [cardinality]
  rw [← Finset.sum_div]
  ring
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.ClassicalInformation
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
attribute [local instance] Classical.propDecidable
theorem exactSource_failure_sum_lt_of_uniform
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    {δ : ℝ}
    (failure : uniformRemainingFailure
      (strategyEventLaw (G.repeat n) S)
      (repeatedCoordinateWin G n) D < δ) :
    (∑ i ∈ Finset.univ \ D,
      FiniteEventLaw.failureMass
        (strategyEventLaw (G.repeat n) S)
        (repeatedCoordinateWin G n) D i) <
      ((Finset.univ \ D).card : ℝ) *
        (δ * repeatedPostselectionMass G n S D) := by
  have cardinality : 0 < ((Finset.univ \ D).card : ℝ) := by
    exact_mod_cast remaining
  unfold uniformRemainingFailure conditionalCoordinateFailure at failure
  change
    (∑ i ∈ Finset.univ \ D,
      FiniteEventLaw.failureMass
        (strategyEventLaw (G.repeat n) S)
        (repeatedCoordinateWin G n) D i /
        repeatedPostselectionMass G n S D) /
      ((Finset.univ \ D).card : ℝ) < δ at failure
  rw [← Finset.sum_div] at failure
  have first := (div_lt_iff₀ cardinality).mp failure
  have second := (div_lt_iff₀ positive).mp first
  nlinarith
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.ClassicalInformation
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
attribute [local instance] Classical.propDecidable
theorem exactSourceConditionalWinningProbability_gt_of_uniform_failure
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    {δ : ℝ}
    (failure : uniformRemainingFailure
      (strategyEventLaw (G.repeat n) S)
      (repeatedCoordinateWin G n) D < δ) :
    1 - δ <
      ∑ t : ExactLocallySampleableTuple X Y A B D,
        exactLocallySampleableLaw G n S D t *
          exactSourceConditionalWinningProbability G n S D t := by
  rw [exactSourceConditionalWinningProbability_eq_accepted_average
    G n S D positive]
  have numerator := exactSource_failure_sum_lt_of_uniform
    G n S D remaining positive failure
  have accepted := sourceHistoryAcceptedMass_gt_of_greedy
    G n S D remaining numerator
  apply (lt_div_iff₀ positive).mpr
  exact accepted
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalSampling
open QuantumParallelRepetition.ClassicalInformation
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
variable {X Y A B dA dB : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype dA] [Fintype dB] [DecidableEq dA] [DecidableEq dB]
attribute [local instance] Classical.propDecidable
theorem exactSourceAliceFlagCoupling_supported
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (denominator : ℕ) (denominator_positive : 0 < denominator)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (normalized : ∀ index,
      (∑ history, numerator index history) = denominator)
    (preserves : ∀ index history,
      0 < exactLocalConditionalFamily D base
          (exactLocallySampleableLaw G n S D) index history →
        0 < numerator index history)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    (history : ExactLocallySampleableTuple X Y A B D) :
    groupedMass
        (exactSourceAliceSampleTuple
          D denominator numerator nonempty)
        (flaggedQuestionWeight G
          (exactSourceSharedFlagWeight D denominator)) history = 0 →
      exactLocallySampleableLaw G n S D history = 0 := by
  rw [exactSourceAliceSampleTuple_groupedMass
    G n D denominator numerator normalized nonempty]
  exact exactLocallySampleableLaw_absolute_continuous_roundedJA
    G n S D remaining positive base denominator denominator_positive
    numerator preserves history
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalSampling
open QuantumParallelRepetition.ClassicalInformation
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
variable {X Y A B dA dB : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype dA] [Fintype dB] [DecidableEq dA] [DecidableEq dB]
attribute [local instance] Classical.propDecidable
theorem exactSourceAliceFlagCoupling_expectation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (denominator : ℕ) (denominator_positive : 0 < denominator)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (normalized : ∀ index,
      (∑ history, numerator index history) = denominator)
    (preserves : ∀ index history,
      0 < exactLocalConditionalFamily D base
          (exactLocallySampleableLaw G n S D) index history →
        0 < numerator index history)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    (value : ExactLocallySampleableTuple X Y A B D → ℝ) :
    (∑ outcome :
      ExactSourceSharedFlag X Y A B D denominator × (X × Y),
      exactSourceAliceFlagCoupling
        G n S D denominator numerator nonempty outcome *
        value (exactSourceAliceSampleTuple
          D denominator numerator nonempty outcome)) =
      ∑ history : ExactLocallySampleableTuple X Y A B D,
        exactLocallySampleableLaw G n S D history *
          value history := by
  exact exactFiniteFiberLift_expectation
    (exactSourceAliceSampleTuple
      D denominator numerator nonempty)
    (flaggedQuestionWeight G
      (exactSourceSharedFlagWeight D denominator))
    (exactLocallySampleableLaw G n S D)
    (exactSourceAliceFlagCoupling_supported
      G n S D remaining positive base denominator denominator_positive
      numerator normalized preserves nonempty)
    value
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalSampling
open QuantumParallelRepetition.ClassicalInformation
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
variable {X Y A B dA dB : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype dA] [Fintype dB] [DecidableEq dA] [DecidableEq dB]
attribute [local instance] Classical.propDecidable
theorem exactSourceAliceFlagCoupling_sum
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (denominator : ℕ) (denominator_positive : 0 < denominator)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (normalized : ∀ index,
      (∑ history, numerator index history) = denominator)
    (preserves : ∀ index history,
      0 < exactLocalConditionalFamily D base
          (exactLocallySampleableLaw G n S D) index history →
        0 < numerator index history)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty) :
    (∑ outcome :
      ExactSourceSharedFlag X Y A B D denominator × (X × Y),
      exactSourceAliceFlagCoupling
        G n S D denominator numerator nonempty outcome) = 1 := by
  have expectation := exactSourceAliceFlagCoupling_expectation
    G n S D remaining positive base denominator denominator_positive
    numerator normalized preserves nonempty (fun _ => (1 : ℝ))
  simpa [exactLocallySampleableLaw_sum
    G n S D remaining positive] using expectation
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
variable {X Y A B R : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype R] [DecidableEq R]
variable {ι κ : R → Type}
variable [∀ r, Fintype (ι r)] [∀ r, DecidableEq (ι r)]
variable [∀ r, Fintype (κ r)] [∀ r, DecidableEq (κ r)]
attribute [local instance] Classical.propDecidable
omit [Fintype R] [DecidableEq R] in

theorem actualStoppingBranchWinningEffect_posSemidef
    (G : Game X Y A B)
    (PA : (r : R) → X → POVM A (ι r))
    (PB : (s : R) → Y → POVM B (κ s))
    (r s : R) (x : X) (y : Y) :
    (actualStoppingBranchWinningEffect
      G PA PB r s x y).PosSemidef := by
  classical
  apply Matrix.nonneg_iff_posSemidef.mp
  unfold actualStoppingBranchWinningEffect
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro b _
  split
  · exact ((PA r x).positive a).kronecker
      ((PB s y).positive b) |>.nonneg
  · exact le_rfl
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
variable {X Y A B R : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype R] [DecidableEq R]
variable {ι κ : R → Type}
variable [∀ r, Fintype (ι r)] [∀ r, DecidableEq (ι r)]
variable [∀ r, Fintype (κ r)] [∀ r, DecidableEq (κ r)]
attribute [local instance] Classical.propDecidable
omit [Fintype R] [DecidableEq R] in

theorem actualStoppingBranchBorn_nonneg
    (G : Game X Y A B)
    (PA : (r : R) → X → POVM A (ι r))
    (PB : (s : R) → Y → POVM B (κ s))
    (z : EuclideanSpace ℂ ((Σ r, ι r) × (Σ s, κ s)))
    (r s : R) (x : X) (y : Y) :
    0 ≤ quadraticExpectation
      (Matrix.toEuclideanCLM (n := ι r × κ s) (𝕜 := ℂ)
        (actualStoppingBranchWinningEffect
          G PA PB r s x y))
      (actualStoppingBranchVector z r s) := by
  apply positive_quadraticExpectation_nonneg
  apply matrixEffectCLM_isPositive
  exact actualStoppingBranchWinningEffect_posSemidef
    G PA PB r s x y
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
variable {X Y A B R : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype R] [DecidableEq R]
variable {ι : R → Type}
variable [∀ r, Fintype (ι r)] [∀ r, DecidableEq (ι r)]
attribute [local instance] Classical.propDecidable
theorem actualStoppingQuestionLocalWinningProbability_eq_sum
    (G : Game X Y A B)
    (PA : (r : R) → X → POVM A (ι r))
    (PB : (r : R) → Y → POVM B (ι r))
    (U : X → Matrix.unitaryGroup (Σ r, ι r) ℂ)
    (V : Y → Matrix.unitaryGroup (Σ r, ι r) ℂ)
    (z : EuclideanSpace ℂ ((Σ r, ι r) × (Σ r, ι r)))
    (normalized : ‖z‖ = 1) :
    (pureVectorStrategy G z normalized
      (fun x => unitaryConjugatePOVM (U x)
        (dependentBlockPOVM (fun r => PA r x)))
      (fun y => unitaryConjugatePOVM (V y)
        (dependentBlockPOVM (fun r => PB r y)))).winProbability =
      ∑ x : X, ∑ y : Y, G.questionWeight x y *
        ∑ r : R, ∑ s : R,
          quadraticExpectation
            (Matrix.toEuclideanCLM (n := ι r × ι s) (𝕜 := ℂ)
              (actualStoppingBranchWinningEffect
                G PA PB r s x y))
            (actualStoppingBranchVector
              (actualStoppingQuestionLocalAction
                (U x) (V y) z) r s) := by
  classical
  rw [pureVectorWinningProbability_eq]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  rw [actualStoppingQuestionLocalWinningEffect_quadratic]
  exact actualStoppingGlobalBorn_eq_sum
    G PA PB (actualStoppingQuestionLocalAction
      (U x) (V y) z) x y
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
variable {X Y A B R : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype R] [DecidableEq R]
variable {ι : R → Type}
variable [∀ r, Fintype (ι r)] [∀ r, DecidableEq (ι r)]
attribute [local instance] Classical.propDecidable
theorem actualStoppingQuestionLocalWinningProbability_ge_matched
    {L : ℕ}
    {ι : Fin (L + 1) → Type}
    [∀ r, Fintype (ι r)] [∀ r, DecidableEq (ι r)]
    (G : Game X Y A B)
    (PA : (r : Fin (L + 1)) → X → POVM A (ι r))
    (PB : (r : Fin (L + 1)) → Y → POVM B (ι r))
    (U : X → Matrix.unitaryGroup (Σ r, ι r) ℂ)
    (V : Y → Matrix.unitaryGroup (Σ r, ι r) ℂ)
    (z : EuclideanSpace ℂ
      ((Σ r : Fin (L + 1), ι r) ×
       (Σ r : Fin (L + 1), ι r)))
    (normalized : ‖z‖ = 1) :
    (∑ x : X, ∑ y : Y, G.questionWeight x y *
      ∑ j : Fin L,
        quadraticExpectation
          (Matrix.toEuclideanCLM
            (n := ι j.succ × ι j.succ) (𝕜 := ℂ)
            (actualStoppingBranchWinningEffect
              G PA PB j.succ j.succ x y))
          (actualStoppingBranchVector
            (actualStoppingQuestionLocalAction
              (U x) (V y) z) j.succ j.succ)) ≤
      (pureVectorStrategy G z normalized
        (fun x => unitaryConjugatePOVM (U x)
          (dependentBlockPOVM (fun r => PA r x)))
        (fun y => unitaryConjugatePOVM (V y)
          (dependentBlockPOVM (fun r => PB r y)))).winProbability := by
  classical
  rw [actualStoppingQuestionLocalWinningProbability_eq_sum]
  apply Finset.sum_le_sum
  intro x _
  apply Finset.sum_le_sum
  intro y _
  apply mul_le_mul_of_nonneg_left _ (G.weight_nonneg x y)
  let stopped := actualStoppingQuestionLocalAction
    (U x) (V y) z
  calc
    (∑ j : Fin L,
      quadraticExpectation
        (Matrix.toEuclideanCLM
          (n := ι j.succ × ι j.succ) (𝕜 := ℂ)
          (actualStoppingBranchWinningEffect
            G PA PB j.succ j.succ x y))
        (actualStoppingBranchVector stopped
          j.succ j.succ)) ≤
        ∑ r : Fin (L + 1),
          quadraticExpectation
            (Matrix.toEuclideanCLM (n := ι r × ι r) (𝕜 := ℂ)
              (actualStoppingBranchWinningEffect
                G PA PB r r x y))
            (actualStoppingBranchVector stopped r r) := by
          rw [Fin.sum_univ_succ]
          have nonnegative := actualStoppingBranchBorn_nonneg
            G PA PB stopped (0 : Fin (L + 1)) 0 x y
          linarith
    _ ≤ ∑ r : Fin (L + 1), ∑ s : Fin (L + 1),
          quadraticExpectation
            (Matrix.toEuclideanCLM (n := ι r × ι s) (𝕜 := ℂ)
              (actualStoppingBranchWinningEffect
                G PA PB r s x y))
            (actualStoppingBranchVector stopped r s) := by
          apply Finset.sum_le_sum
          intro r _
          exact Finset.single_le_sum
            (fun s _ => actualStoppingBranchBorn_nonneg
              G PA PB stopped r s x y)
            (Finset.mem_univ r)
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
variable {X Y A B R : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype R] [DecidableEq R]
variable {ι : R → Type}
variable [∀ r, Fintype (ι r)] [∀ r, DecidableEq (ι r)]
attribute [local instance] Classical.propDecidable
theorem actualStoppingQuestionLocalFlaggedWinningProbability_ge_matched
    {L : ℕ} {J : Type} [Fintype J] [DecidableEq J]
    {ι : Fin (L + 1) → Type}
    [∀ r, Fintype (ι r)] [∀ r, DecidableEq (ι r)]
    (G : Game X Y A B)
    (weight : J → ℝ)
    (weight_nonnegative : ∀ j, 0 ≤ weight j)
    (weight_normalized : (∑ j : J, weight j) = 1)
    (PA : J → (r : Fin (L + 1)) → X → POVM A (ι r))
    (PB : J → (r : Fin (L + 1)) → Y → POVM B (ι r))
    (U : J → X → Matrix.unitaryGroup
      (Σ r : Fin (L + 1), ι r) ℂ)
    (V : J → Y → Matrix.unitaryGroup
      (Σ r : Fin (L + 1), ι r) ℂ)
    (z : J → EuclideanSpace ℂ
      ((Σ r : Fin (L + 1), ι r) ×
       (Σ r : Fin (L + 1), ι r)))
    (normalized : ∀ j, ‖z j‖ = 1) :
    (∑ q : J, weight q *
      (∑ x : X, ∑ y : Y, G.questionWeight x y *
        ∑ j : Fin L,
          quadraticExpectation
            (Matrix.toEuclideanCLM
              (n := ι j.succ × ι j.succ) (𝕜 := ℂ)
              (actualStoppingBranchWinningEffect
                G (PA q) (PB q) j.succ j.succ x y))
            (actualStoppingBranchVector
              (actualStoppingQuestionLocalAction
                (U q x) (V q y) (z q)) j.succ j.succ))) ≤
      (pureFlaggedStrategy G weight weight_nonnegative
        weight_normalized z normalized
        (fun q x => unitaryConjugatePOVM (U q x)
          (dependentBlockPOVM (fun r => PA q r x)))
        (fun q y => unitaryConjugatePOVM (V q y)
          (dependentBlockPOVM (fun r => PB q r y)))).winProbability := by
  classical
  rw [pureFlaggedStrategy_winProbability]
  apply Finset.sum_le_sum
  intro q _
  apply mul_le_mul_of_nonneg_left _ (weight_nonnegative q)
  exact actualStoppingQuestionLocalWinningProbability_ge_matched
    G (PA q) (PB q) (U q) (V q) (z q) (normalized q)
end
end QuantumParallelRepetition

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.ClassicalSampling
set_option autoImplicit true
attribute [local instance] Classical.propDecidable
theorem _root_.solution
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (denominator : ℕ) (denominator_positive : 0 < denominator)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (rational_normalized : ∀ index,
      (∑ history, numerator index history) = denominator)
    (support_preserving : ∀ index history,
      0 < exactLocalConditionalFamily D base
          (exactLocallySampleableLaw G n S D) index history →
        0 < numerator index history)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    {L : ℕ} {ι : Fin (L + 1) → Type}
    [∀ r, Fintype (ι r)] [∀ r, DecidableEq (ι r)]
    (PA : ExactSourceSharedFlag X Y A B D denominator →
      (r : Fin (L + 1)) → X → POVM A (ι r))
    (PB : ExactSourceSharedFlag X Y A B D denominator →
      (r : Fin (L + 1)) → Y → POVM B (ι r))
    (U : ExactSourceSharedFlag X Y A B D denominator →
      X → Matrix.unitaryGroup (Σ r : Fin (L + 1), ι r) ℂ)
    (V : ExactSourceSharedFlag X Y A B D denominator →
      Y → Matrix.unitaryGroup (Σ r : Fin (L + 1), ι r) ℂ)
    (z : ExactSourceSharedFlag X Y A B D denominator →
      EuclideanSpace ℂ
        ((Σ r : Fin (L + 1), ι r) ×
          (Σ r : Fin (L + 1), ι r)))
    (z_normalized : ∀ flag, ‖z flag‖ = 1)
    (matched :
      ExactSourceSharedFlag X Y A B D denominator ×
        (X × Y) → Bool)
    {K : Type*} [Fintype K]
    {H : ExactLocallySampleableTuple X Y A B D × K → Type*}
    [∀ p, NormedAddCommGroup (H p)]
    [∀ p, InnerProductSpace ℂ (H p)]
    (effect : (p : ExactLocallySampleableTuple X Y A B D × K) →
      (H p →L[ℂ] H p))
    (contraction : ∀ p, ‖effect p‖ ≤ 1)
    (actual canonical source :
      (p : ExactLocallySampleableTuple X Y A B D × K) → H p)
    (actual_mass :
      (∑ h : ExactLocallySampleableTuple X Y A B D,
        exactLocallySampleableLaw G n S D h *
          ∑ k : K, ‖actual (h, k)‖ ^ 2) ≤ 1)
    (canonical_mass :
      (∑ h : ExactLocallySampleableTuple X Y A B D,
        exactLocallySampleableLaw G n S D h *
          ∑ k : K, ‖canonical (h, k)‖ ^ 2) ≤ 1)
    (canonical_row_mass : ∀ h : ExactLocallySampleableTuple X Y A B D,
      (∑ k : K, ‖canonical (h, k)‖ ^ 2) ≤ 1)
    (same_work_mass : ∀ (h : ExactLocallySampleableTuple X Y A B D)
      (k : K), ‖source (h, k)‖ = ‖canonical (h, k)‖)
    (supported_born : ∀ h : ExactLocallySampleableTuple X Y A B D,
      exactLocallySampleableLaw G n S D h ≠ 0 →
        ∀ k : K,
          quadraticExpectation (effect (h, k)) (source (h, k)) =
            ‖source (h, k)‖ ^ 2 *
              exactSourceConditionalWinningProbability G n S D h)
    (epsilon lam deviation clipping bad : ℝ)
    (clean_deviation :
      (∑ h : ExactLocallySampleableTuple X Y A B D,
        exactLocallySampleableLaw G n S D h *
          ∑ k : K, ‖actual (h, k) - canonical (h, k)‖ ^ 2) ≤ deviation)
    (clip_deviation :
      (∑ h : ExactLocallySampleableTuple X Y A B D,
        exactLocallySampleableLaw G n S D h *
          ∑ k : K, ‖canonical (h, k) - source (h, k)‖ ^ 2) ≤ clipping)
    (actual_success :
      1 - bad ≤
        ∑ h : ExactLocallySampleableTuple X Y A B D,
          exactLocallySampleableLaw G n S D h *
            ∑ k : K, ‖actual (h, k)‖ ^ 2)
    (history_born_nonnegative :
      ∀ h : ExactLocallySampleableTuple X Y A B D,
        0 ≤ ∑ k : K,
          quadraticExpectation (effect (h, k)) (actual (h, k)))
    (history_born_bounded :
      ∀ h : ExactLocallySampleableTuple X Y A B D,
        (∑ k : K,
          quadraticExpectation (effect (h, k)) (actual (h, k))) ≤ 1)
    (source_failure :
      uniformRemainingFailure
          (strategyEventLaw (G.repeat n) S)
          (repeatedCoordinateWin G n) D < epsilon / 2)
    (total_variation :
      QuantumParallelRepetition.Pinsker.finiteTotalVariation
        (flaggedQuestionWeight G
          (exactSourceSharedFlagWeight D denominator))
        (exactSourceAliceFlagCoupling
          G n S D denominator numerator nonempty) ≤ lam)
    (mismatch :
      (∑ outcome :
        ExactSourceSharedFlag X Y A B D denominator × (X × Y),
        flaggedQuestionWeight G
          (exactSourceSharedFlagWeight D denominator) outcome *
          if matched outcome then 0 else 1) ≤ 4 * lam)
    (matched_physical_branch :
      ∀ (flag : ExactSourceSharedFlag X Y A B D denominator)
        (x : X) (y : Y),
        matched (flag, (x, y)) = true →
          (∑ k : K,
            quadraticExpectation
              (effect
                (exactSourceAliceSampleTuple
                  D denominator numerator nonempty (flag, (x, y)), k))
              (actual
                (exactSourceAliceSampleTuple
                  D denominator numerator nonempty (flag, (x, y)), k))) ≤
            ∑ j : Fin L,
              quadraticExpectation
                (Matrix.toEuclideanCLM
                  (n := ι j.succ × ι j.succ) (𝕜 := ℂ)
                  (actualStoppingBranchWinningEffect
                    G (PA flag) (PB flag) j.succ j.succ x y))
                (actualStoppingBranchVector
                  (actualStoppingQuestionLocalAction
                    (U flag x) (V flag y) (z flag))
                  j.succ j.succ)) :
    1 - epsilon / 2 - 5 * lam -
        (bad + 4 * Real.sqrt deviation + 2 * Real.sqrt clipping) ≤
      (pureFlaggedStrategy G
        (exactSourceSharedFlagWeight D denominator)
        (exactSourceSharedFlagWeight_nonneg D denominator)
        (exactSourceSharedFlagWeight_sum D remaining denominator)
        z z_normalized
        (fun flag x => unitaryConjugatePOVM
          (U flag x)
          (dependentBlockPOVM
            (fun r => PA flag r x)))
        (fun flag y => unitaryConjugatePOVM
          (V flag y)
          (dependentBlockPOVM
            (fun r => PB flag r y)))).winProbability := by
  classical
  let weight : ExactSourceSharedFlag X Y A B D denominator → ℝ :=
    exactSourceSharedFlagWeight D denominator
  let p :
      ExactSourceSharedFlag X Y A B D denominator × (X × Y) → ℝ :=
    flaggedQuestionWeight G weight
  let q :
      ExactSourceSharedFlag X Y A B D denominator × (X × Y) → ℝ :=
    exactSourceAliceFlagCoupling
      G n S D denominator numerator nonempty
  let history :
      ExactSourceSharedFlag X Y A B D denominator × (X × Y) →
        ExactLocallySampleableTuple X Y A B D :=
    exactSourceAliceSampleTuple D denominator numerator nonempty
  let physical : ExactLocallySampleableTuple X Y A B D → ℝ :=
    fun h => ∑ k : K,
      quadraticExpectation (effect (h, k)) (actual (h, k))
  let flagPhysical :
      ExactSourceSharedFlag X Y A B D denominator × (X × Y) → ℝ :=
    fun outcome => physical (history outcome)
  have weight_nonnegative : ∀ flag, 0 ≤ weight flag :=
    exactSourceSharedFlagWeight_nonneg D denominator
  have weight_normalized : (∑ flag, weight flag) = 1 :=
    exactSourceSharedFlagWeight_sum D remaining denominator
  have p_normalized : (∑ outcome, p outcome) = 1 :=
    flaggedQuestionWeight_sum G weight weight_normalized
  have q_normalized : (∑ outcome, q outcome) = 1 :=
    exactSourceAliceFlagCoupling_sum
      G n S D remaining positive base denominator denominator_positive
      numerator rational_normalized support_preserving nonempty
  have fair_verifier :=
    unconditionalWeightedClippedMatchedVerifierAndMassLoss
      (exactLocallySampleableLaw G n S D)
      (exactLocallySampleableLaw_nonneg G n S D positive)
      (exactLocallySampleableLaw_sum G n S D remaining positive)
      (exactSourceConditionalWinningProbability G n S D)
      (fun h =>
        (exactSourceConditionalWinningProbability_bounds
          G n S D positive h).2)
      effect contraction actual canonical source
      actual_mass canonical_mass canonical_row_mass
      same_work_mass supported_born
      deviation clipping bad
      clean_deviation clip_deviation actual_success
  have fair_win :
      1 - epsilon / 2 ≤
        ∑ h : ExactLocallySampleableTuple X Y A B D,
          exactLocallySampleableLaw G n S D h *
            exactSourceConditionalWinningProbability
              G n S D h :=
    (exactSourceConditionalWinningProbability_gt_of_uniform_failure
      G n S D remaining positive source_failure).le
  have pushforward :
      (∑ outcome, q outcome * flagPhysical outcome) =
        ∑ h : ExactLocallySampleableTuple X Y A B D,
          exactLocallySampleableLaw G n S D h * physical h := by
    simpa [q, flagPhysical, history] using
      (exactSourceAliceFlagCoupling_expectation
        G n S D remaining positive base denominator denominator_positive
        numerator rational_normalized support_preserving nonempty physical)
  have flagPhysical_nonnegative (outcome :
      ExactSourceSharedFlag X Y A B D denominator × (X × Y)) :
      0 ≤ flagPhysical outcome :=
    history_born_nonnegative (history outcome)
  have flagPhysical_bounded (outcome :
      ExactSourceSharedFlag X Y A B D denominator × (X × Y)) :
      flagPhysical outcome ≤ 1 :=
    history_born_bounded (history outcome)
  have variation : QuantumParallelRepetition.Pinsker.finiteTotalVariation p q ≤ lam := by
    simpa [p, q, weight] using total_variation
  have transferred := winning_expectation_transfer
    p q flagPhysical p_normalized q_normalized
    flagPhysical_nonnegative flagPhysical_bounded
  have p_nonnegative (outcome :
      ExactSourceSharedFlag X Y A B D denominator × (X × Y)) :
      0 ≤ p outcome :=
    flaggedQuestionWeight_nonneg
      G weight weight_nonnegative outcome
  have discarded := matched_payoff_discard_le
    p flagPhysical p_nonnegative flagPhysical_bounded matched
  have mismatch' :
      (∑ outcome, p outcome * if matched outcome then 0 else 1) ≤
        4 * lam := by
    simpa [p, weight] using mismatch
  have physical_transfer :
      1 - epsilon / 2 - 5 * lam -
          (bad + 4 * Real.sqrt deviation + 2 * Real.sqrt clipping) ≤
        ∑ outcome, p outcome *
          if matched outcome then flagPhysical outcome else 0 := by
    rw [← pushforward] at fair_verifier
    change
      (∑ h : ExactLocallySampleableTuple X Y A B D,
        exactLocallySampleableLaw G n S D h *
          exactSourceConditionalWinningProbability G n S D h) -
          bad - 4 * Real.sqrt deviation - 2 * Real.sqrt clipping ≤
        ∑ outcome, q outcome * flagPhysical outcome at fair_verifier
    linarith
  let stop :
      ExactSourceSharedFlag X Y A B D denominator × (X × Y) → ℝ :=
    fun outcome =>
      ∑ j : Fin L,
        quadraticExpectation
          (Matrix.toEuclideanCLM
            (n := ι j.succ × ι j.succ) (𝕜 := ℂ)
            (actualStoppingBranchWinningEffect
              G (PA outcome.1) (PB outcome.1)
              j.succ j.succ outcome.2.1 outcome.2.2))
          (actualStoppingBranchVector
            (actualStoppingQuestionLocalAction
              (U outcome.1 outcome.2.1)
              (V outcome.1 outcome.2.2) (z outcome.1))
            j.succ j.succ)
  have stop_nonnegative (outcome :
      ExactSourceSharedFlag X Y A B D denominator × (X × Y)) :
      0 ≤ stop outcome := by
    unfold stop
    apply Finset.sum_nonneg
    intro j _
    exact actualStoppingBranchBorn_nonneg
      G (PA outcome.1) (PB outcome.1)
      (actualStoppingQuestionLocalAction
        (U outcome.1 outcome.2.1)
        (V outcome.1 outcome.2.2) (z outcome.1))
      j.succ j.succ outcome.2.1 outcome.2.2
  have matched_stop :
      (∑ outcome, p outcome *
        if matched outcome then flagPhysical outcome else 0) ≤
      ∑ outcome, p outcome * stop outcome := by
    apply Finset.sum_le_sum
    intro outcome _
    apply mul_le_mul_of_nonneg_left _ (p_nonnegative outcome)
    by_cases matching : matched outcome = true
    · simp only [matching, ite_true]
      rcases outcome with ⟨flag, x, y⟩
      exact matched_physical_branch flag x y matching
    · have false_match : matched outcome = false :=
        Bool.eq_false_of_not_eq_true matching
      simp only [false_match, Bool.false_eq]
      exact stop_nonnegative outcome
  have physical_stopping :=
    actualStoppingQuestionLocalFlaggedWinningProbability_ge_matched
      G weight weight_nonnegative weight_normalized
      PA PB U V z z_normalized
  have reindex :
      (∑ outcome, p outcome * stop outcome) =
        ∑ flag, weight flag *
          (∑ x : X, ∑ y : Y, G.questionWeight x y *
            ∑ j : Fin L,
              quadraticExpectation
                (Matrix.toEuclideanCLM
                  (n := ι j.succ × ι j.succ) (𝕜 := ℂ)
                  (actualStoppingBranchWinningEffect
                    G (PA flag) (PB flag) j.succ j.succ x y))
                (actualStoppingBranchVector
                  (actualStoppingQuestionLocalAction
                    (U flag x) (V flag y) (z flag))
                  j.succ j.succ)) := by
    simp only [p, flaggedQuestionWeight, stop,
      Fintype.sum_prod_type]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro flag _
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring_nf
  change
    1 - epsilon / 2 - 5 * lam -
        (bad + 4 * Real.sqrt deviation + 2 * Real.sqrt clipping) ≤
      (pureFlaggedStrategy G weight weight_nonnegative weight_normalized
        z z_normalized
        (fun flag x => unitaryConjugatePOVM
          (U flag x)
          (dependentBlockPOVM
            (fun r => PA flag r x)))
        (fun flag y => unitaryConjugatePOVM
          (V flag y)
          (dependentBlockPOVM
            (fun r => PB flag r y)))).winProbability
  rw [reindex] at matched_stop
  exact physical_transfer.trans (matched_stop.trans physical_stopping)
end QuantumParallelRepetition

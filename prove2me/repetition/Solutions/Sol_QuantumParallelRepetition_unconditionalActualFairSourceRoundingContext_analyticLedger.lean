/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Repetition/TenProofs/QuantumParallelRepetition/Part08.lean (solution of QuantumParallelRepetition.unconditionalActualFairSourceRoundingContext_analyticLedger);
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
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalHeterogeneousPhysicalDiagonalSurvival_budget
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass_nonneg
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalHeterogeneousPhysicalStopped_mass_partition
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureVector_norm_sq
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalMixedCanonicalPrefixPhysicalAcceptedSigmaState_norm_sq
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalPhysicalDiagonalBornSuccess_eq
import Theorems.Thm_QuantumParallelRepetition_dSVUniformDensityCorrectedMatchedSigmaWeightedResidual_distance_sq
import Theorems.Thm_QuantumParallelRepetition_dSVUniformDensityMixedProtocolLocalAction_norm
import Theorems.Thm_QuantumParallelRepetition_ePRState_norm
import Theorems.Thm_QuantumParallelRepetition_embezzlementState_norm
import Theorems.Thm_QuantumParallelRepetition_exactGlobalHistoryLocalIndex_card_pos
import Theorems.Thm_QuantumParallelRepetition_exactLocallySampleableLaw_nonneg
import Theorems.Thm_QuantumParallelRepetition_exactLocallySampleableLaw_sum
import Theorems.Thm_QuantumParallelRepetition_finiteTensorVector_norm_sq
import Theorems.Thm_QuantumParallelRepetition_rectangular_matrix_mulVec_norm_sq
import Theorems.Thm_QuantumParallelRepetition_unconditionalMixedConjugateCanonicalAcceptedTarget_sum

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
attribute [instance] QuantumParallelRepetition.Strategy.alice_fintype QuantumParallelRepetition.Strategy.bob_fintype QuantumParallelRepetition.Strategy.alice_decidableEq QuantumParallelRepetition.Strategy.bob_decidableEq

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace QuantumParallelRepetition
section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
theorem finiteTensorVector_norm
    {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d]
    (v : ι → EuclideanSpace ℂ d)
    (hv : ∀ i, ‖v i‖ = 1) :
    ‖finiteTensorVector v‖ = 1 := by
  have hsquare := finiteTensorVector_norm_sq v
  simp_rw [hv, one_pow, Finset.prod_const_one] at hsquare
  nlinarith [norm_nonneg (finiteTensorVector v)]
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexOrder
set_option autoImplicit true
theorem dSVHeterogeneousRealPrefix_nonneg
    (continuation : ℕ → ℝ)
    (nonnegative : ∀ k, 0 ≤ continuation k) (k : ℕ) :
    0 ≤ dSVHeterogeneousRealPrefix continuation k := by
  unfold dSVHeterogeneousRealPrefix
  exact Finset.prod_nonneg (fun i _ => nonnegative i)
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
theorem dSVUniformDensityIndependentSharedState_norm
    (L : ℕ) {N d : ℕ}
    (grid : 0 < N) (dimension : 0 < d) :
    ‖dSVUniformDensityIndependentSharedState L N d‖ = 1 := by
  unfold dSVUniformDensityIndependentSharedState
  rw [LinearIsometryEquiv.norm_map]
  exact finiteTensorVector_norm
    (fun _ : Fin L =>
      dSVUniformDensityThresholdSharedState N d)
    (fun _ =>
      dSVUniformDensityThresholdSharedState_norm
        grid dimension)
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
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
theorem dSVUniformDensityPhysicalAsyncSigmaContinuation_norm
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (U V : ι → Matrix.unitaryGroup κ ℂ)
    (z : EuclideanSpace ℂ
      ((Σ _ : ι, κ) × (Σ _ : ι, κ))) :
    ‖dSVUniformDensityPhysicalAsyncSigmaContinuation U V z‖ =
      ‖z‖ := by
  simpa [dSVUniformDensityPhysicalAsyncSigmaContinuation]
    using dSVUniformDensityMixedProtocolLocalAction_norm
      (coherentSharedRandomControlledUnitary U)
      (coherentSharedRandomControlledUnitary V) z
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
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
theorem dSVDensityRationalPublicBucketCoherentPhaseHistory_apply
    {H : Type*} [Fintype H] (B : ℕ)
    (history : EuclideanSpace ℂ (H × H))
    (φ ψ : Fin B) (a b : H) :
    dSVDensityRationalPublicBucketCoherentPhaseHistory
        B history ((φ, a), (ψ, b)) =
      ePRState B (φ, ψ) * history (a, b) := by
  rfl
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
theorem dSVDensityRationalPublicBucketCoherentPhaseHistory_apply_norm_sq
    {H : Type*} [Fintype H] {B : ℕ}
    (positive : 0 < B)
    (history : EuclideanSpace ℂ (H × H))
    (φ ψ : Fin B) (a b : H) :
    ‖dSVDensityRationalPublicBucketCoherentPhaseHistory
        B history ((φ, a), (ψ, b))‖ ^ 2 =
      (if φ = ψ then (B : ℝ)⁻¹ else 0) *
        ‖history (a, b)‖ ^ 2 := by
  rw [dSVDensityRationalPublicBucketCoherentPhaseHistory_apply,
    norm_mul, mul_pow]
  by_cases same : φ = ψ
  · subst ψ
    simp only [ePRState, ↓reduceIte]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)),
      inv_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ B)]
  · simp [ePRState, same]
end
end QuantumParallelRepetition

attribute [local instance] Classical.propDecidable

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
set_option autoImplicit true
theorem dSVDensityRationalHeterogeneousPhysicalStageOutcome_nonneg
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (k : ℕ) (alice bob : Bool) :
    0 ≤ dSVDensityRationalHeterogeneousPhysicalStageOutcome
      N width schedule ξ ζ k alice bob := by
  unfold dSVDensityRationalHeterogeneousPhysicalStageOutcome
  split_ifs <;> positivity
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
set_option autoImplicit true
theorem dSVDensityRationalHeterogeneousPhysicalSurvival_nonneg
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (k : ℕ) :
    0 ≤ dSVDensityRationalHeterogeneousPhysicalSurvival
      N width schedule ξ ζ k := by
  unfold dSVDensityRationalHeterogeneousPhysicalSurvival
  apply dSVHeterogeneousRealPrefix_nonneg
  intro j
  exact dSVDensityRationalHeterogeneousPhysicalStageOutcome_nonneg
    N width schedule ξ ζ j false false
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
set_option autoImplicit true
theorem dSVDensityRationalHeterogeneousPhysicalTerminalMass_nonneg
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    0 ≤ dSVDensityRationalHeterogeneousPhysicalTerminalMass
      N width schedule ξ ζ :=
  dSVDensityRationalHeterogeneousPhysicalSurvival_nonneg
    N width schedule ξ ζ L
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

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem exactSourceTuplePsi_norm
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (t : ExactLocallySampleableTuple X Y A B D) :
    ‖exactSourceTuplePsi G n S D t‖ = 1 :=
  (exactGlobalHistoryFinPsi
    G n S D t.2.2.2 t.2.1 t.2.2.1).property
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

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
theorem
    dSVDensityRationalMixedCanonicalPrefixPhysicalSigmaWeighted_norm_sq
    {H : Type*} [Fintype H] {n : ℕ}
    (history : EuclideanSpace ℂ (H × H))
    (work : H → H → EuclideanSpace ℂ (Fin n × Fin n)) :
    ‖dSVUniformDensityCorrectedMatchedSigmaWeightedResidual
        history work‖ ^ 2 =
      ∑ i : H, ∑ j : H,
        ‖history (i, j)‖ ^ 2 * ‖work i j‖ ^ 2 := by
  have zero :
      dSVUniformDensityCorrectedMatchedSigmaWeightedResidual
          history (fun _ _ => (0 : EuclideanSpace ℂ (Fin n × Fin n))) =
        0 := by
    ext q
    simp [dSVUniformDensityCorrectedMatchedSigmaWeightedResidual]
  have distance :=
    dSVUniformDensityCorrectedMatchedSigmaWeightedResidual_distance_sq
      history work (fun _ _ => (0 : EuclideanSpace ℂ (Fin n × Fin n)))
  simpa [zero] using distance
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
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option autoImplicit true
theorem unconditionalMatchedVerifierTensor_norm_sq
    {s t : Type*} [Fintype s] [Fintype t]
    (target : EuclideanSpace ℂ s)
    (work : EuclideanSpace ℂ t) :
    ‖unconditionalMatchedVerifierTensor target work‖ ^ 2 =
      ‖target‖ ^ 2 * ‖work‖ ^ 2 := by
  classical
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  change
    (∑ i : s, ∑ j : t, ‖target i * work j‖ ^ 2) =
      ‖target‖ ^ 2 * ‖work‖ ^ 2
  simp_rw [norm_mul, mul_pow]
  rw [← Fintype.sum_mul_sum, ← EuclideanSpace.norm_sq_eq,
    ← EuclideanSpace.norm_sq_eq]
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
theorem unconditionalMatchedVerifierTensor_norm
    {s t : Type*} [Fintype s] [Fintype t]
    (target : EuclideanSpace ℂ s)
    (work : EuclideanSpace ℂ t) :
    ‖unconditionalMatchedVerifierTensor target work‖ =
      ‖target‖ * ‖work‖ := by
  have squared :=
    unconditionalMatchedVerifierTensor_norm_sq target work
  nlinarith [
    norm_nonneg (unconditionalMatchedVerifierTensor target work),
    norm_nonneg target, norm_nonneg work,
    mul_nonneg (norm_nonneg target) (norm_nonneg work)]
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
theorem unconditionalSelectedCopyRetainedWork_norm_sq
    {S N d L : ℕ} {τ : Type*} [Fintype τ]
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (j : Fin L) (rest : EuclideanSpace ℂ τ) :
    ‖unconditionalSelectedCopyRetainedWork
        (N := N) width schedule ξ ζ j rest‖ ^ 2 =
      dSVDensityRationalHeterogeneousPhysicalSurvival
        N width schedule ξ ζ j.val * ‖rest‖ ^ 2 := by
  unfold unconditionalSelectedCopyRetainedWork
  rw [unconditionalMatchedVerifierTensor_norm_sq,
    dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureVector_norm_sq]
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
theorem unconditionalConjugatePureVector_norm_sq
    {ι : Type*} [Fintype ι] (z : EuclideanSpace ℂ ι) :
    ‖unconditionalConjugatePureVector z‖ ^ 2 = ‖z‖ ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq]
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
theorem unconditionalPublicBucketPhysicalCoherentTarget_apply
    {d N B n : ℕ} (w : ℝ)
    (ξ ζ : BipartiteUnitVector d)
    (φ ψ : Fin B) (i j : Fin d) (a b : Fin (N * n)) :
    dSVDensityRationalPublicBucketPhysicalCoherentTargetState
        (N := N) (B := B) w n ξ ζ
        (⟨(φ, i), a⟩, ⟨(ψ, j), b⟩) =
      (ePRState B (φ, ψ) *
        (((‖sharedThresholdResourceRaw (d := Fin d)
          (fun _ : Fin N => (1 : ℝ))‖⁻¹ : ℝ) : ℂ) *
          dSVDensityRationalLocalSpectralPairBasisOverlap
            ξ ζ i j)) *
        ((Real.sqrt
            ((dSVDensityRationalPhysicalAcceptedRank
              w N ξ i).val : ℝ) : ℂ) *
          embezzlementState (N * n) (a, b)) := by
  rfl
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
theorem unconditionalMixedConjugateSigmaAtomLift_apply
    {d m : ℕ} (B : ℕ)
    (U : Matrix.unitaryGroup (Fin d) ℂ)
    (φ ψ : Fin B) (i j : Fin d) (a b : Fin m) :
    (unconditionalMixedConjugateSigmaAtomLift (m := m) B U :
      Matrix (Σ _ : Fin B × Fin d, Fin m)
        (Σ _ : Fin B × Fin d, Fin m) ℂ)
      ⟨(φ, i), a⟩ ⟨(ψ, j), b⟩ =
      if φ = ψ ∧ a = b then
        (U : Matrix (Fin d) (Fin d) ℂ) i j
      else 0 := by
  classical
  by_cases phase : φ = ψ <;>
    by_cases work : a = b <;>
      simp [unconditionalMixedConjugateSigmaAtomLift,
        Matrix.reindex_apply, Matrix.kroneckerMap_apply, phase, work]
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
theorem unconditionalMixedConjugateSigmaLocalAction_apply
    {d m : ℕ} (B : ℕ)
    (U V : Matrix.unitaryGroup (Fin d) ℂ)
    (z : EuclideanSpace ℂ
      ((Σ _ : Fin B × Fin d, Fin m) ×
        (Σ _ : Fin B × Fin d, Fin m)))
    (φ ψ : Fin B) (i j : Fin d) (a b : Fin m) :
    unconditionalMixedConjugateSigmaLocalAction B U V z
        (⟨(φ, i), a⟩, ⟨(ψ, j), b⟩) =
      ∑ k : Fin d, ∑ l : Fin d,
        (U : Matrix (Fin d) (Fin d) ℂ) i k *
        (V : Matrix (Fin d) (Fin d) ℂ) j l *
        z (⟨(φ, k), a⟩, ⟨(ψ, l), b⟩) := by
  classical
  simp [unconditionalMixedConjugateSigmaLocalAction,
    Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Fintype.sum_sigma,
    unconditionalMixedConjugateSigmaAtomLift_apply,
    mul_assoc, ite_and]
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
theorem unconditionalMixedConjugateTargetCovariance
    {d N B n : ℕ} {w : ℝ}
    (width : 0 < w) (grid : 0 < N) (dimension : 0 < d)
    (ξ ζ : BipartiteUnitVector d) :
    Real.sqrt (w * (d : ℝ)) •
      unconditionalMixedConjugateSigmaLocalAction
        (m := N * n) B
        (conjugateUnitary
          (dSVDensityRationalCanonicalAliceBasis ξ))
        (conjugateUnitary
          (dSVUniformDensityThresholdLeftBobBasis ζ))
        (dSVDensityRationalPublicBucketPhysicalCoherentTargetState
          (N := N) (B := B) w n ξ ζ) =
    unconditionalMixedConjugateAcceptedPhaseHarmonicTarget
        (B := B) w n ξ := by
  classical
  ext ⟨⟨⟨φ, i⟩, a⟩, ⟨⟨ψ, j⟩, b⟩⟩
  change
    (Real.sqrt (w * (d : ℝ)) : ℂ) *
      unconditionalMixedConjugateSigmaLocalAction B
        (conjugateUnitary
          (dSVDensityRationalCanonicalAliceBasis ξ))
        (conjugateUnitary
          (dSVUniformDensityThresholdLeftBobBasis ζ))
        (dSVDensityRationalPublicBucketPhysicalCoherentTargetState
          (N := N) (B := B) w n ξ ζ)
        (⟨(φ, i), a⟩, ⟨(ψ, j), b⟩) =
      (ePRState B (φ, ψ) *
        star (dSVDensityRationalCanonicalAcceptedTarget
          w N ξ (i, j))) *
        embezzlementState (N * n) (a, b)
  rw [unconditionalMixedConjugateSigmaLocalAction_apply]
  simp_rw [conjugateUnitary_apply,
    unconditionalPublicBucketPhysicalCoherentTarget_apply]
  rw [← unconditionalMixedConjugateCanonicalAcceptedTarget_sum
    width grid dimension ξ ζ i j]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
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
theorem unconditionalSelectedCopy_coherentPhaseSigma_norm_sq
    {H : Type*} [Fintype H] {B m : ℕ}
    (phases : 0 < B)
    (history : EuclideanSpace ℂ (H × H))
    (work : H → H → EuclideanSpace ℂ (Fin m × Fin m)) :
    ‖dSVDensityRationalPublicBucketCoherentPhaseSigmaState
        B history (fun _ i j => work i j)‖ ^ 2 =
      ‖dSVUniformDensityCorrectedMatchedSigmaWeightedResidual
        history work‖ ^ 2 := by
  classical
  unfold dSVDensityRationalPublicBucketCoherentPhaseSigmaState
  rw [dSVDensityRationalMixedCanonicalPrefixPhysicalSigmaWeighted_norm_sq,
    dSVDensityRationalMixedCanonicalPrefixPhysicalSigmaWeighted_norm_sq]
  simp only [Fintype.sum_prod_type]
  simp_rw [
    dSVDensityRationalPublicBucketCoherentPhaseHistory_apply_norm_sq
      phases]
  have phase_ne : (B : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt phases)
  calc
    (∑ φ : Fin B, ∑ i : H, ∑ ψ : Fin B, ∑ j : H,
        (if φ = ψ then (B : ℝ)⁻¹ else 0) *
          ‖history (i, j)‖ ^ 2 * ‖work i j‖ ^ 2) =
        ∑ φ : Fin B, ∑ i : H, ∑ j : H,
          (B : ℝ)⁻¹ * ‖history (i, j)‖ ^ 2 * ‖work i j‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro φ _
            apply Finset.sum_congr rfl
            intro i _
            simp
    _ = _ := by
      calc
        (∑ φ : Fin B, ∑ i : H, ∑ j : H,
            (B : ℝ)⁻¹ * ‖history (i, j)‖ ^ 2 * ‖work i j‖ ^ 2) =
          ∑ _φ : Fin B, (B : ℝ)⁻¹ *
            (∑ i : H, ∑ j : H,
              ‖history (i, j)‖ ^ 2 * ‖work i j‖ ^ 2) := by
              apply Finset.sum_congr rfl
              intro φ _
              simp_rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              apply Finset.sum_congr rfl
              intro j _
              ring
        _ = _ := by
          rw [Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          field_simp
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
theorem unconditionalSelectedCopy_coherentPhaseConstantWork_norm_sq
    {H : Type*} [Fintype H] {B m : ℕ}
    (phases : 0 < B)
    (history : EuclideanSpace ℂ (H × H))
    (work : EuclideanSpace ℂ (Fin m × Fin m)) :
    ‖dSVDensityRationalPublicBucketCoherentPhaseSigmaState
        B history (fun _ _ _ => work)‖ ^ 2 =
      ‖history‖ ^ 2 * ‖work‖ ^ 2 := by
  rw [unconditionalSelectedCopy_coherentPhaseSigma_norm_sq
    phases history (fun _ _ => work),
    dSVDensityRationalMixedCanonicalPrefixPhysicalSigmaWeighted_norm_sq]
  calc
    (∑ i : H, ∑ j : H, ‖history (i, j)‖ ^ 2 * ‖work‖ ^ 2) =
        (∑ i : H, ∑ j : H, ‖history (i, j)‖ ^ 2) * ‖work‖ ^ 2 := by
          simp_rw [Finset.sum_mul]
    _ = _ := by
      congr 1
      rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
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
theorem unconditionalSelectedCopy_conjugateAcceptedTarget_norm_sq
    {d N B m : ℕ} (phases : 0 < B)
    (grid : 0 < N) (harmonic : 0 < m)
    (w : ℝ) (ξ : BipartiteUnitVector d) :
    ‖unconditionalMixedConjugateAcceptedPhaseHarmonicTarget
        (N := N) (B := B) w m ξ‖ ^ 2 =
      ‖dSVDensityRationalCanonicalAcceptedTarget w N ξ‖ ^ 2 := by
  unfold unconditionalMixedConjugateAcceptedPhaseHarmonicTarget
  rw [unconditionalSelectedCopy_coherentPhaseConstantWork_norm_sq
    phases]
  rw [unconditionalConjugatePureVector_norm_sq,
    embezzlementState_norm (N * m) (Nat.mul_pos grid harmonic)]
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
theorem unconditionalSelectedCopy_mixedConjugateLocalAction_norm
    {d B m : ℕ}
    (U V : Matrix.unitaryGroup (Fin d) ℂ)
    (z : EuclideanSpace ℂ
      ((Σ _ : Fin B × Fin d, Fin m) ×
       (Σ _ : Fin B × Fin d, Fin m))) :
    ‖unconditionalMixedConjugateSigmaLocalAction B U V z‖ = ‖z‖ := by
  simpa [unconditionalMixedConjugateSigmaLocalAction] using
    dSVUniformDensityMixedProtocolLocalAction_norm
      (unconditionalMixedConjugateSigmaAtomLift (m := m) B U)
      (unconditionalMixedConjugateSigmaAtomLift (m := m) B V) z
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
theorem unconditionalSelectedCopyIdealStage_norm_sq
    {d N B m : ℕ} {w : ℝ}
    (phases : 0 < B) (grid : 0 < N)
    (dimension : 0 < d) (harmonic : 0 < m)
    (width : 0 < w)
    (ξ ζ : BipartiteUnitVector d) :
    ‖unconditionalSelectedCopyIdealStage
        (N := N) (B := B) (m := m) w ξ ζ‖ ^ 2 =
      dSVDensityRationalPhysicalDiagonalBornSuccess
        grid dimension w ξ := by
  have covariance :=
    unconditionalMixedConjugateTargetCovariance
      (B := B) (n := m) width grid dimension ξ ζ
  have squared := congrArg (fun z => ‖z‖ ^ 2) covariance
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ w * (d : ℝ)),
    unconditionalSelectedCopy_mixedConjugateLocalAction_norm,
    unconditionalSelectedCopy_conjugateAcceptedTarget_norm_sq
      phases grid harmonic,
    dSVDensityRationalCanonicalAcceptedTarget_norm_sq width]
    at squared
  have dimension_real : 0 < (d : ℝ) := by
    exact_mod_cast dimension
  have cancelled :
      (d : ℝ) *
          ‖unconditionalSelectedCopyIdealStage
            (N := N) (B := B) (m := m) w ξ ζ‖ ^ 2 =
        dSVDensityRationalLeftProjectiveDiagonalMass w N ξ := by
    apply mul_left_cancel₀ (ne_of_gt width)
    simpa [unconditionalSelectedCopyIdealStage, mul_assoc] using squared
  rw [dSVDensityRationalPhysicalDiagonalBornSuccess_eq]
  apply (eq_div_iff (ne_of_gt dimension_real)).2
  simpa [mul_comm] using cancelled
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
theorem unconditionalSelectedCopyCleanedStage_norm_sq
    {d N B m : ℕ} {w : ℝ}
    (phases : 0 < B) (grid : 0 < N) (harmonic : 0 < m)
    (width : 0 < w)
    (ξ ζ : BipartiteUnitVector d)
    (Q : ℕ)
    (A C : Fin B → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ) :
    ‖unconditionalSelectedCopyCleanedStage
        (N := N) (B := B) (m := m) Q w ξ ζ A C‖ ^ 2 =
      ‖dSVDensityRationalCompleteProjectiveOutcome
        w N ξ ζ true true‖ ^ 2 := by
  unfold unconditionalSelectedCopyCleanedStage
    dSVDensityRationalPublicBucketPhysicalCoherentLocalReset
  rw [dSVUniformDensityPhysicalAsyncSigmaContinuation_norm]
  unfold dSVDensityRationalPublicBucketPhysicalCoherentMixedState
  rw [unconditionalSelectedCopy_coherentPhaseSigma_norm_sq phases]
  exact
    dSVDensityRationalMixedCanonicalPrefixPhysicalAcceptedSigmaState_norm_sq
      width grid harmonic ξ ζ
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
theorem unconditionalSelectedCopyCleanedMatchedBranch_norm_sq
    {S N d L B m : ℕ} {τ : Type*} [Fintype τ]
    (phases : 0 < B) (grid : 0 < N) (harmonic : 0 < m)
    (width : Fin S → ℝ) (width_positive : ∀ s, 0 < width s)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (Q : ℕ)
    (A C : Fin B → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (j : Fin L) (rest : EuclideanSpace ℂ τ)
    (rest_unit : ‖rest‖ = 1) :
    ‖unconditionalSelectedCopyCleanedMatchedBranch
        Q width schedule ξ ζ A C j rest‖ ^ 2 =
      dSVDensityRationalHeterogeneousPhysicalSurvival
          N width schedule ξ ζ j.val *
        dSVDensityRationalHeterogeneousPhysicalStageSuccess
          N width schedule ξ ζ j.val := by
  unfold unconditionalSelectedCopyCleanedMatchedBranch
  rw [unconditionalMatchedVerifierTensor_norm_sq,
    unconditionalSelectedCopyCleanedStage_norm_sq
      phases grid harmonic (width_positive (schedule j)),
    unconditionalSelectedCopyRetainedWork_norm_sq,
    rest_unit]
  simp [dSVDensityRationalHeterogeneousPhysicalStageSuccess,
    dSVDensityRationalHeterogeneousPhysicalStageOutcome,
    j.isLt, mul_comm]
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
theorem unconditionalSelectedCopyIdealMatchedBranch_norm_sq
    {S N d L B m : ℕ} {τ : Type*} [Fintype τ]
    (phases : 0 < B) (grid : 0 < N)
    (dimension : 0 < d) (harmonic : 0 < m)
    (width : Fin S → ℝ) (width_positive : ∀ s, 0 < width s)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (j : Fin L) (rest : EuclideanSpace ℂ τ)
    (rest_unit : ‖rest‖ = 1) :
    ‖unconditionalSelectedCopyIdealMatchedBranch
        (N := N) (B := B) (m := m) width schedule ξ ζ j rest‖ ^ 2 =
      dSVDensityRationalHeterogeneousPhysicalSurvival
          N width schedule ξ ζ j.val *
        dSVDensityRationalPhysicalDiagonalBornSuccess
          grid dimension (width (schedule j)) ξ := by
  unfold unconditionalSelectedCopyIdealMatchedBranch
  rw [unconditionalMatchedVerifierTensor_norm_sq,
    unconditionalSelectedCopyIdealStage_norm_sq
      phases grid dimension harmonic (width_positive (schedule j)),
    unconditionalSelectedCopyRetainedWork_norm_sq,
    rest_unit]
  ring
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
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem unconditionalExactFairGammaUnit_eq_global
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (u : ExactLocallySampleableTuple X Y A B D) :
    unconditionalExactFairGammaUnit G n S D u =
      exactGlobalHistoryFinGamma
        G n S D u.2.2.2 u.2.1 := by
  apply Subtype.ext
  rfl
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
theorem unconditionalCanonicalAcceptedScale_sq_eq_diagonalBorn
    {d N : ℕ} {w : ℝ}
    (width : 0 < w) (grid : 0 < N) (dimension : 0 < d)
    (gamma : BipartiteUnitVector d) :
    (‖dSVDensityRationalCanonicalAcceptedTarget
        w N gamma‖ / Real.sqrt (w * (d : ℝ))) ^ 2 =
      dSVDensityRationalPhysicalDiagonalBornSuccess
        grid dimension w gamma := by
  have dimension_real : 0 < (d : ℝ) := by
    exact_mod_cast dimension
  rw [div_pow,
    dSVDensityRationalCanonicalAcceptedTarget_norm_sq
      width N gamma,
    Real.sq_sqrt (by positivity : 0 ≤ w * (d : ℝ)),
    dSVDensityRationalPhysicalDiagonalBornSuccess_eq]
  field_simp [ne_of_gt width, ne_of_gt dimension_real]
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
theorem unconditionalNormalizedCanonicalRetainedWork_norm_sq
    {S N d L B m : ℕ} {T : Type*} [Fintype T]
    (phases : 0 < B) (grid : 0 < N)
    (dimension : 0 < d) (harmonic : 0 < m)
    (width : Fin S → ℝ) (width_positive : ∀ s, 0 < width s)
    (schedule : Fin L → Fin S)
    (gamma phi : BipartiteUnitVector d)
    (j : Fin L) (rest : EuclideanSpace ℂ T)
    (rest_unit : ‖rest‖ = 1) :
    ‖(‖dSVDensityRationalCanonicalAcceptedTarget
          (width (schedule j)) N gamma‖ /
        Real.sqrt ((width (schedule j)) * (d : ℝ))) •
      unconditionalSelectedCopyRetainedWork
        (N := N) width schedule gamma phi j rest‖ ^ 2 =
      ‖unconditionalSelectedCopyIdealMatchedBranch
        (N := N) (B := B) (m := m)
        width schedule gamma phi j rest‖ ^ 2 := by
  have positive := width_positive (schedule j)
  have ratio_nonnegative :
      0 ≤ ‖dSVDensityRationalCanonicalAcceptedTarget
          (width (schedule j)) N gamma‖ /
        Real.sqrt ((width (schedule j)) * (d : ℝ)) := by
    exact div_nonneg (norm_nonneg _)
      (Real.sqrt_nonneg _)
  calc
    _ =
      (‖dSVDensityRationalCanonicalAcceptedTarget
          (width (schedule j)) N gamma‖ /
        Real.sqrt ((width (schedule j)) * (d : ℝ))) ^ 2 *
      ‖unconditionalSelectedCopyRetainedWork
        (N := N) width schedule gamma phi j rest‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg ratio_nonnegative, mul_pow]
    _ =
      dSVDensityRationalPhysicalDiagonalBornSuccess
        grid dimension (width (schedule j)) gamma *
      (dSVDensityRationalHeterogeneousPhysicalSurvival
        N width schedule gamma phi j.val * ‖rest‖ ^ 2) := by
      rw [unconditionalCanonicalAcceptedScale_sq_eq_diagonalBorn
        positive grid dimension gamma,
        unconditionalSelectedCopyRetainedWork_norm_sq]
    _ =
      dSVDensityRationalHeterogeneousPhysicalSurvival
        N width schedule gamma phi j.val *
      dSVDensityRationalPhysicalDiagonalBornSuccess
        grid dimension (width (schedule j)) gamma := by
      rw [rest_unit]
      ring
    _ = _ :=
      (unconditionalSelectedCopyIdealMatchedBranch_norm_sq
        phases grid dimension harmonic width width_positive schedule
        gamma phi j rest rest_unit).symm
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
theorem integratorActualCanonicalRetainedPhaseTail_norm
    {S B N d L : ℕ}
    (phases : 0 < B) (grid : 0 < N) (dimension : 0 < d)
    (j : Fin L) :
    ‖unconditionalActualCanonicalRetainedPhaseTail
        (S := S) (B := B) (N := N) (d := d) (L := L) j‖ = 1 := by
  have residual : 0 < Fintype.card (Fin (S - 1) → Fin B) := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨fun _ => ⟨0, phases⟩⟩
  change
    ‖unconditionalMatchedVerifierTensor
        (dSVUniformDensityIndependentSharedState
          (L - j.val) N d)
        (ePRState
          (Fintype.card (Fin (S - 1) → Fin B)))‖ = 1
  rw [unconditionalMatchedVerifierTensor_norm,
    dSVUniformDensityIndependentSharedState_norm
      (L - j.val) grid dimension,
    ePRState_norm _ residual]
  norm_num
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
theorem unconditionalActualC485NormalizedDiagonalWork_mass_sum_le_one
    {S B N d L m : ℕ}
    (phases : 0 < B) (grid : 0 < N)
    (dimension : 0 < d) (harmonic : 0 < m)
    (width : Fin S → ℝ) (positive : ∀ s, 0 < width s)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    (∑ j : Fin L,
      ‖integratorActualC485NormalizedDiagonalWork
          (S := S) (B := B) (N := N) (d := d) (L := L)
          width schedule ξ ζ j‖ ^ 2) ≤ 1 := by
  classical
  calc
    _ = ∑ j : Fin L,
      dSVDensityRationalHeterogeneousPhysicalSurvival
          N width schedule ξ ζ j.val *
        dSVDensityRationalPhysicalDiagonalBornSuccess
          grid dimension (width (schedule j)) ξ := by
      apply Finset.sum_congr rfl
      intro j _
      unfold integratorActualC485NormalizedDiagonalWork
        integratorActualC485OriginalRetainedWork
      rw [unconditionalNormalizedCanonicalRetainedWork_norm_sq
        (B := B) (m := m) phases grid dimension harmonic
        width positive schedule ξ ζ j
        (unconditionalActualCanonicalRetainedPhaseTail
          (S := S) (B := B) (N := N) (d := d) (L := L) j)
        (integratorActualCanonicalRetainedPhaseTail_norm
          phases grid dimension j)]
      exact unconditionalSelectedCopyIdealMatchedBranch_norm_sq
        phases grid dimension harmonic width positive schedule ξ ζ j
        (unconditionalActualCanonicalRetainedPhaseTail
          (S := S) (B := B) (N := N) (d := d) (L := L) j)
        (integratorActualCanonicalRetainedPhaseTail_norm
          phases grid dimension j)
    _ ≤ 1 :=
      dSVDensityRationalHeterogeneousPhysicalDiagonalSurvival_budget
        grid dimension width schedule ξ ζ
end
end QuantumParallelRepetition

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
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option autoImplicit true
theorem unconditionalActualFairSelectedLocalAction_norm_sq
    {ι τ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype τ] [DecidableEq τ]
    (U V : Matrix.unitaryGroup ι ℂ)
    (z : EuclideanSpace ℂ ((ι × ι) × τ)) :
    ‖unconditionalMixedConjugateSelectedBranchLocalAction
        U V z‖ ^ 2 = ‖z‖ ^ 2 := by
  classical
  let M : Matrix ((ι × ι) × τ) ((ι × ι) × τ) ℂ :=
    (unconditionalMixedConjugateSelectedBranchUnitary
      (τ := τ) U V : Matrix _ _ ℂ)
  have gram : M.conjTranspose * M = 1 := by
    simpa [M, Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff'.mp
        (unconditionalMixedConjugateSelectedBranchUnitary
          (τ := τ) U V).property)
  change ‖toLp 2 (M.mulVec (ofLp z))‖ ^ 2 = ‖z‖ ^ 2
  rw [rectangular_matrix_mulVec_norm_sq, gram]
  simp [quadraticExpectation, ← Complex.ofReal_pow]
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
theorem unconditionalActualFairCleanedVector_norm_sq
    {S B N d L m : Nat}
    (phases : 0 < B) (grid : 0 < N)
    (dimension : 0 < d) (harmonic : 0 < m)
    (width : Fin S → ℝ) (width_positive : ∀ s, 0 < width s)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (Q : Nat)
    (A C : Fin B → Option Nat →
      Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (j : Fin L) :
    ‖integratorActualC485CleanedVector
        Q width schedule ξ ζ A C j‖ ^ 2 =
      dSVDensityRationalHeterogeneousPhysicalSurvival
          N width schedule ξ ζ j.val *
        dSVDensityRationalHeterogeneousPhysicalStageSuccess
          N width schedule ξ ζ j.val := by
  letI : DecidableEq
      (IntegratorActualC485RetainedIndex S B N d L j) :=
    FinEnum.decEq
  unfold integratorActualC485CleanedVector
  rw [unconditionalActualFairSelectedLocalAction_norm_sq]
  exact unconditionalSelectedCopyCleanedMatchedBranch_norm_sq
    phases grid harmonic width width_positive schedule ξ ζ Q A C j
    (unconditionalActualCanonicalRetainedPhaseTail
      (S := S) (B := B) (N := N) (d := d) (L := L) j)
    (integratorActualCanonicalRetainedPhaseTail_norm
      phases grid dimension j)
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
theorem unconditionalActualFairCleanedRow_eq_stoppedSuccess
    {S B N d L m : Nat}
    (phases : 0 < B) (grid : 0 < N)
    (dimension : 0 < d) (harmonic : 0 < m)
    (width : Fin S → ℝ) (width_positive : ∀ s, 0 < width s)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (Q : Nat)
    (A C : Fin B → Option Nat →
      Matrix.unitaryGroup (Fin (N * m)) ℂ) :
    (∑ j : Fin L,
      ‖integratorActualC485CleanedVector
        Q width schedule ξ ζ A C j‖ ^ 2) =
      dSVDensityRationalHeterogeneousPhysicalStoppedSuccessMass
        N width schedule ξ ζ := by
  simp_rw [unconditionalActualFairCleanedVector_norm_sq
    phases grid dimension harmonic width width_positive schedule ξ ζ Q A C]
  unfold dSVDensityRationalHeterogeneousPhysicalStoppedSuccessMass
  simpa using
    (Fin.sum_univ_eq_sum_range
      (fun k : Nat =>
        dSVDensityRationalHeterogeneousPhysicalSurvival
            N width schedule ξ ζ k *
          dSVDensityRationalHeterogeneousPhysicalStageSuccess
            N width schedule ξ ζ k) L)
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
theorem unconditionalActualFairCleanedRow_le_one
    {S B N d L m : Nat}
    (phases : 0 < B) (grid : 0 < N)
    (dimension : 0 < d) (harmonic : 0 < m)
    (width : Fin S → ℝ) (width_positive : ∀ s, 0 < width s)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (Q : Nat)
    (A C : Fin B → Option Nat →
      Matrix.unitaryGroup (Fin (N * m)) ℂ) :
    (∑ j : Fin L,
      ‖integratorActualC485CleanedVector
        Q width schedule ξ ζ A C j‖ ^ 2) ≤ 1 := by
  rw [unconditionalActualFairCleanedRow_eq_stoppedSuccess
    phases grid dimension harmonic width width_positive schedule ξ ζ Q A C]
  have partition :=
    dSVDensityRationalHeterogeneousPhysicalStopped_mass_partition
      grid dimension width schedule ξ ζ
  have asynchronous :=
    dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass_nonneg
      N width schedule ξ ζ
  have terminal :=
    dSVDensityRationalHeterogeneousPhysicalTerminalMass_nonneg
      N width schedule ξ ζ
  linarith
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
theorem unconditionalActualFairWeightedCleanedMass_le_one
    {I : Type} [Fintype I]
    {S B N d L m : Nat}
    (weight : I → ℝ)
    (weight_nonnegative : ∀ h, 0 ≤ weight h)
    (weight_normalized : (∑ h : I, weight h) = 1)
    (phases : 0 < B) (grid : 0 < N)
    (dimension : 0 < d) (harmonic : 0 < m)
    (width : Fin S → ℝ) (width_positive : ∀ s, 0 < width s)
    (schedule : Fin L → Fin S)
    (ξ ζ : I → BipartiteUnitVector d)
    (Q : Nat)
    (A C : Fin B → Option Nat →
      Matrix.unitaryGroup (Fin (N * m)) ℂ) :
    (∑ h : I, weight h *
      ∑ j : Fin L,
        ‖integratorActualC485CleanedVector
          Q width schedule (ξ h) (ζ h) A C j‖ ^ 2) ≤ 1 := by
  calc
    _ ≤ ∑ h : I, weight h * 1 := by
      apply Finset.sum_le_sum
      intro h _
      exact mul_le_mul_of_nonneg_left
        (unconditionalActualFairCleanedRow_le_one
          phases grid dimension harmonic width width_positive
          schedule (ξ h) (ζ h) Q A C)
        (weight_nonnegative h)
    _ = 1 := by simpa using weight_normalized
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
theorem unconditionalActualFairWeightedStoppedSuccess
    {I : Type} [Fintype I]
    {S B N d L m : Nat}
    (weight : I → ℝ)
    (weight_normalized : (∑ h : I, weight h) = 1)
    (phases : 0 < B) (grid : 0 < N)
    (dimension : 0 < d) (harmonic : 0 < m)
    (width : Fin S → ℝ) (width_positive : ∀ s, 0 < width s)
    (schedule : Fin L → Fin S)
    (ξ ζ : I → BipartiteUnitVector d)
    (Q : Nat)
    (A C : Fin B → Option Nat →
      Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (async terminal : ℝ)
    (asynchronous_bound :
      (∑ h : I, weight h *
        dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
          N width schedule (ξ h) (ζ h)) ≤ async)
    (terminal_bound :
      (∑ h : I, weight h *
        dSVDensityRationalHeterogeneousPhysicalTerminalMass
          N width schedule (ξ h) (ζ h)) ≤ terminal) :
    1 - (async + terminal) ≤
      ∑ h : I, weight h *
        ∑ j : Fin L,
          ‖integratorActualC485CleanedVector
            Q width schedule (ξ h) (ζ h) A C j‖ ^ 2 := by
  have partition :
      (∑ h : I, weight h *
        dSVDensityRationalHeterogeneousPhysicalStoppedSuccessMass
          N width schedule (ξ h) (ζ h)) +
      (∑ h : I, weight h *
        dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
          N width schedule (ξ h) (ζ h)) +
      (∑ h : I, weight h *
        dSVDensityRationalHeterogeneousPhysicalTerminalMass
          N width schedule (ξ h) (ζ h)) = 1 := by
    calc
      _ = ∑ h : I, weight h *
        (dSVDensityRationalHeterogeneousPhysicalStoppedSuccessMass
            N width schedule (ξ h) (ζ h) +
          dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
            N width schedule (ξ h) (ζ h) +
          dSVDensityRationalHeterogeneousPhysicalTerminalMass
            N width schedule (ξ h) (ζ h)) := by
            simp_rw [mul_add, Finset.sum_add_distrib]
      _ = ∑ h : I, weight h := by
        apply Finset.sum_congr rfl
        intro h _
        rw [dSVDensityRationalHeterogeneousPhysicalStopped_mass_partition
          grid dimension width schedule (ξ h) (ζ h)]
        ring
      _ = 1 := weight_normalized
  simp_rw [unconditionalActualFairCleanedRow_eq_stoppedSuccess
    phases grid dimension harmonic width width_positive
    schedule _ _ Q A C]
  linarith
end
end QuantumParallelRepetition

attribute [local instance] Classical.propDecidable

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option autoImplicit true
theorem unconditionalActualFairCanonicalVector_norm_sq
    {S B N d L m : ℕ}
    (phases : 0 < B) (grid : 0 < N) (harmonic : 0 < m)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (j : Fin L)
    (positive : 0 < width (schedule j))
    (fine : (d : ℝ) / (N : ℝ) < 1 / (width (schedule j) + 1)) :
    ‖integratorActualC485CanonicalVector
        (B := B) (m := m) schedule ξ ζ j positive grid fine‖ ^ 2 =
      ‖integratorActualC485NormalizedDiagonalWork
          (B := B) (N := N) width schedule ξ ζ j‖ ^ 2 := by
  unfold integratorActualC485CanonicalVector
  rw [unconditionalMatchedVerifierTensor_norm_sq,
    unconditionalSelectedCopy_coherentPhaseConstantWork_norm_sq
      phases,
    unconditionalConjugatePureVector_norm_sq,
    (dSVDensityRationalCanonicalAcceptedUnitTarget
      positive grid fine ξ).property,
    embezzlementState_norm (N * m)
      (Nat.mul_pos grid harmonic)]
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
theorem unconditionalActualFairCanonicalRow_le_one
    {S B N d L m : ℕ}
    (phases : 0 < B) (grid : 0 < N)
    (dimension : 0 < d) (harmonic : 0 < m)
    (width : Fin S → ℝ) (width_positive : ∀ s, 0 < width s)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (fine : ∀ s,
      (d : ℝ) / (N : ℝ) < 1 / (width s + 1)) :
    (∑ j : Fin L,
      ‖integratorActualC485CanonicalVector
        (B := B) (m := m) schedule ξ ζ j
        (width_positive (schedule j)) grid
        (fine (schedule j))‖ ^ 2) ≤ 1 := by
  calc
    _ = ∑ j : Fin L,
      ‖integratorActualC485NormalizedDiagonalWork
        (B := B) (N := N) width schedule ξ ζ j‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      exact unconditionalActualFairCanonicalVector_norm_sq
        phases grid harmonic width schedule ξ ζ j
        (width_positive (schedule j)) (fine (schedule j))
    _ ≤ 1 :=
      unconditionalActualC485NormalizedDiagonalWork_mass_sum_le_one
        (m := m) phases grid dimension harmonic
        width width_positive schedule ξ ζ
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
theorem unconditionalActualFairWeightedCanonicalMass_le_one
    {I : Type} [Fintype I]
    {S B N d L m : ℕ}
    (weight : I → ℝ)
    (weight_nonnegative : ∀ h, 0 ≤ weight h)
    (weight_normalized : (∑ h : I, weight h) = 1)
    (phases : 0 < B) (grid : 0 < N)
    (dimension : 0 < d) (harmonic : 0 < m)
    (width : Fin S → ℝ) (width_positive : ∀ s, 0 < width s)
    (schedule : Fin L → Fin S)
    (ξ ζ : I → BipartiteUnitVector d)
    (fine : ∀ s,
      (d : ℝ) / (N : ℝ) < 1 / (width s + 1)) :
    (∑ h : I, weight h *
      ∑ j : Fin L,
        ‖integratorActualC485CanonicalVector
          (B := B) (m := m) schedule (ξ h) (ζ h) j
          (width_positive (schedule j)) grid
          (fine (schedule j))‖ ^ 2) ≤ 1 := by
  calc
    _ ≤ ∑ h : I, weight h * 1 := by
      apply Finset.sum_le_sum
      intro h _
      exact mul_le_mul_of_nonneg_left
        (unconditionalActualFairCanonicalRow_le_one
          phases grid dimension harmonic width width_positive
          schedule (ξ h) (ζ h) fine)
        (weight_nonnegative h)
    _ = 1 := by simpa using weight_normalized
end
end QuantumParallelRepetition

attribute [local instance] Classical.propDecidable

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option autoImplicit true
theorem unconditionalActualFairSourceVector_norm_sq
    {S B N d L m : ℕ}
    (phases : 0 < B) (grid : 0 < N) (harmonic : 0 < m)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (ψ : EuclideanSpace ℂ (Fin d × Fin d))
    (unit : ‖ψ‖ = 1) (j : Fin L) :
    ‖integratorActualC485SourceVector
        (S := S) (B := B) (N := N) (d := d) (L := L) (m := m)
        width schedule ξ ζ ψ j‖ ^ 2 =
      ‖integratorActualC485NormalizedDiagonalWork
          (S := S) (B := B) (N := N) (d := d) (L := L)
          width schedule ξ ζ j‖ ^ 2 := by
  unfold integratorActualC485SourceVector
  rw [unconditionalMatchedVerifierTensor_norm_sq,
    unconditionalSelectedCopy_coherentPhaseConstantWork_norm_sq
      phases,
    unconditionalConjugatePureVector_norm_sq,
    unit,
    embezzlementState_norm (N * m)
      (Nat.mul_pos grid harmonic)]
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
theorem unconditionalActualFairSourceCanonicalVector_norm_sq
    {S B N d L m : ℕ}
    (phases : 0 < B) (grid : 0 < N) (harmonic : 0 < m)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (ψ : EuclideanSpace ℂ (Fin d × Fin d))
    (unit : ‖ψ‖ = 1) (j : Fin L)
    (positive : 0 < width (schedule j))
    (fine : (d : ℝ) / (N : ℝ) < 1 / (width (schedule j) + 1)) :
    ‖integratorActualC485SourceVector
        (S := S) (B := B) (N := N) (d := d) (L := L) (m := m)
        width schedule ξ ζ ψ j‖ ^ 2 =
      ‖integratorActualC485CanonicalVector
          (S := S) (B := B) (N := N) (d := d) (L := L) (m := m)
          (width := width) schedule ξ ζ j positive grid fine‖ ^ 2 := by
  rw [unconditionalActualFairSourceVector_norm_sq
    phases grid harmonic width schedule ξ ζ ψ unit j,
    unconditionalActualFairCanonicalVector_norm_sq
      phases grid harmonic width schedule ξ ζ j positive fine]
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
theorem unconditionalActualFairSourceCanonicalVector_norm
    {S B N d L m : ℕ}
    (phases : 0 < B) (grid : 0 < N) (harmonic : 0 < m)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (ψ : EuclideanSpace ℂ (Fin d × Fin d))
    (unit : ‖ψ‖ = 1) (j : Fin L)
    (positive : 0 < width (schedule j))
    (fine : (d : ℝ) / (N : ℝ) < 1 / (width (schedule j) + 1)) :
    ‖integratorActualC485SourceVector
        (S := S) (B := B) (N := N) (d := d) (L := L) (m := m)
        width schedule ξ ζ ψ j‖ =
      ‖integratorActualC485CanonicalVector
          (S := S) (B := B) (N := N) (d := d) (L := L) (m := m)
          (width := width) schedule ξ ζ j positive grid fine‖ := by
  have squared :=
    unconditionalActualFairSourceCanonicalVector_norm_sq
      phases grid harmonic width schedule ξ ζ ψ unit j positive fine
  nlinarith [
    norm_nonneg (integratorActualC485SourceVector
      (S := S) (B := B) (N := N) (d := d) (L := L) (m := m)
      width schedule ξ ζ ψ j),
    norm_nonneg (integratorActualC485CanonicalVector
      (S := S) (B := B) (N := N) (d := d) (L := L) (m := m)
      (width := width) schedule ξ ζ j positive grid fine)]
end
end QuantumParallelRepetition

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

namespace QuantumParallelRepetition.UnconditionalActualFairSourceRoundingContext
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.ClassicalSampling
set_option autoImplicit true
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {G : Game X Y A B} {n : ℕ} {S : Strategy (G.repeat n)}
variable {D : Finset (Fin n)} {alpha gamma : ℝ}
theorem dimension_pos
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) : 0 < d c :=
  exactGlobalHistoryLocalIndex_card_pos G n S D
end
end QuantumParallelRepetition.UnconditionalActualFairSourceRoundingContext

attribute [local instance] Classical.propDecidable

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.ClassicalSampling
open UnconditionalActualFairSourceRoundingContext
set_option autoImplicit true
theorem _root_.solution
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} {n : ℕ} {S : Strategy (G.repeat n)}
    {D : Finset (Fin n)} {alpha gamma : ℝ}
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) :
    UnconditionalActualFairCachedStoppedAnalyticLedger
      (law c) (actual c) (canonical c) (source c)
      (deviation c) (clipping c) (bad c) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact unconditionalActualFairWeightedCleanedMass_le_one
      (law c)
      (exactLocallySampleableLaw_nonneg G n S D c.positive)
      (exactLocallySampleableLaw_sum
        G n S D c.remaining c.positive)
      c.stopping.phases c.stopping.grid (dimension_pos c)
      c.stopping.harmonic (width c) (width_all c) (schedule c)
      (gammaVector c) (phiVector c)
      c.stopping.Q c.stopping.UA c.stopping.UB
  · exact unconditionalActualFairWeightedCanonicalMass_le_one
      (law c)
      (exactLocallySampleableLaw_nonneg G n S D c.positive)
      (exactLocallySampleableLaw_sum
        G n S D c.remaining c.positive)
      c.stopping.phases c.stopping.grid (dimension_pos c)
      c.stopping.harmonic (width c) (width_all c) (schedule c)
      (gammaVector c) (phiVector c) (fine_all c)
  · intro h
    exact unconditionalActualFairCanonicalRow_le_one
      c.stopping.phases c.stopping.grid (dimension_pos c)
      c.stopping.harmonic (width c) (width_all c) (schedule c)
      (gammaVector c h) (phiVector c h) (fine_all c)
  · intro h j
    exact unconditionalActualFairSourceCanonicalVector_norm
      c.stopping.phases c.stopping.grid c.stopping.harmonic
      (width c) (schedule c) (gammaVector c h) (phiVector c h)
      (psiVector c h) (exactSourceTuplePsi_norm G n S D h) j
      (width_all c (schedule c j)) (fine_all c (schedule c j))
  · exact le_refl (deviation c)
  · change
      (∑ h : ExactLocallySampleableTuple X Y A B D,
        law c h *
          ∑ j : Fin c.stopping.L,
            ‖canonical c (h, j) - source c (h, j)‖ ^ 2) ≤
        unconditionalActualC485FairSourceClipEnergy
          (P := c.stopping.P) (m := c.stopping.m)
          G n S D (width_positive c) c.stopping.grid
          c.stopping.fine (schedule c)
    unfold unconditionalActualC485FairSourceClipEnergy
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro h _
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    change
      ‖canonical c (h, j) - source c (h, j)‖ ^ 2 =
        ‖source c (h, j) - canonical c (h, j)‖ ^ 2
    rw [norm_sub_rev]
  · have async :
        (∑ h : ExactLocallySampleableTuple X Y A B D,
          law c h *
            dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
              c.stopping.N (width c) (schedule c)
              (gammaVector c h) (phiVector c h)) ≤
          64 * Real.sqrt (martingaleRate G n S D) +
            alpha ^ (1 / 3 : ℝ) := by
      change
        (∑ h : ExactLocallySampleableTuple X Y A B D,
          exactLocallySampleableLaw G n S D h *
            dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
              c.stopping.N
              (fun _ : Fin 1 => c.stopping.w)
              (fun _ : Fin c.stopping.L => 0)
              (unconditionalExactFairGammaUnit G n S D h)
              (exactGlobalHistoryFinPhi
                G n S D h.2.2.2 h.2.2.1)) ≤ _
      simpa only [unconditionalExactFairGammaUnit_eq_global] using
        c.stopping.asynchronous
    have finish :
        (∑ h : ExactLocallySampleableTuple X Y A B D,
          law c h *
            dSVDensityRationalHeterogeneousPhysicalTerminalMass
              c.stopping.N (width c) (schedule c)
              (gammaVector c h) (phiVector c h)) ≤
          (alpha ^ (1 / 3 : ℝ)) ^ 2 := by
      change
        (∑ h : ExactLocallySampleableTuple X Y A B D,
          exactLocallySampleableLaw G n S D h *
            dSVDensityRationalHeterogeneousPhysicalTerminalMass
              c.stopping.N
              (fun _ : Fin 1 => c.stopping.w)
              (fun _ : Fin c.stopping.L => 0)
              (unconditionalExactFairGammaUnit G n S D h)
              (exactGlobalHistoryFinPhi
                G n S D h.2.2.2 h.2.2.1)) ≤ _
      simpa only [unconditionalExactFairGammaUnit_eq_global] using
        c.stopping.terminal
    exact unconditionalActualFairWeightedStoppedSuccess
      (law c)
      (exactLocallySampleableLaw_sum
        G n S D c.remaining c.positive)
      c.stopping.phases c.stopping.grid (dimension_pos c)
      c.stopping.harmonic (width c) (width_all c) (schedule c)
      (gammaVector c) (phiVector c)
      c.stopping.Q c.stopping.UA c.stopping.UB
      (64 * Real.sqrt (martingaleRate G n S D) +
        alpha ^ (1 / 3 : ℝ))
      ((alpha ^ (1 / 3 : ℝ)) ^ 2) async finish
end QuantumParallelRepetition

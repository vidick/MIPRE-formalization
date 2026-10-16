/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Repetition/TenProofs/QuantumParallelRepetition/Part07.lean (solution of QuantumParallelRepetition.unconditionalActualCanonicalFullSource_eq_rawSelectedStage);
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
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalPublicLogPhasePhysicalAlignedLocalAction_apply
import Theorems.Thm_QuantumParallelRepetition_directDSVActualStoppingSelectedHistory_sourceProduct

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
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
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
set_option autoImplicit true
theorem dSVDensityRationalHeterogeneousActualPhysicalState_apply
    (N : ℕ) {S d L : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (a b : DSVUniformDensityThresholdWholeHistoryLocalIndex
      N d L) :
    dSVDensityRationalHeterogeneousActualPhysicalState
        N width schedule ξ ζ (a, b) =
      ∑ x : DSVUniformDensityThresholdWholeHistoryLocalIndex
          N d L,
        ∑ y : DSVUniformDensityThresholdWholeHistoryLocalIndex
            N d L,
          (dSVDensityRationalHeterogeneousActualAliceUnitary
              N width schedule ξ :
            Matrix
              (DSVUniformDensityThresholdWholeHistoryLocalIndex
                N d L)
              (DSVUniformDensityThresholdWholeHistoryLocalIndex
                N d L) ℂ) a x *
          (dSVDensityRationalHeterogeneousActualBobUnitary
              N width schedule ζ :
            Matrix
              (DSVUniformDensityThresholdWholeHistoryLocalIndex
                N d L)
              (DSVUniformDensityThresholdWholeHistoryLocalIndex
                N d L) ℂ) b y *
          dSVUniformDensityThresholdWholeHistorySharedState
            N d L (x, y) := by
  classical
  unfold dSVDensityRationalHeterogeneousActualPhysicalState
  change
    (∑ q :
      DSVUniformDensityThresholdWholeHistoryLocalIndex N d L ×
        DSVUniformDensityThresholdWholeHistoryLocalIndex N d L,
      ((dSVDensityRationalHeterogeneousActualAliceUnitary
            N width schedule ξ :
          Matrix
            (DSVUniformDensityThresholdWholeHistoryLocalIndex
              N d L)
            (DSVUniformDensityThresholdWholeHistoryLocalIndex
              N d L) ℂ) ⊗ₖ
        (dSVDensityRationalHeterogeneousActualBobUnitary
            N width schedule ζ :
          Matrix
            (DSVUniformDensityThresholdWholeHistoryLocalIndex
              N d L)
            (DSVUniformDensityThresholdWholeHistoryLocalIndex
              N d L) ℂ)) (a, b) q *
        dSVUniformDensityThresholdWholeHistorySharedState
          N d L q) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rfl
end
end QuantumParallelRepetition

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
set_option autoImplicit true
theorem
    dSVDensityRationalHeterogeneousTargetFirstSpectralPhysicalSource_apply
    (S B N d L m : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (φ ψ : DSVDensityRationalPublicMultiscalePhase S B)
    (a b : DSVUniformDensityThresholdWholeHistoryLocalIndex
      N d L) (i j : Fin m) :
    dSVDensityRationalHeterogeneousTargetFirstSpectralPhysicalSource
        S B N d L m width schedule ξ ζ
        (dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
            S B N d L m
            (((Fintype.equivFin
                (DSVDensityRationalPublicMultiscalePhase S B)) φ,
              a), i),
         dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
            S B N d L m
            (((Fintype.equivFin
                (DSVDensityRationalPublicMultiscalePhase S B)) ψ,
              b), j)) =
      (if φ = ψ then
        (((Real.sqrt ((B ^ S : ℕ) : ℝ))⁻¹ : ℝ) : ℂ)
      else 0) *
        dSVDensityRationalHeterogeneousActualPhysicalState
          N width schedule ξ ζ (a, b) *
        embezzlementState m (i, j) := by
  unfold
    dSVDensityRationalHeterogeneousTargetFirstSpectralPhysicalSource
    dSVDensityRationalHeterogeneousTargetFirstSpectralAlice
    dSVDensityRationalHeterogeneousTargetFirstSpectralBob
    dSVDensityRationalPublicMultiscalePhaseTargetFirstPreparedSource
    dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
    dSVDensityRationalPublicMultiscalePhaseResidual
  rw [dSVDensityRationalPublicLogPhasePhysicalAlignedLocalAction_apply]
  rw [← dSVDensityRationalHeterogeneousActualPhysicalState_apply]
  simp
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

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
set_option autoImplicit true
theorem
    dSVDensityRationalHeterogeneousOriginalSameStopSigmaSource_apply
    (S B N d L m : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (φ ψ : DSVDensityRationalPublicMultiscalePhaseIndex S B)
    (a b : DSVUniformDensityThresholdWholeHistoryLocalIndex
      N d L) (i j : Fin m) :
    dSVDensityRationalHeterogeneousOriginalSameStopSigmaSource
        S B N d L m width schedule ξ ζ
        (dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
            S B N d L m ((φ, a), i),
         dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
            S B N d L m ((ψ, b), j)) =
      ePRState
          (Fintype.card
            (DSVDensityRationalPublicMultiscalePhase S B))
          (φ, ψ) *
        dSVDensityRationalHeterogeneousActualPhysicalState
          N width schedule ξ ζ (a, b) *
        embezzlementState m (i, j) := by
  simp [dSVDensityRationalHeterogeneousOriginalSameStopSigmaSource,
    dSVDensityRationalHeterogeneousOriginalSameStopStateEquiv,
    dSVDensityRationalPublicMultiscaleOriginalSigmaTargetFirstEquiv,
    dSVDensityRationalPublicBucketCoherentPhaseSigmaProductEquiv,
    LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft',
    dSVDensityRationalHeterogeneousPureStoppedSigmaState,
    dSVDensityRationalPublicMultiscaleBucketCoherentSigmaState,
    dSVDensityRationalPublicBucketCoherentPhaseSigmaState,
    dSVUniformDensityCorrectedMatchedSigmaWeightedResidual,
    dSVDensityRationalPublicBucketCoherentPhaseHistory]
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
set_option autoImplicit true
theorem
    dSVDensityRationalHeterogeneousOriginalSameStopSigmaSource_eq_stopped
    (S B N d L m : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalHeterogeneousOriginalSameStopSigmaSource
        S B N d L m width schedule ξ ζ =
      dSVDensityRationalHeterogeneousOriginalStoppedState
        S B N d L m width schedule ξ ζ := by
  classical
  ext ⟨x, y⟩
  obtain ⟨⟨⟨φ, a⟩, i⟩, rfl⟩ :=
    (dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
      S B N d L m).surjective x
  obtain ⟨⟨⟨ψ, b⟩, j⟩, rfl⟩ :=
    (dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
      S B N d L m).surjective y
  obtain ⟨φ', rfl⟩ :=
    (Fintype.equivFin
      (DSVDensityRationalPublicMultiscalePhase S B)).surjective φ
  obtain ⟨ψ', rfl⟩ :=
    (Fintype.equivFin
      (DSVDensityRationalPublicMultiscalePhase S B)).surjective ψ
  rw [dSVDensityRationalHeterogeneousOriginalSameStopSigmaSource_apply]
  change _ =
    dSVDensityRationalHeterogeneousTargetFirstSpectralPhysicalSource
      S B N d L m width schedule ξ ζ
      (dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
        S B N d L m
        (((Fintype.equivFin
          (DSVDensityRationalPublicMultiscalePhase S B)) φ', a), i),
       dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
        S B N d L m
        (((Fintype.equivFin
          (DSVDensityRationalPublicMultiscalePhase S B)) ψ', b), j))
  rw [dSVDensityRationalHeterogeneousTargetFirstSpectralPhysicalSource_apply]
  simp [ePRState]
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
set_option autoImplicit true
theorem dSVDensityRationalHeterogeneousOriginalStoppedState_apply
    (S B N d L m : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (φ ψ : DSVDensityRationalPublicMultiscalePhaseIndex S B)
    (a b : DSVUniformDensityThresholdWholeHistoryLocalIndex N d L)
    (i j : Fin m) :
    dSVDensityRationalHeterogeneousOriginalStoppedState
        S B N d L m width schedule ξ ζ
        (dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
            S B N d L m ((φ, a), i),
         dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
            S B N d L m ((ψ, b), j)) =
      ePRState
          (Fintype.card
            (DSVDensityRationalPublicMultiscalePhase S B))
          (φ, ψ) *
        dSVDensityRationalHeterogeneousActualPhysicalState
          N width schedule ξ ζ (a, b) *
        embezzlementState m (i, j) := by
  rw [←
    dSVDensityRationalHeterogeneousOriginalSameStopSigmaSource_eq_stopped]
  exact
    dSVDensityRationalHeterogeneousOriginalSameStopSigmaSource_apply
      S B N d L m width schedule ξ ζ φ ψ a b i j
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
@[simp] theorem directDSVSelectedCopyLocalHistoryEquiv_before
    {L : ℕ} {β : Type*} (j : Fin L)
    (selected : β) (before : Fin j.val → β)
    (after : Fin (L - j.val) → β) (i : Fin j.val) :
    directDSVSelectedCopyLocalHistoryEquiv j
        (selected, (before, after))
        ⟨i.val, by omega⟩ = before i := by
  let k : Fin L := ⟨i.val, by omega⟩
  have earlier : k < j := by
    change i.val < j.val
    exact i.isLt
  have selected_index :
      j.castSucc.succAbove k =
        (⟨i.val, by omega⟩ : Fin (L + 1)) := by
    rw [Fin.succAbove_castSucc_of_lt j k earlier]
    rfl
  unfold directDSVSelectedCopyLocalHistoryEquiv
  simp only [Equiv.trans_apply, Equiv.prodCongr_apply,
    Fin.insertNthEquiv_apply]
  rw [← selected_index, Fin.insertNth_apply_succAbove]
  change
    (if h : k.val < j.val
      then before ⟨k.val, h⟩
      else after ⟨k.val - j.val, by omega⟩) = before i
  simp only [k, i.isLt, ↓reduceDIte]
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
@[simp] theorem directDSVSelectedCopyLocalHistoryEquiv_after
    {L : ℕ} {β : Type*} (j : Fin L)
    (selected : β) (before : Fin j.val → β)
    (after : Fin (L - j.val) → β) (i : Fin (L - j.val)) :
    directDSVSelectedCopyLocalHistoryEquiv j
        (selected, (before, after))
        ⟨j.val + 1 + i.val, by omega⟩ = after i := by
  let k : Fin L := ⟨j.val + i.val, by omega⟩
  have later : j ≤ k := by
    change j.val ≤ j.val + i.val
    omega
  have selected_index :
      j.castSucc.succAbove k =
        (⟨j.val + 1 + i.val, by omega⟩ : Fin (L + 1)) := by
    rw [Fin.succAbove_castSucc_of_le j k later]
    apply Fin.ext
    change j.val + i.val + 1 = j.val + 1 + i.val
    omega
  unfold directDSVSelectedCopyLocalHistoryEquiv
  simp only [Equiv.trans_apply, Equiv.prodCongr_apply,
    Fin.insertNthEquiv_apply]
  rw [← selected_index, Fin.insertNth_apply_succAbove]
  change
    (if h : k.val < j.val
      then before ⟨k.val, h⟩
      else after ⟨k.val - j.val, by omega⟩) = after i
  have not_before : ¬ j.val + i.val < j.val := by omega
  simp [k, not_before]
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
theorem unconditionalSourcePhysicalStoppingTargetFirst_branch_apply
    {S B N d L m : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (r s : Fin (L + 1))
    (φ ψ : DSVDensityRationalPublicMultiscalePhaseIndex S B)
    (a b : DSVUniformDensityIndependentHistoryLocalIndex
      (L + 1) N d)
    (i k : Fin m) :
    actualStoppingBranchVector
      (unconditionalSourcePhysicalStoppingTargetFirstStateEquiv
        S B N d L m
        (dSVDensityRationalHeterogeneousOriginalStoppedState
          S B N d L m width schedule ξ ζ)) r s
      (⟨(φ, a), i⟩, ⟨(ψ, b), k⟩) =
        ePRState
          (Fintype.card
            (DSVDensityRationalPublicMultiscalePhase S B))
          (φ, ψ) *
        dSVDensityRationalHeterogeneousActualPhysicalState
          N width schedule ξ ζ
          (⟨r, a⟩, ⟨s, b⟩) *
        embezzlementState m (i, k) := by
  change
    dSVDensityRationalHeterogeneousOriginalStoppedState
      S B N d L m width schedule ξ ζ
      (dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
        S B N d L m ((φ, ⟨r, a⟩), i),
       dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
        S B N d L m ((ψ, ⟨s, b⟩), k)) = _
  exact dSVDensityRationalHeterogeneousOriginalStoppedState_apply
    S B N d L m width schedule ξ ζ φ ψ ⟨r, a⟩ ⟨s, b⟩ i k
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
theorem unconditionalSelectedMultiscalePhase_card
    (S B : ℕ) :
    Fintype.card
        (DSVDensityRationalPublicMultiscalePhase (S + 1) B) =
      B * Fintype.card (Fin S → Fin B) := by
  simp [DSVDensityRationalPublicMultiscalePhase,
    pow_succ, Nat.mul_comm]
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
theorem unconditionalSelectedMultiscalePhase_EPR_apply
    {S B : ℕ} (scale : Fin (S + 1))
    (p q : Fin B)
    (r t : Fin (Fintype.card (Fin S → Fin B))) :
    ePRState
        (Fintype.card
          (DSVDensityRationalPublicMultiscalePhase (S + 1) B))
        (unconditionalSelectedMultiscalePhaseIndexEquiv
            scale (p, r),
         unconditionalSelectedMultiscalePhaseIndexEquiv
            scale (q, t)) =
      ePRState B (p, q) *
        ePRState (Fintype.card (Fin S → Fin B)) (r, t) := by
  classical
  by_cases selected : p = q
  · subst q
    by_cases residual : r = t
    · subst t
      simp only [ePRState, ↓reduceIte]
      rw [unconditionalSelectedMultiscalePhase_card,
        Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg B), mul_inv]
      exact Complex.ofReal_mul _ _
    · have different :
          unconditionalSelectedMultiscalePhaseIndexEquiv
              scale (p, r) ≠
            unconditionalSelectedMultiscalePhaseIndexEquiv
              scale (p, t) := by
          intro equal
          exact residual
            (congrArg Prod.snd
              ((unconditionalSelectedMultiscalePhaseIndexEquiv
                scale).injective equal))
      simp [ePRState, different, residual]
  · have different :
        unconditionalSelectedMultiscalePhaseIndexEquiv
            scale (p, r) ≠
          unconditionalSelectedMultiscalePhaseIndexEquiv
            scale (q, t) := by
        intro equal
        exact selected
          (congrArg Prod.fst
            ((unconditionalSelectedMultiscalePhaseIndexEquiv
              scale).injective equal))
    simp [ePRState, different, selected]
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
theorem unconditionalActualMultiscalePhase_EPR_apply
    {S B : ℕ} (scale : Fin S)
    (p q : Fin B)
    (r t : Fin (Fintype.card (Fin (S - 1) → Fin B))) :
    ePRState
        (Fintype.card
          (DSVDensityRationalPublicMultiscalePhase S B))
        (unconditionalActualMultiscalePhaseIndexEquiv
            scale (p, r),
         unconditionalActualMultiscalePhaseIndexEquiv
            scale (q, t)) =
      ePRState B (p, q) *
        ePRState (Fintype.card (Fin (S - 1) → Fin B))
          (r, t) := by
  cases S with
  | zero => exact Fin.elim0 scale
  | succ S =>
      exact unconditionalSelectedMultiscalePhase_EPR_apply
        scale p q r t
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
theorem
    unconditionalSourcePhysicalCleanedStoppingLocalAction_reindex
    {S B N d L m : ℕ}
    (U V : Matrix.unitaryGroup
      (Fin (d *
        dSVDensityRationalPublicMultiscalePhaseResidual
          S B N d L m)) ℂ)
    (z : EuclideanSpace ℂ
      (Fin (d *
        dSVDensityRationalPublicMultiscalePhaseResidual
          S B N d L m) ×
       Fin (d *
        dSVDensityRationalPublicMultiscalePhaseResidual
          S B N d L m))) :
    actualStoppingQuestionLocalAction
      (unconditionalSourcePhysicalCleanedTargetFirstUnitary
        S B N d L m U)
      (unconditionalSourcePhysicalCleanedTargetFirstUnitary
        S B N d L m V)
      (unconditionalSourcePhysicalStoppingTargetFirstStateEquiv
        S B N d L m z) =
      unconditionalSourcePhysicalStoppingTargetFirstStateEquiv
        S B N d L m (localUnitaryAction U V z) := by
  classical
  let e := unconditionalSourcePhysicalStoppingTargetFirstIndexEquiv
    S B N d L m
  ext ⟨a, b⟩
  change
    (∑ q :
      (Σ _ : Fin (L + 1),
        UnconditionalSourcePhysicalStoppingPhaseFiber
          S B N d L m) ×
      (Σ _ : Fin (L + 1),
        UnconditionalSourcePhysicalStoppingPhaseFiber
          S B N d L m),
      (U : Matrix _ _ ℂ) (e.symm a) (e.symm q.1) *
        (V : Matrix _ _ ℂ) (e.symm b) (e.symm q.2) *
        z (e.symm q.1, e.symm q.2)) =
      ∑ q :
        Fin (d *
          dSVDensityRationalPublicMultiscalePhaseResidual
            S B N d L m) ×
        Fin (d *
          dSVDensityRationalPublicMultiscalePhaseResidual
            S B N d L m),
        (U : Matrix _ _ ℂ) (e.symm a) q.1 *
          (V : Matrix _ _ ℂ) (e.symm b) q.2 * z q
  simpa using
    (Equiv.sum_comp (Equiv.prodCongr e e)
      (fun q :
        (Σ _ : Fin (L + 1),
          UnconditionalSourcePhysicalStoppingPhaseFiber
            S B N d L m) ×
        (Σ _ : Fin (L + 1),
          UnconditionalSourcePhysicalStoppingPhaseFiber
            S B N d L m) =>
        (U : Matrix _ _ ℂ) (e.symm a) (e.symm q.1) *
          (V : Matrix _ _ ℂ) (e.symm b) (e.symm q.2) *
          z (e.symm q.1, e.symm q.2))).symm
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
theorem
    unconditionalSourcePhysicalCleanedStoppingFixedSource_physicalAction
    {S B N d L m : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    actualStoppingQuestionLocalAction
      (unconditionalSourcePhysicalCleanedTargetFirstUnitary
        S B N d L m
        (dSVDensityRationalHeterogeneousTargetFirstSpectralAlice
          S B N d L m width schedule ξ))
      (unconditionalSourcePhysicalCleanedTargetFirstUnitary
        S B N d L m
        (dSVDensityRationalHeterogeneousTargetFirstSpectralBob
          S B N d L m width schedule ζ))
      (unconditionalSourcePhysicalCleanedStoppingFixedSource
        S B N d L m) =
      unconditionalSourcePhysicalStoppingTargetFirstStateEquiv
        S B N d L m
        (dSVDensityRationalHeterogeneousOriginalStoppedState
          S B N d L m width schedule ξ ζ) := by
  unfold unconditionalSourcePhysicalCleanedStoppingFixedSource
  rw [unconditionalSourcePhysicalCleanedStoppingLocalAction_reindex]
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
theorem
    unconditionalSourcePhysicalCleanedStoppingFixedSource_branch_apply
    {S B N d L m : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (r s : Fin (L + 1))
    (φ ψ : DSVDensityRationalPublicMultiscalePhaseIndex S B)
    (a b : DSVUniformDensityIndependentHistoryLocalIndex
      (L + 1) N d)
    (i k : Fin m) :
    actualStoppingBranchVector
      (actualStoppingQuestionLocalAction
        (unconditionalSourcePhysicalCleanedTargetFirstUnitary
          S B N d L m
          (dSVDensityRationalHeterogeneousTargetFirstSpectralAlice
            S B N d L m width schedule ξ))
        (unconditionalSourcePhysicalCleanedTargetFirstUnitary
          S B N d L m
          (dSVDensityRationalHeterogeneousTargetFirstSpectralBob
            S B N d L m width schedule ζ))
        (unconditionalSourcePhysicalCleanedStoppingFixedSource
          S B N d L m)) r s
      (⟨(φ, a), i⟩, ⟨(ψ, b), k⟩) =
        ePRState
          (Fintype.card
            (DSVDensityRationalPublicMultiscalePhase S B))
          (φ, ψ) *
        dSVDensityRationalHeterogeneousActualPhysicalState
          N width schedule ξ ζ (⟨r, a⟩, ⟨s, b⟩) *
        embezzlementState m (i, k) := by
  rw [unconditionalSourcePhysicalCleanedStoppingFixedSource_physicalAction]
  exact
    unconditionalSourcePhysicalStoppingTargetFirst_branch_apply
      width schedule ξ ζ r s φ ψ a b i k
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
set_option autoImplicit true
theorem unconditionalActualCanonicalCleanedHistorySymm_eq_direct
    {L : ℕ} (j : Fin L) (β : Type*)
    (selected : β) (before : Fin j.val → β)
    (later : Fin (L - j.val) → β) :
    (unconditionalSourcePhysicalCleanedSelectedHistoryEquiv
      j β).symm (selected, (before, later)) =
      directDSVSelectedCopyLocalHistoryEquiv
        j (selected, (before, later)) := by
  apply (unconditionalSourcePhysicalCleanedSelectedHistoryEquiv
    j β).injective
  rw [Equiv.apply_symm_apply]
  apply Prod.ext
  · exact
      (directDSVSelectedCopyLocalHistoryEquiv_hit
        j selected before later).symm
  · apply Prod.ext
    · funext i
      exact
        (directDSVSelectedCopyLocalHistoryEquiv_before
          j selected before later i).symm
    · funext i
      exact
        (directDSVSelectedCopyLocalHistoryEquiv_after
          j selected before later i).symm
end
end QuantumParallelRepetition

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
theorem _root_.solution
    {S B N d L m : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (j : Fin L) :
    unconditionalSourcePhysicalCleanedFullBilateralStateIsometry
        (unconditionalActualMultiscalePhaseIndexEquiv
          (schedule j)).symm j
        (unconditionalActualCanonicalFixedSourceMatchedBranch
          (B := B) (m := m) width schedule ξ ζ j) =
      unconditionalMatchedVerifierTensor
        (unconditionalActualCanonicalRawSelectedPhysicalStage
          (B := B) (m := m) (width (schedule j)) ξ ζ)
        (unconditionalSelectedCopyRetainedWork
          (N := N) width schedule ξ ζ j
          (unconditionalActualCanonicalRetainedPhaseTail
            (S := S) (B := B) j)) := by
  classical
  ext ⟨⟨⟨⟨p, i⟩, packedA⟩, ⟨⟨q, k⟩, packedB⟩⟩,
    ⟨before, ⟨⟨afterA, afterB⟩, ⟨tailA, tailB⟩⟩⟩⟩
  let a := finProdFinEquiv.symm packedA
  let b := finProdFinEquiv.symm packedB
  let historyA :=
    (unconditionalSourcePhysicalCleanedSelectedHistoryEquiv j
      (DSVUniformDensityThresholdLocalIndex N d)).symm
      (⟨a.1, i⟩,
       ((fun t => (before t).1), afterA))
  let historyB :=
    (unconditionalSourcePhysicalCleanedSelectedHistoryEquiv j
      (DSVUniformDensityThresholdLocalIndex N d)).symm
      (⟨b.1, k⟩,
       ((fun t => (before t).2), afterB))
  change
    unconditionalActualCanonicalFixedSourceMatchedBranch
        width schedule ξ ζ j
        (⟨(unconditionalActualMultiscalePhaseIndexEquiv
              (schedule j) (p, tailA), historyA), a.2⟩,
         ⟨(unconditionalActualMultiscalePhaseIndexEquiv
              (schedule j) (q, tailB), historyB), b.2⟩) =
      unconditionalActualCanonicalRawSelectedPhysicalStage
        (width (schedule j)) ξ ζ
        (⟨(p, i), packedA⟩, ⟨(q, k), packedB⟩) *
      unconditionalSelectedCopyRetainedWork
        width schedule ξ ζ j
        (unconditionalActualCanonicalRetainedPhaseTail j)
        (before, ((afterA, afterB), (tailA, tailB)))
  unfold unconditionalActualCanonicalFixedSourceMatchedBranch
  rw [unconditionalSourcePhysicalCleanedStoppingFixedSource_branch_apply
    width schedule ξ ζ j.succ j.succ]
  rw [unconditionalActualMultiscalePhase_EPR_apply
    (schedule j) p q tailA tailB]
  change
    (ePRState B (p, q) *
       ePRState (Fintype.card (Fin (S - 1) → Fin B))
         (tailA, tailB)) *
       dSVDensityRationalHeterogeneousActualPhysicalState
         N width schedule ξ ζ
         (⟨j.succ, historyA⟩, ⟨j.succ, historyB⟩) *
       embezzlementState m (a.2, b.2) =
      (ePRState B (p, q) *
        dSVDensityRationalPhysicalAcceptedOutcome
          (width (schedule j)) N ξ ζ (⟨a.1, i⟩, ⟨b.1, k⟩) *
        embezzlementState m (a.2, b.2)) *
        (dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureVector
          (N := N) width schedule ξ ζ j before *
          (dSVUniformDensityIndependentSharedState
             (L - j.val) N d (afterA, afterB) *
           ePRState (Fintype.card (Fin (S - 1) → Fin B))
             (tailA, tailB)))
  rw [show historyA =
    directDSVSelectedCopyLocalHistoryEquiv j
      (⟨a.1, i⟩, ((fun t => (before t).1), afterA)) from
        unconditionalActualCanonicalCleanedHistorySymm_eq_direct
          j _ _ _ _,
    show historyB =
    directDSVSelectedCopyLocalHistoryEquiv j
      (⟨b.1, k⟩, ((fun t => (before t).2), afterB)) from
        unconditionalActualCanonicalCleanedHistorySymm_eq_direct
          j _ _ _ _]
  rw [directDSVActualStoppingSelectedHistory_sourceProduct]
  unfold dSVDensityRationalPhysicalAcceptedOutcome
  ring
end QuantumParallelRepetition

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Repetition/TenProofs/QuantumParallelRepetition/Part05.lean (solution of QuantumParallelRepetition.dSVDensityRationalHeterogeneousActualPhysicalFlagBornState_allFlags);
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
import Definitions.Def_MIPRE_Background_Repetition_TenProofs_QuantumParallelRepetition_Part04
import Definitions.Def_MIPRE_Background_Repetition_TenProofs_QuantumParallelRepetition_Part05
import Theorems.Thm_QuantumParallelRepetition_controlledFiniteTensorLocalUnitary_apply
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalFirstAcceptPhysicalEffect_eq_spectralMask
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalHeterogeneousActualFirstAcceptUnitary_zeroFlag
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalHeterogeneousActualFirstAccepted_sourceProduct
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyConditionMask
import Theorems.Thm_QuantumParallelRepetition_dSVUniformDensityCompletePureHistory_zeroFlag_apply
import Theorems.Thm_QuantumParallelRepetition_dSVUniformDensityFirstAcceptControlledTensor_inv_apply
import Theorems.Thm_QuantumParallelRepetition_dSVUniformDensityPhysicalMatched_doubleTensorSourceFactor

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
theorem dSVUniformDensityIndependentSharedState_apply
    (L N d : ℕ)
    (alice bob :
      DSVUniformDensityIndependentHistoryLocalIndex L N d) :
    dSVUniformDensityIndependentSharedState L N d
        (alice, bob) =
      ∏ j : Fin L,
        dSVUniformDensityThresholdSharedState N d
          (alice j, bob j) := by
  simp [dSVUniformDensityIndependentSharedState,
    dSVUniformDensityIndependentHistoryPairReindex,
    LinearIsometryEquiv.piLpCongrLeft_apply,
    finiteTensorVector,
    bilateralWorkPairEquiv]
end
end QuantumParallelRepetition

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

attribute [local instance] Classical.propDecidable

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
theorem dSVUniformDensityPhysicalSpectralAliceCopy_transpose
    {N d : ℕ} (ξ : BipartiteUnitVector d) :
    (dSVUniformDensityAliceHistorySpectralCopy
      (N := N) ξ : Matrix
        (DSVUniformDensityThresholdLocalIndex N d)
        (DSVUniformDensityThresholdLocalIndex N d) ℂ).transpose =
      (dSVUniformDensityBobHistoryCopyBasis
        (N := N) ξ : Matrix
          (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) := by
  classical
  change
    (Matrix.blockDiagonal'
      (fun _ : Fin N =>
        (((dSVUniformDensityThresholdLeftBobBasis ξ)⁻¹ :
          Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ))).transpose =
      Matrix.blockDiagonal'
        (fun _ : Fin N =>
          (conjugateUnitary
            (dSVUniformDensityThresholdLeftBobBasis ξ) :
            Matrix (Fin d) (Fin d) ℂ))
  rw [Matrix.blockDiagonal'_transpose]
  apply congrArg Matrix.blockDiagonal'
  funext k
  ext i j
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
theorem dSVUniformDensityPhysicalSpectralAliceCopy_inv_transpose
    {N d : ℕ} (ξ : BipartiteUnitVector d) :
    ((((dSVUniformDensityAliceHistorySpectralCopy
      (N := N) ξ)⁻¹ : Matrix.unitaryGroup
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
        Matrix (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ)).transpose =
      (((dSVUniformDensityBobHistoryCopyBasis
        (N := N) ξ)⁻¹ : Matrix.unitaryGroup
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
        Matrix (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) := by
  calc
    _ = (dSVUniformDensityAliceHistorySpectralCopy
      (N := N) ξ : Matrix
        (DSVUniformDensityThresholdLocalIndex N d)
        (DSVUniformDensityThresholdLocalIndex N d) ℂ).transpose.conjTranspose := by
          ext i j
          rfl
    _ = (dSVUniformDensityBobHistoryCopyBasis
      (N := N) ξ : Matrix
        (DSVUniformDensityThresholdLocalIndex N d)
        (DSVUniformDensityThresholdLocalIndex N d) ℂ).conjTranspose := by
          rw [dSVUniformDensityPhysicalSpectralAliceCopy_transpose]
    _ = _ := by
          rfl
end
end QuantumParallelRepetition

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
open scoped Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
theorem dSVDensityRationalFirstAcceptLocalSpectralMask_transpose
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) (outcome : Bool) :
    (dSVDensityRationalFirstAcceptLocalSpectralMask
      w N ξ outcome).transpose =
      dSVDensityRationalFirstAcceptLocalSpectralMask
        w N ξ outcome := by
  classical
  simp [dSVDensityRationalFirstAcceptLocalSpectralMask]
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
theorem
    dSVDensityRationalFirstAcceptPhysicalBobEffect_eq_spectralMask
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ζ : BipartiteUnitVector d) (outcome : Bool) :
    (transposePOVM
        (dSVDensityRationalCompleteProjectiveBinaryPOVM
          w N ζ)).effect outcome =
      (dSVUniformDensityBobHistoryCopyBasis
          (N := N) ζ :
          Matrix (DSVUniformDensityThresholdLocalIndex N d)
            (DSVUniformDensityThresholdLocalIndex N d) ℂ) *
        dSVDensityRationalFirstAcceptLocalSpectralMask
          w N ζ outcome *
        (((dSVUniformDensityBobHistoryCopyBasis
            (N := N) ζ)⁻¹ : Matrix.unitaryGroup
              (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
            Matrix (DSVUniformDensityThresholdLocalIndex N d)
              (DSVUniformDensityThresholdLocalIndex N d) ℂ) := by
  change
    ((dSVDensityRationalCompleteProjectiveBinaryPOVM
      w N ζ).effect outcome).transpose = _
  rw [dSVDensityRationalFirstAcceptPhysicalEffect_eq_spectralMask
    w N ζ outcome, Matrix.transpose_mul, Matrix.transpose_mul,
    dSVDensityRationalFirstAcceptLocalSpectralMask_transpose,
    dSVUniformDensityPhysicalSpectralAliceCopy_transpose,
    dSVUniformDensityPhysicalSpectralAliceCopy_inv_transpose]
  simp [Matrix.mul_assoc]
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

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
set_option autoImplicit true
theorem dSVDensityRationalHeterogeneousActualPhysicalState_apply_zeroFlag
    (N : ℕ) {S d L : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (a b : DSVUniformDensityThresholdWholeHistoryLocalIndex
      N d L) :
    dSVDensityRationalHeterogeneousActualPhysicalState
        N width schedule ξ ζ (a, b) =
      ∑ x : DSVUniformDensityIndependentHistoryLocalIndex
          (L + 1) N d,
        ∑ y : DSVUniformDensityIndependentHistoryLocalIndex
            (L + 1) N d,
          (dSVDensityRationalHeterogeneousActualAliceUnitary
              N width schedule ξ :
            Matrix
              (DSVUniformDensityThresholdWholeHistoryLocalIndex
                N d L)
              (DSVUniformDensityThresholdWholeHistoryLocalIndex
                N d L) ℂ) a ⟨0, x⟩ *
          (dSVDensityRationalHeterogeneousActualBobUnitary
              N width schedule ζ :
            Matrix
              (DSVUniformDensityThresholdWholeHistoryLocalIndex
                N d L)
              (DSVUniformDensityThresholdWholeHistoryLocalIndex
                N d L) ℂ) b ⟨0, y⟩ *
          dSVUniformDensityIndependentSharedState
            (L + 1) N d (x, y) := by
  classical
  have split_zero (p q : Prop) [Decidable p] [Decidable q]
      (v : ℂ) :
      (if p ∧ q then v else 0) =
        if p then (if q then v else 0) else 0 := by
    split_ifs <;> simp_all
  rw [dSVDensityRationalHeterogeneousActualPhysicalState_apply]
  simp only [Fintype.sum_sigma]
  simp_rw [dSVUniformDensityCompletePureHistory_zeroFlag_apply,
    mul_ite, mul_zero]
  simp_rw [split_zero]
  simp
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
set_option autoImplicit true
theorem dSVDensityRationalHeterogeneousActualSpectralStopping_apply
    {β : Type*} [Fintype β] [DecidableEq β]
    {L : ℕ} (accepted : Fin L → β → Prop)
    (U : Matrix.unitaryGroup β ℂ)
    (flag : Fin (L + 1))
    (history input : Fin (L + 1) → β) :
    ((dSVDensityRationalHeterogeneousActualFirstAcceptUnitary
        accepted *
      dSVDensityRationalFirstAcceptActualTensorBasis
        (L := L) U :
      Matrix.unitaryGroup (Σ _ : Fin (L + 1), Fin (L + 1) → β) ℂ) :
      Matrix (Σ _ : Fin (L + 1), Fin (L + 1) → β)
        (Σ _ : Fin (L + 1), Fin (L + 1) → β) ℂ)
        ⟨flag, history⟩ ⟨0, input⟩ =
      if flag =
        dSVDensityRationalHeterogeneousActualFirstAccepted
          accepted history
      then ∏ i : Fin (L + 1),
        (U : Matrix β β ℂ) (history i) (input i)
      else 0 := by
  classical
  let T := dSVDensityRationalFirstAcceptActualTensorBasis
    (L := L) U
  let W := dSVDensityRationalHeterogeneousActualFirstAcceptUnitary
    accepted
  let v : (Fin (L + 1) → β) → ℂ := fun h =>
    ∏ i : Fin (L + 1), (U : Matrix β β ℂ) (h i) (input i)
  have spectral_column :
      (fun q : (Σ _ : Fin (L + 1), Fin (L + 1) → β) =>
        (T : Matrix (Σ _ : Fin (L + 1), Fin (L + 1) → β)
          (Σ _ : Fin (L + 1), Fin (L + 1) → β) ℂ)
          q ⟨0, input⟩) =
      fun q => if q.1 = 0 then v q.2 else 0 := by
    funext q
    rcases q with ⟨stop, copies⟩
    change
      (controlledFiniteTensorLocalUnitary
          (fun (_ : Fin (L + 1)) (_ : Fin (L + 1)) => U) :
        Matrix (Σ _ : Fin (L + 1), Fin (L + 1) → β)
          (Σ _ : Fin (L + 1), Fin (L + 1) → β) ℂ)
          ⟨stop, copies⟩ ⟨0, input⟩ =
        if stop = 0 then v copies else 0
    rw [controlledFiniteTensorLocalUnitary_apply]
  change
    (W : Matrix (Σ _ : Fin (L + 1), Fin (L + 1) → β)
      (Σ _ : Fin (L + 1), Fin (L + 1) → β) ℂ).mulVec
      (fun q =>
        (T : Matrix (Σ _ : Fin (L + 1), Fin (L + 1) → β)
          (Σ _ : Fin (L + 1), Fin (L + 1) → β) ℂ)
          q ⟨0, input⟩)
      ⟨flag, history⟩ =
      if flag =
        dSVDensityRationalHeterogeneousActualFirstAccepted
          accepted history
      then v history else 0
  rw [spectral_column]
  exact
    dSVDensityRationalHeterogeneousActualFirstAcceptUnitary_zeroFlag
      accepted v flag history
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
set_option autoImplicit true
theorem dSVDensityRationalHeterogeneousActualPhysicalLocalUnitary_apply
    {β : Type*} [Fintype β] [DecidableEq β]
    {L : ℕ} (accepted : Fin L → β → Prop)
    (U : Matrix.unitaryGroup β ℂ)
    (flag : Fin (L + 1))
    (output input : Fin (L + 1) → β) :
    (dSVDensityRationalHeterogeneousActualPhysicalLocalUnitary
        accepted U :
      Matrix (Σ _ : Fin (L + 1), Fin (L + 1) → β)
        (Σ _ : Fin (L + 1), Fin (L + 1) → β) ℂ)
      ⟨flag, output⟩ ⟨0, input⟩ =
      ∑ history : Fin (L + 1) → β,
        (∏ i : Fin (L + 1),
          star ((U : Matrix β β ℂ) (history i) (output i))) *
        (if flag =
          dSVDensityRationalHeterogeneousActualFirstAccepted
            accepted history
        then ∏ i : Fin (L + 1),
          (U : Matrix β β ℂ) (history i) (input i)
        else 0) := by
  classical
  have restoration (other : Fin (L + 1))
      (history : Fin (L + 1) → β) :
      (((dSVDensityRationalFirstAcceptActualTensorBasis
          (L := L) U)⁻¹ :
          Matrix.unitaryGroup
            (Σ _ : Fin (L + 1), Fin (L + 1) → β) ℂ) :
        Matrix (Σ _ : Fin (L + 1), Fin (L + 1) → β)
          (Σ _ : Fin (L + 1), Fin (L + 1) → β) ℂ)
        ⟨flag, output⟩ ⟨other, history⟩ =
        if flag = other then
          ∏ i : Fin (L + 1),
            star ((U : Matrix β β ℂ) (history i) (output i))
        else 0 := by
    exact dSVUniformDensityFirstAcceptControlledTensor_inv_apply
      (fun (_ : Fin (L + 1)) (_ : Fin (L + 1)) => U)
      flag other output history
  unfold dSVDensityRationalHeterogeneousActualPhysicalLocalUnitary
  rw [mul_assoc]
  change
    ((((dSVDensityRationalFirstAcceptActualTensorBasis
          (L := L) U)⁻¹ :
        Matrix.unitaryGroup
          (Σ _ : Fin (L + 1), Fin (L + 1) → β) ℂ) :
        Matrix (Σ _ : Fin (L + 1), Fin (L + 1) → β)
          (Σ _ : Fin (L + 1), Fin (L + 1) → β) ℂ) *
      ((dSVDensityRationalHeterogeneousActualFirstAcceptUnitary
          accepted *
        dSVDensityRationalFirstAcceptActualTensorBasis
          (L := L) U :
        Matrix.unitaryGroup
          (Σ _ : Fin (L + 1), Fin (L + 1) → β) ℂ) :
        Matrix (Σ _ : Fin (L + 1), Fin (L + 1) → β)
          (Σ _ : Fin (L + 1), Fin (L + 1) → β) ℂ))
        ⟨flag, output⟩ ⟨0, input⟩ = _
  rw [Matrix.mul_apply, Fintype.sum_sigma, Finset.sum_comm]
  simp_rw [restoration,
    dSVDensityRationalHeterogeneousActualSpectralStopping_apply]
  simp [ite_mul]
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
    dSVDensityRationalHeterogeneousActualPhysicalLocalUnitary_sourceProduct
    {β : Type*} [Fintype β] [DecidableEq β]
    {L : ℕ} (accepted : Fin L → β → Prop)
    (U : Matrix.unitaryGroup β ℂ)
    (flag : Fin (L + 1))
    (output input : Fin (L + 1) → β) :
    (dSVDensityRationalHeterogeneousActualPhysicalLocalUnitary
        accepted U :
      Matrix (Σ _ : Fin (L + 1), Fin (L + 1) → β)
        (Σ _ : Fin (L + 1), Fin (L + 1) → β) ℂ)
      ⟨flag, output⟩ ⟨0, input⟩ =
      ∏ i : Fin (L + 1),
        ∑ atom : β,
          star ((U : Matrix β β ℂ) atom (output i)) *
          (if dSVDensityRationalHeterogeneousActualCopyCondition
              accepted flag i atom
          then (U : Matrix β β ℂ) atom (input i)
          else 0) := by
  rw [dSVDensityRationalHeterogeneousActualPhysicalLocalUnitary_apply]
  exact
    dSVDensityRationalHeterogeneousActualFirstAccepted_sourceProduct
      accepted flag
      (fun i atom => star ((U : Matrix β β ℂ) atom (output i)))
      (fun i atom => (U : Matrix β β ℂ) atom (input i))
end
end QuantumParallelRepetition

attribute [local instance] Classical.propDecidable

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
theorem dSVDensityRationalFirstAcceptActualOptionalOutcome_apply
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d)
    (a b : Option Bool)
    (alice bob : DSVUniformDensityThresholdLocalIndex N d) :
    dSVDensityRationalCompleteStoppedOptionalOutcome
        w N ξ ζ a b (alice, bob) =
      ∑ x : DSVUniformDensityThresholdLocalIndex N d,
        ∑ y : DSVUniformDensityThresholdLocalIndex N d,
          dSVDensityRationalCompleteStoppedOptionalLocalEffect
            w N ξ a alice x *
          (dSVDensityRationalCompleteStoppedOptionalLocalEffect
            w N ζ b).transpose bob y *
          dSVUniformDensityThresholdSharedState N d (x, y) := by
  classical
  unfold dSVDensityRationalCompleteStoppedOptionalOutcome
  change
    (∑ q :
      DSVUniformDensityThresholdLocalIndex N d ×
        DSVUniformDensityThresholdLocalIndex N d,
      (dSVDensityRationalCompleteStoppedOptionalLocalEffect
          w N ξ a ⊗ₖ
        (dSVDensityRationalCompleteStoppedOptionalLocalEffect
          w N ζ b).transpose) (alice, bob) q *
        dSVUniformDensityThresholdSharedState N d q) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rfl
end
end QuantumParallelRepetition

attribute [local instance] Classical.propDecidable

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
set_option autoImplicit true
theorem
    dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyMatrix_eq_spectralMask
    {β : Type*} [Fintype β] [DecidableEq β] {L : ℕ}
    (accepted : Fin L → β → Prop) (U : Matrix.unitaryGroup β ℂ)
    (flag : Fin (L + 1)) (i : Fin (L + 1)) :
    dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyMatrix
        accepted U flag i =
      (((U⁻¹ : Matrix.unitaryGroup β ℂ) : Matrix β β ℂ) *
        (Matrix.diagonal fun atom : β =>
          if dSVDensityRationalHeterogeneousActualCopyCondition
              accepted flag i atom then (1 : ℂ) else 0) *
        (U : Matrix β β ℂ)) := by
  classical
  ext output input
  simp [dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyMatrix,
    Matrix.mul_apply, Matrix.diagonal_apply, mul_ite]
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
    dSVDensityRationalHeterogeneousActualPhysicalFlagBornAliceCopy_eq_optionalEffect
    {S d N L : ℕ} (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ : BipartiteUnitVector d)
    (flag i : Fin (L + 1)) :
    dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyMatrix
        (dSVDensityRationalHeterogeneousActualCopyAccepted
          width schedule ξ)
        (dSVUniformDensityAliceHistorySpectralCopy (N := N) ξ)
        flag i =
      dSVDensityRationalCompleteStoppedOptionalLocalEffect
        (dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyWidth
          width schedule i) N ξ
        (dSVDensityRationalCompleteStoppedOptionalLocalSchedule
          L flag i) := by
  rw [dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyMatrix_eq_spectralMask,
    dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyConditionMask]
  cases h : dSVDensityRationalCompleteStoppedOptionalLocalSchedule
      L flag i with
  | none => simp [dSVDensityRationalCompleteStoppedOptionalLocalEffect]
  | some outcome =>
      simpa [h, dSVDensityRationalCompleteStoppedOptionalLocalEffect]
        using
          (dSVDensityRationalFirstAcceptPhysicalEffect_eq_spectralMask
            (dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyWidth
              width schedule i) N ξ outcome).symm
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
    dSVDensityRationalHeterogeneousActualPhysicalFlagBornBobCopy_eq_optionalEffect
    {S d N L : ℕ} (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ζ : BipartiteUnitVector d)
    (flag i : Fin (L + 1)) :
    dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyMatrix
        (dSVDensityRationalHeterogeneousActualCopyAccepted
          width schedule ζ)
        ((dSVUniformDensityBobHistoryCopyBasis (N := N) ζ)⁻¹)
        flag i =
      (dSVDensityRationalCompleteStoppedOptionalLocalEffect
        (dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyWidth
          width schedule i) N ζ
        (dSVDensityRationalCompleteStoppedOptionalLocalSchedule
          L flag i)).transpose := by
  rw [dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyMatrix_eq_spectralMask,
    dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyConditionMask]
  cases h : dSVDensityRationalCompleteStoppedOptionalLocalSchedule
      L flag i with
  | none => simp [dSVDensityRationalCompleteStoppedOptionalLocalEffect]
  | some outcome =>
      change
        _ = (transposePOVM
          (dSVDensityRationalCompleteProjectiveBinaryPOVM
            (dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyWidth
              width schedule i) N ζ)).effect outcome
      simpa only [inv_inv] using
        (dSVDensityRationalFirstAcceptPhysicalBobEffect_eq_spectralMask
          (dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyWidth
            width schedule i) N ζ outcome).symm
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
    dSVDensityRationalHeterogeneousActualPhysicalFlagBornAlice_sourceProduct
    {S d N L : ℕ} (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ : BipartiteUnitVector d) (flag : Fin (L + 1))
    (output input : DSVUniformDensityIndependentHistoryLocalIndex
      (L + 1) N d) :
    (dSVDensityRationalHeterogeneousActualAliceUnitary
        N width schedule ξ :
      Matrix (DSVUniformDensityThresholdWholeHistoryLocalIndex N d L)
        (DSVUniformDensityThresholdWholeHistoryLocalIndex N d L) ℂ)
        ⟨flag, output⟩ ⟨0, input⟩ =
      ∏ i : Fin (L + 1),
        dSVDensityRationalCompleteStoppedOptionalLocalEffect
          (dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyWidth
            width schedule i) N ξ
          (dSVDensityRationalCompleteStoppedOptionalLocalSchedule
            L flag i) (output i) (input i) := by
  change
    (dSVDensityRationalHeterogeneousActualPhysicalLocalUnitary
      (dSVDensityRationalHeterogeneousActualCopyAccepted
        width schedule ξ)
      (dSVUniformDensityAliceHistorySpectralCopy (N := N) ξ) :
      Matrix (DSVUniformDensityThresholdWholeHistoryLocalIndex N d L)
        (DSVUniformDensityThresholdWholeHistoryLocalIndex N d L) ℂ)
      ⟨flag, output⟩ ⟨0, input⟩ = _
  rw [dSVDensityRationalHeterogeneousActualPhysicalLocalUnitary_sourceProduct]
  apply Finset.prod_congr rfl
  intro i _
  change
    dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyMatrix
      (dSVDensityRationalHeterogeneousActualCopyAccepted
        width schedule ξ)
      (dSVUniformDensityAliceHistorySpectralCopy (N := N) ξ)
      flag i (output i) (input i) = _
  exact congrArg (fun M => M (output i) (input i))
    (dSVDensityRationalHeterogeneousActualPhysicalFlagBornAliceCopy_eq_optionalEffect
      width schedule ξ flag i)
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
    dSVDensityRationalHeterogeneousActualPhysicalFlagBornBob_sourceProduct
    {S d N L : ℕ} (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ζ : BipartiteUnitVector d) (flag : Fin (L + 1))
    (output input : DSVUniformDensityIndependentHistoryLocalIndex
      (L + 1) N d) :
    (dSVDensityRationalHeterogeneousActualBobUnitary
        N width schedule ζ :
      Matrix (DSVUniformDensityThresholdWholeHistoryLocalIndex N d L)
        (DSVUniformDensityThresholdWholeHistoryLocalIndex N d L) ℂ)
        ⟨flag, output⟩ ⟨0, input⟩ =
      ∏ i : Fin (L + 1),
        (dSVDensityRationalCompleteStoppedOptionalLocalEffect
          (dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyWidth
            width schedule i) N ζ
          (dSVDensityRationalCompleteStoppedOptionalLocalSchedule
            L flag i)).transpose (output i) (input i) := by
  change
    (dSVDensityRationalHeterogeneousActualPhysicalLocalUnitary
      (dSVDensityRationalHeterogeneousActualCopyAccepted
        width schedule ζ)
      ((dSVUniformDensityBobHistoryCopyBasis (N := N) ζ)⁻¹) :
      Matrix (DSVUniformDensityThresholdWholeHistoryLocalIndex N d L)
        (DSVUniformDensityThresholdWholeHistoryLocalIndex N d L) ℂ)
      ⟨flag, output⟩ ⟨0, input⟩ = _
  rw [dSVDensityRationalHeterogeneousActualPhysicalLocalUnitary_sourceProduct]
  apply Finset.prod_congr rfl
  intro i _
  change
    dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyMatrix
      (dSVDensityRationalHeterogeneousActualCopyAccepted
        width schedule ζ)
      ((dSVUniformDensityBobHistoryCopyBasis (N := N) ζ)⁻¹)
      flag i (output i) (input i) = _
  exact congrArg (fun M => M (output i) (input i))
    (dSVDensityRationalHeterogeneousActualPhysicalFlagBornBobCopy_eq_optionalEffect
      width schedule ζ flag i)
end
end QuantumParallelRepetition

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
set_option autoImplicit true
theorem _root_.solution
    {S d N L : ℕ} (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (flagAlice flagBob : Fin (L + 1))
    (alice bob : DSVUniformDensityIndependentHistoryLocalIndex
      (L + 1) N d) :
    dSVDensityRationalHeterogeneousActualPhysicalState
        N width schedule ξ ζ
        (⟨flagAlice, alice⟩, ⟨flagBob, bob⟩) =
      ∏ i : Fin (L + 1),
        dSVDensityRationalCompleteStoppedOptionalOutcome
          (dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyWidth
            width schedule i) N ξ ζ
          (dSVDensityRationalCompleteStoppedOptionalLocalSchedule
            L flagAlice i)
          (dSVDensityRationalCompleteStoppedOptionalLocalSchedule
            L flagBob i) (alice i, bob i) := by
  rw [dSVDensityRationalHeterogeneousActualPhysicalState_apply_zeroFlag]
  simp_rw [dSVUniformDensityIndependentSharedState_apply,
    dSVDensityRationalHeterogeneousActualPhysicalFlagBornAlice_sourceProduct,
    dSVDensityRationalHeterogeneousActualPhysicalFlagBornBob_sourceProduct]
  calc
    _ = ∏ i : Fin (L + 1),
          ∑ x : DSVUniformDensityThresholdLocalIndex N d,
            ∑ y : DSVUniformDensityThresholdLocalIndex N d,
              dSVDensityRationalCompleteStoppedOptionalLocalEffect
                  (dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyWidth
                    width schedule i) N ξ
                  (dSVDensityRationalCompleteStoppedOptionalLocalSchedule
                    L flagAlice i) (alice i) x *
                (dSVDensityRationalCompleteStoppedOptionalLocalEffect
                  (dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyWidth
                    width schedule i) N ζ
                  (dSVDensityRationalCompleteStoppedOptionalLocalSchedule
                    L flagBob i)).transpose (bob i) y *
                dSVUniformDensityThresholdSharedState N d (x, y) :=
      dSVUniformDensityPhysicalMatched_doubleTensorSourceFactor
        (fun i =>
          dSVDensityRationalCompleteStoppedOptionalLocalEffect
            (dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyWidth
              width schedule i) N ξ
            (dSVDensityRationalCompleteStoppedOptionalLocalSchedule
              L flagAlice i))
        (fun i =>
          (dSVDensityRationalCompleteStoppedOptionalLocalEffect
            (dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyWidth
              width schedule i) N ζ
            (dSVDensityRationalCompleteStoppedOptionalLocalSchedule
              L flagBob i)).transpose)
        (dSVUniformDensityThresholdSharedState N d)
        alice bob
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      exact
        (dSVDensityRationalFirstAcceptActualOptionalOutcome_apply
          (dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyWidth
            width schedule i) N ξ ζ
          (dSVDensityRationalCompleteStoppedOptionalLocalSchedule
            L flagAlice i)
          (dSVDensityRationalCompleteStoppedOptionalLocalSchedule
            L flagBob i) (alice i) (bob i)).symm
end QuantumParallelRepetition

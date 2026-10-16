/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Repetition/TenProofs/QuantumParallelRepetition/Part03.lean (solution of QuantumParallelRepetition.dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass_le_targetDistance);
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
import Mathlib.Logic.Embedding.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
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
import Theorems.Thm_QuantumParallelRepetition_coherentBinaryJointOutcome_norm_sq
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalActualMixedAsynchronousMass_eq_crossHazard
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalCompleteProjectiveOutcome_norm_sq_eq
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalHeterogeneousPhysicalStoppedEscape_budget
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalLargeWidthDiagonalMass_half
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalLargeWidthRelativeMismatch_le_discrepancy
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalPhysicalDiagonalBornSuccess_eq
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalPhysicalProjectorSquare_grid_eq
import Theorems.Thm_QuantumParallelRepetition_dSVUniformDensitySpectralAtomDiscrepancy_le
import Theorems.Thm_QuantumParallelRepetition_sharedThresholdResource_block_action_norm_sq

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
theorem transposePOVM_projective
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (P : POVM ι d)
    (hP : ∀ b : ι, P.effect b * P.effect b = P.effect b)
    (b : ι) :
    (transposePOVM P).effect b *
      (transposePOVM P).effect b =
        (transposePOVM P).effect b := by
  change
    (P.effect b).transpose * (P.effect b).transpose =
      (P.effect b).transpose
  rw [← Matrix.transpose_mul, hP b]
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
theorem dSVMixedProjectorSuccessLoss_le_square
    {d : Type*} [Fintype d] [DecidableEq d]
    (P R : Matrix d d ℂ)
    (hcomplement : (1 - P).PosSemidef)
    (hR : R.PosSemidef)
    (hPP : P * P = P) (hRR : R * R = R) :
    (Matrix.trace P).re - (Matrix.trace (P * R)).re ≤
      (Matrix.trace ((P - R) * (P - R))).re := by
  have remainder := trace_mul_posSemidef_nonneg hcomplement hR
  have square :
      (Matrix.trace ((P - R) * (P - R))).re =
        (Matrix.trace P).re + (Matrix.trace R).re -
          2 * (Matrix.trace (P * R)).re := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      hPP, hRR, Matrix.trace_sub, Matrix.trace_sub,
      Matrix.trace_sub, Matrix.trace_mul_comm R P]
    simp [Complex.sub_re]
    ring
  have rest :
      0 ≤ (Matrix.trace R).re - (Matrix.trace (P * R)).re := by
    simpa [Matrix.sub_mul, Matrix.trace_sub] using remainder
  rw [square]
  linarith
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
theorem dSVWeightedMixedProjectorSuccessLoss_le_square
    {κ d : Type*} [Fintype κ] [Fintype d]
    [DecidableEq d]
    (w : κ → ℝ) (nonnegative : ∀ k, 0 ≤ w k)
    (P R : κ → Matrix d d ℂ)
    (hcomplement : ∀ k, (1 - P k).PosSemidef)
    (hR : ∀ k, (R k).PosSemidef)
    (hPP : ∀ k, P k * P k = P k)
    (hRR : ∀ k, R k * R k = R k) :
    (∑ k : κ, w k * (Matrix.trace (P k)).re) -
        (∑ k : κ, w k * (Matrix.trace (P k * R k)).re) ≤
      ∑ k : κ, w k *
        (Matrix.trace ((P k - R k) * (P k - R k))).re := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro k _
  rw [← mul_sub]
  exact mul_le_mul_of_nonneg_left
    (dSVMixedProjectorSuccessLoss_le_square
      (P k) (R k) (hcomplement k) (hR k) (hPP k) (hRR k))
    (nonnegative k)
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
theorem dSVGlobalProjectorBinaryPOVM_projective
    {κ d : Type*} [Fintype κ] [Fintype d]
    [DecidableEq κ] [DecidableEq d]
    (P : κ → Matrix d d ℂ)
    (positive : ∀ k, (P k).PosSemidef)
    (complement : ∀ k, (1 - P k).PosSemidef)
    (projective : ∀ k, P k * P k = P k)
    (b : Bool) :
    (dSVGlobalProjectorBinaryPOVM
      P positive complement).effect b *
      (dSVGlobalProjectorBinaryPOVM
        P positive complement).effect b =
      (dSVGlobalProjectorBinaryPOVM
        P positive complement).effect b := by
  change
    Matrix.blockDiagonal' (fun k => if b then P k else 1 - P k) *
      Matrix.blockDiagonal' (fun k => if b then P k else 1 - P k) =
      Matrix.blockDiagonal' (fun k => if b then P k else 1 - P k)
  rw [← Matrix.blockDiagonal'_mul]
  apply congrArg (fun A : κ → Matrix d d ℂ => Matrix.blockDiagonal' A)
  funext k
  cases b
  · simp [Matrix.mul_sub, Matrix.sub_mul, projective k]
  · exact projective k
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
theorem dSVActualGlobalMixedBornSuccess_eq
    {κ d : Type*} [Fintype κ] [Fintype d]
    [DecidableEq κ] [DecidableEq d]
    (τ : κ → ℝ) (k₀ : κ) (i₀ : d) (nonzero : τ k₀ ≠ 0)
    (P R : κ → Matrix d d ℂ)
    (hP : ∀ k, (P k).PosSemidef)
    (hPc : ∀ k, (1 - P k).PosSemidef)
    (hR : ∀ k, (R k).PosSemidef)
    (hRc : ∀ k, (1 - R k).PosSemidef)
    (hPP : ∀ k, P k * P k = P k)
    (hRR : ∀ k, R k * R k = R k) :
    binaryJointSuccessProbability
      (pureDensityMatrix
        (sharedThresholdResource (d := d) τ)
        (sharedThresholdResource_norm τ k₀ i₀ nonzero))
      (dSVGlobalProjectorBinaryPOVM P hP hPc)
      (transposePOVM
        (dSVGlobalProjectorBinaryPOVM R hR hRc)) =
      (∑ k : κ, τ k ^ 2 * (Matrix.trace (P k * R k)).re) /
        ((Fintype.card d : ℝ) * ∑ k : κ, τ k ^ 2) := by
  let A := dSVGlobalProjectorBinaryPOVM P hP hPc
  let B := transposePOVM
    (dSVGlobalProjectorBinaryPOVM R hR hRc)
  let z := sharedThresholdResource (d := d) τ
  have hz : ‖z‖ = 1 :=
    sharedThresholdResource_norm τ k₀ i₀ nonzero
  have hA : ∀ b : Bool, A.effect b * A.effect b = A.effect b :=
    dSVGlobalProjectorBinaryPOVM_projective
      P hP hPc hPP
  have hB : ∀ b : Bool, B.effect b * B.effect b = B.effect b :=
    transposePOVM_projective
      (dSVGlobalProjectorBinaryPOVM R hR hRc)
      (dSVGlobalProjectorBinaryPOVM_projective
        R hR hRc hRR)
  change binaryJointSuccessProbability
    (pureDensityMatrix z hz) A B = _
  unfold binaryJointSuccessProbability
    binaryBornProbability
  rw [← coherentBinaryJointOutcome_norm_sq
    A B hA hB z hz true true]
  change
    ‖toLp 2
      ((Matrix.blockDiagonal' P ⊗ₖ
        (Matrix.blockDiagonal' R).transpose).mulVec
          (ofLp (sharedThresholdResource (d := d) τ)))‖ ^ 2 = _
  exact sharedThresholdResource_block_action_norm_sq
    τ P R hP hR hPP hRR
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
theorem dSVUniformDensityThresholdShared_mixedBorn_eq
    {N d : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (P R : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hP : ∀ k, (P k).PosSemidef)
    (hPc : ∀ k, (1 - P k).PosSemidef)
    (hR : ∀ k, (R k).PosSemidef)
    (hRc : ∀ k, (1 - R k).PosSemidef)
    (hPP : ∀ k, P k * P k = P k)
    (hRR : ∀ k, R k * R k = R k) :
    binaryJointSuccessProbability
      (dSVUniformDensityThresholdSharedDensity
        grid dimension)
      (dSVGlobalProjectorBinaryPOVM P hP hPc)
      (transposePOVM
        (dSVGlobalProjectorBinaryPOVM R hR hRc)) =
      (∑ k : Fin N, (Matrix.trace (P k * R k)).re) /
        ((d : ℝ) * (N : ℝ)) := by
  simpa [dSVUniformDensityThresholdSharedDensity,
    dSVUniformDensityThresholdSharedState] using
    dSVActualGlobalMixedBornSuccess_eq
      (fun _ : Fin N => (1 : ℝ))
      ⟨0, grid⟩ ⟨0, dimension⟩ (by norm_num)
      P R hP hPc hR hRc hPP hRR
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
theorem dSVUniformDensityThresholdShared_diagonalBorn_eq
    {N d : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (P : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hP : ∀ k, (P k).PosSemidef)
    (hPc : ∀ k, (1 - P k).PosSemidef)
    (hPP : ∀ k, P k * P k = P k) :
    binaryJointSuccessProbability
      (dSVUniformDensityThresholdSharedDensity
        grid dimension)
      (dSVGlobalProjectorBinaryPOVM P hP hPc)
      (transposePOVM
        (dSVGlobalProjectorBinaryPOVM P hP hPc)) =
      (∑ k : Fin N, (Matrix.trace (P k)).re) /
        ((d : ℝ) * (N : ℝ)) := by
  rw [dSVUniformDensityThresholdShared_mixedBorn_eq
    grid dimension P P hP hPc hP hPc hPP hPP]
  simp_rw [hPP]
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators ComplexOrder MatrixOrder
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
set_option maxRecDepth 3072
theorem dSVUniformLeftDensityConjugateSwapVector_distance
    {d : ℕ} (z w : EuclideanSpace ℂ (Fin d × Fin d)) :
    ‖dSVUniformLeftDensityConjugateSwapVector z -
        dSVUniformLeftDensityConjugateSwapVector w‖ =
      ‖z - w‖ := by
  have difference :
      dSVUniformLeftDensityConjugateSwapVector z -
        dSVUniformLeftDensityConjugateSwapVector w =
      dSVUniformLeftDensityConjugateSwapVector (z - w) := by
    ext ij
    change star (z (ij.2, ij.1)) - star (w (ij.2, ij.1)) =
      star ((z - w) (ij.2, ij.1))
    simp
  rw [difference,
    dSVUniformLeftDensityConjugateSwapVector_norm]
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators ComplexOrder MatrixOrder
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
set_option maxRecDepth 3072
theorem dSVUniformLeftDensityConjugateSwap_coefficient
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    targetCoefficientMatrix
        (dSVUniformLeftDensityConjugateSwap ξ) =
      (targetCoefficientMatrix ξ).conjTranspose := by
  ext b a
  rfl
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators ComplexOrder MatrixOrder
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
set_option maxRecDepth 3072
theorem dSVUniformLeftDensityConjugateSwap_density
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    targetReducedDensity
        (dSVUniformLeftDensityConjugateSwap ξ) =
      dSVSoftBobLeftReducedDensity ξ := by
  unfold targetReducedDensity
    dSVSoftBobLeftReducedDensity
  rw [dSVUniformLeftDensityConjugateSwap_coefficient,
    Matrix.conjTranspose_conjTranspose]
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators ComplexOrder MatrixOrder
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
set_option maxRecDepth 3072
theorem dSVUniformLeftDensityConjugateSwap_distance
    {d : ℕ} (ξ ζ : BipartiteUnitVector d) :
    ‖(dSVUniformLeftDensityConjugateSwap ξ).val -
        (dSVUniformLeftDensityConjugateSwap ζ).val‖ =
      ‖ξ.val - ζ.val‖ :=
  dSVUniformLeftDensityConjugateSwapVector_distance
    ξ.val ζ.val
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators ComplexOrder MatrixOrder
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
set_option maxRecDepth 3072
theorem dSVUniformLeftDensitySpectralAtomDiscrepancy_eq_swap
    {d : ℕ} (ξ ζ : BipartiteUnitVector d) :
    dSVUniformLeftDensitySpectralAtomDiscrepancy ξ ζ =
      dSVUniformDensitySpectralAtomDiscrepancy
        (dSVUniformLeftDensityConjugateSwap ξ)
        (dSVUniformLeftDensityConjugateSwap ζ) := by
  unfold dSVUniformLeftDensitySpectralAtomDiscrepancy
    dSVUniformDensitySpectralAtomDiscrepancy
    dSVUniformLeftDensitySchmidtCoefficient
    targetCanonicalSchmidtCoefficient
  simp only [dSVUniformLeftDensityConjugateSwap_density]
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators ComplexOrder MatrixOrder
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
set_option maxRecDepth 3072
theorem dSVUniformLeftDensitySpectralAtomDiscrepancy_le
    {d : ℕ} (ξ ζ : BipartiteUnitVector d) :
    dSVUniformLeftDensitySpectralAtomDiscrepancy ξ ζ ≤
      2 * Real.sqrt 2 * ‖ξ.val - ζ.val‖ := by
  rw [dSVUniformLeftDensitySpectralAtomDiscrepancy_eq_swap]
  have bound := dSVUniformDensitySpectralAtomDiscrepancy_le
    (dSVUniformLeftDensityConjugateSwap ξ)
    (dSVUniformLeftDensityConjugateSwap ζ)
  rwa [dSVUniformLeftDensityConjugateSwap_distance] at bound
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
theorem dSVDensityRationalPhysicalProjectorCrossHazard_eq
    {d N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (w : ℝ) (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalPhysicalProjectorCrossHazard N w ξ ζ =
      dSVDensityRationalLeftProjectiveThresholdAtomMismatch
        w N ξ ζ / (d : ℝ) := by
  have d_nonzero : (d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt dimension)
  have n_nonzero : (N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt grid)
  unfold dSVDensityRationalPhysicalProjectorCrossHazard
  calc
    (∑ k : Fin N,
      (Matrix.trace
        ((dSVDensityRationalPhysicalProjector w ξ k -
          dSVDensityRationalPhysicalProjector w ζ k) *
         (dSVDensityRationalPhysicalProjector w ξ k -
          dSVDensityRationalPhysicalProjector w ζ k))).re) /
        ((d : ℝ) * (N : ℝ)) =
      ((∑ k : Fin N,
        (Matrix.trace
          ((dSVDensityRationalPhysicalProjector w ξ k -
            dSVDensityRationalPhysicalProjector w ζ k) *
           (dSVDensityRationalPhysicalProjector w ξ k -
            dSVDensityRationalPhysicalProjector w ζ k))).re) /
          (N : ℝ)) / (d : ℝ) := by
      field_simp
    _ = dSVDensityRationalLeftProjectiveThresholdAtomMismatch
          w N ξ ζ / (d : ℝ) := by
      rw [dSVDensityRationalPhysicalProjectorSquare_grid_eq w ξ ζ]
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators ComplexOrder MatrixOrder
set_option autoImplicit true
theorem dSVDensityRationalLargeWidthDiagonalMass_pos
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / N ≤ 1 / (2 * (w + 1)))
    (ξ : BipartiteUnitVector d) :
    0 < dSVDensityRationalLeftProjectiveDiagonalMass w N ξ := by
  have lower := dSVDensityRationalLargeWidthDiagonalMass_half
    width grid fine ξ
  have positive : 0 < 1 / (2 * (w + 1)) := by positivity
  exact positive.trans_le lower
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators ComplexOrder MatrixOrder
set_option autoImplicit true
theorem
    dSVDensityRationalLargeWidthRelativeMismatch_le_targetDistance
    {d N : ℕ} {w : ℝ} (large : 1 ≤ w) (grid : 0 < N)
    (fine : (d : ℝ) / N ≤ 1 / (2 * (w + 1)))
    (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalLeftProjectiveThresholdAtomMismatch
        w N ξ ζ /
      dSVDensityRationalLeftProjectiveDiagonalMass w N ξ ≤
        8 * Real.sqrt 2 * ‖ξ.val - ζ.val‖ +
          2 * (w + 1) * ((d : ℝ) / N) := by
  have width : 0 < w := lt_of_lt_of_le (by norm_num) large
  have distance := dSVUniformLeftDensitySpectralAtomDiscrepancy_le
    ξ ζ
  have root : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
  have distance_nonnegative : 0 ≤ ‖ξ.val - ζ.val‖ := norm_nonneg _
  have denominator : 0 < w := width
  have ratio : (w + 1) / w ≤ 2 := by
    apply (div_le_iff₀ denominator).mpr
    nlinarith
  calc
    dSVDensityRationalLeftProjectiveThresholdAtomMismatch
        w N ξ ζ /
      dSVDensityRationalLeftProjectiveDiagonalMass w N ξ ≤
        2 * (w + 1) *
          (dSVUniformLeftDensitySpectralAtomDiscrepancy ξ ζ / w +
            (d : ℝ) / N) :=
      dSVDensityRationalLargeWidthRelativeMismatch_le_discrepancy
        width grid fine ξ ζ
    _ ≤ 2 * (w + 1) *
          ((2 * Real.sqrt 2 * ‖ξ.val - ζ.val‖) / w +
            (d : ℝ) / N) := by
      gcongr
    _ = 4 * Real.sqrt 2 * ‖ξ.val - ζ.val‖ * ((w + 1) / w) +
          2 * (w + 1) * ((d : ℝ) / N) := by
      field_simp; ring
    _ ≤ (4 * Real.sqrt 2 * ‖ξ.val - ζ.val‖) * 2 +
          2 * (w + 1) * ((d : ℝ) / N) := by
      have scale_nonnegative :
          0 ≤ 4 * Real.sqrt 2 * ‖ξ.val - ζ.val‖ := by positivity
      have scaled := mul_le_mul_of_nonneg_left ratio scale_nonnegative
      exact add_le_add scaled (le_refl _)
    _ = 8 * Real.sqrt 2 * ‖ξ.val - ζ.val‖ +
          2 * (w + 1) * ((d : ℝ) / N) := by
      ring
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators ComplexOrder MatrixOrder
set_option autoImplicit true
theorem dSVDensityRationalLargeWidthPhysicalDiagonalBornSuccess_pos
    {d N : ℕ} (dimension : 0 < d) {w : ℝ}
    (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / N ≤ 1 / (2 * (w + 1)))
    (ξ : BipartiteUnitVector d) :
    0 < dSVDensityRationalPhysicalDiagonalBornSuccess
      grid dimension w ξ := by
  rw [dSVDensityRationalPhysicalDiagonalBornSuccess_eq
    grid dimension w ξ]
  exact div_pos
    (dSVDensityRationalLargeWidthDiagonalMass_pos
      width grid fine ξ)
    (by exact_mod_cast dimension)
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators ComplexOrder MatrixOrder
set_option autoImplicit true
theorem dSVDensityRationalLargeWidthPhysicalRelativeHazard_eq
    {d N : ℕ} (dimension : 0 < d) {w : ℝ}
    (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / N ≤ 1 / (2 * (w + 1)))
    (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalPhysicalProjectorCrossHazard N w ξ ζ /
      dSVDensityRationalPhysicalDiagonalBornSuccess
        grid dimension w ξ =
      dSVDensityRationalLeftProjectiveThresholdAtomMismatch
        w N ξ ζ /
        dSVDensityRationalLeftProjectiveDiagonalMass w N ξ := by
  rw [dSVDensityRationalPhysicalProjectorCrossHazard_eq
    grid dimension w ξ ζ,
    dSVDensityRationalPhysicalDiagonalBornSuccess_eq
      grid dimension w ξ]
  have dimension_ne : (d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt dimension)
  have mass_ne :
      dSVDensityRationalLeftProjectiveDiagonalMass w N ξ ≠ 0 :=
    ne_of_gt (dSVDensityRationalLargeWidthDiagonalMass_pos
      width grid fine ξ)
  field_simp
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators ComplexOrder MatrixOrder
set_option autoImplicit true
theorem dSVDensityRationalLargeWidthPhysicalRelativeHazard_le
    {d N : ℕ} (dimension : 0 < d) {w : ℝ}
    (large : 1 ≤ w) (grid : 0 < N)
    (fine : (d : ℝ) / N ≤ 1 / (2 * (w + 1)))
    (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalPhysicalProjectorCrossHazard N w ξ ζ /
      dSVDensityRationalPhysicalDiagonalBornSuccess
        grid dimension w ξ ≤
      8 * Real.sqrt 2 * ‖ξ.val - ζ.val‖ +
        2 * (w + 1) * ((d : ℝ) / N) := by
  have width : 0 < w := lt_of_lt_of_le (by norm_num) large
  rw [dSVDensityRationalLargeWidthPhysicalRelativeHazard_eq
    dimension width grid fine ξ ζ]
  exact
    dSVDensityRationalLargeWidthRelativeMismatch_le_targetDistance
      large grid fine ξ ζ
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
theorem dSVDensityRationalPhysicalMixedBornSuccess_eq
    {d N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (w : ℝ) (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalPhysicalMixedBornSuccess
        grid dimension w ξ ζ =
      (∑ k : Fin N, (Matrix.trace
        (dSVDensityRationalPhysicalProjector w ξ k *
          dSVDensityRationalPhysicalProjector w ζ k)).re) /
        ((d : ℝ) * (N : ℝ)) := by
  unfold dSVDensityRationalPhysicalMixedBornSuccess
    dSVDensityRationalPhysicalGlobalPOVM
  exact dSVUniformDensityThresholdShared_mixedBorn_eq
    grid dimension
    (dSVDensityRationalPhysicalProjector w ξ)
    (dSVDensityRationalPhysicalProjector w ζ)
    (dSVDensityRationalPhysicalProjector_pos w ξ)
    (dSVDensityRationalPhysicalProjector_complement_pos w ξ)
    (dSVDensityRationalPhysicalProjector_pos w ζ)
    (dSVDensityRationalPhysicalProjector_complement_pos w ζ)
    (dSVDensityRationalPhysicalProjector_projective w ξ)
    (dSVDensityRationalPhysicalProjector_projective w ζ)
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
theorem dSVDensityRationalPhysicalMixedBornSuccess_loss_le
    {d N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (w : ℝ) (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalPhysicalDiagonalBornSuccess
        grid dimension w ξ -
      dSVDensityRationalPhysicalMixedBornSuccess
        grid dimension w ξ ζ ≤
      dSVDensityRationalPhysicalProjectorCrossHazard
        N w ξ ζ := by
  have denominator : 0 < (d : ℝ) * (N : ℝ) := by
    exact mul_pos (by exact_mod_cast dimension)
      (by exact_mod_cast grid)
  have diagonal :
      dSVDensityRationalPhysicalDiagonalBornSuccess
          grid dimension w ξ =
        (∑ k : Fin N,
          (Matrix.trace
            (dSVDensityRationalPhysicalProjector w ξ k)).re) /
          ((d : ℝ) * (N : ℝ)) := by
    unfold dSVDensityRationalPhysicalDiagonalBornSuccess
      dSVDensityRationalPhysicalGlobalPOVM
    exact dSVUniformDensityThresholdShared_diagonalBorn_eq
      grid dimension
      (dSVDensityRationalPhysicalProjector w ξ)
      (dSVDensityRationalPhysicalProjector_pos w ξ)
      (dSVDensityRationalPhysicalProjector_complement_pos w ξ)
      (dSVDensityRationalPhysicalProjector_projective w ξ)
  have ledger := dSVWeightedMixedProjectorSuccessLoss_le_square
    (fun _ : Fin N => (1 : ℝ)) (fun _ => zero_le_one)
    (dSVDensityRationalPhysicalProjector w ξ)
    (dSVDensityRationalPhysicalProjector w ζ)
    (dSVDensityRationalPhysicalProjector_complement_pos w ξ)
    (dSVDensityRationalPhysicalProjector_pos w ζ)
    (dSVDensityRationalPhysicalProjector_projective w ξ)
    (dSVDensityRationalPhysicalProjector_projective w ζ)
  simp only [one_mul] at ledger
  rw [diagonal,
    dSVDensityRationalPhysicalMixedBornSuccess_eq
      grid dimension w ξ ζ]
  unfold dSVDensityRationalPhysicalProjectorCrossHazard
  rw [← sub_div]
  exact (div_le_div_iff_of_pos_right denominator).mpr ledger
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
set_option autoImplicit true
theorem dSVDensityRationalActualMixedSuccessMass_eq
    {d N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (w : ℝ) (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalActualMixedSuccessMass w N ξ ζ =
      dSVDensityRationalPhysicalMixedBornSuccess
        grid dimension w ξ ζ := by
  unfold dSVDensityRationalActualMixedSuccessMass
  rw [dSVDensityRationalCompleteProjectiveOutcome_norm_sq_eq,
    dSVDensityRationalPhysicalMixedBornSuccess_eq
      grid dimension w ξ ζ]
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
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
set_option autoImplicit true
theorem dSVDensityRationalActualMixed_escape_ge_diagonal
    {d N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (w : ℝ) (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalPhysicalDiagonalBornSuccess
        grid dimension w ξ ≤
      dSVDensityRationalActualMixedSuccessMass w N ξ ζ +
        dSVDensityRationalActualMixedAsynchronousMass
          w N ξ ζ := by
  have loss := dSVDensityRationalPhysicalMixedBornSuccess_loss_le
    grid dimension w ξ ζ
  rw [← dSVDensityRationalActualMixedSuccessMass_eq
      grid dimension w ξ ζ,
    ← dSVDensityRationalActualMixedAsynchronousMass_eq_crossHazard
      w N ξ ζ] at loss
  linarith
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
theorem
    dSVDensityRationalHeterogeneousPhysicalStageAsynchronous_eq_hazard
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (k : Fin L) :
    dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
        N width schedule ξ ζ k.val =
      dSVDensityRationalPhysicalProjectorCrossHazard
        N (width (schedule k)) ξ ζ := by
  simpa [
    dSVDensityRationalHeterogeneousPhysicalStageAsynchronous,
    dSVDensityRationalHeterogeneousPhysicalStageOutcome,
    k.isLt,
    dSVDensityRationalActualMixedAsynchronousMass] using
      (dSVDensityRationalActualMixedAsynchronousMass_eq_crossHazard
        (width (schedule k)) N ξ ζ)
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
theorem
    dSVDensityRationalHeterogeneousPhysicalStageAsynchronous_eq_escape_mul_ratio
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (k : ℕ) :
    dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
        N width schedule ξ ζ k =
      (dSVDensityRationalHeterogeneousPhysicalStageSuccess
          N width schedule ξ ζ k +
        dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
          N width schedule ξ ζ k) *
        dSVDensityRationalHeterogeneousPhysicalStageHazardRatio
          N width schedule ξ ζ k := by
  let p := dSVDensityRationalHeterogeneousPhysicalStageSuccess
    N width schedule ξ ζ k
  let h := dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
    N width schedule ξ ζ k
  have p_nonnegative : 0 ≤ p :=
    dSVDensityRationalHeterogeneousPhysicalStageOutcome_nonneg
      N width schedule ξ ζ k true true
  have h_nonnegative : 0 ≤ h := add_nonneg
    (dSVDensityRationalHeterogeneousPhysicalStageOutcome_nonneg
      N width schedule ξ ζ k true false)
    (dSVDensityRationalHeterogeneousPhysicalStageOutcome_nonneg
      N width schedule ξ ζ k false true)
  change h = (p + h) * (h / (p + h))
  by_cases vanished : p + h = 0
  · have h_zero : h = 0 := by linarith
    simp [h_zero]
  · field_simp
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
set_option autoImplicit true
theorem
    dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass_eq_ratioLedger
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
        N width schedule ξ ζ =
      ∑ k ∈ Finset.range L,
        dSVDensityRationalHeterogeneousPhysicalSurvival
            N width schedule ξ ζ k *
          (dSVDensityRationalHeterogeneousPhysicalStageSuccess
              N width schedule ξ ζ k +
            dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
              N width schedule ξ ζ k) *
          dSVDensityRationalHeterogeneousPhysicalStageHazardRatio
            N width schedule ξ ζ k := by
  unfold
    dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
  apply Finset.sum_congr rfl
  intro k _
  calc
    dSVDensityRationalHeterogeneousPhysicalSurvival
        N width schedule ξ ζ k *
      dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
        N width schedule ξ ζ k =
      dSVDensityRationalHeterogeneousPhysicalSurvival
          N width schedule ξ ζ k *
        ((dSVDensityRationalHeterogeneousPhysicalStageSuccess
            N width schedule ξ ζ k +
          dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
            N width schedule ξ ζ k) *
          dSVDensityRationalHeterogeneousPhysicalStageHazardRatio
            N width schedule ξ ζ k) :=
      congrArg
        (fun x : ℝ =>
          dSVDensityRationalHeterogeneousPhysicalSurvival
            N width schedule ξ ζ k * x)
        (dSVDensityRationalHeterogeneousPhysicalStageAsynchronous_eq_escape_mul_ratio
          N width schedule ξ ζ k)
    _ = _ := by ring
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
set_option autoImplicit true
theorem
    dSVDensityRationalHeterogeneousPhysicalStage_escape_ge_diagonal
    {d S L N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (k : Fin L) :
    dSVDensityRationalPhysicalDiagonalBornSuccess
        grid dimension (width (schedule k)) ξ ≤
      dSVDensityRationalHeterogeneousPhysicalStageSuccess
          N width schedule ξ ζ k.val +
        dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
          N width schedule ξ ζ k.val := by
  simpa [
    dSVDensityRationalHeterogeneousPhysicalStageSuccess,
    dSVDensityRationalHeterogeneousPhysicalStageAsynchronous,
    dSVDensityRationalHeterogeneousPhysicalStageOutcome,
    k.isLt,
    dSVDensityRationalActualMixedSuccessMass,
    dSVDensityRationalActualMixedAsynchronousMass]
    using dSVDensityRationalActualMixed_escape_ge_diagonal
      grid dimension (width (schedule k)) ξ ζ
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
set_option autoImplicit true
theorem
    dSVDensityRationalHeterogeneousPhysicalStageAsynchronous_relative_diagonal_le
    {d S L N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (width : Fin S → ℝ) (large : ∀ s, 1 ≤ width s)
    (fine : ∀ s : Fin S,
      (d : ℝ) / N ≤ 1 / (2 * (width s + 1)))
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (k : Fin L) :
    dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
        N width schedule ξ ζ k.val /
      dSVDensityRationalPhysicalDiagonalBornSuccess
        grid dimension (width (schedule k)) ξ ≤
      8 * Real.sqrt 2 * ‖ξ.val - ζ.val‖ +
        2 * (width (schedule k) + 1) * ((d : ℝ) / N) := by
  rw [
    dSVDensityRationalHeterogeneousPhysicalStageAsynchronous_eq_hazard
      N width schedule ξ ζ k]
  exact dSVDensityRationalLargeWidthPhysicalRelativeHazard_le
    dimension (large (schedule k)) grid (fine (schedule k)) ξ ζ
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
set_option autoImplicit true
theorem
    dSVDensityRationalHeterogeneousPhysicalStageHazardRatio_le_relative_diagonal
    {d S L N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (width : Fin S → ℝ) (large : ∀ s, 1 ≤ width s)
    (fine : ∀ s : Fin S,
      (d : ℝ) / N ≤ 1 / (2 * (width s + 1)))
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (k : Fin L) :
    dSVDensityRationalHeterogeneousPhysicalStageHazardRatio
        N width schedule ξ ζ k.val ≤
      dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
          N width schedule ξ ζ k.val /
        dSVDensityRationalPhysicalDiagonalBornSuccess
          grid dimension (width (schedule k)) ξ := by
  have width_positive : 0 < width (schedule k) :=
    lt_of_lt_of_le (by norm_num) (large (schedule k))
  have self_positive :=
    dSVDensityRationalLargeWidthPhysicalDiagonalBornSuccess_pos
      dimension width_positive grid (fine (schedule k)) ξ
  have self_lower :=
    dSVDensityRationalHeterogeneousPhysicalStage_escape_ge_diagonal
      grid dimension width schedule ξ ζ k
  have asynchronous_nonnegative :
      0 ≤ dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
        N width schedule ξ ζ k.val := by
    exact add_nonneg
      (dSVDensityRationalHeterogeneousPhysicalStageOutcome_nonneg
        N width schedule ξ ζ k.val true false)
      (dSVDensityRationalHeterogeneousPhysicalStageOutcome_nonneg
        N width schedule ξ ζ k.val false true)
  unfold dSVDensityRationalHeterogeneousPhysicalStageHazardRatio
  exact div_le_div_of_nonneg_left
    asynchronous_nonnegative self_positive self_lower
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
set_option autoImplicit true
theorem
    dSVDensityRationalHeterogeneousPhysicalStageHazardRatio_le_targetDistance
    {d S L N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (width : Fin S → ℝ) (large : ∀ s, 1 ≤ width s)
    (fine : ∀ s : Fin S,
      (d : ℝ) / N ≤ 1 / (2 * (width s + 1)))
    {W : ℝ} (upper : ∀ s, width s ≤ W)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (k : Fin L) :
    dSVDensityRationalHeterogeneousPhysicalStageHazardRatio
        N width schedule ξ ζ k.val ≤
      8 * Real.sqrt 2 * ‖ξ.val - ζ.val‖ +
        2 * (W + 1) * ((d : ℝ) / N) := by
  calc
    _ ≤ dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
          N width schedule ξ ζ k.val /
        dSVDensityRationalPhysicalDiagonalBornSuccess
          grid dimension (width (schedule k)) ξ :=
      dSVDensityRationalHeterogeneousPhysicalStageHazardRatio_le_relative_diagonal
        grid dimension width large fine schedule ξ ζ k
    _ ≤ 8 * Real.sqrt 2 * ‖ξ.val - ζ.val‖ +
        2 * (width (schedule k) + 1) * ((d : ℝ) / N) :=
      dSVDensityRationalHeterogeneousPhysicalStageAsynchronous_relative_diagonal_le
        grid dimension width large fine schedule ξ ζ k
    _ ≤ 8 * Real.sqrt 2 * ‖ξ.val - ζ.val‖ +
        2 * (W + 1) * ((d : ℝ) / N) := by
      have scale := upper (schedule k)
      have grid_cost : 0 ≤ (d : ℝ) / N := by positivity
      nlinarith [mul_nonneg grid_cost (sub_nonneg.mpr scale)]
end
end QuantumParallelRepetition

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
set_option autoImplicit true
theorem _root_.solution
    {d S L N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (width : Fin S → ℝ) (large : ∀ s, 1 ≤ width s)
    (fine : ∀ s : Fin S,
      (d : ℝ) / N ≤ 1 / (2 * (width s + 1)))
    {W : ℝ} (upper : ∀ s, width s ≤ W) (W_nonnegative : 0 ≤ W)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
        N width schedule ξ ζ ≤
      8 * Real.sqrt 2 * ‖ξ.val - ζ.val‖ +
        2 * (W + 1) * ((d : ℝ) / N) := by
  let bound : ℝ :=
    8 * Real.sqrt 2 * ‖ξ.val - ζ.val‖ +
      2 * (W + 1) * ((d : ℝ) / N)
  have bound_nonnegative : 0 ≤ bound := by
    dsimp [bound]
    positivity
  have escape_budget :=
    dSVDensityRationalHeterogeneousPhysicalStoppedEscape_budget
      grid dimension width schedule ξ ζ
  rw [
    dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass_eq_ratioLedger]
  change
    (∑ k ∈ Finset.range L,
      dSVDensityRationalHeterogeneousPhysicalSurvival
          N width schedule ξ ζ k *
        (dSVDensityRationalHeterogeneousPhysicalStageSuccess
            N width schedule ξ ζ k +
          dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
            N width schedule ξ ζ k) *
        dSVDensityRationalHeterogeneousPhysicalStageHazardRatio
          N width schedule ξ ζ k) ≤ bound
  calc
    _ ≤ ∑ k ∈ Finset.range L,
      dSVDensityRationalHeterogeneousPhysicalSurvival
          N width schedule ξ ζ k *
        (dSVDensityRationalHeterogeneousPhysicalStageSuccess
            N width schedule ξ ζ k +
          dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
            N width schedule ξ ζ k) * bound := by
      apply Finset.sum_le_sum
      intro k member
      have active : k < L := Finset.mem_range.mp member
      let stage : Fin L := ⟨k, active⟩
      have ratio :=
        dSVDensityRationalHeterogeneousPhysicalStageHazardRatio_le_targetDistance
          grid dimension width large fine upper schedule ξ ζ stage
      have survival_nonnegative :=
        dSVDensityRationalHeterogeneousPhysicalSurvival_nonneg
          N width schedule ξ ζ k
      have success_nonnegative :=
        dSVDensityRationalHeterogeneousPhysicalStageOutcome_nonneg
          N width schedule ξ ζ k true true
      have asynchronous_nonnegative :
          0 ≤
            dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
              N width schedule ξ ζ k := by
        exact add_nonneg
          (dSVDensityRationalHeterogeneousPhysicalStageOutcome_nonneg
            N width schedule ξ ζ k true false)
          (dSVDensityRationalHeterogeneousPhysicalStageOutcome_nonneg
            N width schedule ξ ζ k false true)
      have coefficient_nonnegative :
          0 ≤
            dSVDensityRationalHeterogeneousPhysicalSurvival
                N width schedule ξ ζ k *
              (dSVDensityRationalHeterogeneousPhysicalStageSuccess
                  N width schedule ξ ζ k +
                dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
                  N width schedule ξ ζ k) :=
        mul_nonneg survival_nonnegative
          (add_nonneg success_nonnegative asynchronous_nonnegative)
      apply mul_le_mul_of_nonneg_left _ coefficient_nonnegative
      simpa [stage, bound] using ratio
    _ =
      (∑ k ∈ Finset.range L,
        dSVDensityRationalHeterogeneousPhysicalSurvival
            N width schedule ξ ζ k *
          (dSVDensityRationalHeterogeneousPhysicalStageSuccess
              N width schedule ξ ζ k +
            dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
              N width schedule ξ ζ k)) * bound := by
      rw [Finset.sum_mul]
    _ ≤ bound := by
      nlinarith [mul_nonneg bound_nonnegative
        (sub_nonneg.mpr escape_budget)]
end QuantumParallelRepetition

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Repetition/TenProofs/QuantumParallelRepetition/Part05.lean (solution of QuantumParallelRepetition.exists_proofDSVDensityRationalPublicBucketPhysicalMixedPrefixCleanup_sq);
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
import Theorems.Thm_QuantumParallelRepetition_dSVCanonicalFailurePrefix_norm_sq
import Theorems.Thm_QuantumParallelRepetition_dSVCanonicalFailurePrefix_sub_norm_sq
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor_norm_sq
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalPublicBucketCanonicalPrefixCleanup_sq
import Theorems.Thm_QuantumParallelRepetition_localUnitaryAction_norm

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
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
theorem localUnitaryAction_sub
    {m : ℕ}
    (U V : Matrix.unitaryGroup (Fin m) ℂ)
    (z w : EuclideanSpace ℂ (Fin m × Fin m)) :
    localUnitaryAction U V (z - w) =
      localUnitaryAction U V z -
        localUnitaryAction U V w := by
  apply WithLp.ofLp_injective
  change
    ((U.val ⊗ₖ V.val).mulVec
      ((ofLp z) - (ofLp w))) =
        ((U.val ⊗ₖ V.val).mulVec (ofLp z)) -
          ((U.val ⊗ₖ V.val).mulVec (ofLp w))
  exact Matrix.mulVec_sub _ _ _
end
end QuantumParallelRepetition

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 3072
theorem dSVCanonicalFailurePrefix_eq_zero_of_rank_zero
    {d : ℕ} (rank : Fin (d + 1))
    (zero : rank.val = 0) :
    dSVCanonicalFailurePrefix rank = 0 := by
  have squared :
      ‖dSVCanonicalFailurePrefix rank‖ ^ 2 = 0 := by
    simpa [zero] using dSVCanonicalFailurePrefix_norm_sq rank
  have normzero : ‖dSVCanonicalFailurePrefix rank‖ = 0 := by
    nlinarith [norm_nonneg (dSVCanonicalFailurePrefix rank)]
  exact norm_eq_zero.mp normzero
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 3072
theorem dSVCanonicalFailurePrefix_norm_eq_sqrt
    {d : ℕ} (rank : Fin (d + 1)) :
    ‖dSVCanonicalFailurePrefix rank‖ =
      Real.sqrt (rank.val : ℝ) := by
  have squared := dSVCanonicalFailurePrefix_norm_sq rank
  have root := Real.sq_sqrt (by positivity : 0 ≤ (rank.val : ℝ))
  nlinarith [norm_nonneg (dSVCanonicalFailurePrefix rank),
    Real.sqrt_nonneg (rank.val : ℝ)]
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
    dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor_unit
    {N n : ℕ} (z : BipartiteUnitVector N) :
    dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
        n z.val =
      tensorEmbezzlementTarget (n := n) z := by
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
    dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor_sub
    {N : ℕ} (n : ℕ)
    (x y : EuclideanSpace ℂ (Fin N × Fin N)) :
    dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
        n (x - y) =
      dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
          n x -
        dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
          n y := by
  ext q
  change
    (x ((finProdFinEquiv.symm q.1).1,
          (finProdFinEquiv.symm q.2).1) -
      y ((finProdFinEquiv.symm q.1).1,
          (finProdFinEquiv.symm q.2).1)) *
        embezzlementState n
          ((finProdFinEquiv.symm q.1).2,
            (finProdFinEquiv.symm q.2).2) =
      x ((finProdFinEquiv.symm q.1).1,
          (finProdFinEquiv.symm q.2).1) *
        embezzlementState n
          ((finProdFinEquiv.symm q.1).2,
            (finProdFinEquiv.symm q.2).2) -
      y ((finProdFinEquiv.symm q.1).1,
          (finProdFinEquiv.symm q.2).1) *
        embezzlementState n
          ((finProdFinEquiv.symm q.1).2,
            (finProdFinEquiv.symm q.2).2)
  ring
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
    dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor_prefix_sub_norm_sq
    {N n : ℕ} (positive : 0 < n)
    (r s : Fin (N + 1)) :
    ‖dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
          n (dSVCanonicalFailurePrefix r) -
        dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
          n (dSVCanonicalFailurePrefix s)‖ ^ 2 =
      |(r.val : ℝ) - (s.val : ℝ)| := by
  rw [← dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor_sub,
    dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor_norm_sq
      positive,
    dSVCanonicalFailurePrefix_sub_norm_sq]
end
end QuantumParallelRepetition

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
    dSVDensityRationalMixedCanonicalPrefixPhysicalLocalAction_real_smul
    {n : ℕ} (A B : Matrix.unitaryGroup (Fin n) ℂ)
    (r : ℝ) (z : EuclideanSpace ℂ (Fin n × Fin n)) :
    localUnitaryAction A B (r • z) =
      r • localUnitaryAction A B z := by
  change
    Matrix.toEuclideanLin
        ((A : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ
          (B : Matrix (Fin n) (Fin n) ℂ)) (r • z) =
      r • Matrix.toEuclideanLin
        ((A : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ
          (B : Matrix (Fin n) (Fin n) ℂ)) z
  exact (Matrix.toEuclideanLin
    ((A : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ
      (B : Matrix (Fin n) (Fin n) ℂ))).map_smul_of_tower r z
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
    dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor_real_smul
    {N : ℕ} (n : ℕ) (r : ℝ)
    (z : EuclideanSpace ℂ (Fin N × Fin N)) :
    dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
        n (r • z) =
      r • dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
        n z := by
  ext q
  change
    ((r : ℂ) * z ((finProdFinEquiv.symm q.1).1,
        (finProdFinEquiv.symm q.2).1)) *
      embezzlementState n
        ((finProdFinEquiv.symm q.1).2,
          (finProdFinEquiv.symm q.2).2) =
    (r : ℂ) *
      (z ((finProdFinEquiv.symm q.1).1,
          (finProdFinEquiv.symm q.2).1) *
        embezzlementState n
          ((finProdFinEquiv.symm q.1).2,
            (finProdFinEquiv.symm q.2).2))
  ring
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
    dSVDensityRationalMixedCanonicalPrefixPhysicalRawHarmonicTensor_eq
    {N : ℕ} (grid : 0 < N) (n : ℕ)
    (rank : Fin (N + 1)) :
    dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
        n (dSVCanonicalFailurePrefix rank) =
      Real.sqrt (rank.val : ℝ) •
        tensorEmbezzlementTarget (n := n)
          (dSVCanonicalFailureUnitRankFamily N grid rank) := by
  classical
  have raw : dSVCanonicalFailurePrefix rank =
      Real.sqrt (rank.val : ℝ) •
        (dSVCanonicalFailureUnitRankFamily N grid rank :
          EuclideanSpace ℂ (Fin N × Fin N)) := by
    by_cases zero : rank.val = 0
    · rw [dSVCanonicalFailurePrefix_eq_zero_of_rank_zero
        rank zero]
      simp [zero]
    · have nonzero : dSVCanonicalFailurePrefix rank ≠ 0 := by
        intro vanished
        have mass := dSVCanonicalFailurePrefix_norm_sq rank
        rw [vanished] at mass
        have cast_zero : (rank.val : ℝ) = 0 := by
          simpa using mass.symm
        exact zero (by exact_mod_cast cast_zero)
      change dSVCanonicalFailurePrefix rank =
        Real.sqrt (rank.val : ℝ) •
          normalizeOrDefault
            (embezzlementState N)
            (dSVCanonicalFailurePrefix rank)
      rw [normalizeOrDefault, if_neg nonzero,
        ← dSVCanonicalFailurePrefix_norm_eq_sqrt rank]
      exact (NormedSpace.norm_smul_normalize
        (dSVCanonicalFailurePrefix rank)).symm
  rw [raw,
    dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor_real_smul,
    dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor_unit]
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
    dSVDensityRationalMixedCanonicalPrefixPhysicalRankWeightedAtomError_eq
    {N n : ℕ} (grid : 0 < N)
    (rank : Fin (N + 1))
    (A B : Matrix.unitaryGroup (Fin (N * n)) ℂ) :
    ‖localUnitaryAction A B
          (dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
            n (dSVCanonicalFailurePrefix rank)) -
        Real.sqrt (rank.val : ℝ) •
          embezzlementState (N * n)‖ ^ 2 =
      (rank.val : ℝ) *
        ‖localUnitaryAction A B
            (tensorEmbezzlementTarget (n := n)
              (dSVCanonicalFailureUnitRankFamily
                N grid rank)) -
          embezzlementState (N * n)‖ ^ 2 := by
  rw [dSVDensityRationalMixedCanonicalPrefixPhysicalRawHarmonicTensor_eq
    grid n rank]
  rw [dSVDensityRationalMixedCanonicalPrefixPhysicalLocalAction_real_smul]
  rw [← smul_sub, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (by positivity : 0 ≤ (rank.val : ℝ))]
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
    exists_proofDSVDensityRationalPublicBucketPhysicalRawRankCleanup_sq
    {Ω I : Type*} [DecidableEq I] {N : ℕ} (grid : 0 < N)
    (bucket : Ω → Fin (N + 1) → I)
    (representative : Ω → I → Fin (N + 1))
    (ε : ℝ) (precision : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧
      ∃ A B : Ω → I → Matrix.unitaryGroup (Fin (N * n)) ℂ,
        ∀ (phase : Ω) (r s : Fin (N + 1)),
          ‖localUnitaryAction
              (A phase (bucket phase r))
              (B phase (bucket phase s))
              (dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
                n (dSVCanonicalFailurePrefix r)) -
            Real.sqrt (r.val : ℝ) •
              embezzlementState (N * n)‖ ^ 2 ≤
            (r.val : ℝ) *
              (2 * ε ^ 2 +
                8 * |(r.val : ℝ) -
                  ((representative phase (bucket phase r)).val : ℝ)| /
                  (max 1
                    (min r.val
                      (representative phase (bucket phase r)).val) : ℕ) +
                4 * (if bucket phase r = bucket phase s
                  then (0 : ℝ) else 1)) := by
  obtain ⟨n, positive, A, B, accurate⟩ :=
    dSVDensityRationalPublicBucketCanonicalPrefixCleanup_sq
      grid bucket representative ε precision
  refine ⟨n, positive, A, B, ?_⟩
  intro phase r s
  rw [dSVDensityRationalMixedCanonicalPrefixPhysicalRankWeightedAtomError_eq
    grid r]
  exact mul_le_mul_of_nonneg_left
    (accurate phase r s) (Nat.cast_nonneg r.val)
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
    {Ω I : Type*} [DecidableEq I] {N : ℕ} (grid : 0 < N)
    (bucket : Ω → Fin (N + 1) → I)
    (representative : Ω → I → Fin (N + 1))
    (ε : ℝ) (precision : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧
      ∃ A B : Ω → I → Matrix.unitaryGroup (Fin (N * n)) ℂ,
        ∀ (phase : Ω) (r s : Fin (N + 1)),
          ‖localUnitaryAction
              (A phase (bucket phase r))
              (B phase (bucket phase s))
              (dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
                n (dSVCanonicalFailurePrefix
                  (dSVDensityRationalPublicBucketPhysicalCommonRank
                    r s))) -
            Real.sqrt (r.val : ℝ) •
              embezzlementState (N * n)‖ ^ 2 ≤
            2 * |(r.val : ℝ) - (s.val : ℝ)| +
              2 * (r.val : ℝ) *
                (2 * ε ^ 2 +
                  8 * |(r.val : ℝ) -
                    ((representative phase (bucket phase r)).val : ℝ)| /
                    (max 1
                      (min r.val
                        (representative phase (bucket phase r)).val) : ℕ) +
                  4 * (if bucket phase r = bucket phase s
                    then (0 : ℝ) else 1)) := by
  obtain ⟨n, positive, A, B, accurate⟩ :=
    exists_proofDSVDensityRationalPublicBucketPhysicalRawRankCleanup_sq
      grid bucket representative ε precision
  refine ⟨n, positive, A, B, ?_⟩
  intro phase r s
  let U := A phase (bucket phase r)
  let V := B phase (bucket phase s)
  let common := dSVDensityRationalPublicBucketPhysicalCommonRank r s
  let mixed :=
    dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
      n (dSVCanonicalFailurePrefix common)
  let alice :=
    dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
      n (dSVCanonicalFailurePrefix r)
  let target := Real.sqrt (r.val : ℝ) •
    embezzlementState (N * n)
  have pure_distance :
      ‖localUnitaryAction U V mixed -
        localUnitaryAction U V alice‖ ^ 2 ≤
          |(r.val : ℝ) - (s.val : ℝ)| := by
    rw [← localUnitaryAction_sub,
      localUnitaryAction_norm]
    dsimp [mixed, alice]
    rw [dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor_prefix_sub_norm_sq
      positive]
    dsimp [common,
      dSVDensityRationalPublicBucketPhysicalCommonRank]
    rcases le_total r.val s.val with ordered | ordered
    · rw [min_eq_left ordered]
      simp
    · rw [min_eq_right ordered]
      rw [abs_sub_comm]
  have cleanup := accurate phase r s
  change
    ‖localUnitaryAction U V mixed - target‖ ^ 2 ≤ _
  have triangle :
      ‖localUnitaryAction U V mixed - target‖ ≤
        ‖localUnitaryAction U V mixed -
          localUnitaryAction U V alice‖ +
        ‖localUnitaryAction U V alice - target‖ := by
    calc
      _ = ‖(localUnitaryAction U V mixed -
          localUnitaryAction U V alice) +
          (localUnitaryAction U V alice - target)‖ := by
            congr 1
            abel
      _ ≤ _ := norm_add_le _ _
  change
    ‖localUnitaryAction U V alice - target‖ ^ 2 ≤ _
    at cleanup
  nlinarith [
    norm_nonneg (localUnitaryAction U V mixed - target),
    norm_nonneg (localUnitaryAction U V mixed -
      localUnitaryAction U V alice),
    norm_nonneg (localUnitaryAction U V alice - target),
    sq_nonneg
      (‖localUnitaryAction U V mixed -
          localUnitaryAction U V alice‖ -
        ‖localUnitaryAction U V alice - target‖)]
end QuantumParallelRepetition

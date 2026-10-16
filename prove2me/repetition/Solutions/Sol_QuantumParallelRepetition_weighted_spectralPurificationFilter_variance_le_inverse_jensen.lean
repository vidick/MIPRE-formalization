/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Repetition/TenProofs/QuantumParallelRepetition/Part01.lean (solution of QuantumParallelRepetition.weighted_spectralPurificationFilter_variance_le_inverse_jensen);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharZero.Defs
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
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Basic
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Opposites
import Mathlib.Algebra.Order.Archimedean.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
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
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
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
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.StarOrder
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
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Analysis.Normed.Operator.Basic
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
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Holder
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finite.Sigma
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
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
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
import Mathlib.Data.Nat.Init
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
import Mathlib.Data.Set.Operations
import Mathlib.Data.Set.Restrict
import Mathlib.Data.SetLike.Basic
import Mathlib.Data.Sigma.Basic
import Mathlib.Data.Subtype
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.GroupAction.Ring
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
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Embedding.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Function.Defs
import Mathlib.Logic.IsEmpty.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
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
import Mathlib.Order.Max
import Mathlib.Order.MinMax
import Mathlib.Order.Monotone.Defs
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
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
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
import Mathlib.Topology.Constructions
import Mathlib.Topology.Continuous
import Mathlib.Topology.ContinuousMap.ContinuousSqrt
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
import Theorems.Thm_QuantumParallelRepetition_spectralPurificationFilter_mul_shift
import Theorems.Thm_QuantumParallelRepetition_spectralPurificationFilter_square_contraction

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
attribute [instance] QuantumParallelRepetition.Strategy.alice_fintype QuantumParallelRepetition.Strategy.bob_fintype QuantumParallelRepetition.Strategy.alice_decidableEq QuantumParallelRepetition.Strategy.bob_decidableEq

namespace QuantumParallelRepetition
section
open scoped BigOperators
set_option autoImplicit true
theorem noncommutative_resolvent_identity
    {R : Type*} [Ring R]
    (F M S RF RM : R)
    (hF : RF * (F + S) = 1)
    (hM : (M + S) * RM = 1) :
    RF - RM = RF * (M - F) * RM := by
  calc
    RF - RM = RF * ((M + S) * RM) - (RF * (F + S)) * RM := by
      rw [hM, hF]
      simp
    _ = RF * (M - F) * RM := by
      noncomm_ring
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped BigOperators
set_option autoImplicit true
theorem noncommutative_filtered_resolvent_identity
    {R : Type*} [Ring R]
    (F M S RF RM : R)
    (hF_left : (F + S) * RF = 1)
    (hF_right : RF * (F + S) = 1)
    (hM_left : (M + S) * RM = 1) :
    F * RF - M * RM = S * (RF * (F - M) * RM) := by
  have hFR : F * RF = 1 - S * RF := by
    have h : F * RF + S * RF = 1 := by
      simpa [add_mul] using hF_left
    exact eq_sub_of_add_eq h
  have hMR : M * RM = 1 - S * RM := by
    have h : M * RM + S * RM = 1 := by
      simpa [add_mul] using hM_left
    exact eq_sub_of_add_eq h
  have hdiff : RM - RF = RF * (F - M) * RM := by
    calc
      RM - RF = -(RF - RM) := by noncomm_ring
      _ = -(RF * (M - F) * RM) := by
        rw [noncommutative_resolvent_identity F M S RF RM hF_right hM_left]
      _ = RF * (F - M) * RM := by noncomm_ring
  rw [hFR, hMR]
  calc
    (1 - S * RF) - (1 - S * RM) = S * (RM - RF) := by
      noncomm_ring
    _ = S * (RF * (F - M) * RM) := by rw [hdiff]
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped BigOperators
set_option autoImplicit true
theorem noncommutative_resolvent_second_order
    {R : Type*} [Ring R]
    (F M S RF RM : R)
    (hF_left : (F + S) * RF = 1)
    (hF_right : RF * (F + S) = 1)
    (hM_left : (M + S) * RM = 1)
    (hM_right : RM * (M + S) = 1) :
    RF = RM - RM * (F - M) * RM +
      RM * (F - M) * RF * (F - M) * RM := by
  have hleft : RM - RF = RM * (F - M) * RF :=
    noncommutative_resolvent_identity M F S RM RF hM_right hF_left
  have hright : RF - RM = RF * (M - F) * RM :=
    noncommutative_resolvent_identity F M S RF RM hF_right hM_left
  have hfirst : RF = RM - RM * (F - M) * RF := by
    calc
      RF = RM - (RM - RF) := by noncomm_ring
      _ = RM - RM * (F - M) * RF := by rw [hleft]
  have hsecond : RF = RM - RF * (F - M) * RM := by
    calc
      RF = RM + (RF - RM) := by noncomm_ring
      _ = RM + RF * (M - F) * RM := by rw [hright]
      _ = RM - RF * (F - M) * RM := by noncomm_ring
  calc
    RF = RM - RM * (F - M) * RF := hfirst
    _ = RM - RM * (F - M) *
      (RM - RF * (F - M) * RM) := by rw [← hsecond]
    _ = RM - RM * (F - M) * RM +
      RM * (F - M) * RF * (F - M) * RM := by noncomm_ring
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped BigOperators
set_option autoImplicit true
theorem noncommutative_weighted_resolvent_second_order
    {ι R : Type*} [Fintype ι] [Ring R]
    (weight : ι → R) (F : ι → R) (M S : R)
    (RF : ι → R) (RM : R)
    (normalized : (∑ i : ι, weight i) = 1)
    (centered : (∑ i : ι, weight i * (F i - M)) = 0)
    (commute_mean : ∀ i, weight i * RM = RM * weight i)
    (hF_left : ∀ i, (F i + S) * RF i = 1)
    (hF_right : ∀ i, RF i * (F i + S) = 1)
    (hM_left : (M + S) * RM = 1)
    (hM_right : RM * (M + S) = 1) :
    (∑ i : ι, weight i * RF i) - RM =
      RM * (∑ i : ι,
        weight i * ((F i - M) * RF i * (F i - M))) * RM := by
  have hterm (i : ι) :
      weight i * RF i =
        weight i * RM - RM * (weight i * (F i - M)) * RM +
          RM * (weight i * ((F i - M) * RF i * (F i - M))) * RM := by
    nth_rewrite 1 [noncommutative_resolvent_second_order
      (F i) M S (RF i) RM (hF_left i) (hF_right i) hM_left hM_right]
    have hw := commute_mean i
    calc
      weight i *
        (RM - RM * (F i - M) * RM +
          RM * (F i - M) * RF i * (F i - M) * RM) =
        weight i * RM -
          (weight i * RM) * (F i - M) * RM +
          (weight i * RM) * ((F i - M) * RF i * (F i - M)) * RM := by
            noncomm_ring
      _ = weight i * RM -
          (RM * weight i) * (F i - M) * RM +
          (RM * weight i) * ((F i - M) * RF i * (F i - M)) * RM := by
            rw [hw]
      _ = weight i * RM - RM * (weight i * (F i - M)) * RM +
          RM * (weight i * ((F i - M) * RF i * (F i - M))) * RM := by
            noncomm_ring
  calc
    (∑ i : ι, weight i * RF i) - RM =
        (∑ i : ι,
          (weight i * RM - RM * (weight i * (F i - M)) * RM +
            RM * (weight i * ((F i - M) * RF i * (F i - M))) * RM)) - RM := by
              congr 1
              exact Finset.sum_congr rfl (fun i _ => hterm i)
    _ = (∑ i : ι, weight i) * RM -
          RM * (∑ i : ι, weight i * (F i - M)) * RM +
          RM * (∑ i : ι,
            weight i * ((F i - M) * RF i * (F i - M))) * RM - RM := by
              simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
                ← Finset.sum_mul, ← Finset.mul_sum]
    _ = RM * (∑ i : ι,
          weight i * ((F i - M) * RF i * (F i - M))) * RM := by
            rw [normalized, centered]
            noncomm_ring
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped BigOperators ComplexOrder MatrixOrder
set_option autoImplicit true
theorem posSemidef_hermitian_sandwich
    {d : Type*} [Fintype d] [DecidableEq d]
    {A D : Matrix d d ℂ}
    (hA : A.PosSemidef) (hD : D.IsHermitian) :
    (D * A * D).PosSemidef := by
  simpa [hD.eq] using hA.mul_mul_conjTranspose_same D
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped BigOperators ComplexOrder MatrixOrder
set_option autoImplicit true
theorem shifted_posSemidef_matrix_posDef
    {d : Type*} [Fintype d] [DecidableEq d]
    {F : Matrix d d ℂ} (hF : F.PosSemidef)
    {s : ℝ} (hs : 0 < s) :
    (F + s • (1 : Matrix d d ℂ)).PosDef := by
  have hshift : (s • (1 : Matrix d d ℂ)).PosDef :=
    Matrix.PosDef.one.smul hs
  exact Matrix.PosDef.posSemidef_add hF hshift
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped BigOperators ComplexOrder MatrixOrder
set_option autoImplicit true
theorem shifted_posSemidef_matrix_inverse_posSemidef
    {d : Type*} [Fintype d] [DecidableEq d]
    {F : Matrix d d ℂ} (hF : F.PosSemidef)
    {s : ℝ} (hs : 0 < s) :
    ((F + s • (1 : Matrix d d ℂ))⁻¹).PosSemidef :=
  (shifted_posSemidef_matrix_posDef hF hs).posSemidef.inv
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped BigOperators ComplexOrder MatrixOrder
set_option autoImplicit true
theorem matrix_weighted_centered
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (weight : ι → ℝ) (F : ι → Matrix d d ℂ)
    (M : Matrix d d ℂ)
    (normalized : (∑ i : ι, weight i) = 1)
    (mean : (∑ i : ι, weight i • F i) = M) :
    (∑ i : ι, weight i • (F i - M)) = 0 := by
  simp_rw [smul_sub]
  rw [Finset.sum_sub_distrib, mean, ← Finset.sum_smul, normalized]
  simp
end
end QuantumParallelRepetition

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace QuantumParallelRepetition
section
open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
theorem spectralPurificationFilter_eq_resolvent
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    {s : ℝ} (hs : 0 < s) :
    spectralPurificationFilter F hF s =
      F * (F + s • (1 : Matrix d d ℂ))⁻¹ := by
  have hdet : IsUnit (F + s • (1 : Matrix d d ℂ)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp
      (shifted_posSemidef_matrix_posDef hF hs).isUnit
  calc
    spectralPurificationFilter F hF s =
        spectralPurificationFilter F hF s *
          ((F + s • (1 : Matrix d d ℂ)) *
            (F + s • (1 : Matrix d d ℂ))⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ hdet, mul_one]
    _ = (spectralPurificationFilter F hF s *
          (F + s • (1 : Matrix d d ℂ))) *
          (F + s • (1 : Matrix d d ℂ))⁻¹ := by
          rw [mul_assoc]
    _ = F * (F + s • (1 : Matrix d d ℂ))⁻¹ := by
          rw [spectralPurificationFilter_mul_shift F hF hs]
end
end QuantumParallelRepetition

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace QuantumParallelRepetition
section
open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
theorem spectralPurificationFilter_eq_one_sub_shifted_inverse
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    {s : ℝ} (hs : 0 < s) :
    spectralPurificationFilter F hF s =
      1 - s • (F + s • (1 : Matrix d d ℂ))⁻¹ := by
  have hdet : IsUnit (F + s • (1 : Matrix d d ℂ)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp
      (shifted_posSemidef_matrix_posDef hF hs).isUnit
  rw [spectralPurificationFilter_eq_resolvent F hF hs]
  apply eq_sub_of_add_eq
  simpa [add_mul, smul_mul_assoc] using
    Matrix.mul_nonsing_inv
      (F + s • (1 : Matrix d d ℂ)) hdet
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
theorem shifted_inverse_square_contraction
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    {s : ℝ} (hs : 0 < s) :
    (s • (F + s • (1 : Matrix d d ℂ))⁻¹ -
      s ^ 2 •
        ((F + s • (1 : Matrix d d ℂ))⁻¹ *
          (F + s • (1 : Matrix d d ℂ))⁻¹)).PosSemidef := by
  let R : Matrix d d ℂ := (F + s • (1 : Matrix d d ℂ))⁻¹
  have hstar : star R = R := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (shifted_posSemidef_matrix_inverse_posSemidef hF hs).isHermitian.eq
  have h := spectralPurificationFilter_square_contraction F hF hs
  rw [spectralPurificationFilter_eq_one_sub_shifted_inverse F hF hs] at h
  change (s • R - s ^ 2 • (R * R)).PosSemidef
  change ((1 - s • R) - star (1 - s • R) *
    (1 - s • R)).PosSemidef at h
  convert h using 1
  simp only [star_sub, star_one, star_smul, star_trivial, hstar,
    sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc,
    mul_smul_comm, pow_two]
  module
end
end QuantumParallelRepetition

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace QuantumParallelRepetition
section
open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
theorem spectralPurificationFilter_sub_resolvent
    {d : Type*} [Fintype d] [DecidableEq d]
    (F M : Matrix d d ℂ)
    (hF : F.PosSemidef) (hM : M.PosSemidef)
    {s : ℝ} (hs : 0 < s) :
    spectralPurificationFilter F hF s -
        spectralPurificationFilter M hM s =
      s • ((F + s • (1 : Matrix d d ℂ))⁻¹ *
        (F - M) * (M + s • (1 : Matrix d d ℂ))⁻¹) := by
  have hdetF : IsUnit (F + s • (1 : Matrix d d ℂ)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp
      (shifted_posSemidef_matrix_posDef hF hs).isUnit
  have hdetM : IsUnit (M + s • (1 : Matrix d d ℂ)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp
      (shifted_posSemidef_matrix_posDef hM hs).isUnit
  rw [spectralPurificationFilter_eq_resolvent F hF hs,
    spectralPurificationFilter_eq_resolvent M hM hs]
  simpa [smul_mul_assoc] using
    noncommutative_filtered_resolvent_identity
      F M (s • (1 : Matrix d d ℂ))
      (F + s • (1 : Matrix d d ℂ))⁻¹
      (M + s • (1 : Matrix d d ℂ))⁻¹
      (Matrix.mul_nonsing_inv _ hdetF)
      (Matrix.nonsing_inv_mul _ hdetF)
      (Matrix.mul_nonsing_inv _ hdetM)
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
theorem spectralPurificationFilter_sub_gram
    {d : Type*} [Fintype d] [DecidableEq d]
    (F M : Matrix d d ℂ)
    (hF : F.PosSemidef) (hM : M.PosSemidef)
    {s : ℝ} (hs : 0 < s) :
    star (spectralPurificationFilter F hF s -
        spectralPurificationFilter M hM s) *
      (spectralPurificationFilter F hF s -
        spectralPurificationFilter M hM s) =
      s ^ 2 •
        ((M + s • (1 : Matrix d d ℂ))⁻¹ * (F - M) *
          ((F + s • (1 : Matrix d d ℂ))⁻¹ *
            (F + s • (1 : Matrix d d ℂ))⁻¹) *
          (F - M) * (M + s • (1 : Matrix d d ℂ))⁻¹) := by
  let RF : Matrix d d ℂ := (F + s • (1 : Matrix d d ℂ))⁻¹
  let RM : Matrix d d ℂ := (M + s • (1 : Matrix d d ℂ))⁻¹
  let D : Matrix d d ℂ := F - M
  have hRF : star RF = RF := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (shifted_posSemidef_matrix_inverse_posSemidef hF hs).isHermitian.eq
  have hRM : star RM = RM := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (shifted_posSemidef_matrix_inverse_posSemidef hM hs).isHermitian.eq
  have hD : star D = D := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (hF.isHermitian.sub hM.isHermitian).eq
  rw [spectralPurificationFilter_sub_resolvent F M hF hM hs]
  change star (s • (RF * D * RM)) * (s • (RF * D * RM)) =
    s ^ 2 • (RM * D * (RF * RF) * D * RM)
  simp only [star_smul, star_trivial, star_mul, hRF, hRM, hD,
    smul_mul_assoc, mul_smul_comm, smul_smul, pow_two]
  congr 1
  noncomm_ring
end
end QuantumParallelRepetition

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace QuantumParallelRepetition
section
open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
theorem weighted_shifted_inverse_second_order
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (weight : ι → ℝ) (F : ι → Matrix d d ℂ)
    (M : Matrix d d ℂ)
    (normalized : (∑ i : ι, weight i) = 1)
    (mean : (∑ i : ι, weight i • F i) = M)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef)
    {s : ℝ} (hs : 0 < s) :
    (∑ i : ι, weight i •
      (F i + s • (1 : Matrix d d ℂ))⁻¹) -
        (M + s • (1 : Matrix d d ℂ))⁻¹ =
      (M + s • (1 : Matrix d d ℂ))⁻¹ *
        (∑ i : ι, weight i •
          ((F i - M) * (F i + s • (1 : Matrix d d ℂ))⁻¹ *
            (F i - M))) *
        (M + s • (1 : Matrix d d ℂ))⁻¹ := by
  let W : ι → Matrix d d ℂ := fun i =>
    weight i • (1 : Matrix d d ℂ)
  let RF : ι → Matrix d d ℂ := fun i =>
    (F i + s • (1 : Matrix d d ℂ))⁻¹
  let RM : Matrix d d ℂ :=
    (M + s • (1 : Matrix d d ℂ))⁻¹
  have hW_normalized : (∑ i : ι, W i) = 1 := by
    dsimp [W]
    rw [← Finset.sum_smul, normalized]
    simp
  have hW_centered : (∑ i : ι, W i * (F i - M)) = 0 := by
    dsimp [W]
    simp_rw [smul_mul_assoc, one_mul]
    exact matrix_weighted_centered weight F M normalized mean
  have hW_commutes (i : ι) : W i * RM = RM * W i := by
    dsimp [W]
    rw [smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
  have hdetF (i : ι) :
      IsUnit (F i + s • (1 : Matrix d d ℂ)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp
      (shifted_posSemidef_matrix_posDef (positive i) hs).isUnit
  have hdetM : IsUnit (M + s • (1 : Matrix d d ℂ)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp
      (shifted_posSemidef_matrix_posDef hM hs).isUnit
  have hidentity := noncommutative_weighted_resolvent_second_order
    W F M (s • (1 : Matrix d d ℂ)) RF RM
    hW_normalized hW_centered hW_commutes
    (fun i => Matrix.mul_nonsing_inv _ (hdetF i))
    (fun i => Matrix.nonsing_inv_mul _ (hdetF i))
    (Matrix.mul_nonsing_inv _ hdetM)
    (Matrix.nonsing_inv_mul _ hdetM)
  simpa [W, RF, RM, smul_mul_assoc] using hidentity
end
end QuantumParallelRepetition

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace QuantumParallelRepetition
open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
theorem _root_.solution
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (weight : ι → ℝ) (F : ι → Matrix d d ℂ)
    (M : Matrix d d ℂ)
    (nonnegative : ∀ i, 0 ≤ weight i)
    (normalized : (∑ i : ι, weight i) = 1)
    (mean : (∑ i : ι, weight i • F i) = M)
    (positive : ∀ i, (F i).PosSemidef)
    {s : ℝ} (hs : 0 < s) :
    let hM : M.PosSemidef := by
      rw [← mean]
      exact weighted_positive_matrix_mean weight F nonnegative positive
    (s •
      ((∑ i : ι, weight i •
        (F i + s • (1 : Matrix d d ℂ))⁻¹) -
        (M + s • (1 : Matrix d d ℂ))⁻¹) -
      ∑ i : ι, weight i •
        (star (spectralPurificationFilter (F i) (positive i) s -
            spectralPurificationFilter M hM s) *
          (spectralPurificationFilter (F i) (positive i) s -
            spectralPurificationFilter M hM s))).PosSemidef := by
  dsimp
  let hM : M.PosSemidef := by
    rw [← mean]
    exact weighted_positive_matrix_mean weight F nonnegative positive
  let RF : ι → Matrix d d ℂ := fun i =>
    (F i + s • (1 : Matrix d d ℂ))⁻¹
  let RM : Matrix d d ℂ :=
    (M + s • (1 : Matrix d d ℂ))⁻¹
  let D : ι → Matrix d d ℂ := fun i => F i - M
  let K : ι → Matrix d d ℂ := fun i =>
    s • RF i - s ^ 2 • (RF i * RF i)
  have hK (i : ι) : (K i).PosSemidef :=
    shifted_inverse_square_contraction (F i) (positive i) hs
  have hD (i : ι) : (D i).IsHermitian :=
    (positive i).isHermitian.sub hM.isHermitian
  have hinner :
      (∑ i : ι, weight i • (D i * K i * D i)).PosSemidef := by
    apply Matrix.posSemidef_sum
    intro i _
    exact (posSemidef_hermitian_sandwich (hK i) (hD i)).smul
      (nonnegative i)
  have hRM : RM.IsHermitian :=
    (shifted_posSemidef_matrix_inverse_posSemidef hM hs).isHermitian
  have houter :
      (RM * (∑ i : ι, weight i • (D i * K i * D i)) * RM).PosSemidef :=
    posSemidef_hermitian_sandwich hinner hRM
  have hsecond :
      (∑ i : ι, weight i • RF i) - RM =
        RM * (∑ i : ι, weight i • (D i * RF i * D i)) * RM :=
    weighted_shifted_inverse_second_order
      weight F M normalized mean positive hM hs
  have hgram (i : ι) :
      star (spectralPurificationFilter (F i) (positive i) s -
          spectralPurificationFilter M hM s) *
        (spectralPurificationFilter (F i) (positive i) s -
          spectralPurificationFilter M hM s) =
        s ^ 2 • (RM * D i * (RF i * RF i) * D i * RM) :=
    spectralPurificationFilter_sub_gram
      (F i) M (positive i) hM hs
  change
    (s • ((∑ i : ι, weight i • RF i) - RM) -
      ∑ i : ι, weight i •
        (star (spectralPurificationFilter (F i) (positive i) s -
            spectralPurificationFilter M hM s) *
          (spectralPurificationFilter (F i) (positive i) s -
            spectralPurificationFilter M hM s))).PosSemidef
  rw [hsecond]
  simp_rw [hgram]
  convert houter using 1
  simp only [Finset.mul_sum, Finset.sum_mul, Finset.smul_sum,
    mul_smul_comm, smul_mul_assoc,
    smul_smul, mul_sub, sub_mul, K]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_sub, smul_smul, smul_smul, mul_comm s (weight i)]
  simp only [mul_assoc]
end QuantumParallelRepetition

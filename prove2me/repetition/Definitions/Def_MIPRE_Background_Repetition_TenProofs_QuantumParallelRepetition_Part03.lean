/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Repetition/TenProofs/QuantumParallelRepetition/Part03.lean (definition bundle: declarations the uploaded statements rest on);
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
import Theorems.Thm_QuantumParallelRepetition_Game_conditionalXGivenY_nonneg
import Theorems.Thm_QuantumParallelRepetition_Game_conditionalYGivenX_nonneg
import Theorems.Thm_QuantumParallelRepetition_conditionedAliceEffect_positive
import Theorems.Thm_QuantumParallelRepetition_conditionedBobEffect_positive
import Theorems.Thm_QuantumParallelRepetition_finitePurificationMatrix_gram

set_option autoImplicit true

namespace QuantumParallelRepetition

open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset

noncomputable section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder

attribute [local instance] Classical.propDecidable

def dSVDensityRationalHeterogeneousActualAcceptSet
    {β : Type*} {L : ℕ}
    (accepted : Fin L → β → Prop)
    (history : Fin (L + 1) → β) : Finset (Fin L) := by
  classical
  exact Finset.univ.filter fun j : Fin L =>
    accepted j (history j.castSucc)

def dSVDensityRationalHeterogeneousActualFirstAccepted
    {β : Type*} {L : ℕ}
    (accepted : Fin L → β → Prop)
    (history : Fin (L + 1) → β) : Fin (L + 1) := by
  classical
  let hits := dSVDensityRationalHeterogeneousActualAcceptSet
    accepted history
  exact if nonempty : hits.Nonempty then
    (hits.min' nonempty).succ
  else 0

def dSVDensityRationalHeterogeneousActualFirstAcceptEquiv
    {β : Type*} {L : ℕ}
    (accepted : Fin L → β → Prop) :
    Equiv.Perm (Σ _ : Fin (L + 1), Fin (L + 1) → β) where
  toFun q :=
    ⟨(Equiv.swap (0 : Fin (L + 1))
      (dSVDensityRationalHeterogeneousActualFirstAccepted
        accepted q.2)) q.1, q.2⟩
  invFun q :=
    ⟨(Equiv.swap (0 : Fin (L + 1))
      (dSVDensityRationalHeterogeneousActualFirstAccepted
        accepted q.2)) q.1, q.2⟩
  left_inv := by
    rintro ⟨flag, history⟩
    simp
  right_inv := by
    rintro ⟨flag, history⟩
    simp

def dSVDensityRationalHeterogeneousActualFirstAcceptUnitary
    {β : Type*} [Fintype β] [DecidableEq β]
    {L : ℕ} (accepted : Fin L → β → Prop) :
    Matrix.unitaryGroup (Σ _ : Fin (L + 1), Fin (L + 1) → β) ℂ :=
  permutationUnitary
    (dSVDensityRationalHeterogeneousActualFirstAcceptEquiv
      accepted)

def dSVDensityRationalHeterogeneousActualCopyAccepted
    {S N d L : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ : BipartiteUnitVector d)
    (j : Fin L)
    (atom : DSVUniformDensityThresholdLocalIndex N d) : Prop :=
  dSVDensityRationalCompletePhysicalStoppingCopyAccepted
    (width (schedule j)) ξ atom

def dSVDensityRationalHeterogeneousActualCopyCondition
    {β : Type*} {L : ℕ}
    (accepted : Fin L → β → Prop)
    (flag : Fin (L + 1)) (i : Fin (L + 1)) (atom : β) : Prop :=
  if active : i.val < L then
    if flag = 0 then
      ¬ accepted ⟨i.val, active⟩ atom
    else if i.val + 1 < flag.val then
      ¬ accepted ⟨i.val, active⟩ atom
    else if i.val + 1 = flag.val then
      accepted ⟨i.val, active⟩ atom
    else True
  else True

def dSVDensityRationalHeterogeneousActualPhysicalLocalUnitary
    {β : Type*} [Fintype β] [DecidableEq β]
    {L : ℕ} (accepted : Fin L → β → Prop)
    (U : Matrix.unitaryGroup β ℂ) :
    Matrix.unitaryGroup (Σ _ : Fin (L + 1), Fin (L + 1) → β) ℂ :=
  (dSVDensityRationalFirstAcceptActualTensorBasis
      (L := L) U)⁻¹ *
    dSVDensityRationalHeterogeneousActualFirstAcceptUnitary
      accepted *
    dSVDensityRationalFirstAcceptActualTensorBasis
      (L := L) U

def dSVDensityRationalHeterogeneousActualAliceUnitary
    (N : ℕ) {S d L : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ : BipartiteUnitVector d) :
    Matrix.unitaryGroup
      (DSVUniformDensityThresholdWholeHistoryLocalIndex
        N d L) ℂ :=
  dSVDensityRationalHeterogeneousActualPhysicalLocalUnitary
    (dSVDensityRationalHeterogeneousActualCopyAccepted
      width schedule ξ)
    (dSVUniformDensityAliceHistorySpectralCopy (N := N) ξ)

def dSVDensityRationalHeterogeneousActualBobUnitary
    (N : ℕ) {S d L : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ζ : BipartiteUnitVector d) :
    Matrix.unitaryGroup
      (DSVUniformDensityThresholdWholeHistoryLocalIndex
        N d L) ℂ :=
  dSVDensityRationalHeterogeneousActualPhysicalLocalUnitary
    (dSVDensityRationalHeterogeneousActualCopyAccepted
      width schedule ζ)
    ((dSVUniformDensityBobHistoryCopyBasis (N := N) ζ)⁻¹)

def dSVDensityRationalHeterogeneousActualPhysicalState
    (N : ℕ) {S d L : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    EuclideanSpace ℂ
      (DSVUniformDensityThresholdWholeHistoryLocalIndex N d L ×
       DSVUniformDensityThresholdWholeHistoryLocalIndex N d L) :=
  toLp 2
    ((((dSVDensityRationalHeterogeneousActualAliceUnitary
          N width schedule ξ :
          Matrix (DSVUniformDensityThresholdWholeHistoryLocalIndex
            N d L)
            (DSVUniformDensityThresholdWholeHistoryLocalIndex
              N d L) ℂ) ⊗ₖ
        (dSVDensityRationalHeterogeneousActualBobUnitary
          N width schedule ζ :
          Matrix (DSVUniformDensityThresholdWholeHistoryLocalIndex
            N d L)
            (DSVUniformDensityThresholdWholeHistoryLocalIndex
              N d L) ℂ)).mulVec
      (ofLp
        (dSVUniformDensityThresholdWholeHistorySharedState
          N d L))))

end

noncomputable section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder

def dSVDensityRationalHeterogeneousPhysicalStageOutcome
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (k : ℕ) (alice bob : Bool) : ℝ :=
  if active : k < L then
    ‖dSVDensityRationalCompleteProjectiveOutcome
      (width (schedule ⟨k, active⟩)) N ξ ζ alice bob‖ ^ 2
  else if alice = false ∧ bob = false then 1 else 0

def dSVDensityRationalHeterogeneousPhysicalStageContinue
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (k : ℕ) : ℝ :=
  dSVDensityRationalHeterogeneousPhysicalStageOutcome
    N width schedule ξ ζ k false false

def dSVDensityRationalHeterogeneousPhysicalStageSuccess
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (k : ℕ) : ℝ :=
  dSVDensityRationalHeterogeneousPhysicalStageOutcome
    N width schedule ξ ζ k true true

def dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (k : ℕ) : ℝ :=
  dSVDensityRationalHeterogeneousPhysicalStageOutcome
      N width schedule ξ ζ k true false +
    dSVDensityRationalHeterogeneousPhysicalStageOutcome
      N width schedule ξ ζ k false true

def dSVDensityRationalHeterogeneousPhysicalSurvival
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (k : ℕ) : ℝ :=
  dSVHeterogeneousRealPrefix
    (dSVDensityRationalHeterogeneousPhysicalStageContinue
      N width schedule ξ ζ) k

def dSVDensityRationalHeterogeneousPhysicalStoppedSuccessMass
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) : ℝ :=
  ∑ k ∈ Finset.range L,
    dSVDensityRationalHeterogeneousPhysicalSurvival
        N width schedule ξ ζ k *
      dSVDensityRationalHeterogeneousPhysicalStageSuccess
        N width schedule ξ ζ k

def dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) : ℝ :=
  ∑ k ∈ Finset.range L,
    dSVDensityRationalHeterogeneousPhysicalSurvival
        N width schedule ξ ζ k *
      dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
        N width schedule ξ ζ k

def dSVDensityRationalHeterogeneousPhysicalTerminalMass
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) : ℝ :=
  dSVDensityRationalHeterogeneousPhysicalSurvival
    N width schedule ξ ζ L

def dSVDensityRationalHeterogeneousPhysicalStageHazardRatio
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (k : ℕ) : ℝ :=
  dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
      N width schedule ξ ζ k /
    (dSVDensityRationalHeterogeneousPhysicalStageSuccess
        N width schedule ξ ζ k +
      dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
        N width schedule ξ ζ k)

def dSVDensityRationalHeterogeneousPhysicalUniformEscapeRate
    (d : ℕ) (W : ℝ) : ℝ :=
  1 / (2 * (W + 1) * (d : ℝ))

end

noncomputable section

open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

def fairPartitionWeight (α : Type*) [Fintype α] : ℝ :=
  ((2 : ℝ) ^ Fintype.card α)⁻¹

def reversePartitionWeight (s : Finset α) : ℝ :=
  fairPartitionWeight α *
    (2 * (s.card : ℝ) / (Fintype.card α : ℝ))

def forwardMarkedPartitionWeight (α : Type*) [Fintype α] : ℝ :=
  2 * fairPartitionWeight α / (Fintype.card α : ℝ)

def reverseMarkedPartitionWeight (s : Finset α) (i : α) : ℝ :=
  if i ∈ s then reversePartitionWeight s / (s.card : ℝ) else 0

omit [DecidableEq α] in

@[simp] theorem reversePartitionWeight_empty :
    reversePartitionWeight (α := α) ∅ = 0 := by
  simp [reversePartitionWeight]

end

noncomputable section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def rightSpectralBornWeight
    {dA dB : Type*}
    [Fintype dA] [Fintype dB]
    [DecidableEq dA] [DecidableEq dB]
    (ρ : DensityMatrix (dA × dB))
    (F : Matrix dA dA ℂ)
    (G : Matrix dB dB ℂ) (hG : G.PosSemidef)
    (i : dB) : ℝ :=
  bornTracePairing ρ.matrix F
    (positiveMatrixSpectralAtom G hG i)

section HistoryNormalization

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def fullSubsetHistoryFieldEquiv
    {n : ℕ} (D L : Finset (Fin n)) :
    FullSubsetHistory X Y n D L ≃
      (({i : Fin n // i ∈ D} → X × Y) ×
       ({i : Fin n // i ∈ L} → X) ×
       ({i : Fin n // i ∈ fullHistoryRemaining n D L} → Y)) where
  toFun h :=
    (fun i => (h.aliceConditioned i, h.bobConditioned i),
      h.aliceRevealed, h.bobRemaining)
  invFun t :=
    ⟨fun i => (t.1 i).1,
      fun i => (t.1 i).2,
      t.2.1, t.2.2⟩
  left_inv h := by
    apply FullSubsetHistory.ext <;> rfl
  right_inv t := by
    rcases t with ⟨q, x, y⟩
    simp

end HistoryNormalization

end

noncomputable section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def fullHistoryAnswerCount
    {A B : Type*} [Fintype A] [Fintype B]
    {n : ℕ} (D : Finset (Fin n)) : ℝ :=
  (Fintype.card ({i : Fin n // i ∈ D} → A) : ℝ) *
    (Fintype.card ({i : Fin n // i ∈ D} → B) : ℝ)

abbrev FullHistoryEntropyAtom
    (X Y A B : Type*)
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (n : ℕ) (D L : Finset (Fin n)) :=
  FullSubsetHistory X Y n D L ×
    ({i : Fin n // i ∈ D} → A) ×
    ({i : Fin n // i ∈ D} → B)

def fullHistoryAtomCountingWeight
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n))
    (t : FullHistoryEntropyAtom X Y A B n D L) : ℝ :=
  fullHistoryWeight G t.1 *
    fullHistoryWinIndicator G t.1 t.2.1 t.2.2

def fullHistoryAtomBornMass
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D L : Finset (Fin n))
    (t : FullHistoryEntropyAtom X Y A B n D L) : ℝ :=
  bornTracePairing S.state.matrix
    (fullHistoryAliceFilter G n S D L t.1 t.2.1)
    (fullHistoryBobFilter G n S D L t.1 t.2.2)

end

noncomputable section

open scoped BigOperators

@[ext (iff := false)] structure FullCoordinateRevealHistory
    (X Y : Type*) [Fintype X] [Fintype Y]
    (n : ℕ) (D L : Finset (Fin n)) (i : Fin n) where
  aliceConditioned : {j : Fin n // j ∈ D} → X
  bobConditioned : {j : Fin n // j ∈ D} → Y
  aliceRevealed : {j : Fin n // j ∈ L} → X
  bobRemaining :
    {j : Fin n // j ∈ fullHistoryRemaining n D (insert i L)} → Y
  deriving Fintype

theorem fullHistoryRemaining_insert_subset
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n) :
    fullHistoryRemaining n D (insert i L) ⊆
      fullHistoryRemaining n D L := by
  intro j hj
  simp only [fullHistoryRemaining, Finset.mem_sdiff,
    Finset.mem_univ, true_and, Finset.mem_insert] at hj ⊢
  exact ⟨hj.1, fun h => hj.2 (Or.inr h)⟩

def fullCoordinateBaseOfOldHistory
    {X Y : Type*} [Fintype X] [Fintype Y]
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (h : FullSubsetHistory X Y n D L) :
    FullCoordinateRevealHistory X Y n D L i where
  aliceConditioned := h.aliceConditioned
  bobConditioned := h.bobConditioned
  aliceRevealed := h.aliceRevealed
  bobRemaining := fun j => h.bobRemaining
    ⟨j, fullHistoryRemaining_insert_subset D L i j.property⟩

def fullCoordinateOldHistory
    {X Y : Type*} [Fintype X] [Fintype Y]
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (h : FullCoordinateRevealHistory X Y n D L i)
    (y : Y) : FullSubsetHistory X Y n D L := by
  classical
  refine ⟨h.aliceConditioned, h.bobConditioned, h.aliceRevealed,
    fun j => if hj : (j : Fin n) = i then y else
      h.bobRemaining ⟨j, ?_⟩⟩
  have hjD : (j : Fin n) ∉ D :=
    (Finset.mem_sdiff.mp
      (Finset.mem_sdiff.mp j.property).1).2
  have hjL : (j : Fin n) ∉ L :=
    (Finset.mem_sdiff.mp j.property).2
  simp [fullHistoryRemaining, hjD, hjL, hj]

def fullCoordinateBaseOfNewHistory
    {X Y : Type*} [Fintype X] [Fintype Y]
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (h : FullSubsetHistory X Y n D (insert i L)) :
    FullCoordinateRevealHistory X Y n D L i where
  aliceConditioned := h.aliceConditioned
  bobConditioned := h.bobConditioned
  aliceRevealed := fun j => h.aliceRevealed
    ⟨j, Finset.mem_insert_of_mem j.property⟩
  bobRemaining := h.bobRemaining

def fullCoordinateNewHistory
    {X Y : Type*} [Fintype X] [Fintype Y]
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (h : FullCoordinateRevealHistory X Y n D L i)
    (x : X) : FullSubsetHistory X Y n D (insert i L) := by
  classical
  refine ⟨h.aliceConditioned, h.bobConditioned,
    fun j => if hj : (j : Fin n) = i then x else
      h.aliceRevealed ⟨j, ?_⟩,
    h.bobRemaining⟩
  exact (Finset.mem_insert.mp j.property).resolve_left hj

def fullCoordinateOldHistoryEquiv
    {X Y : Type*} [Fintype X] [Fintype Y]
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L) :
    FullSubsetHistory X Y n D L ≃
      FullCoordinateRevealHistory X Y n D L i × Y where
  toFun h :=
    (fullCoordinateBaseOfOldHistory D L i h,
      h.bobRemaining
        ⟨i, by simp [fullHistoryRemaining, hiD, hiL]⟩)
  invFun t := fullCoordinateOldHistory D L i t.1 t.2
  left_inv h := by
    apply FullSubsetHistory.ext
    · rfl
    · rfl
    · rfl
    · funext j
      by_cases hj : (j : Fin n) = i
      · subst i
        simp [fullCoordinateOldHistory,
          fullCoordinateBaseOfOldHistory]
      · simp [fullCoordinateOldHistory,
          fullCoordinateBaseOfOldHistory, hj]
  right_inv t := by
    rcases t with ⟨h, y⟩
    apply Prod.ext
    · apply FullCoordinateRevealHistory.ext
      · rfl
      · rfl
      · rfl
      · funext j
        have hj : (j : Fin n) ≠ i := by
          intro he
          have hnot : (j : Fin n) ∉ insert i L :=
            (Finset.mem_sdiff.mp j.property).2
          apply hnot
          simp [he]
        simp [fullCoordinateBaseOfOldHistory,
          fullCoordinateOldHistory, hj]
    · simp [fullCoordinateOldHistory]

def fullCoordinateNewHistoryEquiv
    {X Y : Type*} [Fintype X] [Fintype Y]
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (hiL : i ∉ L) :
    FullSubsetHistory X Y n D (insert i L) ≃
      FullCoordinateRevealHistory X Y n D L i × X where
  toFun h :=
    (fullCoordinateBaseOfNewHistory D L i h,
      h.aliceRevealed ⟨i, Finset.mem_insert_self i L⟩)
  invFun t := fullCoordinateNewHistory D L i t.1 t.2
  left_inv h := by
    apply FullSubsetHistory.ext
    · rfl
    · rfl
    · funext j
      by_cases hj : (j : Fin n) = i
      · have hjsub :
            j = (⟨i, Finset.mem_insert_self i L⟩ :
              {j : Fin n // j ∈ insert i L}) :=
          Subtype.ext hj
        subst j
        simp [fullCoordinateNewHistory,
          fullCoordinateBaseOfNewHistory]
      · simp [fullCoordinateNewHistory,
          fullCoordinateBaseOfNewHistory, hj]
    · rfl
  right_inv t := by
    rcases t with ⟨h, x⟩
    apply Prod.ext
    · apply FullCoordinateRevealHistory.ext
      · rfl
      · rfl
      · funext j
        have hj : (j : Fin n) ≠ i := by
          intro he
          exact hiL (he ▸ j.property)
        simp [fullCoordinateBaseOfNewHistory,
          fullCoordinateNewHistory, hj]
      · rfl
    · simp [fullCoordinateNewHistory]

end

noncomputable section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def fullHistoryRemainingCoordinateEquiv
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L) :
    {j : Fin n // j ∈ fullHistoryRemaining n D L} ≃
      Option {j : Fin n //
        j ∈ fullHistoryRemaining n D (insert i L)} where
  toFun j :=
    if hj : (j : Fin n) = i then none
    else some ⟨j, by
      have hjD : (j : Fin n) ∉ D :=
        (Finset.mem_sdiff.mp
          (Finset.mem_sdiff.mp j.property).1).2
      have hjL : (j : Fin n) ∉ L :=
        (Finset.mem_sdiff.mp j.property).2
      simp [fullHistoryRemaining, hjD, hjL, hj]⟩
  invFun
    | none => ⟨i, by simp [fullHistoryRemaining, hiD, hiL]⟩
    | some j =>
      ⟨j, fullHistoryRemaining_insert_subset D L i j.property⟩
  left_inv j := by
    apply Subtype.ext
    by_cases hj : (j : Fin n) = i
    · simp [hj]
    · simp [hj]
  right_inv j := by
    cases j with
    | none => simp
    | some j =>
      have hj : (j : Fin n) ≠ i := by
        intro he
        have hnot : (j : Fin n) ∉ insert i L :=
          (Finset.mem_sdiff.mp j.property).2
        apply hnot
        simp [he]
      simp [hj]

section CoordinateWeights

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def fullCoordinateBaseWeight
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n)
    (h : FullCoordinateRevealHistory X Y n D L i) : ℝ :=
  (∏ j : {j : Fin n // j ∈ D},
    G.questionWeight (h.aliceConditioned j) (h.bobConditioned j)) *
  (∏ j : {j : Fin n // j ∈ L},
    G.marginalX (h.aliceRevealed j)) *
  (∏ j : {j : Fin n //
      j ∈ fullHistoryRemaining n D (insert i L)},
    G.marginalY (h.bobRemaining j))

end CoordinateWeights

end

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder
  Matrix.Norms.Elementwise InnerProductSpace

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end

noncomputable section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

end

noncomputable section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def fullCoordinateAliceQuestionFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (α : {j : Fin n // j ∈ D} → A) (x : X) :
    Matrix S.Alice S.Alice ℂ :=
  fullHistoryAliceFilter G n S D (insert i L)
    (fullCoordinateNewHistory D L i r x) α

def fullCoordinateAliceMeanFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (α : {j : Fin n // j ∈ D} → A) (y : Y) :
    Matrix S.Alice S.Alice ℂ :=
  fullHistoryAliceFilter G n S D L
    (fullCoordinateOldHistory D L i r y) α

def fullCoordinateBobQuestionFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (β : {j : Fin n // j ∈ D} → B) (y : Y) :
    Matrix S.Bob S.Bob ℂ :=
  fullHistoryBobFilter G n S D L
    (fullCoordinateOldHistory D L i r y) β

def fullCoordinateBobMeanFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (β : {j : Fin n // j ∈ D} → B) (x : X) :
    Matrix S.Bob S.Bob ℂ :=
  fullHistoryBobFilter G n S D (insert i L)
    (fullCoordinateNewHistory D L i r x) β

end

noncomputable section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def fullCoordinateAssembleHiddenAlice
    {X : Type*} {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n)
    (x : X)
    (hidden : {j : Fin n //
      j ∈ fullHistoryRemaining n D (insert i L)} → X) :
    {j : Fin n // j ∈ fullHistoryRemaining n D L} → X := by
  classical
  intro j
  by_cases hj : (j : Fin n) = i
  · exact x
  · exact hidden ⟨j, by
      have hjD : (j : Fin n) ∉ D :=
        (Finset.mem_sdiff.mp
          (Finset.mem_sdiff.mp j.property).1).2
      have hjL : (j : Fin n) ∉ L :=
        (Finset.mem_sdiff.mp j.property).2
      simp [fullHistoryRemaining, hjD, hjL, hj]⟩

def fullCoordinateHiddenAliceEquiv
    {X : Type*} [Fintype X] {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L) :
    ({j : Fin n // j ∈ fullHistoryRemaining n D L} → X) ≃
      X × ({j : Fin n //
        j ∈ fullHistoryRemaining n D (insert i L)} → X) where
  toFun hidden :=
    (hidden ⟨i, by simp [fullHistoryRemaining, hiD, hiL]⟩,
      fun j => hidden
        ⟨j, fullHistoryRemaining_insert_subset D L i j.property⟩)
  invFun t := fullCoordinateAssembleHiddenAlice D L i t.1 t.2
  left_inv hidden := by
    funext j
    by_cases hj : (j : Fin n) = i
    · have hjsub :
          j = (⟨i, by simp [fullHistoryRemaining, hiD, hiL]⟩ :
            {j : Fin n // j ∈ fullHistoryRemaining n D L}) :=
        Subtype.ext hj
      subst j
      simp [fullCoordinateAssembleHiddenAlice]
    · simp [fullCoordinateAssembleHiddenAlice, hj]
  right_inv t := by
    rcases t with ⟨x, hidden⟩
    apply Prod.ext
    · simp [fullCoordinateAssembleHiddenAlice]
    · funext j
      have hj : (j : Fin n) ≠ i := by
        intro he
        have hnot : (j : Fin n) ∉ insert i L :=
          (Finset.mem_sdiff.mp j.property).2
        apply hnot
        simp [he]
      simp [fullCoordinateAssembleHiddenAlice, hj]

def fullCoordinateAssembleHiddenBob
    {Y : Type*} {n : ℕ}
    (L : Finset (Fin n)) (i : Fin n)
    (y : Y) (hidden : {j : Fin n // j ∈ L} → Y) :
    {j : Fin n // j ∈ insert i L} → Y := by
  classical
  intro j
  by_cases hj : (j : Fin n) = i
  · exact y
  · exact hidden
      ⟨j, (Finset.mem_insert.mp j.property).resolve_left hj⟩

def fullCoordinateHiddenBobEquiv
    {Y : Type*} [Fintype Y] {n : ℕ}
    (L : Finset (Fin n)) (i : Fin n) (hiL : i ∉ L) :
    ({j : Fin n // j ∈ insert i L} → Y) ≃
      Y × ({j : Fin n // j ∈ L} → Y) where
  toFun hidden :=
    (hidden ⟨i, Finset.mem_insert_self i L⟩,
      fun j => hidden ⟨j, Finset.mem_insert_of_mem j.property⟩)
  invFun t := fullCoordinateAssembleHiddenBob L i t.1 t.2
  left_inv hidden := by
    funext j
    by_cases hj : (j : Fin n) = i
    · have hjsub :
          j = (⟨i, Finset.mem_insert_self i L⟩ :
            {j : Fin n // j ∈ insert i L}) :=
        Subtype.ext hj
      subst j
      simp [fullCoordinateAssembleHiddenBob]
    · simp [fullCoordinateAssembleHiddenBob, hj]
  right_inv t := by
    rcases t with ⟨y, hidden⟩
    apply Prod.ext
    · simp [fullCoordinateAssembleHiddenBob]
    · funext j
      have hj : (j : Fin n) ≠ i := by
        intro he
        exact hiL (he ▸ j.property)
      simp [fullCoordinateAssembleHiddenBob, hj]

section CoordinateFilters

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

end CoordinateFilters

section ConditionalJensen

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def fullCoordinateAliceEntropyIncrement
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (α : {j : Fin n // j ∈ D} → A)
    (β : {j : Fin n // j ∈ D} → B) : ℝ :=
  ∑ y : Y, G.marginalY y *
    bornTracePairing S.state.matrix
      (conditionalAliceAverage G
        (fun x => cfc (fun z : ℝ => z * Real.log z)
          (fullCoordinateAliceQuestionFilter G n S D L i r α x)) y -
        cfc (fun z : ℝ => z * Real.log z)
          (fullCoordinateAliceMeanFilter G n S D L i r α y))
      (fullCoordinateBobQuestionFilter G n S D L i r β y)

end ConditionalJensen

end

noncomputable section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def fullCoordinateBaseWinIndicator
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (α : {j : Fin n // j ∈ D} → A)
    (β : {j : Fin n // j ∈ D} → B) : ℝ := by
  classical
  exact if ∀ j : {j : Fin n // j ∈ D},
    G.predicate (r.aliceConditioned j) (r.bobConditioned j)
      (α j) (β j) = true then 1 else 0

def fullCoordinateAliceTotalEntropyIncrement
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n) : ℝ :=
  ∑ r : FullCoordinateRevealHistory X Y n D L i,
  ∑ α : {j : Fin n // j ∈ D} → A,
  ∑ β : {j : Fin n // j ∈ D} → B,
    fullCoordinateBaseWeight G D L i r *
      fullCoordinateBaseWinIndicator G D L i r α β *
      fullCoordinateAliceEntropyIncrement G n S D L i r α β

end

noncomputable section

open scoped BigOperators

abbrev SourceRemainingCoordinate {n : ℕ} (D : Finset (Fin n)) :=
  ↥(Finset.univ \ D)

abbrev SourceRemainingPermutation {n : ℕ} (D : Finset (Fin n)) :=
  Equiv.Perm (SourceRemainingCoordinate D)

def sourceRemainingPermutationRank
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D) :
    SourceRemainingCoordinate D ≃ Fin (Finset.univ \ D).card :=
  π.symm.trans (Finset.equivFin (Finset.univ \ D))

def sourceRemainingPermutationCoordinateSubtype
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D)
    (k : Fin (Finset.univ \ D).card) :
    SourceRemainingCoordinate D :=
  (sourceRemainingPermutationRank D π).symm k

def sourceRemainingPermutationCoordinate
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D)
    (k : Fin (Finset.univ \ D).card) : Fin n :=
  (sourceRemainingPermutationCoordinateSubtype D π k).val

@[simp] theorem sourceRemainingPermutationRank_coordinate
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D)
    (k : Fin (Finset.univ \ D).card) :
    sourceRemainingPermutationRank D π
      (sourceRemainingPermutationCoordinateSubtype D π k) = k := by
  simp [sourceRemainingPermutationCoordinateSubtype]

def sourceRemainingPermutationPrefixSubtype
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D)
    (k : Fin ((Finset.univ \ D).card + 1)) :
    Finset (SourceRemainingCoordinate D) := by
  classical
  exact Finset.univ.filter fun i =>
    (sourceRemainingPermutationRank D π i).val < k.val

def sourceRemainingPermutationPrefix
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D)
    (k : Fin ((Finset.univ \ D).card + 1)) : Finset (Fin n) := by
  classical
  exact (sourceRemainingPermutationPrefixSubtype D π k).image
    (fun i : SourceRemainingCoordinate D => i.val)

@[simp] theorem sourceRemainingPermutationPrefix_zero
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D) :
    sourceRemainingPermutationPrefix D π 0 = ∅ := by
  classical
  simp [sourceRemainingPermutationPrefix,
    sourceRemainingPermutationPrefixSubtype]

section ActualEntropyBudgets

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def sourcePermutationAliceEntropyIncrement
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (π : SourceRemainingPermutation D)
    (k : Fin (Finset.univ \ D).card) : ℝ :=
  fullCoordinateAliceTotalEntropyIncrement G n S D
    (sourceRemainingPermutationPrefix D π k.castSucc)
    (sourceRemainingPermutationCoordinate D π k)

def sourceUniformPermutationAverage
    {n : ℕ} (D : Finset (Fin n))
    (f : SourceRemainingPermutation D →
      Fin (Finset.univ \ D).card → ℝ) : ℝ :=
  (∑ π : SourceRemainingPermutation D,
    ∑ k : Fin (Finset.univ \ D).card, f π k) /
    ((Fintype.card (SourceRemainingPermutation D) : ℝ) *
      ((Finset.univ \ D).card : ℝ))

end ActualEntropyBudgets

end

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

def exactLeft
    {M : Type*} [Fintype M] [DecidableEq M]
    (coordinate : M) (partition : M → Bool) : Finset M :=
  Finset.univ.filter fun j => j ≠ coordinate ∧ partition j = false

def exactRight
    {M : Type*} [Fintype M] [DecidableEq M]
    (coordinate : M) (partition : M → Bool) : Finset M :=
  Finset.univ.filter fun j => j ≠ coordinate ∧ partition j = true

structure ExactForwardSeed
    (M : Type*) [Fintype M] [DecidableEq M] where
  coordinate : M
  partition : M → Bool
  leftOrder : Equiv.Perm
    {j : M // j ∈ exactLeft coordinate partition}
  rightOrder : Equiv.Perm
    {j : M // j ∈ exactRight coordinate partition}
  leftCut : Fin ((exactLeft coordinate partition).card + 1)
  rightCut : Fin ((exactRight coordinate partition).card + 1)
  deriving Fintype

abbrev ExactRemainingSeed
    {n : ℕ} (D : Finset (Fin n)) :=
  ExactForwardSeed (SourceRemainingCoordinate D)

def exactLeftRank
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    {j : M // j ∈ exactLeft seed.coordinate seed.partition} ≃
      Fin (exactLeft seed.coordinate seed.partition).card :=
  seed.leftOrder.symm.trans
    (Finset.equivFin (exactLeft seed.coordinate seed.partition))

def exactRightRank
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    {j : M // j ∈ exactRight seed.coordinate seed.partition} ≃
      Fin (exactRight seed.coordinate seed.partition).card :=
  seed.rightOrder.symm.trans
    (Finset.equivFin (exactRight seed.coordinate seed.partition))

def exactLeftPrefix
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) : Finset M :=
  (Finset.univ.filter
    (fun j : {j : M //
      j ∈ exactLeft seed.coordinate seed.partition} =>
      (exactLeftRank seed j).val < seed.leftCut.val)).image
        Subtype.val

def exactRightPrefix
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) : Finset M :=
  (Finset.univ.filter
    (fun j : {j : M //
      j ∈ exactRight seed.coordinate seed.partition} =>
      (exactRightRank seed j).val < seed.rightCut.val)).image
        Subtype.val

def exactSeedWeight
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) : ℝ :=
  (1 / (Fintype.card M : ℝ)) *
    (1 / (Fintype.card (M → Bool) : ℝ)) *
    (1 / (Fintype.card
      (Equiv.Perm
        {j : M // j ∈
          exactLeft seed.coordinate seed.partition}) : ℝ)) *
    (1 / (Fintype.card
      (Equiv.Perm
        {j : M // j ∈
          exactRight seed.coordinate seed.partition}) : ℝ)) *
    (1 / ((exactLeft
      seed.coordinate seed.partition).card + 1 : ℝ)) *
    (1 / ((exactRight
      seed.coordinate seed.partition).card + 1 : ℝ))

abbrev ExactSeedTuple
    (M : Type*) [Fintype M] [DecidableEq M] :=
  Σ i : M, Σ partition : M → Bool,
    (Equiv.Perm {j : M // j ∈ exactLeft i partition}) ×
    (Equiv.Perm {j : M // j ∈ exactRight i partition}) ×
    Fin ((exactLeft i partition).card + 1) ×
    Fin ((exactRight i partition).card + 1)

def exactSeedEquiv
    (M : Type*) [Fintype M] [DecidableEq M] :
    ExactForwardSeed M ≃ ExactSeedTuple M where
  toFun seed := ⟨seed.coordinate, seed.partition,
    seed.leftOrder, seed.rightOrder, seed.leftCut, seed.rightCut⟩
  invFun t :=
    ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1,
      t.2.2.2.2.1, t.2.2.2.2.2⟩
  left_inv seed := by
    cases seed
    rfl
  right_inv t := by
    rcases t with ⟨i, partition, leftOrder, rightOrder,
      leftCut, rightCut⟩
    rfl

@[simp] theorem exactSeedEquiv_symm_apply
    {M : Type*} [Fintype M] [DecidableEq M]
    (t : ExactSeedTuple M) :
    (exactSeedEquiv M).symm t =
      ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1,
        t.2.2.2.2.1, t.2.2.2.2.2⟩ := by
  rfl

end

noncomputable section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

set_option backward.isDefEq.respectTransparency false

end

noncomputable section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

end

noncomputable section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def conditionedAliceCoordinateEffect
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (α : {j : Fin n // j ∈ D} → A)
    (xs : Fin n → X) (i : Fin n) (a : A) :
    Matrix S.Alice S.Alice ℂ := by
  classical
  exact ∑ answers : Fin n → A,
    if (∀ (j : Fin n) (hj : j ∈ D), answers j = α ⟨j, hj⟩) ∧
      answers i = a
    then (S.aliceMeasurement xs).effect answers
    else 0

def conditionedBobCoordinateEffect
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (β : {j : Fin n // j ∈ D} → B)
    (ys : Fin n → Y) (i : Fin n) (b : B) :
    Matrix S.Bob S.Bob ℂ := by
  classical
  exact ∑ answers : Fin n → B,
    if (∀ (j : Fin n) (hj : j ∈ D), answers j = β ⟨j, hj⟩) ∧
      answers i = b
    then (S.bobMeasurement ys).effect answers
    else 0

theorem conditionedAliceCoordinateEffect_posSemidef
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (α : {j : Fin n // j ∈ D} → A)
    (xs : Fin n → X) (i : Fin n) (a : A) :
    (conditionedAliceCoordinateEffect G n S D α xs i a).PosSemidef := by
  classical
  unfold conditionedAliceCoordinateEffect
  apply Matrix.posSemidef_sum Finset.univ
  intro answers _
  split_ifs
  · exact (S.aliceMeasurement xs).positive answers
  · exact Matrix.PosSemidef.zero

theorem conditionedBobCoordinateEffect_posSemidef
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (β : {j : Fin n // j ∈ D} → B)
    (ys : Fin n → Y) (i : Fin n) (b : B) :
    (conditionedBobCoordinateEffect G n S D β ys i b).PosSemidef := by
  classical
  unfold conditionedBobCoordinateEffect
  apply Matrix.posSemidef_sum Finset.univ
  intro answers _
  split_ifs
  · exact (S.bobMeasurement ys).positive answers
  · exact Matrix.PosSemidef.zero

theorem conditionedAliceCoordinateEffect_sum
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (α : {j : Fin n // j ∈ D} → A)
    (xs : Fin n → X) (i : Fin n) :
    (∑ a : A, conditionedAliceCoordinateEffect G n S D α xs i a) =
      conditionedAliceEffect G n S D α xs := by
  classical
  unfold conditionedAliceCoordinateEffect conditionedAliceEffect
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro answers _
  calc
    (∑ a : A,
      if (∀ (j : Fin n) (hj : j ∈ D), answers j = α ⟨j, hj⟩) ∧
        answers i = a
      then (S.aliceMeasurement xs).effect answers
      else 0) =
      if (∀ (j : Fin n) (hj : j ∈ D), answers j = α ⟨j, hj⟩) ∧
        answers i = answers i
      then (S.aliceMeasurement xs).effect answers
      else 0 := by
        apply Fintype.sum_eq_single (answers i)
        intro a ha
        simp [ha.symm]
    _ = _ := by simp

theorem conditionedBobCoordinateEffect_sum
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (β : {j : Fin n // j ∈ D} → B)
    (ys : Fin n → Y) (i : Fin n) :
    (∑ b : B, conditionedBobCoordinateEffect G n S D β ys i b) =
      conditionedBobEffect G n S D β ys := by
  classical
  unfold conditionedBobCoordinateEffect conditionedBobEffect
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro answers _
  calc
    (∑ b : B,
      if (∀ (j : Fin n) (hj : j ∈ D), answers j = β ⟨j, hj⟩) ∧
        answers i = b
      then (S.bobMeasurement ys).effect answers
      else 0) =
      if (∀ (j : Fin n) (hj : j ∈ D), answers j = β ⟨j, hj⟩) ∧
        answers i = answers i
      then (S.bobMeasurement ys).effect answers
      else 0 := by
        apply Fintype.sum_eq_single (answers i)
        intro b hb
        simp [hb.symm]
    _ = _ := by simp

def fullHistoryAliceCoordinateEffect
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n))
    (h : FullSubsetHistory X Y n D L)
    (α : {j : Fin n // j ∈ D} → A)
    (i : Fin n) (a : A) :
    Matrix S.Alice S.Alice ℂ :=
  ∑ hidden : {j : Fin n // j ∈ fullHistoryRemaining n D L} → X,
    fullHistoryHiddenAliceWeight G h hidden •
      conditionedAliceCoordinateEffect G n S D α
        (fullHistoryAliceQuestion h hidden) i a

def fullHistoryBobCoordinateEffect
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n))
    (h : FullSubsetHistory X Y n D L)
    (β : {j : Fin n // j ∈ D} → B)
    (i : Fin n) (b : B) :
    Matrix S.Bob S.Bob ℂ :=
  ∑ hidden : {j : Fin n // j ∈ L} → Y,
    fullHistoryHiddenBobWeight G h hidden •
      conditionedBobCoordinateEffect G n S D β
        (fullHistoryBobQuestion h hidden) i b

def fullCoordinateAliceRefinementEffect
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (α : {j : Fin n // j ∈ D} → A)
    (x : X) (a : A) : Matrix S.Alice S.Alice ℂ :=
  fullHistoryAliceCoordinateEffect G n S D (insert i L)
    (fullCoordinateNewHistory D L i r x) α i a

def fullCoordinateBobRefinementEffect
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (β : {j : Fin n // j ∈ D} → B)
    (y : Y) (b : B) : Matrix S.Bob S.Bob ℂ :=
  fullHistoryBobCoordinateEffect G n S D L
    (fullCoordinateOldHistory D L i r y) β i b

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

structure ExactRevealHistory
    (X Y : Type*) [Fintype X] [Fintype Y]
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D) where
  aliceConditioned : {j : Fin n // j ∈ D} → X
  bobConditioned : {j : Fin n // j ∈ D} → Y
  aliceLeft :
    {j : SourceRemainingCoordinate D //
      j ∈ exactLeft seed.coordinate seed.partition} → X
  bobRight :
    {j : SourceRemainingCoordinate D //
      j ∈ exactRight seed.coordinate seed.partition} → Y
  bobLeftPrefix :
    {j : SourceRemainingCoordinate D //
      j ∈ exactLeftPrefix seed} → Y
  aliceRightPrefix :
    {j : SourceRemainingCoordinate D //
      j ∈ exactRightPrefix seed} → X

abbrev ExactRevealHistoryTuple
    (X Y : Type*) [Fintype X] [Fintype Y]
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D) :=
  ({j : Fin n // j ∈ D} → X) ×
  ({j : Fin n // j ∈ D} → Y) ×
  ({j : SourceRemainingCoordinate D //
      j ∈ exactLeft seed.coordinate seed.partition} → X) ×
  ({j : SourceRemainingCoordinate D //
      j ∈ exactRight seed.coordinate seed.partition} → Y) ×
  ({j : SourceRemainingCoordinate D //
      j ∈ exactLeftPrefix seed} → Y) ×
  ({j : SourceRemainingCoordinate D //
      j ∈ exactRightPrefix seed} → X)

def exactRevealHistoryEquiv
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D) :
    ExactRevealHistory X Y D seed ≃
      ExactRevealHistoryTuple X Y D seed where
  toFun h := ⟨h.aliceConditioned, h.bobConditioned,
    h.aliceLeft, h.bobRight, h.bobLeftPrefix, h.aliceRightPrefix⟩
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1,
    t.2.2.2.2.1, t.2.2.2.2.2⟩
  left_inv h := by cases h; rfl
  right_inv t := by
    rcases t with ⟨ac, bc, al, br, bl, ar⟩
    rfl

noncomputable instance exactRevealHistoryFintype
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D) :
    Fintype (ExactRevealHistory X Y D seed) := by
  classical
  exact Fintype.ofEquiv (ExactRevealHistoryTuple X Y D seed)
    (exactRevealHistoryEquiv
      (X := X) (Y := Y) D seed).symm

abbrev ExactFullQuestion
    (X Y : Type*) (n : ℕ) :=
  (Fin n → X) × (Fin n → Y)

def exactRevealCode
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (q : ExactFullQuestion X Y n) :
    ExactRevealHistory X Y D seed where
  aliceConditioned j := q.1 j.val
  bobConditioned j := q.2 j.val
  aliceLeft j := q.1 j.val.val
  bobRight j := q.2 j.val.val
  bobLeftPrefix j := q.2 j.val.val
  aliceRightPrefix j := q.1 j.val.val

def exactPriorQuestionWeight
    (G : Game X Y A B) (n : ℕ)
    (q : ExactFullQuestion X Y n) : ℝ :=
  (G.repeat n).questionWeight q.1 q.2

theorem exactPriorQuestionWeight_nonneg
    (G : Game X Y A B) (n : ℕ)
    (q : ExactFullQuestion X Y n) :
    0 ≤ exactPriorQuestionWeight G n q :=
  (G.repeat n).weight_nonneg q.1 q.2

def exactRevealMass
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed) : ℝ :=
  ∑ q : ExactFullQuestion X Y n,
    if exactRevealCode D seed q = history
    then exactPriorQuestionWeight G n q
    else 0

def exactAliceQuestionMass
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) : ℝ :=
  ∑ q : ExactFullQuestion X Y n,
    if exactRevealCode D seed q = history ∧
      q.1 seed.coordinate.val = x
    then exactPriorQuestionWeight G n q
    else 0

def exactBobQuestionMass
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (y : Y) : ℝ :=
  ∑ q : ExactFullQuestion X Y n,
    if exactRevealCode D seed q = history ∧
      q.2 seed.coordinate.val = y
    then exactPriorQuestionWeight G n q
    else 0

def exactJointQuestionMass
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y) : ℝ :=
  ∑ q : ExactFullQuestion X Y n,
    if exactRevealCode D seed q = history ∧
      q.1 seed.coordinate.val = x ∧
      q.2 seed.coordinate.val = y
    then exactPriorQuestionWeight G n q
    else 0

theorem exactAliceQuestionMass_nonneg
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) :
    0 ≤ exactAliceQuestionMass G n D seed history x := by
  unfold exactAliceQuestionMass
  apply Finset.sum_nonneg
  intro q _
  split
  · exact exactPriorQuestionWeight_nonneg G n q
  · exact le_rfl

theorem exactBobQuestionMass_nonneg
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (y : Y) :
    0 ≤ exactBobQuestionMass G n D seed history y := by
  unfold exactBobQuestionMass
  apply Finset.sum_nonneg
  intro q _
  split
  · exact exactPriorQuestionWeight_nonneg G n q
  · exact le_rfl

def exactAliceQuestionFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (x : X) : Matrix S.Alice S.Alice ℂ :=
  ∑ q : ExactFullQuestion X Y n,
    if exactRevealCode D seed q = history ∧
      q.1 seed.coordinate.val = x
    then
      (exactPriorQuestionWeight G n q /
        exactAliceQuestionMass G n D seed history x) •
        conditionedAliceEffect G n S D answer q.1
    else 0

def exactBobQuestionFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (y : Y) : Matrix S.Bob S.Bob ℂ :=
  ∑ q : ExactFullQuestion X Y n,
    if exactRevealCode D seed q = history ∧
      q.2 seed.coordinate.val = y
    then
      (exactPriorQuestionWeight G n q /
        exactBobQuestionMass G n D seed history y) •
        conditionedBobEffect G n S D answer q.2
    else 0

theorem exactAliceQuestionFilter_posSemidef
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (x : X) :
    (exactAliceQuestionFilter
      G n S D seed history answer x).PosSemidef := by
  unfold exactAliceQuestionFilter
  apply Matrix.posSemidef_sum Finset.univ
  intro q _
  split
  · exact (conditionedAliceEffect_positive G n S D answer q.1).smul
      (div_nonneg
        (exactPriorQuestionWeight_nonneg G n q)
        (exactAliceQuestionMass_nonneg
          G n D seed history x))
  · exact Matrix.PosSemidef.zero

theorem exactBobQuestionFilter_posSemidef
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (y : Y) :
    (exactBobQuestionFilter
      G n S D seed history answer y).PosSemidef := by
  unfold exactBobQuestionFilter
  apply Matrix.posSemidef_sum Finset.univ
  intro q _
  split
  · exact (conditionedBobEffect_positive G n S D answer q.2).smul
      (div_nonneg
        (exactPriorQuestionWeight_nonneg G n q)
        (exactBobQuestionMass_nonneg
          G n D seed history y))
  · exact Matrix.PosSemidef.zero

def exactAliceMeanFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (y : Y) : Matrix S.Alice S.Alice ℂ :=
  ∑ x : X, G.conditionalXGivenY y x •
    exactAliceQuestionFilter G n S D seed history answer x

def exactBobMeanFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (x : X) : Matrix S.Bob S.Bob ℂ :=
  ∑ y : Y, G.conditionalYGivenX x y •
    exactBobQuestionFilter G n S D seed history answer y

theorem exactAliceMeanFilter_posSemidef
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (y : Y) :
    (exactAliceMeanFilter
      G n S D seed history answer y).PosSemidef := by
  unfold exactAliceMeanFilter
  apply Matrix.posSemidef_sum Finset.univ
  intro x _
  exact (exactAliceQuestionFilter_posSemidef
    G n S D seed history answer x).smul
    (G.conditionalXGivenY_nonneg y x)

theorem exactBobMeanFilter_posSemidef
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (x : X) :
    (exactBobMeanFilter
      G n S D seed history answer x).PosSemidef := by
  unfold exactBobMeanFilter
  apply Matrix.posSemidef_sum Finset.univ
  intro y _
  exact (exactBobQuestionFilter_posSemidef
    G n S D seed history answer y).smul
    (G.conditionalYGivenX_nonneg x y)

def exactAliceCoordinateFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (x : X) (a : A) : Matrix S.Alice S.Alice ℂ :=
  ∑ q : ExactFullQuestion X Y n,
    if exactRevealCode D seed q = history ∧
      q.1 seed.coordinate.val = x
    then
      (exactPriorQuestionWeight G n q /
        exactAliceQuestionMass G n D seed history x) •
        conditionedAliceCoordinateEffect G n S D answer q.1
          seed.coordinate.val a
    else 0

def exactBobCoordinateFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (y : Y) (b : B) : Matrix S.Bob S.Bob ℂ :=
  ∑ q : ExactFullQuestion X Y n,
    if exactRevealCode D seed q = history ∧
      q.2 seed.coordinate.val = y
    then
      (exactPriorQuestionWeight G n q /
        exactBobQuestionMass G n D seed history y) •
        conditionedBobCoordinateEffect G n S D answer q.2
          seed.coordinate.val b
    else 0

theorem exactAliceCoordinateFilter_posSemidef
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (x : X) (a : A) :
    (exactAliceCoordinateFilter
      G n S D seed history answer x a).PosSemidef := by
  unfold exactAliceCoordinateFilter
  apply Matrix.posSemidef_sum Finset.univ
  intro q _
  split
  · exact (conditionedAliceCoordinateEffect_posSemidef
      G n S D answer q.1 seed.coordinate.val a).smul
      (div_nonneg
        (exactPriorQuestionWeight_nonneg G n q)
        (exactAliceQuestionMass_nonneg
          G n D seed history x))
  · exact Matrix.PosSemidef.zero

theorem exactBobCoordinateFilter_posSemidef
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (y : Y) (b : B) :
    (exactBobCoordinateFilter
      G n S D seed history answer y b).PosSemidef := by
  unfold exactBobCoordinateFilter
  apply Matrix.posSemidef_sum Finset.univ
  intro q _
  split
  · exact (conditionedBobCoordinateEffect_posSemidef
      G n S D answer q.2 seed.coordinate.val b).smul
      (div_nonneg
        (exactPriorQuestionWeight_nonneg G n q)
        (exactBobQuestionMass_nonneg
          G n D seed history y))
  · exact Matrix.PosSemidef.zero

theorem exactAliceCoordinateFilter_sum
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (x : X) :
    (∑ a : A,
      exactAliceCoordinateFilter
        G n S D seed history answer x a) =
      exactAliceQuestionFilter
        G n S D seed history answer x := by
  classical
  unfold exactAliceCoordinateFilter
    exactAliceQuestionFilter
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : exactRevealCode D seed q = history ∧
      q.1 seed.coordinate.val = x
  · simp [hq, ← Finset.smul_sum,
      conditionedAliceCoordinateEffect_sum]
  · simp [hq]

theorem exactBobCoordinateFilter_sum
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (y : Y) :
    (∑ b : B,
      exactBobCoordinateFilter
        G n S D seed history answer y b) =
      exactBobQuestionFilter
        G n S D seed history answer y := by
  classical
  unfold exactBobCoordinateFilter
    exactBobQuestionFilter
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : exactRevealCode D seed q = history ∧
      q.2 seed.coordinate.val = y
  · simp [hq, ← Finset.smul_sum,
      conditionedBobCoordinateEffect_sum]
  · simp [hq]

def exactAlicePurificationFamily
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A) :
    Sum X Y → Matrix S.Alice S.Alice ℂ :=
  Sum.elim
    (exactAliceQuestionFilter G n S D seed history answer)
    (exactAliceMeanFilter G n S D seed history answer)

def exactBobPurificationFamily
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B) :
    Sum Y X → Matrix S.Bob S.Bob ℂ :=
  Sum.elim
    (exactBobQuestionFilter G n S D seed history answer)
    (exactBobMeanFilter G n S D seed history answer)

theorem exactAlicePurificationFamily_posSemidef
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (q : Sum X Y) :
    (exactAlicePurificationFamily
      G n S D seed history answer q).PosSemidef := by
  cases q with
  | inl x =>
      exact exactAliceQuestionFilter_posSemidef
        G n S D seed history answer x
  | inr y =>
      exact exactAliceMeanFilter_posSemidef
        G n S D seed history answer y

theorem exactBobPurificationFamily_posSemidef
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (q : Sum Y X) :
    (exactBobPurificationFamily
      G n S D seed history answer q).PosSemidef := by
  cases q with
  | inl y =>
      exact exactBobQuestionFilter_posSemidef
        G n S D seed history answer y
  | inr x =>
      exact exactBobMeanFilter_posSemidef
        G n S D seed history answer x

abbrev ExactAliceLiftIndex
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A) :=
  S.Alice × Fin (Module.finrank ℂ
    (commonPurificationSubspace
      (exactAlicePurificationFamily
        G n S D seed history answer)
      (0 : Matrix S.Alice S.Alice ℂ)
      (exactAlicePurificationFamily_posSemidef
        G n S D seed history answer)
      Matrix.PosSemidef.zero))

abbrev ExactBobLiftIndex
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B) :=
  S.Bob × Fin (Module.finrank ℂ
    (commonPurificationSubspace
      (exactBobPurificationFamily
        G n S D seed history answer)
      (0 : Matrix S.Bob S.Bob ℂ)
      (exactBobPurificationFamily_posSemidef
        G n S D seed history answer)
      Matrix.PosSemidef.zero))

def exactAlicePurificationMatrix
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (q : Sum X Y) :
    Matrix (ExactAliceLiftIndex
      G n S D seed history answer) S.Alice ℂ :=
  finitePurificationMatrix
    (exactAlicePurificationFamily
      G n S D seed history answer)
    0
    (exactAlicePurificationFamily_posSemidef
      G n S D seed history answer)
    Matrix.PosSemidef.zero q

def exactBobPurificationMatrix
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (q : Sum Y X) :
    Matrix (ExactBobLiftIndex
      G n S D seed history answer) S.Bob ℂ :=
  finitePurificationMatrix
    (exactBobPurificationFamily
      G n S D seed history answer)
    0
    (exactBobPurificationFamily_posSemidef
      G n S D seed history answer)
    Matrix.PosSemidef.zero q

theorem exactAlicePurificationMatrix_gram
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (q : Sum X Y) :
    (exactAlicePurificationMatrix
      G n S D seed history answer q).conjTranspose *
      exactAlicePurificationMatrix
        G n S D seed history answer q =
      exactAlicePurificationFamily
        G n S D seed history answer q :=
  finitePurificationMatrix_gram
    (exactAlicePurificationFamily
      G n S D seed history answer)
    0
    (exactAlicePurificationFamily_posSemidef
      G n S D seed history answer)
    Matrix.PosSemidef.zero q

theorem exactBobPurificationMatrix_gram
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (q : Sum Y X) :
    (exactBobPurificationMatrix
      G n S D seed history answer q).conjTranspose *
      exactBobPurificationMatrix
        G n S D seed history answer q =
      exactBobPurificationFamily
        G n S D seed history answer q :=
  finitePurificationMatrix_gram
    (exactBobPurificationFamily
      G n S D seed history answer)
    0
    (exactBobPurificationFamily_posSemidef
      G n S D seed history answer)
    Matrix.PosSemidef.zero q

@[ext (iff := false)] structure ExactHistoryFlag
    (X Y A B : Type*)
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {n : ℕ} (D : Finset (Fin n)) where
  seed : ExactRemainingSeed D
  history : ExactRevealHistory X Y D seed
  aliceAnswer : {j : Fin n // j ∈ D} → A
  bobAnswer : {j : Fin n // j ∈ D} → B

abbrev ExactHistoryFlagTuple
    (X Y A B : Type*)
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {n : ℕ} (D : Finset (Fin n)) :=
  Σ seed : ExactRemainingSeed D,
    ExactRevealHistory X Y D seed ×
      ({j : Fin n // j ∈ D} → A) ×
      ({j : Fin n // j ∈ D} → B)

def exactHistoryFlagEquiv
    {n : ℕ} (D : Finset (Fin n)) :
    ExactHistoryFlag X Y A B D ≃
      ExactHistoryFlagTuple X Y A B D where
  toFun r := ⟨r.seed, r.history, r.aliceAnswer, r.bobAnswer⟩
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩
  left_inv r := by cases r; rfl
  right_inv t := by
    rcases t with ⟨seed, history, aliceAnswer, bobAnswer⟩
    rfl

noncomputable instance exactHistoryFlagFintype
    {n : ℕ} (D : Finset (Fin n)) :
    Fintype (ExactHistoryFlag X Y A B D) := by
  classical
  exact Fintype.ofEquiv (ExactHistoryFlagTuple X Y A B D)
    (exactHistoryFlagEquiv
      (X := X) (Y := Y) (A := A) (B := B) D).symm

abbrev ExactAliceLocalIndex
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) :=
  ExactAliceLiftIndex
    G n S D r.seed r.history r.aliceAnswer × (S.Alice × S.Bob)

abbrev ExactBobLocalIndex
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) :=
  ExactBobLiftIndex
    G n S D r.seed r.history r.bobAnswer

def exactUnnormalizedPsi
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y) :
    EuclideanSpace ℂ
      (ExactAliceLocalIndex G n S D r ×
        ExactBobLocalIndex G n S D r) :=
  finiteLocalPurificationVector S
    (exactAlicePurificationMatrix
      G n S D r.seed r.history r.aliceAnswer (.inl x))
    (exactBobPurificationMatrix
      G n S D r.seed r.history r.bobAnswer (.inl y))

def exactUnnormalizedPhi
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (y : Y) :
    EuclideanSpace ℂ
      (ExactAliceLocalIndex G n S D r ×
        ExactBobLocalIndex G n S D r) :=
  finiteLocalPurificationVector S
    (exactAlicePurificationMatrix
      G n S D r.seed r.history r.aliceAnswer (.inr y))
    (exactBobPurificationMatrix
      G n S D r.seed r.history r.bobAnswer (.inl y))

def exactUnnormalizedGamma
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) :
    EuclideanSpace ℂ
      (ExactAliceLocalIndex G n S D r ×
        ExactBobLocalIndex G n S D r) :=
  finiteLocalPurificationVector S
    (exactAlicePurificationMatrix
      G n S D r.seed r.history r.aliceAnswer (.inl x))
    (exactBobPurificationMatrix
      G n S D r.seed r.history r.bobAnswer (.inr x))

theorem exactAliceQuestionPurificationMatrix_gram
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) :
    (exactAlicePurificationMatrix
      G n S D r.seed r.history r.aliceAnswer (.inl x)).conjTranspose *
      exactAlicePurificationMatrix
        G n S D r.seed r.history r.aliceAnswer (.inl x) =
      exactAliceQuestionFilter
        G n S D r.seed r.history r.aliceAnswer x :=
  exactAlicePurificationMatrix_gram
    G n S D r.seed r.history r.aliceAnswer (.inl x)

theorem exactBobQuestionPurificationMatrix_gram
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (y : Y) :
    (exactBobPurificationMatrix
      G n S D r.seed r.history r.bobAnswer (.inl y)).conjTranspose *
      exactBobPurificationMatrix
        G n S D r.seed r.history r.bobAnswer (.inl y) =
      exactBobQuestionFilter
        G n S D r.seed r.history r.bobAnswer y :=
  exactBobPurificationMatrix_gram
    G n S D r.seed r.history r.bobAnswer (.inl y)

def exactAliceRefinedPOVM
    [DecidableEq A]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (x : X) :
    POVM A (ExactAliceLiftIndex
      G n S D r.seed r.history r.aliceAnswer) :=
  purifiedRefinedPOVM
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
    a₀

def exactBobRefinedPOVM
    [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (b₀ : B) (y : Y) :
    POVM B (ExactBobLiftIndex
      G n S D r.seed r.history r.bobAnswer) :=
  purifiedRefinedPOVM
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
    b₀

abbrev ExactPaddedLocalIndex
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) :=
  PUnit.{1} ⊕
    (ExactAliceLocalIndex G n S D r ⊕
      ExactBobLocalIndex G n S D r)

def exactPaddedVector
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (z : EuclideanSpace ℂ
      (ExactAliceLocalIndex G n S D r ×
        ExactBobLocalIndex G n S D r)) :
    EuclideanSpace ℂ
      (ExactPaddedLocalIndex G n S D r ×
        ExactPaddedLocalIndex G n S D r) :=
  toLp 2 fun q =>
    match q.1, q.2 with
    | .inr (.inl a), .inr (.inr b) => z (a, b)
    | _, _ => 0

def exactPaddedDefault
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) :
    EuclideanSpace ℂ
      (ExactPaddedLocalIndex G n S D r ×
        ExactPaddedLocalIndex G n S D r) := by
  classical
  exact PiLp.single 2 (.inl PUnit.unit, .inl PUnit.unit) (1 : ℂ)

def exactPsi
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y) :
    EuclideanSpace ℂ
      (ExactPaddedLocalIndex G n S D r ×
        ExactPaddedLocalIndex G n S D r) :=
  normalizeOrDefault (exactPaddedDefault G n S D r)
    (exactPaddedVector G n S D r
      (exactUnnormalizedPsi G n S D r x y))

def exactPhi
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (y : Y) :
    EuclideanSpace ℂ
      (ExactPaddedLocalIndex G n S D r ×
        ExactPaddedLocalIndex G n S D r) :=
  normalizeOrDefault (exactPaddedDefault G n S D r)
    (exactPaddedVector G n S D r
      (exactUnnormalizedPhi G n S D r y))

def exactGamma
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) :
    EuclideanSpace ℂ
      (ExactPaddedLocalIndex G n S D r ×
        ExactPaddedLocalIndex G n S D r) :=
  normalizeOrDefault (exactPaddedDefault G n S D r)
    (exactPaddedVector G n S D r
      (exactUnnormalizedGamma G n S D r x))

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def exactAliceQuestionCompatible
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (xs : Fin n → X) : Prop :=
  (∀ j : {j : Fin n // j ∈ D},
      xs j.val = history.aliceConditioned j) ∧
  (∀ j : {j : SourceRemainingCoordinate D //
      j ∈ exactLeft seed.coordinate seed.partition},
      xs j.val.val = history.aliceLeft j) ∧
  (∀ j : {j : SourceRemainingCoordinate D //
      j ∈ exactRightPrefix seed},
      xs j.val.val = history.aliceRightPrefix j) ∧
  xs seed.coordinate.val = x

def exactBobQuestionCompatible
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (y : Y) (ys : Fin n → Y) : Prop :=
  (∀ j : {j : Fin n // j ∈ D},
      ys j.val = history.bobConditioned j) ∧
  (∀ j : {j : SourceRemainingCoordinate D //
      j ∈ exactRight seed.coordinate seed.partition},
      ys j.val.val = history.bobRight j) ∧
  (∀ j : {j : SourceRemainingCoordinate D //
      j ∈ exactLeftPrefix seed},
      ys j.val.val = history.bobLeftPrefix j) ∧
  ys seed.coordinate.val = y

def exactFiberQuestionWeight
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y)
    (xs : Fin n → X) (ys : Fin n → Y) : ℝ :=
  if exactAliceQuestionCompatible
      D seed history x xs ∧
      exactBobQuestionCompatible
        D seed history y ys
  then (G.repeat n).questionWeight xs ys
  else 0

def exactFiberAliceMarginal
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y) (xs : Fin n → X) : ℝ :=
  ∑ ys : Fin n → Y,
    exactFiberQuestionWeight G n D seed history x y xs ys

def exactFiberBobMarginal
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y) (ys : Fin n → Y) : ℝ :=
  ∑ xs : Fin n → X,
    exactFiberQuestionWeight G n D seed history x y xs ys

def exactFiberQuestionMass
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y) : ℝ :=
  ∑ xs : Fin n → X, ∑ ys : Fin n → Y,
    exactFiberQuestionWeight G n D seed history x y xs ys

end

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1200000

attribute [local instance] Classical.propDecidable

end

noncomputable section

open scoped BigOperators

end

noncomputable section

open scoped BigOperators

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

end

noncomputable section

open scoped BigOperators

open QuantumParallelRepetition.Pinsker

end

noncomputable section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

section ActualSharedFlag

variable {X Y A B dA dB J : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype dA] [Fintype dB] [DecidableEq dA] [DecidableEq dB]
variable [Fintype J] [DecidableEq J]

def pureVerifierEffect
    (G : Game X Y A B)
    (z : EuclideanSpace ℂ (dA × dB)) (hz : ‖z‖ = 1)
    (PA : X → POVM A dA) (PB : Y → POVM B dB)
    (x : X) (y : Y) : Matrix (dA × dB) (dA × dB) ℂ :=
  (pureVectorStrategy G z hz PA PB).winningEffect x y

def flaggedQuestionWeight
    (G : Game X Y A B) (flagWeight : J → ℝ)
    (ω : J × (X × Y)) : ℝ :=
  flagWeight ω.1 * G.questionWeight ω.2.1 ω.2.2

end ActualSharedFlag

end

noncomputable section

open Filter
open scoped Topology

def universalErrorCeiling (K₀ : ℝ) : ℝ :=
  K₀ * (1 + (2 : ℝ) ^ (1 / 6 : ℝ)) + 2

def totalSamplingLoss (K₀ α η lam : ℝ) : ℝ :=
  5 * lam +
    2 * (K₀ * (α ^ (1 / 12 : ℝ) +
        (32 * η) ^ (1 / 12 : ℝ)) +
      Real.sqrt (8 * η) + universalErrorCeiling K₀ * lam)

def roundedWinningLowerBound (ε K₀ α η lam : ℝ) : ℝ :=
  1 - ε / 2 - totalSamplingLoss K₀ α η lam

end

noncomputable section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

end

noncomputable section

open scoped BigOperators

end

noncomputable section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

theorem fullHistoryRemaining_insert_conditioned
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n) :
    fullHistoryRemaining n (insert i D) L =
      fullHistoryRemaining n D (insert i L) := by
  ext j
  simp only [fullHistoryRemaining, Finset.mem_sdiff,
    Finset.mem_univ, true_and, Finset.mem_insert]
  tauto

def fullHistoryRemainingInsertedEquiv
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n) :
    {j : Fin n // j ∈ fullHistoryRemaining n (insert i D) L} ≃
      {j : Fin n // j ∈ fullHistoryRemaining n D (insert i L)} :=
  Equiv.subtypeEquivRight fun j => by
    rw [fullHistoryRemaining_insert_conditioned D L i]

def fullCoordinateAnswerExtension
    {T : Type*} {n : ℕ}
    (D : Finset (Fin n)) (i : Fin n)
    (α : {j : Fin n // j ∈ D} → T) (a : T) :
    {j : Fin n // j ∈ insert i D} → T := by
  classical
  intro j
  by_cases hj : (j : Fin n) = i
  · exact a
  · exact α ⟨j, (Finset.mem_insert.mp j.property).resolve_left hj⟩

def fullCoordinateAnswerExtensionEquiv
    {T : Type*} [Fintype T] {n : ℕ}
    (D : Finset (Fin n)) (i : Fin n) (hiD : i ∉ D) :
    (({j : Fin n // j ∈ D} → T) × T) ≃
      ({j : Fin n // j ∈ insert i D} → T) where
  toFun t := fullCoordinateAnswerExtension D i t.1 t.2
  invFun α :=
    (fun j => α ⟨j, Finset.mem_insert_of_mem j.property⟩,
      α ⟨i, Finset.mem_insert_self i D⟩)
  left_inv t := by
    rcases t with ⟨α, a⟩
    apply Prod.ext
    · funext j
      have hj : (j : Fin n) ≠ i := by
        intro he
        exact hiD (he ▸ j.property)
      simp [fullCoordinateAnswerExtension, hj]
    · simp [fullCoordinateAnswerExtension]
  right_inv α := by
    funext j
    by_cases hj : (j : Fin n) = i
    · have hjsub :
          j = (⟨i, Finset.mem_insert_self i D⟩ :
            {j : Fin n // j ∈ insert i D}) := Subtype.ext hj
      subst j
      simp [fullCoordinateAnswerExtension]
    · simp [fullCoordinateAnswerExtension, hj]

def fullCoordinateInsertedHistory
    {X Y : Type*} [Fintype X] [Fintype Y]
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (x : X) (y : Y) :
    FullSubsetHistory X Y n (insert i D) L := by
  classical
  refine ⟨
    fullCoordinateAnswerExtension D i r.aliceConditioned x,
    fullCoordinateAnswerExtension D i r.bobConditioned y,
    r.aliceRevealed,
    fun j => r.bobRemaining ⟨j, ?_⟩⟩
  rw [← fullHistoryRemaining_insert_conditioned D L i]
  exact j.property

def fullCoordinateBaseOfInsertedHistory
    {X Y : Type*} [Fintype X] [Fintype Y]
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (h : FullSubsetHistory X Y n (insert i D) L) :
    FullCoordinateRevealHistory X Y n D L i := by
  refine ⟨
    fun j => h.aliceConditioned
      ⟨j, Finset.mem_insert_of_mem j.property⟩,
    fun j => h.bobConditioned
      ⟨j, Finset.mem_insert_of_mem j.property⟩,
    h.aliceRevealed,
    fun j => h.bobRemaining ⟨j, ?_⟩⟩
  rw [fullHistoryRemaining_insert_conditioned D L i]
  exact j.property

def fullCoordinateInsertedHistoryEquiv
    {X Y : Type*} [Fintype X] [Fintype Y]
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) :
    (FullCoordinateRevealHistory X Y n D L i × X × Y) ≃
      FullSubsetHistory X Y n (insert i D) L where
  toFun t := fullCoordinateInsertedHistory D L i t.1 t.2.1 t.2.2
  invFun h :=
    (fullCoordinateBaseOfInsertedHistory D L i h,
      h.aliceConditioned ⟨i, Finset.mem_insert_self i D⟩,
      h.bobConditioned ⟨i, Finset.mem_insert_self i D⟩)
  left_inv t := by
    rcases t with ⟨r, x, y⟩
    apply Prod.ext
    · apply FullCoordinateRevealHistory.ext
      · funext j
        have hj : (j : Fin n) ≠ i := by
          intro he
          exact hiD (he ▸ j.property)
        simp [fullCoordinateBaseOfInsertedHistory,
          fullCoordinateInsertedHistory,
          fullCoordinateAnswerExtension, hj]
      · funext j
        have hj : (j : Fin n) ≠ i := by
          intro he
          exact hiD (he ▸ j.property)
        simp [fullCoordinateBaseOfInsertedHistory,
          fullCoordinateInsertedHistory,
          fullCoordinateAnswerExtension, hj]
      · rfl
      · rfl
    · apply Prod.ext <;>
        simp [fullCoordinateInsertedHistory,
          fullCoordinateAnswerExtension]
  right_inv h := by
    apply FullSubsetHistory.ext
    · funext j
      by_cases hj : (j : Fin n) = i
      · have hjsub :
            j = (⟨i, Finset.mem_insert_self i D⟩ :
              {j : Fin n // j ∈ insert i D}) := Subtype.ext hj
        subst j
        simp [fullCoordinateInsertedHistory,
          fullCoordinateBaseOfInsertedHistory,
          fullCoordinateAnswerExtension]
      · simp [fullCoordinateInsertedHistory,
          fullCoordinateBaseOfInsertedHistory,
          fullCoordinateAnswerExtension, hj]
    · funext j
      by_cases hj : (j : Fin n) = i
      · have hjsub :
            j = (⟨i, Finset.mem_insert_self i D⟩ :
              {j : Fin n // j ∈ insert i D}) := Subtype.ext hj
        subst j
        simp [fullCoordinateInsertedHistory,
          fullCoordinateBaseOfInsertedHistory,
          fullCoordinateAnswerExtension]
      · simp [fullCoordinateInsertedHistory,
          fullCoordinateBaseOfInsertedHistory,
          fullCoordinateAnswerExtension, hj]
    · rfl
    · rfl

section InsertedWeights

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

end InsertedWeights

end

noncomputable section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

end

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

def normalizedPureVector
    {d : Type*} [Fintype d]
    (z : EuclideanSpace ℂ d) : EuclideanSpace ℂ d :=
  ((‖z‖⁻¹ : ℝ) : ℂ) • z

end

noncomputable section

open scoped BigOperators

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

end

noncomputable section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

structure SourceHistoryFlag
    (X Y A B : Type*)
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {n : ℕ} (D : Finset (Fin n)) where
  permutation : SourceRemainingPermutation D
  position : Fin (Finset.univ \ D).card
  history : FullCoordinateRevealHistory X Y n D
    (sourceRemainingPermutationPrefix D permutation position.castSucc)
    (sourceRemainingPermutationCoordinate D permutation position)
  aliceAnswer : {i : Fin n // i ∈ D} → A
  bobAnswer : {i : Fin n // i ∈ D} → B

abbrev SourceHistoryFlagTuple
    (X Y A B : Type*)
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {n : ℕ} (D : Finset (Fin n)) :=
  Σ π : SourceRemainingPermutation D,
    Σ k : Fin (Finset.univ \ D).card,
      FullCoordinateRevealHistory X Y n D
        (sourceRemainingPermutationPrefix D π k.castSucc)
        (sourceRemainingPermutationCoordinate D π k) ×
      ({i : Fin n // i ∈ D} → A) ×
      ({i : Fin n // i ∈ D} → B)

def sourceHistoryFlagEquiv
    {n : ℕ} (D : Finset (Fin n)) :
    SourceHistoryFlag X Y A B D ≃ SourceHistoryFlagTuple X Y A B D where
  toFun r := ⟨r.permutation, r.position,
    r.history, r.aliceAnswer, r.bobAnswer⟩
  invFun t := ⟨t.1, t.2.1,
    t.2.2.1, t.2.2.2.1, t.2.2.2.2⟩
  left_inv r := by cases r; rfl
  right_inv t := by
    rcases t with ⟨π, k, r, α, β⟩
    rfl

noncomputable instance sourceHistoryFlagFintype
    {n : ℕ} (D : Finset (Fin n)) :
    Fintype (SourceHistoryFlag X Y A B D) := by
  classical
  exact Fintype.ofEquiv (SourceHistoryFlagTuple X Y A B D)
    (sourceHistoryFlagEquiv (X := X) (Y := Y)
      (A := A) (B := B) D).symm

def sourceHistoryPermutationPositionWeight
    {n : ℕ} (D : Finset (Fin n)) : ℝ :=
  1 / ((Fintype.card (SourceRemainingPermutation D) : ℝ) *
    ((Finset.univ \ D).card : ℝ))

def sourceHistoryRaw
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (r : SourceHistoryFlag X Y A B D) : ℝ :=
  sourceHistoryPermutationPositionWeight D *
    fullCoordinateBaseWeight G D
      (sourceRemainingPermutationPrefix D
        r.permutation r.position.castSucc)
      (sourceRemainingPermutationCoordinate D
        r.permutation r.position)
      r.history *
    fullCoordinateBaseWinIndicator G D
      (sourceRemainingPermutationPrefix D
        r.permutation r.position.castSucc)
      (sourceRemainingPermutationCoordinate D
        r.permutation r.position)
      r.history r.aliceAnswer r.bobAnswer

end

noncomputable section

open scoped BigOperators

section FiniteSamples

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]

def postselectionMass
    (law : FiniteEventLaw Ω) (wins : ι → Ω → Bool)
    (C : Finset ι) : ℝ :=
  law.eventMass (FiniteEventLaw.winEvent wins C)

def conditionalCoordinateFailure
    (law : FiniteEventLaw Ω) (wins : ι → Ω → Bool)
    (C : Finset ι) (i : ι) : ℝ :=
  FiniteEventLaw.failureMass law wins C i /
    postselectionMass law wins C

def uniformRemainingFailure
    (law : FiniteEventLaw Ω) (wins : ι → Ω → Bool)
    (C : Finset ι) : ℝ :=
  (∑ i ∈ Finset.univ \ C,
    conditionalCoordinateFailure law wins C i) /
    ((Finset.univ \ C).card : ℝ)

end FiniteSamples

section ActualRepeatedStrategy

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def repeatedPostselectionMass
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n)) (C : Finset (Fin n)) : ℝ :=
  postselectionMass (strategyEventLaw (G.repeat n) S)
    (repeatedCoordinateWin G n) C

end ActualRepeatedStrategy

end

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder

end

noncomputable section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048

section ActualFilters

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def postselectionLogCost
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) : ℝ :=
  Real.log (1 / repeatedPostselectionMass G n S D)

def answerLogCost
    {A B : Type*} [Fintype A] [Fintype B]
    {n : ℕ} (D : Finset (Fin n)) : ℝ :=
  (D.card : ℝ) *
    Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ))

def martingaleRate
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) : ℝ :=
  (postselectionLogCost G n S D +
      answerLogCost (A := A) (B := B) D) /
    ((Finset.univ \ D).card : ℝ)

end ActualFilters

section ActualPurificationHistories

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

end ActualPurificationHistories

end

noncomputable section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def fullCoordinateInsertedHiddenAliceEquiv
    {X : Type*} {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n) :
    ({j : Fin n // j ∈ fullHistoryRemaining n (insert i D) L} → X) ≃
      ({j : Fin n // j ∈ fullHistoryRemaining n D (insert i L)} → X) where
  toFun hidden j :=
    hidden ((fullHistoryRemainingInsertedEquiv D L i).symm j)
  invFun hidden j := hidden (fullHistoryRemainingInsertedEquiv D L i j)
  left_inv hidden := by
    funext j
    simp
  right_inv hidden := by
    funext j
    simp

def fullCoordinateAcceptedPostselectedMass
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n) : ℝ :=
  ∑ r : FullCoordinateRevealHistory X Y n D L i,
  ∑ α : {j : Fin n // j ∈ D} → A,
  ∑ β : {j : Fin n // j ∈ D} → B,
    fullCoordinateBaseWeight G D L i r *
      fullCoordinateBaseWinIndicator G D L i r α β *
      (∑ x : X, ∑ y : Y, G.questionWeight x y *
        (∑ a : A, ∑ b : B,
          (if G.predicate x y a b = true then 1 else 0) *
            bornTracePairing S.state.matrix
              (fullCoordinateAliceRefinementEffect
                G n S D L i r α x a)
              (fullCoordinateBobRefinementEffect
                G n S D L i r β y b)))

end

noncomputable section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def sourceHistoryAcceptedQuestionMass
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n)) (D : Finset (Fin n))
    (r : SourceHistoryFlag X Y A B D)
    (x : X) (y : Y) : ℝ :=
  ∑ a : A, ∑ b : B,
    (if G.predicate x y a b = true then 1 else 0) *
      bornTracePairing S.state.matrix
        (fullCoordinateAliceRefinementEffect G n S D
          (sourceRemainingPermutationPrefix D
            r.permutation r.position.castSucc)
          (sourceRemainingPermutationCoordinate D
            r.permutation r.position)
          r.history r.aliceAnswer x a)
        (fullCoordinateBobRefinementEffect G n S D
          (sourceRemainingPermutationPrefix D
            r.permutation r.position.castSucc)
          (sourceRemainingPermutationCoordinate D
            r.permutation r.position)
          r.history r.bobAnswer y b)

def sourceHistoryAcceptedMass
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n)) (D : Finset (Fin n)) : ℝ :=
  ∑ r : SourceHistoryFlag X Y A B D,
    sourceHistoryRaw G n D r *
      (∑ x : X, ∑ y : Y, G.questionWeight x y *
        sourceHistoryAcceptedQuestionMass G n S D r x y)

end

noncomputable section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

end

noncomputable section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048

section TaggedTensorBlocks

variable {R : Type*} [Fintype R]
variable {ι : R → Type*} [∀ r, Fintype (ι r)]

def taggedTensorVector
    (r : R) (z : EuclideanSpace ℂ (ι r × ι r)) :
    EuclideanSpace ℂ
      ((PUnit.{1} ⊕ (Σ r : R, ι r)) ×
        (PUnit.{1} ⊕ (Σ r : R, ι r))) := by
  classical
  exact toLp 2 fun q =>
    match q.1, q.2 with
    | .inr ⟨rA, a⟩, .inr ⟨rB, b⟩ =>
        if hA : rA = r then
          if hB : rB = r then
            z (hA ▸ a, hB ▸ b)
          else 0
        else 0
    | _, _ => 0

end TaggedTensorBlocks

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
open QuantumParallelRepetition.ClassicalSampling

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def weightedConditionalJoint
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (weight : κ → ℝ) (conditional : κ → ι → ℝ) :
    κ × ι → ℝ :=
  fun t => weight t.1 * conditional t.1 t.2

abbrev LocalQuestionContext
    (X Y : Type*) [Fintype X] [Fintype Y]
    {n : ℕ} (D : Finset (Fin n)) :=
  SourceRemainingCoordinate D × (X × Y)

def localQuestionWeight
    (G : Game X Y A B) (n : ℕ) (D : Finset (Fin n))
    (c : LocalQuestionContext X Y D) : ℝ :=
  G.questionWeight c.2.1 c.2.2 /
    (Fintype.card (SourceRemainingCoordinate D) : ℝ)

def conditionedEventDistribution
    {Ω : Type*} [Fintype Ω]
    (law : FiniteEventLaw Ω) (event : Finset Ω) : Ω → ℝ :=
  fun ω => if ω ∈ event then law.weight ω / law.eventMass event else 0

def repeatedConditionedOutcomeLaw
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) :
    StrategyOutcome
      (Fin n → X) (Fin n → Y)
      (Fin n → A) (Fin n → B) → ℝ :=
  conditionedEventDistribution
    (strategyEventLaw (G.repeat n) S)
    (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)

end

noncomputable section

open scoped BigOperators

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

def finiteUniformWeight (Z : Type*) [Fintype Z] : ℝ :=
  1 / (Fintype.card Z : ℝ)

def uniformFlagReference
    {Ω Z : Type*} [Fintype Ω] [Fintype Z]
    (prior : Ω → ℝ) : Ω × Z → ℝ :=
  fun t => prior t.1 * finiteUniformWeight Z

def finitePrefixMask
    {Ω Y : Type*} {h : ℕ} (base : Y)
    (k : Fin (h + 1)) :
    (Ω × (Fin h → Y)) → (Ω × (Fin h → Y)) :=
  fun t => (t.1, fun j => if j.val < k.val then t.2 j else base)

def finitePrefixRelativeEntropy
    {Ω Y : Type*} [Fintype Ω] [Fintype Y] {h : ℕ}
    (joint prior : Ω × (Fin h → Y) → ℝ)
    (base : Y) (k : Fin (h + 1)) : ℝ :=
  finiteRelativeEntropy
    (groupedMass (finitePrefixMask base k) joint)
    (groupedMass (finitePrefixMask base k) prior)

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

abbrev ConditionedAnswerFlag
    (A B : Type*) [Fintype A] [Fintype B]
    {n : ℕ} (D : Finset (Fin n)) :=
  ({i : Fin n // i ∈ D} → A) ×
    ({i : Fin n // i ∈ D} → B)

def repeatedConditionedAnswerFlag
    (G : Game X Y A B) (n : ℕ) (_S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (ω : StrategyOutcome
      (Fin n → X) (Fin n → Y)
      (Fin n → A) (Fin n → B)) :
    ConditionedAnswerFlag A B D :=
  (fun i => ω.2.2.1 i, fun i => ω.2.2.2 i)

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

abbrev ExactOutcome (X Y A B : Type*) (n : ℕ) :=
  StrategyOutcome (Fin n → X) (Fin n → Y)
    (Fin n → A) (Fin n → B)

abbrev ExactJointOutcome
    (X Y A B : Type*) {n : ℕ} (D : Finset (Fin n)) :=
  ExactRemainingSeed D × ExactOutcome X Y A B n

def exactPostselectedJointLaw
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (q : ExactJointOutcome X Y A B D) : ℝ :=
  exactSeedWeight q.1 *
    repeatedConditionedOutcomeLaw G n S D q.2

def exactSourcePushforward
    {K : Type*} [Fintype K]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (projection : ExactJointOutcome X Y A B D → K) :
    K → ℝ :=
  groupedMass projection (exactPostselectedJointLaw G n S D)

end

end QuantumParallelRepetition

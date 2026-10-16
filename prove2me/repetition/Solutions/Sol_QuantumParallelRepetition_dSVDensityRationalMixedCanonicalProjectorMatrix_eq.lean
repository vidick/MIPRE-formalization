/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Repetition/TenProofs/QuantumParallelRepetition/Part02.lean (solution of QuantumParallelRepetition.dSVDensityRationalMixedCanonicalProjectorMatrix_eq);
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
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sigma
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

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
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
theorem coherentSharedRandomControlledUnitary_inv
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (U : ι → Matrix.unitaryGroup κ ℂ) :
    (coherentSharedRandomControlledUnitary U)⁻¹ =
      coherentSharedRandomControlledUnitary
        (fun i => (U i)⁻¹) := by
  classical
  apply Subtype.ext
  ext ⟨i, x⟩ ⟨j, y⟩
  change
    star ((coherentSharedRandomControlledUnitary U :
      Matrix (Σ _ : ι, κ) (Σ _ : ι, κ) ℂ) ⟨j, y⟩ ⟨i, x⟩) =
      (coherentSharedRandomControlledUnitary
        (fun i => (U i)⁻¹) :
        Matrix (Σ _ : ι, κ) (Σ _ : ι, κ) ℂ) ⟨i, x⟩ ⟨j, y⟩
  by_cases same : i = j
  · subst j
    simp [coherentSharedRandomControlledUnitary,
      Matrix.blockDiagonal'_apply]
  · have reversed : j ≠ i := Ne.symm same
    simp [coherentSharedRandomControlledUnitary,
      Matrix.blockDiagonal'_apply, same, reversed]
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
theorem spectralPartitionPOVM_effect_eq_spectralDiagonal
    {κ ι : Type*}
    [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (F : Matrix ι ι ℂ) (positive : F.PosSemidef)
    (bin : ι → κ) (outcome : κ) :
    (spectralPartitionPOVM F positive bin).effect outcome =
      spectralConjugationCLM positive.isHermitian.eigenvectorUnitary
        (Matrix.diagonal fun i : ι =>
          if bin i = outcome then (1 : ℂ) else 0) := by
  classical
  let selected : Finset ι :=
    Finset.univ.filter fun i : ι => bin i = outcome
  have diagonal :
      (∑ i ∈ selected,
        Matrix.diagonal (Pi.single i (1 : ℂ))) =
        Matrix.diagonal fun i : ι =>
          if bin i = outcome then (1 : ℂ) else 0 := by
    ext i j
    by_cases same : i = j
    · subst j
      simp [Matrix.sum_apply, selected, Pi.single_apply]
    · simp [Matrix.sum_apply, same]
  change
    (∑ i ∈ selected,
      spectralConjugationCLM positive.isHermitian.eigenvectorUnitary
        (Matrix.diagonal (Pi.single i (1 : ℂ)))) = _
  rw [← map_sum, diagonal]
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
theorem dSVUniformDensityPhysicalSpectralAliceCopy_inv
    {N d : ℕ} (ξ : BipartiteUnitVector d) :
    (dSVUniformDensityAliceHistorySpectralCopy
      (N := N) ξ)⁻¹ =
      coherentSharedRandomControlledUnitary
        (fun _ : Fin N =>
          dSVUniformDensityThresholdLeftBobBasis ξ) := by
  unfold dSVUniformDensityAliceHistorySpectralCopy
  rw [coherentSharedRandomControlledUnitary_inv]
  simp
end
end QuantumParallelRepetition

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
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
theorem dSVDensityRationalCanonicalPrefixMask_transpose
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) :
    (dSVDensityRationalCanonicalPrefixMask
      w N ξ).transpose =
      dSVDensityRationalCanonicalPrefixMask w N ξ := by
  classical
  simp [dSVDensityRationalCanonicalPrefixMask]
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
theorem dSVDensityRationalPhysicalAcceptedProjector_eq_spectralMask
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) :
    Matrix.blockDiagonal'
        (dSVDensityRationalPhysicalProjector w ξ) =
      (((dSVUniformDensityAliceHistorySpectralCopy
        (N := N) ξ)⁻¹ : Matrix.unitaryGroup
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
          Matrix (DSVUniformDensityThresholdLocalIndex N d)
            (DSVUniformDensityThresholdLocalIndex N d) ℂ) *
        dSVDensityRationalCanonicalPrefixMask w N ξ *
        (dSVUniformDensityAliceHistorySpectralCopy
          (N := N) ξ :
          Matrix (DSVUniformDensityThresholdLocalIndex N d)
            (DSVUniformDensityThresholdLocalIndex N d) ℂ) := by
  classical
  rw [dSVUniformDensityPhysicalSpectralAliceCopy_inv]
  change
    Matrix.blockDiagonal'
      (dSVDensityRationalPhysicalProjector w ξ) =
      Matrix.blockDiagonal'
          (fun _ : Fin N =>
            (dSVUniformDensityThresholdLeftBobBasis ξ :
              Matrix (Fin d) (Fin d) ℂ)) *
        Matrix.blockDiagonal'
          (fun k : Fin N =>
            Matrix.diagonal fun i : Fin d =>
              if dSVDensityRationalProjectiveThresholdBin w N k
                  ((dSVSoftBobLeftReducedDensity_posSemidef
                    ξ).isHermitian.eigenvalues i) = true
              then (1 : ℂ) else 0) *
        Matrix.blockDiagonal'
          (fun _ : Fin N =>
            (((dSVUniformDensityThresholdLeftBobBasis ξ)⁻¹ :
              Matrix.unitaryGroup (Fin d) ℂ) :
                Matrix (Fin d) (Fin d) ℂ))
  rw [← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul]
  apply congrArg Matrix.blockDiagonal'
  funext k
  unfold dSVDensityRationalPhysicalProjector
    dSVDensityRationalLeftProjectiveThresholdPOVM
    dSVDensityRationalProjectiveThresholdPOVM
  rw [spectralPartitionPOVM_effect_eq_spectralDiagonal]
  rfl
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
theorem dSVDensityRationalMixedCanonicalCrossGauge_eq
    {d : ℕ} (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) :
    (((dSVUniformDensityBobHistoryCopyBasis
        (N := N) ζ)⁻¹ : Matrix.unitaryGroup
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
      Matrix (DSVUniformDensityThresholdLocalIndex N d)
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) *
      (dSVUniformDensityBobHistoryCopyBasis
        (N := N) ξ :
        Matrix (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) =
      dSVDensityRationalMixedCanonicalCrossMatrix N ξ ζ := by
  rw [← dSVUniformDensityPhysicalSpectralAliceCopy_inv_transpose ζ,
    ← dSVUniformDensityPhysicalSpectralAliceCopy_transpose ξ,
    ← Matrix.transpose_mul]
  unfold dSVDensityRationalMixedCanonicalCrossMatrix
  congr 1
  rw [dSVUniformDensityPhysicalSpectralAliceCopy_inv]
  change
    Matrix.blockDiagonal' (fun _ : Fin N =>
      (((dSVUniformDensityThresholdLeftBobBasis ξ)⁻¹ :
        Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ)) *
      Matrix.blockDiagonal' (fun _ : Fin N =>
        (dSVUniformDensityThresholdLeftBobBasis ζ :
          Matrix (Fin d) (Fin d) ℂ)) =
      Matrix.blockDiagonal' (fun _ : Fin N =>
        (unitaryBasisOverlap
          (dSVSoftBobLeftReducedDensity_posSemidef
            ξ).isHermitian.eigenvectorUnitary
          (dSVSoftBobLeftReducedDensity_posSemidef
            ζ).isHermitian.eigenvectorUnitary :
          Matrix (Fin d) (Fin d) ℂ))
  rw [← Matrix.blockDiagonal'_mul]
  rfl
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
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) :
    (((dSVUniformDensityBobHistoryCopyBasis
        (N := N) ζ)⁻¹ : Matrix.unitaryGroup
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
      Matrix (DSVUniformDensityThresholdLocalIndex N d)
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) *
      ((Matrix.blockDiagonal'
          (fun k : Fin N =>
            dSVDensityRationalPhysicalProjector w ξ k) *
        Matrix.blockDiagonal'
          (fun k : Fin N =>
            dSVDensityRationalPhysicalProjector w ζ k)).transpose) *
      (dSVUniformDensityAliceHistorySpectralCopy
        (N := N) ξ :
        Matrix (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ).transpose =
      dSVDensityRationalCanonicalPrefixMask w N ζ *
        dSVDensityRationalMixedCanonicalCrossMatrix N ξ ζ *
        dSVDensityRationalCanonicalPrefixMask w N ξ := by
  let S : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
    dSVUniformDensityAliceHistorySpectralCopy (N := N) ξ
  let X : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
    dSVUniformDensityBobHistoryCopyBasis (N := N) ξ
  let Z : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
    dSVUniformDensityBobHistoryCopyBasis (N := N) ζ
  let XI : Matrix
      (DSVUniformDensityThresholdLocalIndex N d)
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
    ((X⁻¹ : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
      Matrix (DSVUniformDensityThresholdLocalIndex N d)
        (DSVUniformDensityThresholdLocalIndex N d) ℂ)
  let ZI : Matrix
      (DSVUniformDensityThresholdLocalIndex N d)
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
    ((Z⁻¹ : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
      Matrix (DSVUniformDensityThresholdLocalIndex N d)
        (DSVUniformDensityThresholdLocalIndex N d) ℂ)
  let M : Matrix
      (DSVUniformDensityThresholdLocalIndex N d)
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
    dSVDensityRationalCanonicalPrefixMask w N ξ
  let R : Matrix
      (DSVUniformDensityThresholdLocalIndex N d)
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
    dSVDensityRationalCanonicalPrefixMask w N ζ
  have physical_x :
      Matrix.blockDiagonal'
          (fun k : Fin N =>
            dSVDensityRationalPhysicalProjector w ξ k) =
        (((S⁻¹ : Matrix.unitaryGroup
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
          Matrix (DSVUniformDensityThresholdLocalIndex N d)
            (DSVUniformDensityThresholdLocalIndex N d) ℂ)) *
          M * (S : Matrix _ _ ℂ) :=
    dSVDensityRationalPhysicalAcceptedProjector_eq_spectralMask
      w N ξ
  have physical_z :
      Matrix.blockDiagonal'
          (fun k : Fin N =>
            dSVDensityRationalPhysicalProjector w ζ k) =
        ((((dSVUniformDensityAliceHistorySpectralCopy
          (N := N) ζ)⁻¹ : Matrix.unitaryGroup
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
          Matrix (DSVUniformDensityThresholdLocalIndex N d)
            (DSVUniformDensityThresholdLocalIndex N d) ℂ)) *
          R * (dSVUniformDensityAliceHistorySpectralCopy
            (N := N) ζ : Matrix _ _ ℂ) :=
    dSVDensityRationalPhysicalAcceptedProjector_eq_spectralMask
      w N ζ
  have transpose_x :
      (S : Matrix
        (DSVUniformDensityThresholdLocalIndex N d)
        (DSVUniformDensityThresholdLocalIndex N d) ℂ).transpose =
        (X : Matrix
          (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) :=
    dSVUniformDensityPhysicalSpectralAliceCopy_transpose
      (N := N) ξ
  have transpose_z :
      (dSVUniformDensityAliceHistorySpectralCopy
          (N := N) ζ : Matrix
            (DSVUniformDensityThresholdLocalIndex N d)
            (DSVUniformDensityThresholdLocalIndex N d) ℂ).transpose =
        (Z : Matrix
          (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) :=
    dSVUniformDensityPhysicalSpectralAliceCopy_transpose
      (N := N) ζ
  have inverse_x :
      (((S⁻¹ : Matrix.unitaryGroup
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
        Matrix (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ)).transpose =
        (((X⁻¹ : Matrix.unitaryGroup
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
          Matrix (DSVUniformDensityThresholdLocalIndex N d)
            (DSVUniformDensityThresholdLocalIndex N d) ℂ)) :=
    dSVUniformDensityPhysicalSpectralAliceCopy_inv_transpose
      (N := N) ξ
  have inverse_z :
      ((((dSVUniformDensityAliceHistorySpectralCopy
        (N := N) ζ)⁻¹ : Matrix.unitaryGroup
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
        Matrix (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ)).transpose =
        (((Z⁻¹ : Matrix.unitaryGroup
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
          Matrix (DSVUniformDensityThresholdLocalIndex N d)
            (DSVUniformDensityThresholdLocalIndex N d) ℂ)) :=
    dSVUniformDensityPhysicalSpectralAliceCopy_inv_transpose
      (N := N) ζ
  have cancel_x :
      XI * (X : Matrix
        (DSVUniformDensityThresholdLocalIndex N d)
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) = 1 := by
    change
      star (X : Matrix
        (DSVUniformDensityThresholdLocalIndex N d)
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) *
        (X : Matrix
          (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) = 1
    exact (Matrix.mem_unitaryGroup_iff').mp X.property
  have cancel_z :
      ZI * (Z : Matrix
        (DSVUniformDensityThresholdLocalIndex N d)
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) = 1 := by
    change
      star (Z : Matrix
        (DSVUniformDensityThresholdLocalIndex N d)
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) *
        (Z : Matrix
          (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) = 1
    exact (Matrix.mem_unitaryGroup_iff').mp Z.property
  change
    ZI *
      ((Matrix.blockDiagonal'
          (fun k : Fin N =>
            dSVDensityRationalPhysicalProjector w ξ k) *
        Matrix.blockDiagonal'
          (fun k : Fin N =>
            dSVDensityRationalPhysicalProjector w ζ k)).transpose) *
      (S : Matrix _ _ ℂ).transpose =
        R * dSVDensityRationalMixedCanonicalCrossMatrix N ξ ζ * M
  calc
    _ = ((ZI * (Z : Matrix _ _ ℂ)) * R) *
        (ZI * (X : Matrix _ _ ℂ)) *
        (M * (XI * (X : Matrix _ _ ℂ))) := by
          rw [physical_x, physical_z]
          dsimp only [XI, ZI]
          simp only [Matrix.transpose_mul,
            dSVDensityRationalCanonicalPrefixMask_transpose,
            transpose_x, transpose_z, inverse_x, inverse_z,
            Matrix.mul_assoc, M, R]
    _ = R * (ZI * (X : Matrix _ _ ℂ)) * M := by
          rw [cancel_x, cancel_z]
          simp
    _ = _ := by
      dsimp only [ZI]
      rw [dSVDensityRationalMixedCanonicalCrossGauge_eq N ξ ζ]
end QuantumParallelRepetition

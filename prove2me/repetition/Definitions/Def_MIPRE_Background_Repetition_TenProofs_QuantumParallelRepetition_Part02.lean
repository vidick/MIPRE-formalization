/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Repetition/TenProofs/QuantumParallelRepetition/Part02.lean (definition bundle: declarations the uploaded statements rest on);
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
import Theorems.Thm_QuantumParallelRepetition_dSVProjectorComplement_posSemidef
import Theorems.Thm_QuantumParallelRepetition_embezzlementState_norm
import Theorems.Thm_QuantumParallelRepetition_exists_proofTargetCanonicalSpectralSchmidtDecomposition
import Theorems.Thm_QuantumParallelRepetition_positiveDensity_eigenvalues_sum
import Theorems.Thm_QuantumParallelRepetition_scalarResolventFilter_memLp_two
import Theorems.Thm_QuantumParallelRepetition_schmidtVector_apply
import Theorems.Thm_QuantumParallelRepetition_schmidtVector_norm_sq
import Theorems.Thm_QuantumParallelRepetition_spectralPartitionPOVM_projective
import Theorems.Thm_QuantumParallelRepetition_spectralPurificationFilter_memLp_two
import Theorems.Thm_QuantumParallelRepetition_targetReducedDensity_trace

set_option autoImplicit true

namespace QuantumParallelRepetition

open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset

noncomputable section

open scoped BigOperators Kronecker ComplexOrder MatrixOrder

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

def dSVGlobalProjectorBinaryPOVM
    {κ d : Type*} [Fintype κ] [Fintype d]
    [DecidableEq κ] [DecidableEq d]
    (P : κ → Matrix d d ℂ)
    (positive : ∀ k, (P k).PosSemidef)
    (complement : ∀ k, (1 - P k).PosSemidef) :
    POVM Bool (Σ _ : κ, d) where
  effect b := Matrix.blockDiagonal' fun k =>
    if b then P k else 1 - P k
  positive b := by
    apply posSemidef_blockDiagonal'
    intro k
    cases b
    · exact complement k
    · exact positive k
  complete := by
    classical
    rw [Fintype.sum_bool]
    ext ⟨k, i⟩ ⟨l, j⟩
    by_cases same : k = l
    · subst l
      simp [Matrix.blockDiagonal'_apply, Matrix.one_apply,
        Matrix.sub_apply]
    · simp [Matrix.blockDiagonal'_apply, same]

end

noncomputable section

open scoped BigOperators

def dSVRationalSoftPass (t x : ℝ) : ℝ :=
  x / (x + t)

theorem dSVRationalSoftPass_mem_unit
    {t x : ℝ} (positive : 0 < t) (nonnegative : 0 ≤ x) :
    0 ≤ dSVRationalSoftPass t x ∧
      dSVRationalSoftPass t x ≤ 1 := by
  unfold dSVRationalSoftPass
  have denominator : 0 < x + t := by linarith
  constructor
  · exact div_nonneg nonnegative denominator.le
  · apply (div_le_iff₀ denominator).mpr
    linarith

end

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
set_option maxRecDepth 3072

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

def dSVSoftBobLeftReducedDensity
    {d : ℕ} (ζ : BipartiteUnitVector d) :
    Matrix (Fin d) (Fin d) ℂ :=
  targetCoefficientMatrix ζ *
    (targetCoefficientMatrix ζ).conjTranspose

theorem dSVSoftBobLeftReducedDensity_posSemidef
    {d : ℕ} (ζ : BipartiteUnitVector d) :
    (dSVSoftBobLeftReducedDensity ζ).PosSemidef := by
  exact Matrix.posSemidef_self_mul_conjTranspose
    (targetCoefficientMatrix ζ)

theorem dSVSoftBobLeftReducedDensity_trace
    {d : ℕ} (ζ : BipartiteUnitVector d) :
    Matrix.trace (dSVSoftBobLeftReducedDensity ζ) = 1 := by
  unfold dSVSoftBobLeftReducedDensity
  calc
    Matrix.trace
        (targetCoefficientMatrix ζ *
          (targetCoefficientMatrix ζ).conjTranspose) =
        Matrix.trace
          ((targetCoefficientMatrix ζ).conjTranspose *
            targetCoefficientMatrix ζ) :=
      Matrix.trace_mul_comm _ _
    _ = 1 := targetReducedDensity_trace ζ

def dSVOriginalComputationalReindexedUnitary
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {D : ℕ} (e : ι ≃ Fin D)
    (U : Matrix.unitaryGroup ι ℂ) :
    Matrix.unitaryGroup (Fin D) ℂ := by
  classical
  let M : Matrix ι ι ℂ := U.val
  refine ⟨(Matrix.reindex e e) M, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff']
  have compatible :
      star ((Matrix.reindex e e) M) =
        (Matrix.reindex e e) (star M) := by
    ext i j
    simp [Matrix.star_eq_conjTranspose,
      Matrix.reindex_apply, Matrix.conjTranspose_apply]
  rw [compatible]
  change (Matrix.reindexRingEquiv ℂ e) (star M) *
    (Matrix.reindexRingEquiv ℂ e) M = 1
  rw [← (Matrix.reindexRingEquiv ℂ e).map_mul,
    (Matrix.mem_unitaryGroup_iff').mp U.property]
  exact (Matrix.reindexRingEquiv ℂ e).map_one

end

noncomputable section

open scoped BigOperators ComplexOrder

def dSVHeterogeneousRealPrefix
    (continuation : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∏ i ∈ Finset.range k, continuation i

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

abbrev DSVUniformDensityThresholdLocalIndex
    (N d : ℕ) :=
  Σ _ : Fin N, Fin d

def dSVUniformDensityThresholdSharedState
    (N d : ℕ) :
    EuclideanSpace ℂ
      (DSVUniformDensityThresholdLocalIndex N d ×
        DSVUniformDensityThresholdLocalIndex N d) :=
  sharedThresholdResource (d := Fin d)
    (fun _ : Fin N => (1 : ℝ))

theorem dSVUniformDensityThresholdSharedState_norm
    {N d : ℕ} (grid : 0 < N) (dimension : 0 < d) :
    ‖dSVUniformDensityThresholdSharedState N d‖ = 1 := by
  exact sharedThresholdResource_norm
    (fun _ : Fin N => (1 : ℝ))
    ⟨0, grid⟩ ⟨0, dimension⟩ (by norm_num)

def dSVUniformDensityThresholdSharedDensity
    {N d : ℕ} (grid : 0 < N) (dimension : 0 < d) :
    DensityMatrix
      (DSVUniformDensityThresholdLocalIndex N d ×
        DSVUniformDensityThresholdLocalIndex N d) :=
  pureDensityMatrix
    (dSVUniformDensityThresholdSharedState N d)
    (dSVUniformDensityThresholdSharedState_norm
      grid dimension)

abbrev DSVUniformDensityIndependentHistoryLocalIndex
    (L N d : ℕ) :=
  Fin L → DSVUniformDensityThresholdLocalIndex N d

def dSVUniformDensityIndependentHistoryPairReindex
    (L N d : ℕ) :
    EuclideanSpace ℂ
      (Fin L →
        (DSVUniformDensityThresholdLocalIndex N d ×
          DSVUniformDensityThresholdLocalIndex N d)) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ
        (DSVUniformDensityIndependentHistoryLocalIndex
            L N d ×
          DSVUniformDensityIndependentHistoryLocalIndex
            L N d) := by
  classical
  exact LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    bilateralWorkPairEquiv.symm

def dSVUniformDensityIndependentSharedState
    (L N d : ℕ) :
    EuclideanSpace ℂ
      (DSVUniformDensityIndependentHistoryLocalIndex L N d ×
        DSVUniformDensityIndependentHistoryLocalIndex L N d) :=
  dSVUniformDensityIndependentHistoryPairReindex L N d
    (finiteTensorVector
      (fun _ : Fin L =>
        dSVUniformDensityThresholdSharedState N d))

end

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
set_option maxRecDepth 3072

def dSVUniformDensitySpectralAtomDiscrepancy
    {d : ℕ} (ξ ζ : BipartiteUnitVector d) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d,
    |targetCanonicalSchmidtCoefficient ξ i ^ 2 -
      targetCanonicalSchmidtCoefficient ζ j ^ 2| *
      spectralAtomOverlap
        (targetReducedDensity ξ)
        (targetReducedDensity ζ)
        (targetReducedDensity_posSemidef ξ)
        (targetReducedDensity_posSemidef ζ) i j

def dSVUniformDensitySchmidtSumMass
    {d : ℕ} (ξ ζ : BipartiteUnitVector d) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d,
    (targetCanonicalSchmidtCoefficient ξ i +
      targetCanonicalSchmidtCoefficient ζ j) ^ 2 *
      spectralAtomOverlap
        (targetReducedDensity ξ)
        (targetReducedDensity ζ)
        (targetReducedDensity_posSemidef ξ)
        (targetReducedDensity_posSemidef ζ) i j

end

noncomputable section

open scoped BigOperators

namespace ClassicalSampling

variable {α : Type*} [Fintype α] [DecidableEq α]

def markedFirst (rank : α ≃ Fin (Fintype.card α))
    (marked : Finset α) (nonempty : marked.Nonempty)
    (permutation : Equiv.Perm α) : α :=
  permutation.symm
    (rank.symm
      ((marked.image (fun a => rank (permutation a))).min'
        (nonempty.image (fun a => rank (permutation a)))))

def firstFiber (rank : α ≃ Fin (Fintype.card α))
    (marked : Finset α) (nonempty : marked.Nonempty)
    (a : α) : Finset (Equiv.Perm α) :=
  Finset.univ.filter fun permutation =>
    markedFirst rank marked nonempty permutation = a

def uniformPermutationProbability (event : Equiv.Perm α → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter fun permutation : Equiv.Perm α =>
      event permutation).card : ℝ) / Fintype.card (Equiv.Perm α)

def markedTotalVariation (left right : Finset α) : ℝ :=
  (((left \ right) ∪ (right \ left)).card : ℝ) /
    (2 * (left.card : ℝ))

section RationalMarks

variable {β : Type*} [Fintype β] [DecidableEq β]

def rationalMarked (denominator : ℕ) (numerator : β → ℕ) :
    Finset (β × Fin denominator) := by
  classical
  exact Finset.univ.filter fun point =>
    point.2.val < numerator point.1

end RationalMarks

end ClassicalSampling

namespace Pinsker

def pinskerScalarGap (x : ℝ) : ℝ :=
  InformationTheory.klFun x - 3 * (x - 1) ^ 2 / (2 * (x + 2))

def finiteRelativeEntropy {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) : ℝ :=
  ∑ i, q i * InformationTheory.klFun (p i / q i)

def finiteTotalVariation {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) : ℝ :=
  (∑ i, |p i - q i|) / 2

end Pinsker

namespace ClassicalInformation

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalSampling

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def distributionFloorNumerator (denominator : ℕ) (p : ι → ℝ) : ι → ℕ :=
  fun i => Nat.floor (p i * (denominator : ℝ))

def distributionFloorResidual (denominator : ℕ) (p : ι → ℝ) : ℕ :=
  denominator - ∑ i, distributionFloorNumerator denominator p i

def distributionRoundedNumerator
    (base : ι) (denominator : ℕ) (p : ι → ℝ) : ι → ℕ :=
  fun i => distributionFloorNumerator denominator p i +
    if i = base then distributionFloorResidual denominator p else 0

def distributionFloorProbability
    (denominator : ℕ) (p : ι → ℝ) : ι → ℝ :=
  fun i => (distributionFloorNumerator denominator p i : ℝ) / denominator

def distributionRoundedProbability
    (base : ι) (denominator : ℕ) (p : ι → ℝ) : ι → ℝ :=
  fun i =>
    (distributionRoundedNumerator base denominator p i : ℝ) / denominator

section CoarseGraining

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def groupedMass (map : ι → κ) (p : ι → ℝ) (j : κ) : ℝ :=
  ∑ i ∈ (Finset.univ.filter fun i => map i = j), p i

end CoarseGraining

section JointChainRule

variable {κ : Type*} [Fintype κ]

def jointFirstMarginal (joint : ι × κ → ℝ) : ι → ℝ :=
  fun i => ∑ j : κ, joint (i, j)

def jointConditional (joint : ι × κ → ℝ) (i : ι) : κ → ℝ :=
  fun j => joint (i, j) / jointFirstMarginal joint i

end JointChainRule

section SharedPermutationSampling

def rationalPermutationOutput
    (denominator : ℕ) (numerator : ι → ℕ)
    (nonempty : (rationalMarked denominator numerator).Nonempty)
    (permutation : Equiv.Perm (ι × Fin denominator)) : ι :=
  (markedFirst (Fintype.equivFin (ι × Fin denominator))
    (rationalMarked denominator numerator) nonempty permutation).1

end SharedPermutationSampling

end ClassicalInformation

end

noncomputable section

open WithLp
open scoped BigOperators ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
set_option maxRecDepth 3072

def dSVUniformLeftDensityConjugateSwapVector
    {d : ℕ} (z : EuclideanSpace ℂ (Fin d × Fin d)) :
    EuclideanSpace ℂ (Fin d × Fin d) :=
  toLp 2 (fun ij : Fin d × Fin d => star (z (ij.2, ij.1)))

theorem dSVUniformLeftDensityConjugateSwapVector_norm
    {d : ℕ} (z : EuclideanSpace ℂ (Fin d × Fin d)) :
    ‖dSVUniformLeftDensityConjugateSwapVector z‖ = ‖z‖ := by
  have squares :
      ‖dSVUniformLeftDensityConjugateSwapVector z‖ ^ 2 =
        ‖z‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      Fintype.sum_prod_type, Fintype.sum_prod_type]
    change
      (∑ i : Fin d, ∑ j : Fin d,
        ‖star (z (j, i))‖ ^ 2) =
        ∑ i : Fin d, ∑ j : Fin d, ‖z (i, j)‖ ^ 2
    simp_rw [norm_star]
    rw [Finset.sum_comm]
  nlinarith [norm_nonneg
    (dSVUniformLeftDensityConjugateSwapVector z),
    norm_nonneg z]

def dSVUniformLeftDensityConjugateSwap
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    BipartiteUnitVector d :=
  ⟨dSVUniformLeftDensityConjugateSwapVector ξ.val,
    (dSVUniformLeftDensityConjugateSwapVector_norm ξ.val).trans
      ξ.property⟩

def dSVUniformLeftDensitySchmidtCoefficient
    {d : ℕ} (ξ : BipartiteUnitVector d)
    (i : Fin d) : ℝ :=
  Real.sqrt
    ((dSVSoftBobLeftReducedDensity_posSemidef ξ).isHermitian.eigenvalues i)

def dSVUniformLeftDensitySpectralAtomDiscrepancy
    {d : ℕ} (ξ ζ : BipartiteUnitVector d) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d,
    |dSVUniformLeftDensitySchmidtCoefficient ξ i ^ 2 -
      dSVUniformLeftDensitySchmidtCoefficient ζ j ^ 2| *
      spectralAtomOverlap
        (dSVSoftBobLeftReducedDensity ξ)
        (dSVSoftBobLeftReducedDensity ζ)
        (dSVSoftBobLeftReducedDensity_posSemidef ξ)
        (dSVSoftBobLeftReducedDensity_posSemidef ζ) i j

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

def dSVUniformDensityThresholdGrid
    (N : ℕ) (k : Fin N) : ℝ :=
  finiteUniformThresholdGrid
    (1 / (N : ℝ)) (1 + 1 / (N : ℝ)) N k

theorem dSVUniformDensityThresholdGrid_apply
    {N : ℕ} (positive : 0 < N) (k : Fin N) :
    dSVUniformDensityThresholdGrid N k =
      ((k.val : ℝ) + 1) / (N : ℝ) := by
  have nonzero : (N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt positive)
  unfold dSVUniformDensityThresholdGrid
    finiteUniformThresholdGrid
  field_simp
  ring

def dSVUniformDensityThresholdWeight
    (N : ℕ) (_k : Fin N) : ℝ :=
  1 / (N : ℝ)

theorem dSVUniformDensityThresholdWeight_nonneg
    (N : ℕ) (k : Fin N) :
    0 ≤ dSVUniformDensityThresholdWeight N k := by
  unfold dSVUniformDensityThresholdWeight
  positivity

def dSVUniformDensityGridPrefix
    (N : ℕ) (density : ℝ) : ℝ :=
  ∑ k : Fin N,
    dSVUniformDensityThresholdWeight N k *
      if dSVUniformDensityThresholdGrid N k ≤ density
      then 1 else 0

theorem dSVUniformDensityGridPrefix_eq_count
    (N : ℕ) (density : ℝ) :
    dSVUniformDensityGridPrefix N density =
      ((Finset.univ.filter fun k : Fin N =>
        dSVUniformDensityThresholdGrid N k ≤ density).card : ℝ) /
        (N : ℝ) := by
  classical
  unfold dSVUniformDensityGridPrefix
    dSVUniformDensityThresholdWeight
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  simp [div_eq_mul_inv, mul_comm]

def dSVUniformDensityThresholdMismatch
    (N : ℕ) (alice bob : ℝ) : ℝ :=
  ∑ k : Fin N,
    dSVUniformDensityThresholdWeight N k *
      if ((dSVUniformDensityThresholdGrid N k ≤ alice) ↔
        (dSVUniformDensityThresholdGrid N k ≤ bob))
      then 0 else 1

theorem dSVUniformDensityThresholdGrid_count_eq_floor
    {N : ℕ} (positive : 0 < N)
    (density : ℝ) (nonnegative : 0 ≤ density) (bounded : density ≤ 1) :
    (Finset.univ.filter fun k : Fin N =>
      dSVUniformDensityThresholdGrid N k ≤ density).card =
        Nat.floor (density * (N : ℝ)) := by
  classical
  have gridpositive : (0 : ℝ) < N := by exact_mod_cast positive
  have densitypositive : 0 ≤ density * (N : ℝ) :=
    mul_nonneg nonnegative gridpositive.le
  have floor_bound : Nat.floor (density * (N : ℝ)) ≤ N := by
    have product : density * (N : ℝ) ≤ (N : ℝ) := by
      nlinarith
    have floor := Nat.floor_mono product
    simpa using floor
  have same :
      (Finset.univ.filter fun k : Fin N =>
        dSVUniformDensityThresholdGrid N k ≤ density) =
      (Finset.univ.filter fun k : Fin N =>
        k.val < Nat.floor (density * (N : ℝ))) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [dSVUniformDensityThresholdGrid_apply positive,
      div_le_iff₀ gridpositive]
    constructor
    · intro threshold
      have cast : ((k.val + 1 : ℕ) : ℝ) ≤ density * (N : ℝ) := by
        simpa using threshold
      have below := (Nat.le_floor_iff densitypositive).2 cast
      omega
    · intro below
      have integer : k.val + 1 ≤ Nat.floor (density * (N : ℝ)) := by
        omega
      have cast := (Nat.le_floor_iff densitypositive).1 integer
      simpa using cast
  rw [same, Fin.card_filter_val_lt, min_eq_right floor_bound]

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
set_option maxRecDepth 4096

end

noncomputable section

open scoped BigOperators Kronecker ComplexOrder MatrixOrder

end

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

attribute [local instance] Classical.propDecidable

def normalizeOrDefault (fallback z : E) : E :=
  if z = 0 then fallback else NormedSpace.normalize z

theorem normalizeOrDefault_norm
    (fallback z : E) (hfallback : ‖fallback‖ = 1) :
    ‖normalizeOrDefault fallback z‖ = 1 := by
  classical
  by_cases hz : z = 0
  · simp [normalizeOrDefault, hz, hfallback]
  · simp [normalizeOrDefault, hz, NormedSpace.norm_normalize hz]

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 3072

def dSVCanonicalFailureUnitRankFamily
    (d : ℕ) (positive : 0 < d) (rank : Fin (d + 1)) :
    BipartiteUnitVector d :=
  ⟨normalizeOrDefault
      (embezzlementState d)
      (dSVCanonicalFailurePrefix rank),
    normalizeOrDefault_norm
      (embezzlementState d)
      (dSVCanonicalFailurePrefix rank)
      (embezzlementState_norm d positive)⟩

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

def dSVUniformDensityThresholdLeftBobBasis
    {d : ℕ} (ζ : BipartiteUnitVector d) :
    Matrix.unitaryGroup (Fin d) ℂ :=
  (dSVSoftBobLeftReducedDensity_posSemidef ζ).isHermitian.eigenvectorUnitary

end

noncomputable section

open WithLp
open scoped BigOperators ComplexOrder MatrixOrder

def dSVUniformDensityPolarConjugateSwap
    {d : ℕ} (v : EuclideanSpace ℂ (Fin d × Fin d)) :
    EuclideanSpace ℂ (Fin d × Fin d) :=
  toLp 2 (fun q : Fin d × Fin d => star (v (q.2, q.1)))

theorem dSVUniformDensityPolarConjugateSwap_norm
    {d : ℕ} (v : EuclideanSpace ℂ (Fin d × Fin d)) :
    ‖dSVUniformDensityPolarConjugateSwap v‖ = ‖v‖ := by
  have squares :
      ‖dSVUniformDensityPolarConjugateSwap v‖ ^ 2 =
        ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp only [dSVUniformDensityPolarConjugateSwap,
      norm_star]
    exact Finset.sum_comm
  nlinarith [norm_nonneg
    (dSVUniformDensityPolarConjugateSwap v), norm_nonneg v]

def dSVUniformDensityPolarConjugateSwapTarget
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    BipartiteUnitVector d :=
  ⟨dSVUniformDensityPolarConjugateSwap ξ.val, by
    rw [dSVUniformDensityPolarConjugateSwap_norm]
    exact ξ.property⟩

theorem dSVUniformDensityPolarConjugateSwap_coefficient
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    targetCoefficientMatrix
        (dSVUniformDensityPolarConjugateSwapTarget ξ) =
      (targetCoefficientMatrix ξ).conjTranspose := by
  ext b a
  rfl

theorem dSVUniformDensityPolarConjugateSwap_reducedDensity
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    targetReducedDensity
        (dSVUniformDensityPolarConjugateSwapTarget ξ) =
      dSVSoftBobLeftReducedDensity ξ := by
  unfold targetReducedDensity
    dSVSoftBobLeftReducedDensity
  rw [dSVUniformDensityPolarConjugateSwap_coefficient]
  simp

def dSVUniformDensityPolarLeftSchmidtCoefficient
    {d : ℕ} (ξ : BipartiteUnitVector d)
    (i : Fin d) : ℝ :=
  Real.sqrt
    ((dSVSoftBobLeftReducedDensity_posSemidef ξ).isHermitian.eigenvalues i)

theorem exists_proofDSVUniformDensityPolarLeftCanonicalSchmidt
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    ∃ A : Matrix.unitaryGroup (Fin d) ℂ,
      ξ.val = schmidtVector
        (dSVUniformDensityPolarLeftSchmidtCoefficient ξ)
        A (dSVUniformDensityThresholdLeftBobBasis ξ) := by
  let χ := dSVUniformDensityPolarConjugateSwapTarget ξ
  have density : targetReducedDensity χ =
      dSVSoftBobLeftReducedDensity ξ :=
    dSVUniformDensityPolarConjugateSwap_reducedDensity ξ
  obtain ⟨V, decomposition⟩ :=
    exists_proofTargetCanonicalSpectralSchmidtDecomposition χ
  have canonical_basis :
      (targetReducedDensity_posSemidef χ).isHermitian.eigenvectorUnitary =
        dSVUniformDensityThresholdLeftBobBasis ξ := by
    unfold dSVUniformDensityThresholdLeftBobBasis
    simp only [density]
  have canonical_coefficient :
      targetCanonicalSchmidtCoefficient χ =
        dSVUniformDensityPolarLeftSchmidtCoefficient ξ := by
    funext i
    unfold targetCanonicalSchmidtCoefficient
      dSVUniformDensityPolarLeftSchmidtCoefficient
    simp only [density]
  rw [canonical_basis, canonical_coefficient] at decomposition
  refine ⟨conjugateUnitary V, ?_⟩
  ext ⟨a, b⟩
  have coordinate := congrArg
    (fun v : EuclideanSpace ℂ (Fin d × Fin d) => v (b, a))
    decomposition
  change star (ξ.val (a, b)) = _ at coordinate
  rw [schmidtVector_apply] at coordinate
  have unconjugated := congrArg star coordinate
  rw [schmidtVector_apply]
  simpa [map_sum, map_mul, conjugateUnitary_apply,
    mul_assoc, mul_left_comm, mul_comm] using unconjugated

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

def finiteTensorLocalUnitaryMatrix
    {ι β : Type*} [Fintype ι] [Fintype β] [DecidableEq β]
    (U : ι → Matrix.unitaryGroup β ℂ) :
    Matrix (ι → β) (ι → β) ℂ :=
  fun q r => ∏ i : ι, (U i : Matrix β β ℂ) (q i) (r i)

theorem finiteTensorLocalUnitaryMatrix_gram
    {ι β : Type*}
    [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (U : ι → Matrix.unitaryGroup β ℂ) :
    (finiteTensorLocalUnitaryMatrix U).conjTranspose *
        finiteTensorLocalUnitaryMatrix U = 1 := by
  classical
  ext p q
  change
    (∑ r : ι → β,
      star (∏ i : ι, (U i : Matrix β β ℂ) (r i) (p i)) *
        (∏ i : ι, (U i : Matrix β β ℂ) (r i) (q i))) =
      (1 : Matrix (ι → β) (ι → β) ℂ) p q
  have factor :
      (∑ r : ι → β,
        star (∏ i : ι, (U i : Matrix β β ℂ) (r i) (p i)) *
          (∏ i : ι, (U i : Matrix β β ℂ) (r i) (q i))) =
        ∏ i : ι, ∑ x : β,
          star ((U i : Matrix β β ℂ) x (p i)) *
            (U i : Matrix β β ℂ) x (q i) := by
    calc
      _ = ∑ r : ι → β, ∏ i : ι,
          (star ((U i : Matrix β β ℂ) (r i) (p i)) *
            (U i : Matrix β β ℂ) (r i) (q i)) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [star_prod, ← Finset.prod_mul_distrib]
      _ = _ :=
        (Fintype.prod_sum fun i : ι => fun x : β =>
          star ((U i : Matrix β β ℂ) x (p i)) *
            (U i : Matrix β β ℂ) x (q i)).symm
  rw [factor]
  have single (i : ι) :
      (∑ x : β,
        star ((U i : Matrix β β ℂ) x (p i)) *
          (U i : Matrix β β ℂ) x (q i)) =
        (1 : Matrix β β ℂ) (p i) (q i) := by
    have gram := (Matrix.mem_unitaryGroup_iff').mp
      (U i).property
    have entry := congrArg
      (fun M : Matrix β β ℂ => M (p i) (q i)) gram
    simpa [Matrix.star_eq_conjTranspose,
      Matrix.mul_apply, Matrix.conjTranspose_apply] using entry
  simp_rw [single]
  by_cases equal : p = q
  · subst q
    simp
  · have different : ∃ i : ι, p i ≠ q i := by
      by_contra h
      push Not at h
      exact equal (funext h)
    obtain ⟨i, hi⟩ := different
    have zero :
        (∏ j : ι, (1 : Matrix β β ℂ) (p j) (q j)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi]
    rw [zero]
    simp [equal]

def finiteTensorLocalUnitary
    {ι β : Type*}
    [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (U : ι → Matrix.unitaryGroup β ℂ) :
    Matrix.unitaryGroup (ι → β) ℂ := by
  refine ⟨finiteTensorLocalUnitaryMatrix U, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff',
    Matrix.star_eq_conjTranspose]
  exact finiteTensorLocalUnitaryMatrix_gram U

def controlledFiniteTensorLocalUnitary
    {Ω ι β : Type*}
    [Fintype Ω] [DecidableEq Ω]
    [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (U : Ω → ι → Matrix.unitaryGroup β ℂ) :
    Matrix.unitaryGroup (Σ _ : Ω, (ι → β)) ℂ :=
  coherentSharedRandomControlledUnitary
    (fun ω => finiteTensorLocalUnitary (U ω))

end

noncomputable section

open scoped BigOperators Kronecker ComplexOrder MatrixOrder

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

abbrev DSVUniformDensityThresholdWholeHistoryLocalIndex
    (N d L : ℕ) :=
  Σ _ : Fin (L + 1),
    Fin (L + 1) → DSVUniformDensityThresholdLocalIndex N d

abbrev DSVUniformDensityThresholdWholeHistoryCatalystIndex
    (N d L : ℕ) :=
  Fin N × (Fin (L + 1) ×
    (Fin L → DSVUniformDensityThresholdLocalIndex N d))

def dSVUniformDensityThresholdWholeHistorySharedState
    (N d L : ℕ) :
    EuclideanSpace ℂ
      (DSVUniformDensityThresholdWholeHistoryLocalIndex N d L ×
        DSVUniformDensityThresholdWholeHistoryLocalIndex N d L) :=
  sharedThresholdResource
    (d := Fin (L + 1) →
      DSVUniformDensityThresholdLocalIndex N d)
    (fun flag : Fin (L + 1) =>
      if flag.val = 0 then (1 : ℝ) else 0)

def dSVUniformDensityThresholdWholeHistoryTargetSplitEquiv
    (N d L : ℕ) :
    DSVUniformDensityThresholdWholeHistoryLocalIndex N d L ≃
      (Fin d ×
        DSVUniformDensityThresholdWholeHistoryCatalystIndex
          N d L) where
  toFun q :=
    ((q.2 0).2,
      ((q.2 0).1, (q.1, fun j => q.2 j.succ)))
  invFun q :=
    ⟨q.2.2.1,
      Fin.cons (⟨q.2.1, q.1⟩ :
        DSVUniformDensityThresholdLocalIndex N d)
        q.2.2.2⟩
  left_inv := by
    rintro ⟨flag, history⟩
    change
      (⟨flag, Fin.cons (history 0) (fun j => history j.succ)⟩ :
        DSVUniformDensityThresholdWholeHistoryLocalIndex
          N d L) = ⟨flag, history⟩
    congr 1
    exact Fin.cons_self_tail history
  right_inv := by
    rintro ⟨target, threshold, flag, history⟩
    simp

def dSVUniformDensityAliceHistorySpectralCopy
    {N d : ℕ} (ξ : BipartiteUnitVector d) :
    Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
  coherentSharedRandomControlledUnitary
    (fun _ : Fin N =>
      (dSVUniformDensityThresholdLeftBobBasis ξ)⁻¹)

def dSVUniformDensityBobHistoryCopyBasis
    {N d : ℕ} (ζ : BipartiteUnitVector d) :
    Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
  coherentSharedRandomControlledUnitary
    (fun _ : Fin N =>
      conjugateUnitary
        (dSVUniformDensityThresholdLeftBobBasis ζ))

end

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def scalarPurificationLp (z : ℝ) (hz : 0 ≤ z) :
    Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) :=
  ((scalarResolventFilter_memLp_two hz).ofReal (K := ℂ)).toLp
    (fun s : ℝ => ((z / (z + s) : ℝ) : ℂ))

theorem scalarPurificationLp_coeFn
    (z : ℝ) (hz : 0 ≤ z) :
    (scalarPurificationLp z hz : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)]
      (fun s : ℝ => ((z / (z + s) : ℝ) : ℂ)) :=
  ((scalarResolventFilter_memLp_two hz).ofReal
    (K := ℂ)).coeFn_toLp

def commonPurificationGenerator
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) :
    Sum (ι × d) d → Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))
  | .inl (i, k) =>
      scalarPurificationLp
        ((positive i).isHermitian.eigenvalues k)
        ((positive i).eigenvalues_nonneg k)
  | .inr k =>
      scalarPurificationLp
        (hM.isHermitian.eigenvalues k)
        (hM.eigenvalues_nonneg k)

def commonPurificationSubspace
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) :
    Submodule ℂ (Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))) :=
  Submodule.span ℂ
    (Set.range (commonPurificationGenerator F M positive hM))

theorem commonPurificationSubspace_finiteDimensional
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) :
    FiniteDimensional ℂ (commonPurificationSubspace F M positive hM) := by
  unfold commonPurificationSubspace
  exact FiniteDimensional.span_of_finite ℂ
    (Set.finite_range (commonPurificationGenerator F M positive hM))

theorem ensemble_scalarPurificationLp_mem_common
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) (i : ι) (k : d) :
    scalarPurificationLp
        ((positive i).isHermitian.eigenvalues k)
        ((positive i).eigenvalues_nonneg k) ∈
      commonPurificationSubspace F M positive hM := by
  apply Submodule.subset_span
  exact ⟨Sum.inl (i, k), rfl⟩

theorem mean_scalarPurificationLp_mem_common
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) (k : d) :
    scalarPurificationLp
        (hM.isHermitian.eigenvalues k)
        (hM.eigenvalues_nonneg k) ∈
      commonPurificationSubspace F M positive hM := by
  apply Submodule.subset_span
  exact ⟨Sum.inr k, rfl⟩

end

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder
  Matrix.Norms.Elementwise InnerProductSpace

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def spectralPurificationFilterEntryLp
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) (i j : d) :
    Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) :=
  (((spectralPurificationFilter_memLp_two F hF).eval i).eval j).toLp
    (fun s : ℝ => spectralPurificationFilter F hF s i j)

theorem spectralPurificationFilterEntryLp_coeFn
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) (i j : d) :
    (spectralPurificationFilterEntryLp F hF i j : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioi 0)]
        (fun s : ℝ => spectralPurificationFilter F hF s i j) :=
  (((spectralPurificationFilter_memLp_two F hF).eval i).eval j).coeFn_toLp

theorem spectralPurificationFilterEntryLp_eq_eigen_sum
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) (i j : d) :
    spectralPurificationFilterEntryLp F hF i j =
      ∑ k : d,
        (((hF.isHermitian.eigenvectorUnitary : Matrix d d ℂ) i k) *
          (star (hF.isHermitian.eigenvectorUnitary : Matrix d d ℂ)) k j) •
        scalarPurificationLp
          (hF.isHermitian.eigenvalues k)
          (hF.eigenvalues_nonneg k) := by
  classical
  let U := hF.isHermitian.eigenvectorUnitary
  let eigenvalue := hF.isHermitian.eigenvalues
  let coefficient : d → ℂ := fun k =>
    (U : Matrix d d ℂ) i k *
      star (U : Matrix d d ℂ) k j
  let generator : d → Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) :=
    fun k => scalarPurificationLp
      (eigenvalue k) (hF.eigenvalues_nonneg k)
  apply Lp.ext
  have hentry := spectralPurificationFilterEntryLp_coeFn F hF i j
  have hsum := Lp.coeFn_fun_finsetSum
    Finset.univ (fun k : d => coefficient k • generator k)
  have hgenerator :
      ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
        ∀ k : d,
          (coefficient k • generator k :
            Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))) s =
            coefficient k *
              ((eigenvalue k / (eigenvalue k + s) : ℝ) : ℂ) := by
    apply ae_all_iff.mpr
    intro k
    have hsmul := Lp.coeFn_smul (coefficient k) (generator k)
    have hscalar := scalarPurificationLp_coeFn
      (eigenvalue k) (hF.eigenvalues_nonneg k)
    filter_upwards [hsmul, hscalar] with s hs ht
    rw [hs]
    change
      coefficient k *
        (scalarPurificationLp (eigenvalue k)
          (hF.eigenvalues_nonneg k) : ℝ → ℂ) s = _
    rw [ht]
  filter_upwards [hentry, hsum, hgenerator] with s he hs hg
  rw [he, hs]
  change
    ((U : Matrix d d ℂ) *
      Matrix.diagonal (fun k =>
        ((eigenvalue k / (eigenvalue k + s) : ℝ) : ℂ)) *
      star (U : Matrix d d ℂ)) i j =
      ∑ k : d, (coefficient k • generator k :
        Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))) s
  simp_rw [hg]
  simp [Matrix.mul_apply, Matrix.diagonal, coefficient,
    mul_assoc, mul_comm]

theorem ensemble_spectralPurificationFilterEntryLp_mem_common
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef)
    (a : ι) (i j : d) :
    spectralPurificationFilterEntryLp (F a) (positive a) i j ∈
      commonPurificationSubspace F M positive hM := by
  rw [spectralPurificationFilterEntryLp_eq_eigen_sum]
  apply (commonPurificationSubspace F M positive hM).sum_mem
  intro k _
  apply (commonPurificationSubspace F M positive hM).smul_mem
  exact ensemble_scalarPurificationLp_mem_common
    F M positive hM a k

theorem mean_spectralPurificationFilterEntryLp_mem_common
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef)
    (i j : d) :
    spectralPurificationFilterEntryLp M hM i j ∈
      commonPurificationSubspace F M positive hM := by
  rw [spectralPurificationFilterEntryLp_eq_eigen_sum]
  apply (commonPurificationSubspace F M positive hM).sum_mem
  intro k _
  apply (commonPurificationSubspace F M positive hM).smul_mem
  exact mean_scalarPurificationLp_mem_common
    F M positive hM k

def ensemblePurificationSubspaceEntry
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef)
    (a : ι) (i j : d) :
    commonPurificationSubspace F M positive hM :=
  ⟨spectralPurificationFilterEntryLp (F a) (positive a) i j,
    ensemble_spectralPurificationFilterEntryLp_mem_common
      F M positive hM a i j⟩

def meanPurificationSubspaceEntry
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef)
    (i j : d) :
    commonPurificationSubspace F M positive hM :=
  ⟨spectralPurificationFilterEntryLp M hM i j,
    mean_spectralPurificationFilterEntryLp_mem_common
      F M positive hM i j⟩

noncomputable def commonPurificationOrthonormalBasis
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) :
    OrthonormalBasis
      (Fin (Module.finrank ℂ
        (commonPurificationSubspace F M positive hM)))
      ℂ (commonPurificationSubspace F M positive hM) := by
  letI : FiniteDimensional ℂ
      (commonPurificationSubspace F M positive hM) :=
    commonPurificationSubspace_finiteDimensional F M positive hM
  exact stdOrthonormalBasis ℂ
    (commonPurificationSubspace F M positive hM)

noncomputable def finitePurificationMatrix
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) (a : ι) :
    Matrix
      (d × Fin (Module.finrank ℂ
        (commonPurificationSubspace F M positive hM))) d ℂ :=
  fun ik j =>
    (commonPurificationOrthonormalBasis F M positive hM).repr
      (ensemblePurificationSubspaceEntry F M positive hM a ik.1 j)
      ik.2

noncomputable def meanFinitePurificationMatrix
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) :
    Matrix
      (d × Fin (Module.finrank ℂ
        (commonPurificationSubspace F M positive hM))) d ℂ :=
  fun ik j =>
    (commonPurificationOrthonormalBasis F M positive hM).repr
      (meanPurificationSubspaceEntry F M positive hM ik.1 j)
      ik.2

end

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder
  Matrix.Norms.Elementwise InnerProductSpace

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder
  Matrix.Norms.Elementwise InnerProductSpace

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

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

def strategyPurificationShuffle
    (dA dB : Type) :
    ((dA × (dA × dB)) × dB) ≃ ((dA × dB) × (dA × dB)) where
  toFun q := (q.1.2, (q.1.1, q.2))
  invFun q := ((q.2.1, q.1), q.2.2)
  left_inv := by
    rintro ⟨⟨a, k⟩, b⟩
    rfl
  right_inv := by
    rintro ⟨k, ⟨a, b⟩⟩
    rfl

def strategyPurificationVector
    {X Y A B : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} (S : Strategy G) :
    EuclideanSpace ℂ ((S.Alice × (S.Alice × S.Bob)) × S.Bob) :=
  toLp 2
    (fun q =>
      Matrix.vec (spectralSupportSqrt S.state.matrix S.state.positive)
        (strategyPurificationShuffle S.Alice S.Bob q))

def purificationAlicePOVM
    {ι d k : Type*} [Fintype ι]
    [Fintype d] [Fintype k] [DecidableEq d] [DecidableEq k]
    (P : POVM ι d) : POVM ι (d × k) where
  effect a := P.effect a ⊗ₖ (1 : Matrix k k ℂ)
  positive a := (P.positive a).kronecker Matrix.PosSemidef.one
  complete := by
    classical
    calc
      (∑ a : ι, P.effect a ⊗ₖ (1 : Matrix k k ℂ)) =
          (∑ a : ι, P.effect a) ⊗ₖ (1 : Matrix k k ℂ) := by
            ext ⟨i, u⟩ ⟨j, v⟩
            simp [Matrix.sum_apply, Matrix.kroneckerMap_apply,
              Finset.sum_mul]
      _ = 1 := by
        rw [P.complete]
        exact Matrix.one_kronecker_one

def finiteLocalPurificationJointMatrix
    {X Y A B eA eB : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype eA] [Fintype eB]
    {G : Game X Y A B} (S : Strategy G)
    (KA : Matrix eA S.Alice ℂ) (KB : Matrix eB S.Bob ℂ) :
    Matrix ((eA × (S.Alice × S.Bob)) × eB)
      ((S.Alice × (S.Alice × S.Bob)) × S.Bob) ℂ :=
  (KA ⊗ₖ
    (1 : Matrix (S.Alice × S.Bob) (S.Alice × S.Bob) ℂ)) ⊗ₖ KB

def finiteLocalPurificationVector
    {X Y A B eA eB : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype eA] [Fintype eB]
    {G : Game X Y A B} (S : Strategy G)
    (KA : Matrix eA S.Alice ℂ) (KB : Matrix eB S.Bob ℂ) :
    EuclideanSpace ℂ ((eA × (S.Alice × S.Bob)) × eB) :=
  toLp 2
    ((finiteLocalPurificationJointMatrix S KA KB).mulVec
      (ofLp (strategyPurificationVector S)))

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder InnerProductSpace

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

def dSVUniformDensityPhysicalAsyncSigmaContinuation
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (U V : ι → Matrix.unitaryGroup κ ℂ)
    (z : EuclideanSpace ℂ
      ((Σ _ : ι, κ) × (Σ _ : ι, κ))) :
    EuclideanSpace ℂ ((Σ _ : ι, κ) × (Σ _ : ι, κ)) := by
  classical
  let A := coherentSharedRandomControlledUnitary U
  let B := coherentSharedRandomControlledUnitary V
  exact toLp 2 ((A.val ⊗ₖ B.val).mulVec (ofLp z))

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option maxRecDepth 3072

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096

attribute [local instance] Classical.propDecidable

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

def dSVUniformDensityCorrectedMatchedSigmaWeightedResidual
    {H : Type*} [Fintype H] {n : ℕ}
    (history : EuclideanSpace ℂ (H × H))
    (work : H → H → EuclideanSpace ℂ (Fin n × Fin n)) :
    EuclideanSpace ℂ
      ((Σ _ : H, Fin n) × (Σ _ : H, Fin n)) :=
  toLp 2 fun q : (Σ _ : H, Fin n) × (Σ _ : H, Fin n) =>
    history (q.1.1, q.2.1) * work q.1.1 q.2.1 (q.1.2, q.2.2)

end

noncomputable section

open WithLp
open scoped BigOperators ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

def dSVDensityRationalProjectiveThresholdBin
    (w : ℝ) (N : ℕ) (k : Fin N) (a : ℝ) : Bool :=
  decide (dSVUniformDensityThresholdGrid N k ≤
    dSVRationalSoftPass w a)

def dSVDensityRationalProjectiveThresholdPOVM
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ℝ) (N : ℕ) (k : Fin N)
    (F : Matrix ι ι ℂ) (positive : F.PosSemidef) : POVM Bool ι :=
  spectralPartitionPOVM F positive
    (fun i : ι => dSVDensityRationalProjectiveThresholdBin
      w N k (positive.isHermitian.eigenvalues i))

theorem dSVDensityRationalProjectiveThresholdPOVM_projective
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ℝ) (N : ℕ) (k : Fin N)
    (F : Matrix ι ι ℂ) (positive : F.PosSemidef) (outcome : Bool) :
    (dSVDensityRationalProjectiveThresholdPOVM
      w N k F positive).effect outcome *
      (dSVDensityRationalProjectiveThresholdPOVM
        w N k F positive).effect outcome =
      (dSVDensityRationalProjectiveThresholdPOVM
        w N k F positive).effect outcome := by
  exact spectralPartitionPOVM_projective F positive
    (fun i : ι => dSVDensityRationalProjectiveThresholdBin
      w N k (positive.isHermitian.eigenvalues i)) outcome

def dSVDensityRationalLeftProjectiveThresholdPOVM
    {d : ℕ} (w : ℝ) (N : ℕ) (k : Fin N)
    (ξ : BipartiteUnitVector d) : POVM Bool (Fin d) :=
  dSVDensityRationalProjectiveThresholdPOVM w N k
    (dSVSoftBobLeftReducedDensity ξ)
    (dSVSoftBobLeftReducedDensity_posSemidef ξ)

def dSVDensityRationalLeftProjectiveThresholdAtomMismatch
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) : ℝ :=
  let F := dSVSoftBobLeftReducedDensity ξ
  let G := dSVSoftBobLeftReducedDensity ζ
  let hF := dSVSoftBobLeftReducedDensity_posSemidef ξ
  let hG := dSVSoftBobLeftReducedDensity_posSemidef ζ
  ∑ i : Fin d, ∑ j : Fin d,
    spectralAtomOverlap F G hF hG i j *
      dSVUniformDensityThresholdMismatch N
        (dSVRationalSoftPass w
          (hF.isHermitian.eigenvalues i))
        (dSVRationalSoftPass w
          (hG.isHermitian.eigenvalues j))

theorem dSVUniformDensityGridPrefix_density_sub_lt
    {N : ℕ} (positive : 0 < N)
    {a : ℝ} (nonnegative : 0 ≤ a) (bounded : a ≤ 1) :
    a - dSVUniformDensityGridPrefix N a < 1 / (N : ℝ) := by
  have cast : (0 : ℝ) < N := by exact_mod_cast positive
  rw [dSVUniformDensityGridPrefix_eq_count,
    dSVUniformDensityThresholdGrid_count_eq_floor
      positive a nonnegative bounded]
  apply (lt_div_iff₀ cast).mpr
  have floor := Nat.lt_floor_add_one (a * (N : ℝ))
  calc
    (a - (Nat.floor (a * (N : ℝ)) : ℝ) / (N : ℝ)) *
        (N : ℝ) =
      a * (N : ℝ) - (Nat.floor (a * (N : ℝ)) : ℝ) := by
        field_simp
    _ < 1 := by linarith

theorem dSVUniformDensityGridPrefix_density_sub_le
    {N : ℕ} (positive : 0 < N)
    {a : ℝ} (nonnegative : 0 ≤ a) (bounded : a ≤ 1) :
    a - 1 / (N : ℝ) ≤ dSVUniformDensityGridPrefix N a := by
  linarith [dSVUniformDensityGridPrefix_density_sub_lt
    positive nonnegative bounded]

def dSVDensityRationalLeftProjectiveDiagonalMass
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) : ℝ :=
  let hF := dSVSoftBobLeftReducedDensity_posSemidef ξ
  ∑ i : Fin d,
    dSVUniformDensityGridPrefix N
      (dSVRationalSoftPass w
        (hF.isHermitian.eigenvalues i))

theorem dSVSoftBobLeftReducedDensity_eigenvalue_le_one
    {d : ℕ} (ξ : BipartiteUnitVector d) (i : Fin d) :
    (dSVSoftBobLeftReducedDensity_posSemidef ξ).isHermitian.eigenvalues i
      ≤ 1 := by
  let F := dSVSoftBobLeftReducedDensity ξ
  let hF : F.PosSemidef :=
    dSVSoftBobLeftReducedDensity_posSemidef ξ
  change hF.isHermitian.eigenvalues i ≤ 1
  calc
    hF.isHermitian.eigenvalues i ≤
        ∑ j : Fin d, hF.isHermitian.eigenvalues j :=
      Finset.single_le_sum
        (fun j _ => hF.eigenvalues_nonneg j) (Finset.mem_univ i)
    _ = 1 := positiveDensity_eigenvalues_sum F hF
      (dSVSoftBobLeftReducedDensity_trace ξ)

theorem dSVRationalSoftPass_ge_density_div_width_add_one
    {w a : ℝ} (width : 0 < w)
    (nonnegative : 0 ≤ a) (bounded : a ≤ 1) :
    a / (w + 1) ≤ dSVRationalSoftPass w a := by
  unfold dSVRationalSoftPass
  have denominator : 0 < a + w := by linarith
  have wider : 0 < w + 1 := by linarith
  apply (div_le_div_iff₀ wider denominator).mpr
  nlinarith

theorem dSVDensityRationalLeftProjectiveDiagonalMass_lower
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (ξ : BipartiteUnitVector d) :
    1 / (w + 1) - (d : ℝ) / N ≤
      dSVDensityRationalLeftProjectiveDiagonalMass w N ξ := by
  let F := dSVSoftBobLeftReducedDensity ξ
  let hF : F.PosSemidef :=
    dSVSoftBobLeftReducedDensity_posSemidef ξ
  have density_sum :
      (∑ i : Fin d, hF.isHermitian.eigenvalues i) = 1 :=
    positiveDensity_eigenvalues_sum F hF
      (dSVSoftBobLeftReducedDensity_trace ξ)
  have rational_sum :
      1 / (w + 1) ≤
        ∑ i : Fin d,
          dSVRationalSoftPass w
            (hF.isHermitian.eigenvalues i) := by
    calc
      1 / (w + 1) =
          ∑ i : Fin d, hF.isHermitian.eigenvalues i / (w + 1) := by
        rw [← Finset.sum_div, density_sum]
      _ ≤ ∑ i : Fin d,
          dSVRationalSoftPass w
            (hF.isHermitian.eigenvalues i) := by
        apply Finset.sum_le_sum
        intro i _
        exact dSVRationalSoftPass_ge_density_div_width_add_one
          width (hF.eigenvalues_nonneg i)
          (dSVSoftBobLeftReducedDensity_eigenvalue_le_one ξ i)
  calc
    1 / (w + 1) - (d : ℝ) / N ≤
        (∑ i : Fin d,
          dSVRationalSoftPass w
            (hF.isHermitian.eigenvalues i)) - (d : ℝ) / N :=
      sub_le_sub_right rational_sum _
    _ = ∑ i : Fin d,
        (dSVRationalSoftPass w
          (hF.isHermitian.eigenvalues i) - 1 / (N : ℝ)) := by
      simp [Finset.sum_sub_distrib]
      ring
    _ ≤ dSVDensityRationalLeftProjectiveDiagonalMass w N ξ := by
      unfold dSVDensityRationalLeftProjectiveDiagonalMass
      change
        (∑ i : Fin d,
          (dSVRationalSoftPass w
            (hF.isHermitian.eigenvalues i) - 1 / (N : ℝ))) ≤
          ∑ i : Fin d,
            dSVUniformDensityGridPrefix N
              (dSVRationalSoftPass w
                (hF.isHermitian.eigenvalues i))
      apply Finset.sum_le_sum
      intro i _
      exact dSVUniformDensityGridPrefix_density_sub_le grid
        (dSVRationalSoftPass_mem_unit width
          (hF.eigenvalues_nonneg i)).1
        (dSVRationalSoftPass_mem_unit width
          (hF.eigenvalues_nonneg i)).2

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

def dSVDensityRationalPhysicalProjector
    {d N : ℕ} (w : ℝ)
    (ξ : BipartiteUnitVector d) (k : Fin N) :
    Matrix (Fin d) (Fin d) ℂ :=
  (dSVDensityRationalLeftProjectiveThresholdPOVM
    w N k ξ).effect true

theorem dSVDensityRationalPhysicalProjector_pos
    {d N : ℕ} (w : ℝ)
    (ξ : BipartiteUnitVector d) (k : Fin N) :
    (dSVDensityRationalPhysicalProjector w ξ k).PosSemidef :=
  (dSVDensityRationalLeftProjectiveThresholdPOVM
    w N k ξ).positive true

theorem dSVDensityRationalPhysicalProjector_projective
    {d N : ℕ} (w : ℝ)
    (ξ : BipartiteUnitVector d) (k : Fin N) :
    dSVDensityRationalPhysicalProjector w ξ k *
        dSVDensityRationalPhysicalProjector w ξ k =
      dSVDensityRationalPhysicalProjector w ξ k := by
  exact dSVDensityRationalProjectiveThresholdPOVM_projective
    w N k (dSVSoftBobLeftReducedDensity ξ)
    (dSVSoftBobLeftReducedDensity_posSemidef ξ) true

theorem dSVDensityRationalPhysicalProjector_complement_pos
    {d N : ℕ} (w : ℝ)
    (ξ : BipartiteUnitVector d) (k : Fin N) :
    (1 - dSVDensityRationalPhysicalProjector w ξ k).PosSemidef :=
  dSVProjectorComplement_posSemidef
    (dSVDensityRationalPhysicalProjector w ξ k)
    (dSVDensityRationalPhysicalProjector_pos w ξ k)
    (dSVDensityRationalPhysicalProjector_projective w ξ k)

def dSVDensityRationalPhysicalGlobalPOVM
    {d N : ℕ} (w : ℝ)
    (ξ : BipartiteUnitVector d) :
    POVM Bool (DSVUniformDensityThresholdLocalIndex N d) :=
  dSVGlobalProjectorBinaryPOVM
    (dSVDensityRationalPhysicalProjector w ξ)
    (dSVDensityRationalPhysicalProjector_pos w ξ)
    (dSVDensityRationalPhysicalProjector_complement_pos w ξ)

def dSVDensityRationalPhysicalDiagonalBornSuccess
    {d N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (w : ℝ) (ξ : BipartiteUnitVector d) : ℝ :=
  binaryJointSuccessProbability
    (dSVUniformDensityThresholdSharedDensity grid dimension)
    (dSVDensityRationalPhysicalGlobalPOVM w ξ)
    (transposePOVM
      (dSVDensityRationalPhysicalGlobalPOVM w ξ))

def dSVDensityRationalPhysicalProjectorCrossHazard
    {d : ℕ} (N : ℕ) (w : ℝ)
    (ξ ζ : BipartiteUnitVector d) : ℝ :=
  (∑ k : Fin N,
    (Matrix.trace
      ((dSVDensityRationalPhysicalProjector w ξ k -
        dSVDensityRationalPhysicalProjector w ζ k) *
       (dSVDensityRationalPhysicalProjector w ξ k -
        dSVDensityRationalPhysicalProjector w ζ k))).re) /
      ((d : ℝ) * (N : ℝ))

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

def dSVDensityRationalCompleteProjectiveThresholdProjector
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) (k : Fin N) :
    Matrix (Fin d) (Fin d) ℂ :=
  (dSVDensityRationalLeftProjectiveThresholdPOVM
    w N k ξ).effect true

theorem dSVDensityRationalCompleteProjectiveThresholdProjector_pos
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) (k : Fin N) :
    (dSVDensityRationalCompleteProjectiveThresholdProjector
      w N ξ k).PosSemidef :=
  (dSVDensityRationalLeftProjectiveThresholdPOVM
    w N k ξ).positive true

theorem dSVDensityRationalCompleteProjectiveThresholdEffect_false
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) (k : Fin N) :
    (dSVDensityRationalLeftProjectiveThresholdPOVM
      w N k ξ).effect false =
      1 - dSVDensityRationalCompleteProjectiveThresholdProjector
        w N ξ k := by
  have complete :=
    (dSVDensityRationalLeftProjectiveThresholdPOVM
      w N k ξ).complete
  rw [Fintype.sum_bool, add_comm] at complete
  exact eq_sub_of_add_eq complete

theorem
    dSVDensityRationalCompleteProjectiveThresholdProjector_complement_pos
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) (k : Fin N) :
    (1 - dSVDensityRationalCompleteProjectiveThresholdProjector
      w N ξ k).PosSemidef := by
  rw [← dSVDensityRationalCompleteProjectiveThresholdEffect_false]
  exact (dSVDensityRationalLeftProjectiveThresholdPOVM
    w N k ξ).positive false

def dSVDensityRationalCompleteProjectiveBinaryPOVM
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) :
    POVM Bool (DSVUniformDensityThresholdLocalIndex N d) :=
  dSVGlobalProjectorBinaryPOVM
    (dSVDensityRationalCompleteProjectiveThresholdProjector
      w N ξ)
    (dSVDensityRationalCompleteProjectiveThresholdProjector_pos
      w N ξ)
    (dSVDensityRationalCompleteProjectiveThresholdProjector_complement_pos
      w N ξ)

def dSVDensityRationalCompleteProjectiveOutcome
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) (a b : Bool) :
    EuclideanSpace ℂ
      (DSVUniformDensityThresholdLocalIndex N d ×
        DSVUniformDensityThresholdLocalIndex N d) :=
  coherentBinaryJointOutcome
    (dSVDensityRationalCompleteProjectiveBinaryPOVM
      w N ξ)
    (transposePOVM
      (dSVDensityRationalCompleteProjectiveBinaryPOVM
        w N ζ))
    (dSVUniformDensityThresholdSharedState N d) a b

end

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder

theorem dSVDensityRationalGridPrefix_nonneg
    (N : ℕ) (a : ℝ) :
    0 ≤ dSVUniformDensityGridPrefix N a := by
  unfold dSVUniformDensityGridPrefix
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg
    (dSVUniformDensityThresholdWeight_nonneg N k)
    (by split <;> norm_num)

def dSVDensityRationalCanonicalAcceptedCoefficient
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) (i : Fin d) : ℝ :=
  Real.sqrt (w * dSVUniformDensityGridPrefix N
    (dSVRationalSoftPass w
      ((dSVSoftBobLeftReducedDensity_posSemidef ξ).isHermitian.eigenvalues i)))

theorem dSVDensityRationalCanonicalAcceptedCoefficient_sq
    {d : ℕ} {w : ℝ} (width : 0 < w) (N : ℕ)
    (ξ : BipartiteUnitVector d) (i : Fin d) :
    dSVDensityRationalCanonicalAcceptedCoefficient
        w N ξ i ^ 2 =
      w * dSVUniformDensityGridPrefix N
        (dSVRationalSoftPass w
          ((dSVSoftBobLeftReducedDensity_posSemidef ξ).isHermitian.eigenvalues i)) := by
  unfold dSVDensityRationalCanonicalAcceptedCoefficient
  apply Real.sq_sqrt
  exact mul_nonneg width.le
    (dSVDensityRationalGridPrefix_nonneg _ _)

def dSVDensityRationalCanonicalAliceBasis
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    Matrix.unitaryGroup (Fin d) ℂ :=
  Classical.choose
    (exists_proofDSVUniformDensityPolarLeftCanonicalSchmidt ξ)

def dSVDensityRationalCanonicalAcceptedTarget
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) :
    EuclideanSpace ℂ (Fin d × Fin d) :=
  schmidtVector
    (dSVDensityRationalCanonicalAcceptedCoefficient w N ξ)
    (dSVDensityRationalCanonicalAliceBasis ξ)
    (dSVUniformDensityThresholdLeftBobBasis ξ)

theorem dSVDensityRationalCanonicalAcceptedTarget_norm_sq
    {d : ℕ} {w : ℝ} (width : 0 < w) (N : ℕ)
    (ξ : BipartiteUnitVector d) :
    ‖dSVDensityRationalCanonicalAcceptedTarget w N ξ‖ ^ 2 =
      w * dSVDensityRationalLeftProjectiveDiagonalMass w N ξ := by
  unfold dSVDensityRationalCanonicalAcceptedTarget
  rw [schmidtVector_norm_sq]
  simp_rw [dSVDensityRationalCanonicalAcceptedCoefficient_sq width]
  unfold dSVDensityRationalLeftProjectiveDiagonalMass
  rw [Finset.mul_sum]

theorem dSVDensityRationalCanonicalAcceptedTarget_ne_zero
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (w + 1))
    (ξ : BipartiteUnitVector d) :
    dSVDensityRationalCanonicalAcceptedTarget w N ξ ≠ 0 := by
  intro zero
  have actual :=
    dSVDensityRationalCanonicalAcceptedTarget_norm_sq
      width N ξ
  rw [zero, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at actual
  have lower :=
    dSVDensityRationalLeftProjectiveDiagonalMass_lower
      width grid ξ
  nlinarith

def dSVDensityRationalCanonicalNormalizedTarget
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) :
    EuclideanSpace ℂ (Fin d × Fin d) :=
  NormedSpace.normalize
    (dSVDensityRationalCanonicalAcceptedTarget w N ξ)

theorem dSVDensityRationalCanonicalNormalizedTarget_norm
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (w + 1))
    (ξ : BipartiteUnitVector d) :
    ‖dSVDensityRationalCanonicalNormalizedTarget
      w N ξ‖ = 1 := by
  unfold dSVDensityRationalCanonicalNormalizedTarget
  exact NormedSpace.norm_normalize
    (dSVDensityRationalCanonicalAcceptedTarget_ne_zero
      width grid fine ξ)

def dSVDensityRationalCanonicalAcceptedUnitTarget
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (w + 1))
    (ξ : BipartiteUnitVector d) :
    BipartiteUnitVector d :=
  ⟨dSVDensityRationalCanonicalNormalizedTarget w N ξ,
    dSVDensityRationalCanonicalNormalizedTarget_norm
      width grid fine ξ⟩

end

noncomputable section

open WithLp
open scoped BigOperators ComplexOrder MatrixOrder

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

def dSVDensityRationalPhysicalMixedBornSuccess
    {d N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (w : ℝ) (ξ ζ : BipartiteUnitVector d) : ℝ :=
  binaryJointSuccessProbability
    (dSVUniformDensityThresholdSharedDensity grid dimension)
    (dSVDensityRationalPhysicalGlobalPOVM w ξ)
    (transposePOVM
      (dSVDensityRationalPhysicalGlobalPOVM w ζ))

end

noncomputable section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder

def dSVDensityRationalActualMixedSuccessMass
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) : ℝ :=
  ‖dSVDensityRationalCompleteProjectiveOutcome
    w N ξ ζ true true‖ ^ 2

def dSVDensityRationalActualMixedContinueMass
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) : ℝ :=
  ‖dSVDensityRationalCompleteProjectiveOutcome
    w N ξ ζ false false‖ ^ 2

def dSVDensityRationalActualMixedAsynchronousMass
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) : ℝ :=
  ‖dSVDensityRationalCompleteProjectiveOutcome
      w N ξ ζ true false‖ ^ 2 +
    ‖dSVDensityRationalCompleteProjectiveOutcome
      w N ξ ζ false true‖ ^ 2

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

def dSVDensityRationalCompletePhysicalStoppingCopyAccepted
    {N d : ℕ} (w : ℝ) (ξ : BipartiteUnitVector d)
    (q : DSVUniformDensityThresholdLocalIndex N d) : Prop :=
  dSVDensityRationalProjectiveThresholdBin w N q.1
    ((dSVSoftBobLeftReducedDensity_posSemidef
      ξ).isHermitian.eigenvalues q.2) = true

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

def dSVDensityRationalPhysicalAcceptedOutcome
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) :
    EuclideanSpace ℂ
      (DSVUniformDensityThresholdLocalIndex N d ×
        DSVUniformDensityThresholdLocalIndex N d) :=
  dSVDensityRationalCompleteProjectiveOutcome
    w N ξ ζ true true

def dSVDensityRationalPhysicalAcceptedRank
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) (i : Fin d) :
    Fin (N + 1) :=
  let selected : Finset (Fin N) :=
    Finset.univ.filter fun k : Fin N =>
      dSVDensityRationalProjectiveThresholdBin w N k
        ((dSVSoftBobLeftReducedDensity_posSemidef
          ξ).isHermitian.eigenvalues i) = true
  ⟨selected.card, by
    have bounded : selected.card ≤ N := by
      simpa using Finset.card_le_univ selected
    omega⟩

end

noncomputable section

open WithLp
open scoped BigOperators ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

def dSVDensityRationalPrefixRankMismatch
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) : ℝ :=
  (∑ i : Fin d, ∑ j : Fin d,
    spectralAtomOverlap
      (dSVSoftBobLeftReducedDensity ξ)
      (dSVSoftBobLeftReducedDensity ζ)
      (dSVSoftBobLeftReducedDensity_posSemidef ξ)
      (dSVSoftBobLeftReducedDensity_posSemidef ζ) i j *
      |((dSVDensityRationalPhysicalAcceptedRank
            w N ξ i).val : ℝ) -
        ((dSVDensityRationalPhysicalAcceptedRank
            w N ζ j).val : ℝ)|) / (N : ℝ)

end

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

def dSVDensityRationalMixedSpectralAtomBlock
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d)
    (a b : Bool) (k : Fin N) : Matrix (Fin d) (Fin d) ℂ :=
  let F := dSVSoftBobLeftReducedDensity ξ
  let G := dSVSoftBobLeftReducedDensity ζ
  let hF := dSVSoftBobLeftReducedDensity_posSemidef ξ
  let hG := dSVSoftBobLeftReducedDensity_posSemidef ζ
  ∑ i : Fin d, ∑ j : Fin d,
    if dSVDensityRationalProjectiveThresholdBin w N k
        (hF.isHermitian.eigenvalues i) = a ∧
      dSVDensityRationalProjectiveThresholdBin w N k
        (hG.isHermitian.eigenvalues j) = b
    then positiveMatrixSpectralAtom F hF i *
      positiveMatrixSpectralAtom G hG j
    else 0

end

noncomputable section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

def dSVDensityRationalPhysicalMixedAcceptedIntersectionRank
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d)
    (i j : Fin d) : Fin (N + 1) :=
  ⟨min
      (dSVDensityRationalPhysicalAcceptedRank w N ξ i).val
      (dSVDensityRationalPhysicalAcceptedRank w N ζ j).val,
    by
      have left :=
        (dSVDensityRationalPhysicalAcceptedRank w N ξ i).isLt
      have right :=
        (dSVDensityRationalPhysicalAcceptedRank w N ζ j).isLt
      omega⟩

def dSVDensityRationalPhysicalMixedAcceptedPrefixWork
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) (i j : Fin d) :
    EuclideanSpace ℂ (Fin N × Fin N) :=
  dSVCanonicalFailurePrefix
    (dSVDensityRationalPhysicalMixedAcceptedIntersectionRank
      w N ξ ζ i j)

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

def dSVDensityRationalCanonicalPrefixMask
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) :
    Matrix (DSVUniformDensityThresholdLocalIndex N d)
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
  Matrix.blockDiagonal' fun k : Fin N =>
    Matrix.diagonal fun i : Fin d =>
      if dSVDensityRationalProjectiveThresholdBin w N k
          ((dSVSoftBobLeftReducedDensity_posSemidef
            ξ).isHermitian.eigenvalues i) = true
      then (1 : ℂ) else 0

def dSVDensityRationalCanonicalPrefixSpectralOutcome
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) :
    EuclideanSpace ℂ
      (DSVUniformDensityThresholdLocalIndex N d ×
        DSVUniformDensityThresholdLocalIndex N d) :=
  toLp 2
    (((dSVUniformDensityAliceHistorySpectralCopy
        (N := N) ξ :
        Matrix (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) ⊗ₖ
      (((dSVUniformDensityBobHistoryCopyBasis
          (N := N) ζ)⁻¹ : Matrix.unitaryGroup
            (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
        Matrix (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ)).mulVec
      (ofLp (dSVDensityRationalPhysicalAcceptedOutcome
        w N ξ ζ)))

def dSVDensityRationalCompleteStoppedOptionalLocalEffect
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) :
    Option Bool → Matrix
      (DSVUniformDensityThresholdLocalIndex N d)
      (DSVUniformDensityThresholdLocalIndex N d) ℂ
  | none => 1
  | some outcome =>
      (dSVDensityRationalCompleteProjectiveBinaryPOVM
        w N ξ).effect outcome

def dSVDensityRationalCompleteStoppedOptionalOutcome
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d)
    (alice bob : Option Bool) :
    EuclideanSpace ℂ
      (DSVUniformDensityThresholdLocalIndex N d ×
       DSVUniformDensityThresholdLocalIndex N d) :=
  toLp 2
    (((dSVDensityRationalCompleteStoppedOptionalLocalEffect
          w N ξ alice) ⊗ₖ
        (dSVDensityRationalCompleteStoppedOptionalLocalEffect
          w N ζ bob).transpose).mulVec
      (ofLp (dSVUniformDensityThresholdSharedState N d)))

def dSVDensityRationalCompleteStoppedOptionalLocalSchedule
    (L : ℕ) (hit copy : Fin (L + 1)) : Option Bool :=
  if copy.val < L then
    if hit = 0 then some false
    else if copy.val + 1 < hit.val then some false
    else if copy.val + 1 = hit.val then some true
    else none
  else none

end

noncomputable section

open scoped Kronecker ComplexOrder MatrixOrder

def dSVDensityRationalFirstAcceptLocalSpectralMask
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) (outcome : Bool) :
    Matrix (DSVUniformDensityThresholdLocalIndex N d)
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
  Matrix.blockDiagonal' fun k : Fin N =>
    Matrix.diagonal fun i : Fin d =>
      if dSVDensityRationalProjectiveThresholdBin w N k
          ((dSVSoftBobLeftReducedDensity_posSemidef
            ξ).isHermitian.eigenvalues i) = outcome
      then (1 : ℂ) else 0

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

def dSVDensityRationalFirstAcceptActualTensorBasis
    {β : Type*} [Fintype β] [DecidableEq β]
    {L : ℕ} (U : Matrix.unitaryGroup β ℂ) :
    Matrix.unitaryGroup (Σ _ : Fin (L + 1), Fin (L + 1) → β) ℂ :=
  controlledFiniteTensorLocalUnitary
    (fun (_stop : Fin (L + 1)) (_copy : Fin (L + 1)) => U)

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048

end

noncomputable section

open scoped BigOperators Kronecker ComplexOrder MatrixOrder

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

def dSVDensityRationalPublicBucketCoherentPhaseHistory
    {H : Type*} [Fintype H] (B : ℕ)
    (history : EuclideanSpace ℂ (H × H)) :
    EuclideanSpace ℂ ((Fin B × H) × (Fin B × H)) :=
  toLp 2 fun q : (Fin B × H) × (Fin B × H) =>
    ePRState B (q.1.1, q.2.1) *
      history (q.1.2, q.2.2)

def dSVDensityRationalPublicBucketCoherentPhaseSigmaState
    {H : Type*} [Fintype H] {m : ℕ} (B : ℕ)
    (history : EuclideanSpace ℂ (H × H))
    (work : Fin B → H → H →
      EuclideanSpace ℂ (Fin m × Fin m)) :
    EuclideanSpace ℂ
      ((Σ _ : Fin B × H, Fin m) ×
       (Σ _ : Fin B × H, Fin m)) :=
  dSVUniformDensityCorrectedMatchedSigmaWeightedResidual
    (dSVDensityRationalPublicBucketCoherentPhaseHistory
      B history)
    (fun a b => work a.1 a.2 b.2)

def dSVDensityRationalPublicBucketCoherentPhaseLocalUnitary
    {H I : Type*} [Fintype H] [DecidableEq H]
    [DecidableEq I] {B D m : ℕ}
    (rank : H → Fin D)
    (bucket : Fin B → Fin D → I)
    (A : Fin B → I → Matrix.unitaryGroup (Fin m) ℂ) :
    Matrix.unitaryGroup (Σ _ : Fin B × H, Fin m) ℂ :=
  coherentSharedRandomControlledUnitary
    (fun q : Fin B × H => A q.1 (bucket q.1 (rank q.2)))

end

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder

def dSVDensityRationalPublicLogRankFineLabel
    {N : ℕ} (Q : ℕ) (r : Fin (N + 1)) : ℕ :=
  Nat.floor ((Q : ℝ) * Real.log ((max 1 r.val : ℕ) : ℝ))

def dSVDensityRationalPublicLogRankPhaseWeight
    (B : ℕ) (_ : Fin B) : ℝ :=
  1 / (B : ℝ)

def dSVDensityRationalPublicLogRankBucket
    {N B : ℕ} (Q : ℕ) (phase : Fin B)
    (r : Fin (N + 1)) : Option ℕ :=
  if r.val = 0 then none
  else some
    ((dSVDensityRationalPublicLogRankFineLabel Q r + phase.val) / B)

def dSVDensityRationalPublicLogRankBucketFiber
    {N B : ℕ} (Q : ℕ) (phase : Fin B) (label : Option ℕ) :
    Finset (Fin (N + 1)) :=
  Finset.univ.filter fun r : Fin (N + 1) =>
    r.val ≠ 0 ∧
      dSVDensityRationalPublicLogRankBucket Q phase r = label

def dSVDensityRationalPublicLogRankBucketRepresentative
    {N B : ℕ} (Q : ℕ) (phase : Fin B) (label : Option ℕ) :
    Fin (N + 1) :=
  if present :
    (dSVDensityRationalPublicLogRankBucketFiber
      Q phase label).Nonempty
  then (dSVDensityRationalPublicLogRankBucketFiber
      Q phase label).min' present
  else 0

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

abbrev DSVDensityRationalPublicMultiscalePhase
    (S B : ℕ) :=
  Fin S → Fin B

abbrev DSVDensityRationalPublicMultiscalePhaseIndex
    (S B : ℕ) :=
  Fin (Fintype.card
    (DSVDensityRationalPublicMultiscalePhase S B))

def dSVDensityRationalPrefixHarmonicSpectralOverlap
    {d : ℕ} (ξ ζ : BipartiteUnitVector d)
    (i j : Fin d) : ℝ :=
  spectralAtomOverlap
    (dSVSoftBobLeftReducedDensity ξ)
    (dSVSoftBobLeftReducedDensity ζ)
    (dSVSoftBobLeftReducedDensity_posSemidef ξ)
    (dSVSoftBobLeftReducedDensity_posSemidef ζ) i j

def dSVDensityRationalLocalSpectralPairBasisOverlap
    {d : ℕ} (ξ ζ : BipartiteUnitVector d)
    (i j : Fin d) : ℂ :=
  unitaryBasisOverlap
    (dSVSoftBobLeftReducedDensity_posSemidef
      ξ).isHermitian.eigenvectorUnitary
    (dSVSoftBobLeftReducedDensity_posSemidef
      ζ).isHermitian.eigenvectorUnitary i j

def dSVDensityRationalLocalSpectralPairHistory
    {d : ℕ} (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) :
    EuclideanSpace ℂ (Fin d × Fin d) :=
  toLp 2 fun q : Fin d × Fin d =>
    ((‖sharedThresholdResourceRaw (d := Fin d)
      (fun _ : Fin N => (1 : ℝ))‖⁻¹ : ℝ) : ℂ) *
      dSVDensityRationalLocalSpectralPairBasisOverlap
        ξ ζ q.1 q.2

def dSVDensityRationalMixedCanonicalCrossMatrix
    {d : ℕ} (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) :
    Matrix (DSVUniformDensityThresholdLocalIndex N d)
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
  (Matrix.blockDiagonal' fun _ : Fin N =>
    (unitaryBasisOverlap
      (dSVSoftBobLeftReducedDensity_posSemidef
        ξ).isHermitian.eigenvectorUnitary
      (dSVSoftBobLeftReducedDensity_posSemidef
        ζ).isHermitian.eigenvectorUnitary :
      Matrix (Fin d) (Fin d) ℂ)).transpose

def dSVDensityRationalMixedCanonicalRawSource
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) :
    EuclideanSpace ℂ
      (DSVUniformDensityThresholdLocalIndex N d ×
        DSVUniformDensityThresholdLocalIndex N d) :=
  toLp 2
    (Matrix.vec
      (dSVDensityRationalCanonicalPrefixMask w N ζ *
        dSVDensityRationalMixedCanonicalCrossMatrix N ξ ζ *
        dSVDensityRationalCanonicalPrefixMask w N ξ))

def dSVDensityRationalPublicLogBilateralPureTensor
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (v : EuclideanSpace ℂ (ι × ι))
    (u : EuclideanSpace ℂ (κ × κ)) :
    EuclideanSpace ℂ ((ι × κ) × (ι × κ)) :=
  toLp 2 fun q : (ι × κ) × (ι × κ) =>
    v (q.1.1, q.2.1) * u (q.1.2, q.2.2)

abbrev DSVDensityRationalPublicLogPhaseHistoryLocalIndex
    (B N d L : ℕ) :=
  Fin B × DSVUniformDensityThresholdWholeHistoryLocalIndex N d L

def dSVDensityRationalPublicLogPhasePureSource
    (B N d L : ℕ) :
    EuclideanSpace ℂ
      (DSVDensityRationalPublicLogPhaseHistoryLocalIndex B N d L ×
       DSVDensityRationalPublicLogPhaseHistoryLocalIndex B N d L) :=
  dSVDensityRationalPublicLogBilateralPureTensor
    (ePRState B)
    (dSVUniformDensityThresholdWholeHistorySharedState N d L)

def dSVDensityRationalPublicLogPhaseHarmonicPureSource
    (B N d L m : ℕ) :
    EuclideanSpace ℂ
      ((DSVDensityRationalPublicLogPhaseHistoryLocalIndex
        B N d L × Fin m) ×
       (DSVDensityRationalPublicLogPhaseHistoryLocalIndex
        B N d L × Fin m)) :=
  dSVDensityRationalPublicLogBilateralPureTensor
    (dSVDensityRationalPublicLogPhasePureSource B N d L)
    (embezzlementState m)

abbrev DSVDensityRationalPublicLogPhaseCatalystIndex
    (B N d L : ℕ) :=
  Fin B × DSVUniformDensityThresholdWholeHistoryCatalystIndex N d L

def dSVDensityRationalPublicLogPhaseTargetSplitEquiv
    (B N d L : ℕ) :
    DSVDensityRationalPublicLogPhaseHistoryLocalIndex B N d L ≃
      (Fin d ×
        DSVDensityRationalPublicLogPhaseCatalystIndex B N d L) where
  toFun q :=
    let actual :=
      dSVUniformDensityThresholdWholeHistoryTargetSplitEquiv
        N d L q.2
    (actual.1, (q.1, actual.2))
  invFun q :=
    (q.2.1,
      (dSVUniformDensityThresholdWholeHistoryTargetSplitEquiv
        N d L).symm (q.1, q.2.2))
  left_inv := by
    rintro ⟨phase, history⟩
    simp
  right_inv := by
    rintro ⟨target, phase, catalyst⟩
    simp

def dSVDensityRationalPublicLogPhaseResidual
    (B N d L m : ℕ) : ℕ :=
  Fintype.card
      (DSVDensityRationalPublicLogPhaseCatalystIndex
        B N d L) * m

def dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
    (B N d L m : ℕ) :
    (DSVDensityRationalPublicLogPhaseHistoryLocalIndex
      B N d L × Fin m) ≃
      Fin (d *
        dSVDensityRationalPublicLogPhaseResidual B N d L m) :=
  (Equiv.prodCongr
    (dSVDensityRationalPublicLogPhaseTargetSplitEquiv B N d L)
    (Equiv.refl (Fin m))).trans
      (dSVRankControlledTargetCatalystIndexEquiv
        (ι := DSVDensityRationalPublicLogPhaseCatalystIndex
          B N d L) d m)

def dSVDensityRationalPublicLogPhaseTargetFirstPreparedSource
    (B N d L m : ℕ) :
    EuclideanSpace ℂ
      (Fin (d *
        dSVDensityRationalPublicLogPhaseResidual B N d L m) ×
       Fin (d *
        dSVDensityRationalPublicLogPhaseResidual B N d L m)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (Equiv.prodCongr
      (dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
        B N d L m)
      (dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
        B N d L m))
    (dSVDensityRationalPublicLogPhaseHarmonicPureSource
      B N d L m)

abbrev DSVDensityRationalPublicMultiscalePhaseHistoryLocalIndex
    (S B N d L : ℕ) :=
  DSVDensityRationalPublicMultiscalePhaseIndex S B ×
    DSVUniformDensityThresholdWholeHistoryLocalIndex N d L

def dSVDensityRationalPublicMultiscalePhaseResidual
    (S B N d L m : ℕ) : ℕ :=
  dSVDensityRationalPublicLogPhaseResidual
    (Fintype.card (DSVDensityRationalPublicMultiscalePhase S B))
    N d L m

def dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
    (S B N d L m : ℕ) :
    (DSVDensityRationalPublicMultiscalePhaseHistoryLocalIndex
      S B N d L × Fin m) ≃
      Fin (d *
        dSVDensityRationalPublicMultiscalePhaseResidual
          S B N d L m) :=
  dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
    (Fintype.card (DSVDensityRationalPublicMultiscalePhase S B))
    N d L m

def dSVDensityRationalPublicMultiscalePhaseTargetFirstPreparedSource
    (S B N d L m : ℕ) :
    EuclideanSpace ℂ
      (Fin (d *
         dSVDensityRationalPublicMultiscalePhaseResidual
           S B N d L m) ×
       Fin (d *
         dSVDensityRationalPublicMultiscalePhaseResidual
           S B N d L m)) :=
  dSVDensityRationalPublicLogPhaseTargetFirstPreparedSource
    (Fintype.card (DSVDensityRationalPublicMultiscalePhase S B))
    N d L m

end

noncomputable section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder

def dSVDensityRationalPublicLogPhaseActualTargetFirstLocalLift
    (B N d L m : ℕ)
    (U : Matrix.unitaryGroup
      (DSVDensityRationalPublicLogPhaseHistoryLocalIndex
        B N d L) ℂ) :
    Matrix.unitaryGroup
      (Fin (d *
        dSVDensityRationalPublicLogPhaseResidual
          B N d L m)) ℂ := by
  classical
  let whole : Matrix.unitaryGroup
      (DSVDensityRationalPublicLogPhaseHistoryLocalIndex
          B N d L × Fin m) ℂ :=
    ⟨U.val ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ),
      Matrix.kronecker_mem_unitary U.property
        (Matrix.unitaryGroup (Fin m) ℂ).one_mem⟩
  exact dSVOriginalComputationalReindexedUnitary
    (dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
      B N d L m) whole

def dSVDensityRationalPublicLogPhasePhysicalHistoryUnitary
    (B : ℕ) {N d L : ℕ}
    (U : Matrix.unitaryGroup
      (DSVUniformDensityThresholdWholeHistoryLocalIndex
        N d L) ℂ) :
    Matrix.unitaryGroup
      (DSVDensityRationalPublicLogPhaseHistoryLocalIndex
        B N d L) ℂ := by
  classical
  exact ⟨(1 : Matrix (Fin B) (Fin B) ℂ) ⊗ₖ U.val,
    Matrix.kronecker_mem_unitary
      (Matrix.unitaryGroup (Fin B) ℂ).one_mem U.property⟩

end

end QuantumParallelRepetition

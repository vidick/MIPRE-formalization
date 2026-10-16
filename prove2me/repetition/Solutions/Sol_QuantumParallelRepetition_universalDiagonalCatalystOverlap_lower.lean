/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Repetition/TenProofs/QuantumParallelRepetition/Part01.lean (solution of QuantumParallelRepetition.universalDiagonalCatalystOverlap_lower);
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
import Theorems.Thm_QuantumParallelRepetition_harmonicSchmidtFiber_count_sq_le
import Theorems.Thm_QuantumParallelRepetition_universalCatalystOverlap_eq_sum

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
theorem rawEmbezzlementState_ne_zero
    (n : ℕ) (hn : 0 < n) :
    rawEmbezzlementState n ≠ 0 := by
  intro h
  let j : Fin n := ⟨0, hn⟩
  have hj := congrArg
    (fun z : EuclideanSpace ℂ (Fin n × Fin n) => z (j, j)) h
  simp [rawEmbezzlementState, j] at hj
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
theorem rawEmbezzlementState_norm_sq (n : ℕ) :
    ‖rawEmbezzlementState n‖ ^ 2 =
      harmonicNumber n := by
  classical
  have hamp (j : Fin n) :
      ‖(↑((Real.sqrt ((j.val : ℝ) + 1))⁻¹) : ℂ)‖ ^ 2 =
        ((j.val : ℝ) + 1)⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), inv_pow,
      Real.sq_sqrt (by positivity)]
  have hterm (i j : Fin n) :
      ‖if i = j then
        (↑((Real.sqrt ((i.val : ℝ) + 1))⁻¹) : ℂ)
      else
        0‖ ^ 2 =
      if i = j then
        ‖(↑((Real.sqrt ((i.val : ℝ) + 1))⁻¹) : ℂ)‖ ^ 2
      else
        0 := by
    split_ifs <;> simp
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  unfold harmonicNumber
  apply Finset.sum_congr rfl
  intro i _
  change
    (∑ j : Fin n,
      ‖if i = j then
        (↑((Real.sqrt ((i.val : ℝ) + 1))⁻¹) : ℂ)
      else
        0‖ ^ 2) = ((i.val : ℝ) + 1)⁻¹
  calc
    (∑ j : Fin n,
      ‖if i = j then
        (↑((Real.sqrt ((i.val : ℝ) + 1))⁻¹) : ℂ)
      else
        0‖ ^ 2) =
        ‖(↑((Real.sqrt ((i.val : ℝ) + 1))⁻¹) : ℂ)‖ ^ 2 := by
          simp_rw [hterm]
          simp
    _ = ((i.val : ℝ) + 1)⁻¹ := hamp i
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
theorem descendingHarmonicSchmidtPermutation_antitone
    {d n : ℕ} (σ : Fin d → ℝ) :
    Antitone (fun q : Fin (d * n) =>
      harmonicTensorSchmidtAmplitude (n := n) σ
        (descendingHarmonicSchmidtPermutation
          (n := n) σ q)) := by
  intro i j hij
  have h := Tuple.monotone_sort
    (fun q : Fin (d * n) =>
      -harmonicTensorSchmidtAmplitude (n := n) σ q)
    hij
  exact neg_le_neg_iff.mp h
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
theorem harmonicSchmidtThreshold_card_eq
    {d n : ℕ} (σ : Fin d → ℝ) (x : ℝ) :
    (((Finset.univ.filter fun q : Fin (d * n) =>
      x ≤ harmonicTensorSchmidtAmplitude (n := n) σ q).card : ℕ) : ℝ) =
      ∑ i : Fin d,
        (((Finset.univ.filter fun j : Fin n =>
          x ≤ σ i * (Real.sqrt ((j.val : ℝ) + 1))⁻¹).card : ℕ) : ℝ) := by
  classical
  calc
    (((Finset.univ.filter fun q : Fin (d * n) =>
      x ≤ harmonicTensorSchmidtAmplitude (n := n) σ q).card : ℕ) : ℝ) =
      ∑ q : Fin (d * n),
        if x ≤ harmonicTensorSchmidtAmplitude (n := n) σ q
          then (1 : ℝ) else 0 := by
            simp
    _ = ∑ p : Fin d × Fin n,
      if x ≤ harmonicTensorSchmidtAmplitude (n := n) σ
          (finProdFinEquiv p)
        then (1 : ℝ) else 0 := by
          exact (Equiv.sum_comp finProdFinEquiv
            (fun q : Fin (d * n) =>
              if x ≤ harmonicTensorSchmidtAmplitude
                (n := n) σ q then (1 : ℝ) else 0)).symm
    _ = ∑ i : Fin d,
        (((Finset.univ.filter fun j : Fin n =>
          x ≤ σ i * (Real.sqrt ((j.val : ℝ) + 1))⁻¹).card : ℕ) : ℝ) := by
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro i _
          simp [harmonicTensorSchmidtAmplitude]
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
theorem harmonicSchmidtThreshold_count_sq_le_one
    {d n : ℕ} (σ : Fin d → ℝ)
    (hσ : ∀ i, 0 ≤ σ i)
    (hunit : (∑ i : Fin d, σ i ^ 2) = 1)
    (x : ℝ) (hx : 0 ≤ x) :
    (((Finset.univ.filter fun q : Fin (d * n) =>
      x ≤ harmonicTensorSchmidtAmplitude (n := n) σ q).card : ℕ) : ℝ) *
        x ^ 2 ≤ 1 := by
  rw [harmonicSchmidtThreshold_card_eq]
  calc
    (∑ i : Fin d,
      (((Finset.univ.filter fun j : Fin n =>
        x ≤ σ i * (Real.sqrt ((j.val : ℝ) + 1))⁻¹).card : ℕ) : ℝ)) *
          x ^ 2 =
        ∑ i : Fin d,
          (((Finset.univ.filter fun j : Fin n =>
            x ≤ σ i * (Real.sqrt ((j.val : ℝ) + 1))⁻¹).card : ℕ) : ℝ) *
              x ^ 2 := by rw [Finset.sum_mul]
    _ ≤ ∑ i : Fin d, σ i ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact harmonicSchmidtFiber_count_sq_le
        (σ i) x (hσ i) hx
    _ = 1 := hunit
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
theorem descendingHarmonicSchmidtAmplitude_rank_sq_le_one
    {d n : ℕ} (σ : Fin d → ℝ)
    (hσ : ∀ i, 0 ≤ σ i)
    (hunit : (∑ i : Fin d, σ i ^ 2) = 1)
    (k : Fin (d * n)) :
    (((k.val : ℝ) + 1) *
      harmonicTensorSchmidtAmplitude (n := n) σ
        (descendingHarmonicSchmidtPermutation
          (n := n) σ k) ^ 2) ≤ 1 := by
  classical
  let π := descendingHarmonicSchmidtPermutation
    (n := n) σ
  let x := harmonicTensorSchmidtAmplitude
    (n := n) σ (π k)
  let S : Finset (Fin (d * n)) :=
    Finset.univ.filter fun q : Fin (d * n) =>
      x ≤ harmonicTensorSchmidtAmplitude (n := n) σ q
  have hx : 0 ≤ x := by
    dsimp [x, harmonicTensorSchmidtAmplitude]
    exact mul_nonneg (hσ _) (inv_nonneg.mpr (Real.sqrt_nonneg _))
  have hanti :=
    descendingHarmonicSchmidtPermutation_antitone
      (n := n) σ
  have hcard : k.val + 1 ≤ S.card := by
    calc
      k.val + 1 = (Finset.Iic k).card := by simp
      _ = ((Finset.Iic k).map π.toEmbedding).card := by simp
      _ ≤ S.card := by
        apply Finset.card_le_card
        intro q hq
        obtain ⟨l, hl, hleq⟩ := Finset.mem_map.mp hq
        subst q
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        exact hanti (Finset.mem_Iic.mp hl)
  have hcardreal : (k.val : ℝ) + 1 ≤ (S.card : ℝ) := by
    exact_mod_cast hcard
  have htotal := harmonicSchmidtThreshold_count_sq_le_one
    (n := n) σ hσ hunit x hx
  change ((k.val : ℝ) + 1) * x ^ 2 ≤ 1
  change (S.card : ℝ) * x ^ 2 ≤ 1 at htotal
  exact (mul_le_mul_of_nonneg_right hcardreal
    (sq_nonneg x)).trans htotal
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
theorem descendingHarmonicSchmidtAmplitude_le_harmonic
    {d n : ℕ} (σ : Fin d → ℝ)
    (hσ : ∀ i, 0 ≤ σ i)
    (hunit : (∑ i : Fin d, σ i ^ 2) = 1)
    (k : Fin (d * n)) :
    harmonicTensorSchmidtAmplitude (n := n) σ
      (descendingHarmonicSchmidtPermutation
        (n := n) σ k) ≤
      (Real.sqrt ((k.val : ℝ) + 1))⁻¹ := by
  let x := harmonicTensorSchmidtAmplitude (n := n) σ
    (descendingHarmonicSchmidtPermutation
      (n := n) σ k)
  have hx : 0 ≤ x := by
    dsimp [x, harmonicTensorSchmidtAmplitude]
    exact mul_nonneg (hσ _)
      (inv_nonneg.mpr (Real.sqrt_nonneg _))
  have hrank : 0 < (k.val : ℝ) + 1 := by positivity
  have hsqrt : 0 < Real.sqrt ((k.val : ℝ) + 1) :=
    Real.sqrt_pos.mpr hrank
  have hrankbound :=
    descendingHarmonicSchmidtAmplitude_rank_sq_le_one
      (n := n) σ hσ hunit k
  change x ≤ (Real.sqrt ((k.val : ℝ) + 1))⁻¹
  rw [← one_div]
  apply (le_div_iff₀ hsqrt).2
  have hsquare :
      (x * Real.sqrt ((k.val : ℝ) + 1)) ^ 2 ≤ 1 := by
    rw [mul_pow, Real.sq_sqrt hrank.le]
    nlinarith
  have hnonneg :
      0 ≤ x * Real.sqrt ((k.val : ℝ) + 1) :=
    mul_nonneg hx hsqrt.le
  nlinarith [sq_nonneg
    (x * Real.sqrt ((k.val : ℝ) + 1) + 1)]
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
theorem harmonicTensorSchmidtAmplitude_sq_sum
    {d n : ℕ} (σ : Fin d → ℝ)
    (hunit : (∑ i : Fin d, σ i ^ 2) = 1) :
    (∑ q : Fin (d * n),
      harmonicTensorSchmidtAmplitude
        (n := n) σ q ^ 2) =
      harmonicNumber n := by
  have hterm (i : Fin d) (j : Fin n) :
      (σ i * (Real.sqrt ((j.val : ℝ) + 1))⁻¹) ^ 2 =
        σ i ^ 2 * ((j.val : ℝ) + 1)⁻¹ := by
    rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity)]
  calc
    (∑ q : Fin (d * n),
      harmonicTensorSchmidtAmplitude
        (n := n) σ q ^ 2) =
      ∑ p : Fin d × Fin n,
        harmonicTensorSchmidtAmplitude
          (n := n) σ (finProdFinEquiv p) ^ 2 := by
            exact (Equiv.sum_comp finProdFinEquiv
              (fun q : Fin (d * n) =>
                harmonicTensorSchmidtAmplitude
                  (n := n) σ q ^ 2)).symm
    _ = ∑ i : Fin d,
      σ i ^ 2 * harmonicNumber n := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro i _
        simp_rw [harmonicTensorSchmidtAmplitude,
          Equiv.symm_apply_apply]
        simp_rw [hterm]
        rw [← Finset.mul_sum]
        rfl
    _ = (∑ i : Fin d, σ i ^ 2) *
      harmonicNumber n := by
        rw [Finset.sum_mul]
    _ = harmonicNumber n := by rw [hunit, one_mul]
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
theorem descendingHarmonicSchmidtAmplitude_sq_sum
    {d n : ℕ} (σ : Fin d → ℝ)
    (hunit : (∑ i : Fin d, σ i ^ 2) = 1) :
    (∑ k : Fin (d * n),
      harmonicTensorSchmidtAmplitude
        (n := n) σ
          (descendingHarmonicSchmidtPermutation
            (n := n) σ k) ^ 2) =
      harmonicNumber n := by
  calc
    (∑ k : Fin (d * n),
      harmonicTensorSchmidtAmplitude
        (n := n) σ
          (descendingHarmonicSchmidtPermutation
            (n := n) σ k) ^ 2) =
        ∑ q : Fin (d * n),
          harmonicTensorSchmidtAmplitude
            (n := n) σ q ^ 2 :=
          Equiv.sum_comp
            (descendingHarmonicSchmidtPermutation
              (n := n) σ)
            (fun q : Fin (d * n) =>
              harmonicTensorSchmidtAmplitude
                (n := n) σ q ^ 2)
    _ = harmonicNumber n :=
      harmonicTensorSchmidtAmplitude_sq_sum
        (n := n) σ hunit
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
theorem universalCatalystOverlapTerm_lower
    {d n : ℕ} (σ : Fin d → ℝ)
    (hσ : ∀ i, 0 ≤ σ i)
    (hunit : (∑ i : Fin d, σ i ^ 2) = 1)
    (k : Fin (d * n)) :
    ‖rawEmbezzlementState (d * n)‖⁻¹ *
      ‖rawEmbezzlementState n‖⁻¹ *
        harmonicTensorSchmidtAmplitude
          (n := n) σ
            (descendingHarmonicSchmidtPermutation
              (n := n) σ k) ^ 2 ≤
      universalCatalystOverlapTerm
        (n := n) σ k := by
  let a := harmonicTensorSchmidtAmplitude
    (n := n) σ
      (descendingHarmonicSchmidtPermutation
        (n := n) σ k)
  let h := (Real.sqrt ((k.val : ℝ) + 1))⁻¹
  let c := ‖rawEmbezzlementState (d * n)‖⁻¹ *
    ‖rawEmbezzlementState n‖⁻¹
  have ha : 0 ≤ a := by
    dsimp [a, harmonicTensorSchmidtAmplitude]
    exact mul_nonneg (hσ _)
      (inv_nonneg.mpr (Real.sqrt_nonneg _))
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  have hah : a ≤ h :=
    descendingHarmonicSchmidtAmplitude_le_harmonic
      (n := n) σ hσ hunit k
  change c * a ^ 2 ≤ _
  calc
    c * a ^ 2 = (c * a) * a := by ring
    _ ≤ (c * a) * h :=
      mul_le_mul_of_nonneg_left hah (mul_nonneg hc ha)
    _ = universalCatalystOverlapTerm
      (n := n) σ k := by
        dsimp [c, a, h, universalCatalystOverlapTerm]
        ring
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
    {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (σ : Fin d → ℝ)
    (hσ : ∀ i, 0 ≤ σ i)
    (hunit : (∑ i : Fin d, σ i ^ 2) = 1) :
    ‖rawEmbezzlementState n‖ /
      ‖rawEmbezzlementState (d * n)‖ ≤
        (inner ℂ
          (localUnitaryAction
            (harmonicSchmidtPermutationUnitary
              (n := n) σ)
            (harmonicSchmidtPermutationUnitary
              (n := n) σ)
            (embezzlementState (d * n)))
          (tensorEmbezzlementTarget (n := n)
            (diagonalSchmidtUnitVector σ hunit))).re := by
  have hnraw : ‖rawEmbezzlementState n‖ ≠ 0 :=
    norm_ne_zero_iff.mpr
      (rawEmbezzlementState_ne_zero n hn)
  have hdnraw :
      ‖rawEmbezzlementState (d * n)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr
      (rawEmbezzlementState_ne_zero
        (d * n) (Nat.mul_pos hd hn))
  calc
    ‖rawEmbezzlementState n‖ /
      ‖rawEmbezzlementState (d * n)‖ =
        ‖rawEmbezzlementState (d * n)‖⁻¹ *
          ‖rawEmbezzlementState n‖⁻¹ *
            harmonicNumber n := by
              rw [← rawEmbezzlementState_norm_sq n]
              field_simp
    _ = ∑ k : Fin (d * n),
      ‖rawEmbezzlementState (d * n)‖⁻¹ *
        ‖rawEmbezzlementState n‖⁻¹ *
          harmonicTensorSchmidtAmplitude
            (n := n) σ
              (descendingHarmonicSchmidtPermutation
                (n := n) σ k) ^ 2 := by
          rw [← descendingHarmonicSchmidtAmplitude_sq_sum
            (n := n) σ hunit, Finset.mul_sum]
    _ ≤ ∑ k : Fin (d * n),
      universalCatalystOverlapTerm
        (n := n) σ k := by
          apply Finset.sum_le_sum
          intro k _
          exact universalCatalystOverlapTerm_lower
            (n := n) σ hσ hunit k
    _ = (inner ℂ
      (localUnitaryAction
        (harmonicSchmidtPermutationUnitary
          (n := n) σ)
        (harmonicSchmidtPermutationUnitary
          (n := n) σ)
        (embezzlementState (d * n)))
      (tensorEmbezzlementTarget (n := n)
        (diagonalSchmidtUnitVector σ hunit))).re :=
      (universalCatalystOverlap_eq_sum
        (n := n) σ hunit).symm
end QuantumParallelRepetition

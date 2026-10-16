/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Repetition/TenProofs/QuantumParallelRepetition/Part01.lean (solution of QuantumParallelRepetition.exists_proofUniversalHarmonicCatalyst);
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
import Theorems.Thm_QuantumParallelRepetition_embezzlementState_norm
import Theorems.Thm_QuantumParallelRepetition_harmonicTargetLift_diagonal_action
import Theorems.Thm_QuantumParallelRepetition_linearMap_exists_singularBases
import Theorems.Thm_QuantumParallelRepetition_localUnitaryAction_norm
import Theorems.Thm_QuantumParallelRepetition_schmidtVector_apply
import Theorems.Thm_QuantumParallelRepetition_schmidtVector_norm_sq
import Theorems.Thm_QuantumParallelRepetition_tensorEmbezzlementTarget_norm
import Theorems.Thm_QuantumParallelRepetition_universalDiagonalCatalystOverlap_lower

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
attribute [instance] QuantumParallelRepetition.Strategy.alice_fintype QuantumParallelRepetition.Strategy.bob_fintype QuantumParallelRepetition.Strategy.alice_decidableEq QuantumParallelRepetition.Strategy.bob_decidableEq

namespace QuantumParallelRepetition
section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
attribute [instance] QuantumParallelRepetition.Strategy.alice_fintype QuantumParallelRepetition.Strategy.bob_fintype QuantumParallelRepetition.Strategy.alice_decidableEq QuantumParallelRepetition.Strategy.bob_decidableEq
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
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
attribute [instance] QuantumParallelRepetition.Strategy.alice_fintype QuantumParallelRepetition.Strategy.bob_fintype QuantumParallelRepetition.Strategy.alice_decidableEq QuantumParallelRepetition.Strategy.bob_decidableEq
theorem unitVector_distance_of_real_overlap
    {ι : Type*} [Fintype ι]
    (z w : EuclideanSpace ℂ ι)
    (hz : ‖z‖ = 1) (hw : ‖w‖ = 1)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hoverlap : 1 - ε ≤ (inner ℂ z w).re) :
    ‖z - w‖ ≤ Real.sqrt (2 * ε) := by
  have hoverlap' : 1 - ε ≤ RCLike.re (inner ℂ z w) := by
    exact hoverlap
  have hsq : ‖z - w‖ ^ 2 ≤ 2 * ε := by
    rw [@norm_sub_sq ℂ, hz, hw]
    nlinarith [hoverlap']
  have hsqrt : (Real.sqrt (2 * ε)) ^ 2 = 2 * ε :=
    Real.sq_sqrt (by positivity)
  nlinarith [norm_nonneg (z - w), Real.sqrt_nonneg (2 * ε)]
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
set_option autoImplicit true
attribute [instance] QuantumParallelRepetition.Strategy.alice_fintype QuantumParallelRepetition.Strategy.bob_fintype QuantumParallelRepetition.Strategy.alice_decidableEq QuantumParallelRepetition.Strategy.bob_decidableEq
set_option backward.isDefEq.respectTransparency false in
theorem exists_proofSchmidtDecomposition
    {d : ℕ}
    (ξ : EuclideanSpace ℂ (Fin d × Fin d)) :
    ∃ (σ : Fin d → ℝ)
      (U V : Matrix.unitaryGroup (Fin d) ℂ),
      (∀ i, 0 ≤ σ i) ∧
        ξ = schmidtVector σ U V := by
  classical
  let C : Matrix (Fin d) (Fin d) ℂ := fun b a => ξ (a, b)
  let T : EuclideanSpace ℂ (Fin d) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin d) := Matrix.toEuclideanLin C
  obtain ⟨σ, u, v, hσ, hsing⟩ :=
    linearMap_exists_singularBases T
  refine ⟨σ,
    conjugateUnitary (orthonormalBasisUnitary v),
    orthonormalBasisUnitary u, hσ, ?_⟩
  ext ⟨a, b⟩
  rw [schmidtVector_apply]
  have hrepr :
      T ((EuclideanSpace.basisFun (Fin d) ℂ) a) =
        ∑ i : Fin d,
          inner ℂ (v i) ((EuclideanSpace.basisFun (Fin d) ℂ) a) •
            T (v i) := by
    calc
      T ((EuclideanSpace.basisFun (Fin d) ℂ) a) =
          T (∑ i : Fin d,
            inner ℂ (v i) ((EuclideanSpace.basisFun (Fin d) ℂ) a) •
              v i) := by
        rw [v.sum_repr']
      _ = _ := by
        simp
  have hcoord := congrArg
    (fun z : EuclideanSpace ℂ (Fin d) => z b) hrepr
  simpa [T, C, Matrix.toLpLin_apply,
    EuclideanSpace.basisFun_apply, Matrix.mulVec_single_one,
    Matrix.col_apply, EuclideanSpace.inner_single_right,
    conjugateUnitary_apply,
    orthonormalBasisUnitary_apply, hsing,
    mul_assoc, mul_left_comm, mul_comm] using hcoord
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
set_option autoImplicit true
attribute [instance] QuantumParallelRepetition.Strategy.alice_fintype QuantumParallelRepetition.Strategy.bob_fintype QuantumParallelRepetition.Strategy.alice_decidableEq QuantumParallelRepetition.Strategy.bob_decidableEq
theorem exists_proofUnitSchmidtDecomposition
    {d : ℕ}
    (ξ : BipartiteUnitVector d) :
    ∃ (σ : Fin d → ℝ)
      (U V : Matrix.unitaryGroup (Fin d) ℂ),
      (∀ i, 0 ≤ σ i) ∧
        (∑ i : Fin d, σ i ^ 2) = 1 ∧
        ξ.val = schmidtVector σ U V := by
  obtain ⟨σ, U, V, hσ, hξ⟩ :=
    exists_proofSchmidtDecomposition ξ.val
  refine ⟨σ, U, V, hσ, ?_, hξ⟩
  have hnorm : ‖schmidtVector σ U V‖ ^ 2 = 1 := by
    rw [← hξ, ξ.property]
    norm_num
  exact (schmidtVector_norm_sq σ U V).symm.trans hnorm
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
set_option autoImplicit true
attribute [instance] QuantumParallelRepetition.Strategy.alice_fintype QuantumParallelRepetition.Strategy.bob_fintype QuantumParallelRepetition.Strategy.alice_decidableEq QuantumParallelRepetition.Strategy.bob_decidableEq
theorem harmonicNumber_eq_harmonic (n : ℕ) :
    harmonicNumber n = (harmonic n : ℝ) := by
  unfold harmonicNumber harmonic
  rw [Finset.sum_fin_eq_sum_range]
  simp only [Rat.cast_sum, Rat.cast_inv, Nat.cast_add, Nat.cast_one]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Finset.mem_range.mp hi]
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
set_option autoImplicit true
attribute [instance] QuantumParallelRepetition.Strategy.alice_fintype QuantumParallelRepetition.Strategy.bob_fintype QuantumParallelRepetition.Strategy.alice_decidableEq QuantumParallelRepetition.Strategy.bob_decidableEq
theorem harmonicNumber_log_lower (n : ℕ) :
    Real.log ((n : ℝ) + 1) ≤ harmonicNumber n := by
  rw [harmonicNumber_eq_harmonic]
  simpa [Nat.cast_add, Nat.cast_one] using log_add_one_le_harmonic n
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
set_option autoImplicit true
attribute [instance] QuantumParallelRepetition.Strategy.alice_fintype QuantumParallelRepetition.Strategy.bob_fintype QuantumParallelRepetition.Strategy.alice_decidableEq QuantumParallelRepetition.Strategy.bob_decidableEq
theorem harmonicNumber_log_upper (n : ℕ) :
    harmonicNumber n ≤ 1 + Real.log (n : ℝ) := by
  rw [harmonicNumber_eq_harmonic]
  exact harmonic_le_one_add_log n
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
set_option autoImplicit true
attribute [instance] QuantumParallelRepetition.Strategy.alice_fintype QuantumParallelRepetition.Strategy.bob_fintype QuantumParallelRepetition.Strategy.alice_decidableEq QuantumParallelRepetition.Strategy.bob_decidableEq
theorem harmonicNumber_pos {n : ℕ} (hn : 0 < n) :
    0 < harmonicNumber n := by
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  exact (Real.log_pos (by linarith : (1 : ℝ) < (n : ℝ) + 1)).trans_le
    (harmonicNumber_log_lower n)
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
set_option autoImplicit true
attribute [instance] QuantumParallelRepetition.Strategy.alice_fintype QuantumParallelRepetition.Strategy.bob_fintype QuantumParallelRepetition.Strategy.alice_decidableEq QuantumParallelRepetition.Strategy.bob_decidableEq
theorem harmonicNumber_mul_le_add
    {d n : ℕ} (hd : 0 < d) (hn : 0 < n) :
    harmonicNumber (d * n) ≤
      harmonicNumber n + (1 + Real.log (d : ℝ)) := by
  have hdreal : 0 < (d : ℝ) := by exact_mod_cast hd
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlogn : Real.log (n : ℝ) ≤ harmonicNumber n := by
    exact (Real.log_le_log hnreal (by linarith :
      (n : ℝ) ≤ (n : ℝ) + 1)).trans
      (harmonicNumber_log_lower n)
  calc
    harmonicNumber (d * n) ≤
        1 + Real.log ((d * n : ℕ) : ℝ) :=
          harmonicNumber_log_upper (d * n)
    _ = 1 + (Real.log (d : ℝ) + Real.log (n : ℝ)) := by
      rw [Nat.cast_mul, Real.log_mul hdreal.ne' hnreal.ne']
    _ ≤ harmonicNumber n + (1 + Real.log (d : ℝ)) := by
      linarith
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
set_option autoImplicit true
attribute [instance] QuantumParallelRepetition.Strategy.alice_fintype QuantumParallelRepetition.Strategy.bob_fintype QuantumParallelRepetition.Strategy.alice_decidableEq QuantumParallelRepetition.Strategy.bob_decidableEq
theorem exists_proofHarmonicNumber_gt (bound : ℝ) :
    ∃ n : ℕ, bound < harmonicNumber n := by
  obtain ⟨n, hn⟩ := exists_nat_gt (Real.exp bound)
  have hpositive : 0 < (n : ℝ) + 1 := by positivity
  have hlog : bound < Real.log ((n : ℝ) + 1) := by
    apply (Real.lt_log_iff_exp_lt hpositive).mpr
    exact lt_trans hn (by linarith)
  exact ⟨n, hlog.trans_le (harmonicNumber_log_lower n)⟩
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
set_option autoImplicit true
attribute [instance] QuantumParallelRepetition.Strategy.alice_fintype QuantumParallelRepetition.Strategy.bob_fintype QuantumParallelRepetition.Strategy.alice_decidableEq QuantumParallelRepetition.Strategy.bob_decidableEq
theorem exists_proofHarmonicNumber_ratio_ge
    (d : ℕ) (hd : 0 < d)
    {ε : ℝ} (hε : 0 < ε) (hεone : ε ≤ 1) :
    ∃ n : ℕ, 0 < n ∧
      1 - ε ≤ harmonicNumber n /
        harmonicNumber (d * n) := by
  let C : ℝ := 1 + Real.log (d : ℝ)
  have hdreal : 0 < (d : ℝ) := by exact_mod_cast hd
  have hlogd : 0 ≤ Real.log (d : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast hd
  have hC : 0 < C := by
    dsimp [C]
    linarith
  obtain ⟨n, hnlarge⟩ :=
    exists_proofHarmonicNumber_gt (C / ε)
  have hn : 0 < n := by
    have hzero : harmonicNumber 0 = 0 := by
      rw [harmonicNumber_eq_harmonic]
      simp
    by_contra hnot
    have hnzero : n = 0 := by omega
    rw [hnzero, hzero] at hnlarge
    have hpositive : 0 < C / ε := div_pos hC hε
    linarith
  have hden : 0 < harmonicNumber (d * n) :=
    harmonicNumber_pos (Nat.mul_pos hd hn)
  have hupper := harmonicNumber_mul_le_add hd hn
  have hbudget : C < ε * harmonicNumber n := by
    have h := (div_lt_iff₀ hε).mp hnlarge
    nlinarith
  refine ⟨n, hn, (le_div_iff₀ hden).mpr ?_⟩
  have hscaled := mul_le_mul_of_nonneg_left
    hupper (sub_nonneg.mpr hεone)
  have hproduct : 0 ≤ ε * C := mul_nonneg hε.le hC.le
  change (1 - ε) * harmonicNumber (d * n) ≤
    harmonicNumber n
  change harmonicNumber (d * n) ≤
    harmonicNumber n + C at hupper
  change (1 - ε) * harmonicNumber (d * n) ≤
    (1 - ε) * (harmonicNumber n + C) at hscaled
  nlinarith
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
attribute [instance] QuantumParallelRepetition.Strategy.alice_fintype QuantumParallelRepetition.Strategy.bob_fintype QuantumParallelRepetition.Strategy.alice_decidableEq QuantumParallelRepetition.Strategy.bob_decidableEq
theorem localUnitaryAction_comp
    {m : ℕ}
    (U₁ V₁ U₂ V₂ : Matrix.unitaryGroup (Fin m) ℂ)
    (ψ : EuclideanSpace ℂ (Fin m × Fin m)) :
    localUnitaryAction U₁ V₁
      (localUnitaryAction U₂ V₂ ψ) =
        localUnitaryAction (U₁ * U₂) (V₁ * V₂) ψ := by
  apply WithLp.ofLp_injective
  change
    ((U₁.val ⊗ₖ V₁.val).mulVec
      ((U₂.val ⊗ₖ V₂.val).mulVec (ofLp ψ))) =
      ((U₁ * U₂).val ⊗ₖ (V₁ * V₂).val).mulVec (ofLp ψ)
  rw [Matrix.mulVec_mulVec,
    ← Matrix.mul_kronecker_mul]
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
attribute [instance] QuantumParallelRepetition.Strategy.alice_fintype QuantumParallelRepetition.Strategy.bob_fintype QuantumParallelRepetition.Strategy.alice_decidableEq QuantumParallelRepetition.Strategy.bob_decidableEq
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

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
attribute [instance] QuantumParallelRepetition.Strategy.alice_fintype QuantumParallelRepetition.Strategy.bob_fintype QuantumParallelRepetition.Strategy.alice_decidableEq QuantumParallelRepetition.Strategy.bob_decidableEq
theorem universalDiagonalCatalystOverlap_of_harmonic_ratio
    {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (σ : Fin d → ℝ)
    (hσ : ∀ i, 0 ≤ σ i)
    (hunit : (∑ i : Fin d, σ i ^ 2) = 1)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    (hratio : 1 - δ ≤
      harmonicNumber n /
        harmonicNumber (d * n)) :
    1 - δ ≤
      (inner ℂ
        (localUnitaryAction
          (harmonicSchmidtPermutationUnitary
            (n := n) σ)
          (harmonicSchmidtPermutationUnitary
            (n := n) σ)
          (embezzlementState (d * n)))
        (tensorEmbezzlementTarget (n := n)
          (diagonalSchmidtUnitVector σ hunit))).re := by
  let q : ℝ :=
    ‖rawEmbezzlementState n‖ /
      ‖rawEmbezzlementState (d * n)‖
  have hq : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg (norm_nonneg _) (norm_nonneg _)
  have hqsquare :
      q ^ 2 = harmonicNumber n /
        harmonicNumber (d * n) := by
    dsimp [q]
    rw [div_pow,
      rawEmbezzlementState_norm_sq,
      rawEmbezzlementState_norm_sq]
  have hgoalnonneg : 0 ≤ 1 - δ := sub_nonneg.mpr hδone
  have hgoalsquare : (1 - δ) ^ 2 ≤ 1 - δ := by
    nlinarith [mul_nonneg hδ hgoalnonneg]
  have hqbound : 1 - δ ≤ q := by
    rw [← hqsquare] at hratio
    nlinarith [sq_nonneg (q + (1 - δ))]
  exact hqbound.trans
    (universalDiagonalCatalystOverlap_lower
      hd hn σ hσ hunit)
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option autoImplicit true
attribute [instance] QuantumParallelRepetition.Strategy.alice_fintype QuantumParallelRepetition.Strategy.bob_fintype QuantumParallelRepetition.Strategy.alice_decidableEq QuantumParallelRepetition.Strategy.bob_decidableEq
theorem universalDiagonalCatalyst_distance
    {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (σ : Fin d → ℝ)
    (hσ : ∀ i, 0 ≤ σ i)
    (hunit : (∑ i : Fin d, σ i ^ 2) = 1)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    (hratio : 1 - δ ≤
      harmonicNumber n /
        harmonicNumber (d * n)) :
    ‖localUnitaryAction
      (harmonicSchmidtPermutationUnitary
        (n := n) σ)
      (harmonicSchmidtPermutationUnitary
        (n := n) σ)
      (embezzlementState (d * n)) -
        tensorEmbezzlementTarget (n := n)
          (diagonalSchmidtUnitVector σ hunit)‖ ≤
      Real.sqrt (2 * δ) := by
  apply unitVector_distance_of_real_overlap
    (localUnitaryAction
      (harmonicSchmidtPermutationUnitary
        (n := n) σ)
      (harmonicSchmidtPermutationUnitary
        (n := n) σ)
      (embezzlementState (d * n)))
    (tensorEmbezzlementTarget (n := n)
      (diagonalSchmidtUnitVector σ hunit))
    (by rw [localUnitaryAction_norm,
      embezzlementState_norm (d * n)
        (Nat.mul_pos hd hn)])
    (tensorEmbezzlementTarget_norm hn
      (diagonalSchmidtUnitVector σ hunit))
    δ hδ
  exact universalDiagonalCatalystOverlap_of_harmonic_ratio
    hd hn σ hσ hunit δ hδ hδone hratio
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
attribute [instance] QuantumParallelRepetition.Strategy.alice_fintype QuantumParallelRepetition.Strategy.bob_fintype QuantumParallelRepetition.Strategy.alice_decidableEq QuantumParallelRepetition.Strategy.bob_decidableEq
theorem _root_.solution
    (d : ℕ) (hd : 0 < d)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧
      ∀ ξ : BipartiteUnitVector d,
        ∃ U V : Matrix.unitaryGroup (Fin (d * n)) ℂ,
          ‖localUnitaryAction U V
            (embezzlementState (d * n)) -
              tensorEmbezzlementTarget (n := n) ξ‖ ≤ ε := by
  let δ : ℝ := min (ε ^ 2 / 2) 1
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (by positivity) zero_lt_one
  have hδone : δ ≤ 1 := min_le_right _ _
  obtain ⟨n, hn, hratio⟩ :=
    exists_proofHarmonicNumber_ratio_ge d hd hδ hδone
  refine ⟨n, hn, ?_⟩
  intro ξ
  obtain ⟨σ, U, V, hσ, hunit, hξ⟩ :=
    exists_proofUnitSchmidtDecomposition ξ
  let LU := harmonicTargetLiftUnitary (n := n) U
  let LV := harmonicTargetLiftUnitary (n := n) V
  let P := harmonicSchmidtPermutationUnitary
    (n := n) σ
  refine ⟨LU * P, LV * P, ?_⟩
  have hdiagonal := universalDiagonalCatalyst_distance
    hd hn σ hσ hunit δ hδ.le hδone hratio
  have htarget := harmonicTargetLift_diagonal_action
    (n := n) ξ σ hunit U V hξ
  have hdeltaeps : 2 * δ ≤ ε ^ 2 := by
    have hmin : δ ≤ ε ^ 2 / 2 := min_le_left _ _
    linarith
  have hsqrt : Real.sqrt (2 * δ) ≤ ε := by
    have hsq : (Real.sqrt (2 * δ)) ^ 2 = 2 * δ :=
      Real.sq_sqrt (by positivity)
    nlinarith [Real.sqrt_nonneg (2 * δ)]
  calc
    ‖localUnitaryAction (LU * P) (LV * P)
      (embezzlementState (d * n)) -
        tensorEmbezzlementTarget (n := n) ξ‖ =
      ‖localUnitaryAction LU LV
        (localUnitaryAction P P
          (embezzlementState (d * n)) -
            tensorEmbezzlementTarget (n := n)
              (diagonalSchmidtUnitVector σ hunit))‖ := by
        rw [localUnitaryAction_sub,
          localUnitaryAction_comp]
        rw [htarget]
    _ = ‖localUnitaryAction P P
      (embezzlementState (d * n)) -
        tensorEmbezzlementTarget (n := n)
          (diagonalSchmidtUnitVector σ hunit)‖ :=
        localUnitaryAction_norm LU LV _
    _ ≤ Real.sqrt (2 * δ) := hdiagonal
    _ ≤ ε := hsqrt
end QuantumParallelRepetition

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Repetition/TenProofs/QuantumParallelRepetition/Part01.lean (solution of QuantumParallelRepetition.exact_matrix_log_entropy_filter_jensen);
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
import Theorems.Thm_QuantumParallelRepetition_scalarResolventFilter_memLp_two
import Theorems.Thm_QuantumParallelRepetition_scalar_entropy_resolvent_integral
import Theorems.Thm_QuantumParallelRepetition_spectralPurificationFilter_memLp_two
import Theorems.Thm_QuantumParallelRepetition_weightedSpectralEntropyJensen_eq_shifted_inverse
import Theorems.Thm_QuantumParallelRepetition_weighted_spectralPurificationFilter_variance_le_inverse_jensen

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
attribute [instance] QuantumParallelRepetition.Strategy.alice_fintype QuantumParallelRepetition.Strategy.bob_fintype QuantumParallelRepetition.Strategy.alice_decidableEq QuantumParallelRepetition.Strategy.bob_decidableEq

namespace QuantumParallelRepetition
section
open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
attribute [instance] QuantumParallelRepetition.Strategy.alice_fintype QuantumParallelRepetition.Strategy.bob_fintype QuantumParallelRepetition.Strategy.alice_decidableEq QuantumParallelRepetition.Strategy.bob_decidableEq
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
theorem bochner_integral_posSemidef
    {α d : Type*} [MeasurableSpace α]
    [Fintype d] [DecidableEq d]
    {μ : Measure α} {f : α → Matrix d d ℂ}
    (hf : Integrable f μ)
    (hpos : ∀ᵐ t ∂μ, (f t).PosSemidef) :
    (∫ t, f t ∂μ).PosSemidef := by
  have hadjoint :
      star (∫ t, f t ∂μ) = ∫ t, star (f t) ∂μ := by
    exact (ContinuousLinearMap.integral_comp_comm
      matrixAdjointCLM hf).symm
  have hadjoint_ae : (fun t => star (f t)) =ᵐ[μ] f := by
    filter_upwards [hpos] with t ht
    simpa only [Matrix.star_eq_conjTranspose] using ht.isHermitian.eq
  have hhermitian : (∫ t, f t ∂μ).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    have hstar : star (∫ t, f t ∂μ) = ∫ t, f t ∂μ :=
      hadjoint.trans (integral_congr_ae hadjoint_ae)
    have hentry := congr_fun (congr_fun hstar i) j
    simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose] using hentry
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hhermitian
  intro x
  have hcomm :
      (∫ t, matrixQuadraticCLM x (f t) ∂μ) =
        matrixQuadraticCLM x (∫ t, f t ∂μ) :=
    ContinuousLinearMap.integral_comp_comm
      (matrixQuadraticCLM x) hf
  change 0 ≤ matrixQuadraticCLM x (∫ t, f t ∂μ)
  rw [← hcomm]
  apply integral_nonneg_of_ae
  filter_upwards [hpos] with t ht
  exact ht.dotProduct_mulVec_nonneg x
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
attribute [instance] QuantumParallelRepetition.Strategy.alice_fintype QuantumParallelRepetition.Strategy.bob_fintype QuantumParallelRepetition.Strategy.alice_decidableEq QuantumParallelRepetition.Strategy.bob_decidableEq
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
theorem matrix_memLp_two_mul_integrable
    {α d : Type*} [MeasurableSpace α]
    [Fintype d] {μ : Measure α}
    {f g : α → Matrix d d ℂ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun t => f t * g t) μ := by
  classical
  apply Integrable.of_eval
  intro i
  apply Integrable.of_eval
  intro j
  change Integrable (fun t => ∑ k : d, f t i k * g t k j) μ
  apply integrable_finsetSum Finset.univ
  intro k _
  exact ((hf.eval i).eval k).integrable_mul ((hg.eval k).eval j)
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
attribute [instance] QuantumParallelRepetition.Strategy.alice_fintype QuantumParallelRepetition.Strategy.bob_fintype QuantumParallelRepetition.Strategy.alice_decidableEq QuantumParallelRepetition.Strategy.bob_decidableEq
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
theorem spectralPurificationFilter_difference_gram_integrable
    {d : Type*} [Fintype d] [DecidableEq d]
    (F M : Matrix d d ℂ)
    (hF : F.PosSemidef) (hM : M.PosSemidef) :
    IntegrableOn
      (fun s : ℝ =>
        star (spectralPurificationFilter F hF s -
          spectralPurificationFilter M hM s) *
        (spectralPurificationFilter F hF s -
          spectralPurificationFilter M hM s))
      (Ioi 0) := by
  have hdelta :
      MemLp (fun s : ℝ =>
        spectralPurificationFilter F hF s -
          spectralPurificationFilter M hM s) 2
        (volume.restrict (Ioi 0)) :=
    (spectralPurificationFilter_memLp_two F hF).sub
      (spectralPurificationFilter_memLp_two M hM)
  exact matrix_memLp_two_mul_integrable hdelta.star hdelta
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
attribute [instance] QuantumParallelRepetition.Strategy.alice_fintype QuantumParallelRepetition.Strategy.bob_fintype QuantumParallelRepetition.Strategy.alice_decidableEq QuantumParallelRepetition.Strategy.bob_decidableEq
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
theorem scalar_entropy_resolvent_integrable
    {z : ℝ} (hz : 0 ≤ z) :
    IntegrableOn
      (fun s : ℝ => z / (1 + s) - z / (z + s))
      (Ioi 0) := by
  have hone :
      MemLp (fun s : ℝ => 1 / (1 + s)) 2
        (volume.restrict (Ioi 0)) :=
    scalarResolventFilter_memLp_two (z := 1) (by norm_num)
  have hzfilter := scalarResolventFilter_memLp_two hz
  have hproduct :
      Integrable
        (fun s : ℝ =>
          (1 / (1 + s)) * (z / (z + s)))
        (volume.restrict (Ioi 0)) :=
    hone.integrable_mul hzfilter
  have hscaled :
      IntegrableOn
        (fun s : ℝ =>
          (z - 1) * ((1 / (1 + s)) * (z / (z + s))))
        (Ioi 0) := hproduct.const_mul (z - 1)
  refine hscaled.congr_fun (fun s hs => ?_) measurableSet_Ioi
  have hspos : 0 < s := hs
  have hzone : 1 + s ≠ 0 := ne_of_gt (by linarith)
  have hzden : z + s ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ; ring
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
attribute [instance] QuantumParallelRepetition.Strategy.alice_fintype QuantumParallelRepetition.Strategy.bob_fintype QuantumParallelRepetition.Strategy.alice_decidableEq QuantumParallelRepetition.Strategy.bob_decidableEq
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
theorem spectralEntropyKernel_integrable
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    IntegrableOn (spectralEntropyKernel F hF) (Ioi 0) := by
  classical
  let eigenvalue := hF.isHermitian.eigenvalues
  have hdiag :
      IntegrableOn
        (fun s : ℝ => Matrix.diagonal fun i : d =>
          ((eigenvalue i / (1 + s) -
            eigenvalue i / (eigenvalue i + s) : ℝ) : ℂ))
        (Ioi 0) := by
    apply Integrable.of_eval
    intro i
    apply Integrable.of_eval
    intro j
    by_cases hij : i = j
    · subst j
      have heigenvalue : 0 ≤ eigenvalue i :=
        hF.eigenvalues_nonneg i
      have hcomplex :
          Integrable
            (fun s : ℝ =>
              ((eigenvalue i / (1 + s) -
                eigenvalue i / (eigenvalue i + s) : ℝ) : ℂ))
            (volume.restrict (Ioi 0)) :=
        MeasureTheory.Integrable.ofReal (𝕜 := ℂ)
          (scalar_entropy_resolvent_integrable heigenvalue)
      simpa only [Matrix.diagonal_apply_eq] using hcomplex
    · simp [hij]
  exact
    (spectralConjugationCLM hF.isHermitian.eigenvectorUnitary).integrable_comp
      hdiag
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
attribute [instance] QuantumParallelRepetition.Strategy.alice_fintype QuantumParallelRepetition.Strategy.bob_fintype QuantumParallelRepetition.Strategy.alice_decidableEq QuantumParallelRepetition.Strategy.bob_decidableEq
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
theorem weightedSpectralFilterVariance_integrable
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (weight : ι → ℝ) (F : ι → Matrix d d ℂ)
    (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) :
    IntegrableOn
      (weightedSpectralFilterVariance weight F M positive hM)
      (Ioi 0) := by
  unfold weightedSpectralFilterVariance
  apply integrable_finsetSum Finset.univ
  intro i _
  exact (spectralPurificationFilter_difference_gram_integrable
    (F i) M (positive i) hM).smul (weight i)
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
attribute [instance] QuantumParallelRepetition.Strategy.alice_fintype QuantumParallelRepetition.Strategy.bob_fintype QuantumParallelRepetition.Strategy.alice_decidableEq QuantumParallelRepetition.Strategy.bob_decidableEq
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
theorem weightedSpectralEntropyJensen_integrable
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (weight : ι → ℝ) (F : ι → Matrix d d ℂ)
    (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) :
    IntegrableOn
      (weightedSpectralEntropyJensen weight F M positive hM)
      (Ioi 0) := by
  unfold weightedSpectralEntropyJensen
  apply Integrable.sub
  · apply integrable_finsetSum Finset.univ
    intro i _
    exact (spectralEntropyKernel_integrable
      (F i) (positive i)).smul (weight i)
  · exact spectralEntropyKernel_integrable M hM
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
attribute [instance] QuantumParallelRepetition.Strategy.alice_fintype QuantumParallelRepetition.Strategy.bob_fintype QuantumParallelRepetition.Strategy.alice_decidableEq QuantumParallelRepetition.Strategy.bob_decidableEq
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
theorem integrated_weighted_spectralPurificationFilter_jensen
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (weight : ι → ℝ) (F : ι → Matrix d d ℂ)
    (M : Matrix d d ℂ)
    (nonnegative : ∀ i, 0 ≤ weight i)
    (normalized : (∑ i : ι, weight i) = 1)
    (mean : (∑ i : ι, weight i • F i) = M)
    (positive : ∀ i, (F i).PosSemidef) :
    let hM : M.PosSemidef := by
      rw [← mean]
      exact weighted_positive_matrix_mean weight F nonnegative positive
    ((∫ s in Ioi (0 : ℝ),
        weightedSpectralEntropyJensen weight F M positive hM s) -
      (∫ s in Ioi (0 : ℝ),
        weightedSpectralFilterVariance weight F M positive hM s)).PosSemidef := by
  dsimp
  let hM : M.PosSemidef := by
    rw [← mean]
    exact weighted_positive_matrix_mean weight F nonnegative positive
  have hentropy := weightedSpectralEntropyJensen_integrable
    weight F M positive hM
  have hvariance := weightedSpectralFilterVariance_integrable
    weight F M positive hM
  have hremainder :
      Integrable
        (fun s : ℝ =>
          weightedSpectralEntropyJensen weight F M positive hM s -
            weightedSpectralFilterVariance weight F M positive hM s)
        (volume.restrict (Ioi 0)) :=
    hentropy.sub hvariance
  have hpointwise :
      ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
        (weightedSpectralEntropyJensen weight F M positive hM s -
          weightedSpectralFilterVariance weight F M positive hM s).PosSemidef := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hspos : 0 < s := hs
    rw [weightedSpectralEntropyJensen_eq_shifted_inverse
      weight F M positive hM normalized mean hspos]
    unfold weightedSpectralFilterVariance
    exact weighted_spectralPurificationFilter_variance_le_inverse_jensen
      weight F M nonnegative normalized mean positive hspos
  have hintegral := bochner_integral_posSemidef hremainder hpointwise
  rw [integral_sub hentropy hvariance] at hintegral
  exact hintegral
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
attribute [instance] QuantumParallelRepetition.Strategy.alice_fintype QuantumParallelRepetition.Strategy.bob_fintype QuantumParallelRepetition.Strategy.alice_decidableEq QuantumParallelRepetition.Strategy.bob_decidableEq
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
theorem diagonalEntropyKernel_integrable
    {d : Type*} [Fintype d] [DecidableEq d]
    (eigenvalue : d → ℝ)
    (nonnegative : ∀ i, 0 ≤ eigenvalue i) :
    IntegrableOn (diagonalEntropyKernel eigenvalue) (Ioi 0) := by
  classical
  apply Integrable.of_eval
  intro i
  apply Integrable.of_eval
  intro j
  by_cases hij : i = j
  · subst j
    have hcomplex :
        Integrable
          (fun s : ℝ =>
            ((eigenvalue i / (1 + s) -
              eigenvalue i / (eigenvalue i + s) : ℝ) : ℂ))
          (volume.restrict (Ioi 0)) :=
      MeasureTheory.Integrable.ofReal (𝕜 := ℂ)
        (scalar_entropy_resolvent_integrable (nonnegative i))
    simpa only [diagonalEntropyKernel,
      Matrix.diagonal_apply_eq] using hcomplex
  · simp [diagonalEntropyKernel, hij]
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
attribute [instance] QuantumParallelRepetition.Strategy.alice_fintype QuantumParallelRepetition.Strategy.bob_fintype QuantumParallelRepetition.Strategy.alice_decidableEq QuantumParallelRepetition.Strategy.bob_decidableEq
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
theorem integral_diagonalEntropyKernel
    {d : Type*} [Fintype d] [DecidableEq d]
    (eigenvalue : d → ℝ)
    (nonnegative : ∀ i, 0 ≤ eigenvalue i) :
    (∫ s in Ioi (0 : ℝ), diagonalEntropyKernel eigenvalue s) =
      Matrix.diagonal fun i =>
        ((eigenvalue i * Real.log (eigenvalue i) : ℝ) : ℂ) := by
  classical
  have hmatrix := diagonalEntropyKernel_integrable
    eigenvalue nonnegative
  have hrows :
      ∀ i : d,
        Integrable
          (fun s : ℝ => diagonalEntropyKernel eigenvalue s i)
          (volume.restrict (Ioi 0)) :=
    fun i => hmatrix.eval i
  have hentry (i : d) :
      ∀ j : d,
        Integrable
          (fun s : ℝ => diagonalEntropyKernel eigenvalue s i j)
          (volume.restrict (Ioi 0)) :=
    fun j => (hrows i).eval j
  ext i j
  rw [MeasureTheory.eval_integral hrows i,
    MeasureTheory.eval_integral (hentry i) j]
  by_cases hij : i = j
  · subst j
    simp only [diagonalEntropyKernel, Matrix.diagonal_apply_eq]
    calc
      (∫ s in Ioi (0 : ℝ),
        ((eigenvalue i / (1 + s) -
          eigenvalue i / (eigenvalue i + s) : ℝ) : ℂ)) =
          ((∫ s in Ioi (0 : ℝ),
            eigenvalue i / (1 + s) -
              eigenvalue i / (eigenvalue i + s) : ℝ) : ℂ) :=
            integral_ofReal
      _ = ((eigenvalue i * Real.log (eigenvalue i) : ℝ) : ℂ) := by
            rw [scalar_entropy_resolvent_integral (nonnegative i)]
  · simp [diagonalEntropyKernel, hij]
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
attribute [instance] QuantumParallelRepetition.Strategy.alice_fintype QuantumParallelRepetition.Strategy.bob_fintype QuantumParallelRepetition.Strategy.alice_decidableEq QuantumParallelRepetition.Strategy.bob_decidableEq
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
theorem integral_spectralEntropyKernel_eq_cfc
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    (∫ s in Ioi (0 : ℝ), spectralEntropyKernel F hF s) =
      cfc (fun z : ℝ => z * Real.log z) F := by
  let U := hF.isHermitian.eigenvectorUnitary
  let eigenvalue := hF.isHermitian.eigenvalues
  have hdiag := diagonalEntropyKernel_integrable
    eigenvalue (fun i => hF.eigenvalues_nonneg i)
  calc
    (∫ s in Ioi (0 : ℝ), spectralEntropyKernel F hF s) =
        spectralConjugationCLM U
          (∫ s in Ioi (0 : ℝ), diagonalEntropyKernel eigenvalue s) := by
            exact ContinuousLinearMap.integral_comp_comm
              (spectralConjugationCLM U) hdiag
    _ = spectralConjugationCLM U
          (Matrix.diagonal fun i =>
            ((eigenvalue i * Real.log (eigenvalue i) : ℝ) : ℂ)) := by
            rw [integral_diagonalEntropyKernel eigenvalue
              (fun i => hF.eigenvalues_nonneg i)]
    _ = cfc (fun z : ℝ => z * Real.log z) F := by
          rw [hF.isHermitian.cfc_eq]
          rfl
end
end QuantumParallelRepetition

namespace QuantumParallelRepetition
section
open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
attribute [instance] QuantumParallelRepetition.Strategy.alice_fintype QuantumParallelRepetition.Strategy.bob_fintype QuantumParallelRepetition.Strategy.alice_decidableEq QuantumParallelRepetition.Strategy.bob_decidableEq
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
theorem integral_weightedSpectralEntropyJensen_eq_cfc
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (weight : ι → ℝ) (F : ι → Matrix d d ℂ)
    (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) :
    (∫ s in Ioi (0 : ℝ),
      weightedSpectralEntropyJensen weight F M positive hM s) =
      (∑ i : ι, weight i •
        cfc (fun z : ℝ => z * Real.log z) (F i)) -
        cfc (fun z : ℝ => z * Real.log z) M := by
  have hterm (i : ι) :
      Integrable
        (fun s : ℝ => weight i •
          spectralEntropyKernel (F i) (positive i) s)
        (volume.restrict (Ioi 0)) :=
    (spectralEntropyKernel_integrable (F i) (positive i)).smul
      (weight i)
  have hsum :
      Integrable
        (fun s : ℝ => ∑ i : ι, weight i •
          spectralEntropyKernel (F i) (positive i) s)
        (volume.restrict (Ioi 0)) :=
    integrable_finsetSum Finset.univ (fun i _ => hterm i)
  have hmean := spectralEntropyKernel_integrable M hM
  unfold weightedSpectralEntropyJensen
  rw [integral_sub hsum hmean]
  rw [integral_finsetSum Finset.univ (fun i _ => hterm i)]
  simp_rw [integral_smul, integral_spectralEntropyKernel_eq_cfc]
end
end QuantumParallelRepetition

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace QuantumParallelRepetition
open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
attribute [instance] QuantumParallelRepetition.Strategy.alice_fintype QuantumParallelRepetition.Strategy.bob_fintype QuantumParallelRepetition.Strategy.alice_decidableEq QuantumParallelRepetition.Strategy.bob_decidableEq
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
theorem _root_.solution
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (weight : ι → ℝ) (F : ι → Matrix d d ℂ)
    (M : Matrix d d ℂ)
    (nonnegative : ∀ i, 0 ≤ weight i)
    (normalized : (∑ i : ι, weight i) = 1)
    (mean : (∑ i : ι, weight i • F i) = M)
    (positive : ∀ i, (F i).PosSemidef) :
    let hM : M.PosSemidef := by
      rw [← mean]
      exact weighted_positive_matrix_mean weight F nonnegative positive
    ((∑ i : ι, weight i •
        cfc (fun z : ℝ => z * Real.log z) (F i)) -
      cfc (fun z : ℝ => z * Real.log z) M -
      (∫ s in Ioi (0 : ℝ),
        weightedSpectralFilterVariance weight F M positive hM s)).PosSemidef := by
  dsimp
  let hM : M.PosSemidef := by
    rw [← mean]
    exact weighted_positive_matrix_mean weight F nonnegative positive
  have h := integrated_weighted_spectralPurificationFilter_jensen
    weight F M nonnegative normalized mean positive
  change
    ((∫ s in Ioi (0 : ℝ),
        weightedSpectralEntropyJensen weight F M positive hM s) -
      (∫ s in Ioi (0 : ℝ),
        weightedSpectralFilterVariance weight F M positive hM s)).PosSemidef at h
  rw [integral_weightedSpectralEntropyJensen_eq_cfc
    weight F M positive hM] at h
  exact h
end QuantumParallelRepetition

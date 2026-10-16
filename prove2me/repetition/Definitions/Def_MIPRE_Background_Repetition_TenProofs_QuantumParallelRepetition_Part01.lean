/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Repetition/TenProofs/QuantumParallelRepetition/Part01.lean (definition bundle: declarations the uploaded statements rest on);
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

set_option autoImplicit true

namespace QuantumParallelRepetition

noncomputable section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix

variable {X Y A B : Type*}

structure Game (X Y A B : Type*)
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B] where
  questionWeight : X → Y → ℝ
  weight_nonneg : ∀ x y, 0 ≤ questionWeight x y
  weight_normalized : (∑ x : X, ∑ y : Y, questionWeight x y) = 1
  predicate : X → Y → A → B → Bool

namespace Game

variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def marginalX (G : Game X Y A B) (x : X) : ℝ :=
  ∑ y : Y, G.questionWeight x y

def marginalY (G : Game X Y A B) (y : Y) : ℝ :=
  ∑ x : X, G.questionWeight x y

def «repeat» (G : Game X Y A B) (n : ℕ) :
    Game (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B) where
  questionWeight xs ys := ∏ i : Fin n, G.questionWeight (xs i) (ys i)
  weight_nonneg xs ys :=
    Finset.prod_nonneg fun i _ => G.weight_nonneg (xs i) (ys i)
  weight_normalized := by
    classical
    calc
      (∑ xs : Fin n → X, ∑ ys : Fin n → Y,
        ∏ i : Fin n, G.questionWeight (xs i) (ys i)) =
          ∑ xs : Fin n → X, ∏ i : Fin n, ∑ y : Y,
            G.questionWeight (xs i) y := by
              apply Finset.sum_congr rfl
              intro xs _
              exact (Fintype.prod_sum
                (fun i : Fin n => fun y : Y => G.questionWeight (xs i) y)).symm
      _ = ∏ _i : Fin n, ∑ x : X, ∑ y : Y,
            G.questionWeight x y := by
              exact (Fintype.prod_sum
                (fun _i : Fin n => fun x : X => ∑ y : Y,
                  G.questionWeight x y)).symm
      _ = 1 := by simp [G.weight_normalized]
  predicate xs ys as bs :=
    decide (∀ i : Fin n, G.predicate (xs i) (ys i) (as i) (bs i) = true)

@[simp] theorem repeat_questionWeight (G : Game X Y A B) (n : ℕ)
    (xs : Fin n → X) (ys : Fin n → Y) :
    (G.repeat n).questionWeight xs ys =
      ∏ i : Fin n, G.questionWeight (xs i) (ys i) := rfl

@[simp] theorem repeat_predicate_eq_true (G : Game X Y A B) (n : ℕ)
    (xs : Fin n → X) (ys : Fin n → Y)
    (as : Fin n → A) (bs : Fin n → B) :
    (G.repeat n).predicate xs ys as bs = true ↔
      ∀ i : Fin n, G.predicate (xs i) (ys i) (as i) (bs i) = true := by
  simp [«repeat»]

end Game

structure DensityMatrix (d : Type*) [Fintype d] where
  matrix : Matrix d d ℂ
  positive : matrix.PosSemidef
  trace_one : Matrix.trace matrix = 1

structure POVM (ι d : Type*) [Fintype ι] [Fintype d] [DecidableEq d] where
  effect : ι → Matrix d d ℂ
  positive : ∀ i, (effect i).PosSemidef
  complete : (∑ i : ι, effect i) = 1

structure Strategy [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (_G : Game X Y A B) where
  Alice : Type
  Bob : Type
  [alice_fintype : Fintype Alice]
  [bob_fintype : Fintype Bob]
  [alice_decidableEq : DecidableEq Alice]
  [bob_decidableEq : DecidableEq Bob]
  state : DensityMatrix (Alice × Bob)
  aliceMeasurement : X → POVM A Alice
  bobMeasurement : Y → POVM B Bob

attribute [instance] QuantumParallelRepetition.Strategy.alice_fintype QuantumParallelRepetition.Strategy.bob_fintype QuantumParallelRepetition.Strategy.alice_decidableEq QuantumParallelRepetition.Strategy.bob_decidableEq

theorem trace_mul_posSemidef_nonneg {d : Type*} [Fintype d] [DecidableEq d]
    {R E : Matrix d d ℂ} (hR : R.PosSemidef) (hE : E.PosSemidef) :
    0 ≤ (Matrix.trace (R * E)).re := by
  obtain ⟨K, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hR.nonneg
  have hpositive : (K * E * star K).PosSemidef := by
    simpa [star_eq_conjTranspose] using hE.mul_mul_conjTranspose_same K
  have htrace : 0 ≤ (Matrix.trace (K * E * star K)).re :=
    (Complex.nonneg_iff.mp hpositive.trace_nonneg).1
  rw [Matrix.trace_mul_cycle] at htrace
  exact htrace

namespace Strategy

variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {G : Game X Y A B}

def jointEffect (S : Strategy G) (x : X) (y : Y) (a : A) (b : B) :
    Matrix (S.Alice × S.Bob) (S.Alice × S.Bob) ℂ :=
  (S.aliceMeasurement x).effect a ⊗ₖ (S.bobMeasurement y).effect b

theorem jointEffect_positive (S : Strategy G) (x : X) (y : Y) (a : A) (b : B) :
    (S.jointEffect x y a b).PosSemidef := by
  exact ((S.aliceMeasurement x).positive a).kronecker
    ((S.bobMeasurement y).positive b)

def outcomeProbability (S : Strategy G) (x : X) (y : Y) (a : A) (b : B) : ℝ :=
  (Matrix.trace (S.state.matrix * S.jointEffect x y a b)).re

theorem outcomeProbability_nonneg (S : Strategy G)
    (x : X) (y : Y) (a : A) (b : B) :
    0 ≤ S.outcomeProbability x y a b := by
  exact trace_mul_posSemidef_nonneg S.state.positive
    (S.jointEffect_positive x y a b)

theorem jointEffect_complete (S : Strategy G) (x : X) (y : Y) :
    (∑ a : A, ∑ b : B, S.jointEffect x y a b) = 1 := by
  classical
  calc
    (∑ a : A, ∑ b : B, S.jointEffect x y a b) =
        (∑ a : A, (S.aliceMeasurement x).effect a) ⊗ₖ
          (∑ b : B, (S.bobMeasurement y).effect b) := by
            ext ⟨i, j⟩ ⟨k, l⟩
            simp only [jointEffect, Matrix.sum_apply, Matrix.kroneckerMap_apply]
            rw [Finset.sum_mul]
            simp_rw [Finset.mul_sum]
    _ = 1 := by
      rw [(S.aliceMeasurement x).complete, (S.bobMeasurement y).complete]
      exact Matrix.one_kronecker_one

theorem outcomeProbability_normalized (S : Strategy G) (x : X) (y : Y) :
    (∑ a : A, ∑ b : B, S.outcomeProbability x y a b) = 1 := by
  classical
  calc
    (∑ a : A, ∑ b : B, S.outcomeProbability x y a b) =
        (Matrix.trace
          (S.state.matrix * (∑ a : A, ∑ b : B, S.jointEffect x y a b))).re := by
            simp [outcomeProbability, Matrix.mul_sum, Matrix.trace_sum]
    _ = (Matrix.trace S.state.matrix).re := by
      rw [S.jointEffect_complete x y]
      simp
    _ = 1 := by rw [S.state.trace_one]; rfl

def winProbability (S : Strategy G) : ℝ :=
  ∑ x : X, ∑ y : Y, G.questionWeight x y *
    ∑ a : A, ∑ b : B,
      if G.predicate x y a b = true then S.outcomeProbability x y a b else 0

end Strategy

def entangledValue [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) : ℝ :=
  sSup (Set.range (Strategy.winProbability (G := G)))

def repeatedEntangledValue [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) : ℝ :=
  entangledValue (G.repeat n)

end

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def quadraticExpectation (W : H →L[ℂ] H) (z : H) : ℝ :=
  (⟪z, W z⟫_ℂ).re

end

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Strategy

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {G : Game X Y A B}

def winningEffect (S : Strategy G) (x : X) (y : Y) :
    Matrix (S.Alice × S.Bob) (S.Alice × S.Bob) ℂ :=
  ∑ a : A, ∑ b : B,
    if G.predicate x y a b = true then S.jointEffect x y a b else 0

end Strategy

end

noncomputable section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix

variable {X Y A B : Type*} {J : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype J] [DecidableEq J]
variable {G : Game X Y A B}

theorem posSemidef_blockDiagonal'
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {d : ι → Type*} [∀ j, Fintype (d j)]
    (M : ∀ j, Matrix (d j) (d j) ℂ)
    (hM : ∀ j, (M j).PosSemidef) :
    (Matrix.blockDiagonal' M).PosSemidef := by
  classical
  choose K hK using fun j =>
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (hM j).nonneg
  apply Matrix.LE.le.posSemidef
  apply CStarAlgebra.nonneg_iff_eq_star_mul_self.mpr
  refine ⟨Matrix.blockDiagonal' K, ?_⟩
  calc
    Matrix.blockDiagonal' M =
        Matrix.blockDiagonal' (fun j => star (K j) * K j) := by
          congr 1
          funext j
          exact hK j
    _ = star (Matrix.blockDiagonal' K) * Matrix.blockDiagonal' K := by
          simp [star_eq_conjTranspose, ← Matrix.blockDiagonal'_mul]

abbrev mixtureAlice (S : J → Strategy G) := Σ j : J, (S j).Alice

abbrev mixtureBob (S : J → Strategy G) := Σ j : J, (S j).Bob

abbrev mixtureMatched (S : J → Strategy G) :=
  Σ j : J, (S j).Alice × (S j).Bob

def mixtureMatchedIndex (S : J → Strategy G) :
    mixtureMatched S → mixtureAlice S × mixtureBob S
  | ⟨j, (a, b)⟩ => (⟨j, a⟩, ⟨j, b⟩)

omit [Fintype J] [DecidableEq J] in

theorem mixtureMatchedIndex_injective (S : J → Strategy G) :
    Function.Injective (mixtureMatchedIndex S) := by
  rintro ⟨i, a, b⟩ ⟨j, c, d⟩ h
  have hflag : i = j := congrArg (fun q => q.1.1) h
  subst j
  have ha : a = c :=
    eq_of_heq (Sigma.mk.inj (congrArg Prod.fst h)).2
  have hb : b = d :=
    eq_of_heq (Sigma.mk.inj (congrArg Prod.snd h)).2
  subst c
  subst d
  rfl

def mixtureEmbedding (S : J → Strategy G) :
    Matrix (mixtureAlice S × mixtureBob S) (mixtureMatched S) ℂ := by
  classical
  exact fun q r => if q = mixtureMatchedIndex S r then 1 else 0

theorem mixtureEmbedding_isometry (S : J → Strategy G) :
    (mixtureEmbedding S)ᴴ * mixtureEmbedding S = 1 := by
  classical
  ext i j
  by_cases h : i = j
  · subst j
    simp [mixtureEmbedding, Matrix.mul_apply,
      Matrix.conjTranspose_apply]
  · have hindex : mixtureMatchedIndex S i ≠ mixtureMatchedIndex S j :=
      fun hij => h (mixtureMatchedIndex_injective S hij)
    simp [mixtureEmbedding, Matrix.mul_apply,
      Matrix.conjTranspose_apply, h, hindex.symm]

def mixtureBlockMatrix (p : J → ℝ) (S : J → Strategy G) :
    Matrix (mixtureMatched S) (mixtureMatched S) ℂ :=
  Matrix.blockDiagonal' fun j => p j • (S j).state.matrix

theorem mixtureBlockMatrix_posSemidef
    (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (S : J → Strategy G) :
    (mixtureBlockMatrix p S).PosSemidef := by
  unfold mixtureBlockMatrix
  apply posSemidef_blockDiagonal'
  intro j
  exact (S j).state.positive.smul (hp j)

theorem mixtureBlockMatrix_trace
    (p : J → ℝ) (S : J → Strategy G) :
    Matrix.trace (mixtureBlockMatrix p S) =
      (↑(∑ j : J, p j) : ℂ) := by
  unfold mixtureBlockMatrix
  rw [Matrix.trace_blockDiagonal']
  simp [Matrix.trace_smul, DensityMatrix.trace_one]

def mixtureDensityMatrix (p : J → ℝ)
    (hp : ∀ j, 0 ≤ p j) (h_normalized : (∑ j : J, p j) = 1)
    (S : J → Strategy G) :
    DensityMatrix (mixtureAlice S × mixtureBob S) where
  matrix := mixtureEmbedding S * mixtureBlockMatrix p S *
    (mixtureEmbedding S)ᴴ
  positive :=
    (mixtureBlockMatrix_posSemidef p hp S).mul_mul_conjTranspose_same
      (mixtureEmbedding S)
  trace_one := by
    rw [Matrix.trace_mul_cycle, mixtureEmbedding_isometry,
      Matrix.one_mul, mixtureBlockMatrix_trace, h_normalized]
    norm_num

def mixtureAlicePOVM (S : J → Strategy G) (x : X) :
    POVM A (mixtureAlice S) where
  effect a := Matrix.blockDiagonal' fun j =>
    ((S j).aliceMeasurement x).effect a
  positive a := by
    apply posSemidef_blockDiagonal'
    intro j
    exact ((S j).aliceMeasurement x).positive a
  complete := by
    classical
    ext ⟨i, u⟩ ⟨j, v⟩
    by_cases h : i = j
    · subst j
      have h_complete := congrArg
        (fun M : Matrix (S i).Alice (S i).Alice ℂ => M u v)
        ((S i).aliceMeasurement x).complete
      simpa [Matrix.sum_apply, Matrix.blockDiagonal'_apply,
        Matrix.one_apply] using h_complete
    · simp [Matrix.sum_apply, Matrix.blockDiagonal'_apply,
        h]

def mixtureBobPOVM (S : J → Strategy G) (y : Y) :
    POVM B (mixtureBob S) where
  effect b := Matrix.blockDiagonal' fun j =>
    ((S j).bobMeasurement y).effect b
  positive b := by
    apply posSemidef_blockDiagonal'
    intro j
    exact ((S j).bobMeasurement y).positive b
  complete := by
    classical
    ext ⟨i, u⟩ ⟨j, v⟩
    by_cases h : i = j
    · subst j
      have h_complete := congrArg
        (fun M : Matrix (S i).Bob (S i).Bob ℂ => M u v)
        ((S i).bobMeasurement y).complete
      simpa [Matrix.sum_apply, Matrix.blockDiagonal'_apply,
        Matrix.one_apply] using h_complete
    · simp [Matrix.sum_apply, Matrix.blockDiagonal'_apply,
        h]

def convexMixtureStrategy (p : J → ℝ)
    (hp : ∀ j, 0 ≤ p j) (h_normalized : (∑ j : J, p j) = 1)
    (S : J → Strategy G) : Strategy G where
  Alice := mixtureAlice S
  Bob := mixtureBob S
  alice_fintype := inferInstance
  bob_fintype := inferInstance
  alice_decidableEq := inferInstance
  bob_decidableEq := inferInstance
  state := mixtureDensityMatrix p hp h_normalized S
  aliceMeasurement := mixtureAlicePOVM S
  bobMeasurement := mixtureBobPOVM S

end

noncomputable section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

def pureDensityMatrix
    {d : Type*} [Fintype d] [DecidableEq d]
    (z : EuclideanSpace ℂ d) (hz : ‖z‖ = 1) : DensityMatrix d where
  matrix := Matrix.vecMulVec (ofLp z) (star (ofLp z))
  positive := Matrix.posSemidef_vecMulVec_self_star (ofLp z)
  trace_one := by
    rw [Matrix.trace_vecMulVec,
      ← EuclideanSpace.inner_eq_star_dotProduct z z,
      inner_self_eq_norm_sq_to_K, hz]
    norm_num

def pureVectorStrategy
    {X Y A B : Type*} {dA dB : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype dA] [Fintype dB] [DecidableEq dA] [DecidableEq dB]
    (G : Game X Y A B)
    (z : EuclideanSpace ℂ (dA × dB)) (hz : ‖z‖ = 1)
    (PA : X → POVM A dA) (PB : Y → POVM B dB) : Strategy G where
  Alice := dA
  Bob := dB
  alice_fintype := inferInstance
  bob_fintype := inferInstance
  alice_decidableEq := inferInstance
  bob_decidableEq := inferInstance
  state := pureDensityMatrix z hz
  aliceMeasurement := PA
  bobMeasurement := PB

def pureFlaggedStrategy
    {X Y A B : Type*} {dA dB J : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype dA] [Fintype dB] [DecidableEq dA] [DecidableEq dB]
    [Fintype J] [DecidableEq J]
    (G : Game X Y A B)
    (p : J → ℝ) (hp : ∀ j, 0 ≤ p j)
    (h_normalized : (∑ j : J, p j) = 1)
    (z : J → EuclideanSpace ℂ (dA × dB))
    (hz : ∀ j, ‖z j‖ = 1)
    (PA : J → X → POVM A dA)
    (PB : J → Y → POVM B dB) : Strategy G :=
  convexMixtureStrategy p hp h_normalized
    (fun j => pureVectorStrategy G (z j) (hz j) (PA j) (PB j))

end

noncomputable section

open scoped BigOperators

structure FiniteEventLaw (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  weight_nonneg : ∀ ω, 0 ≤ weight ω
  weight_sum : (∑ ω, weight ω) = 1

namespace FiniteEventLaw

variable {Ω ι : Type*} [Fintype Ω]

def eventMass (law : FiniteEventLaw Ω) (event : Finset Ω) : ℝ :=
  ∑ ω ∈ event, law.weight ω

def winEvent [Fintype ι]
    (wins : ι → Ω → Bool) (D : Finset ι) : Finset Ω :=
  Finset.univ.filter (fun ω => ∀ i ∈ D, wins i ω = true)

def failureMass [Fintype ι] [DecidableEq ι]
    (law : FiniteEventLaw Ω) (wins : ι → Ω → Bool)
    (D : Finset ι) (i : ι) : ℝ :=
  law.eventMass (winEvent wins D) -
    law.eventMass (winEvent wins (insert i D))

end FiniteEventLaw

section StrategyEventLaw

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

abbrev StrategyOutcome (X Y A B : Type*) :=
  X × Y × A × B

def strategyEventLaw (G : Game X Y A B) (S : Strategy G) :
    FiniteEventLaw (StrategyOutcome X Y A B) where
  weight ω :=
    G.questionWeight ω.1 ω.2.1 *
      S.outcomeProbability ω.1 ω.2.1 ω.2.2.1 ω.2.2.2
  weight_nonneg ω :=
    mul_nonneg (G.weight_nonneg ω.1 ω.2.1)
      (S.outcomeProbability_nonneg
        ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
  weight_sum := by
    classical
    change
      (∑ ω : X × Y × A × B,
        G.questionWeight ω.1 ω.2.1 *
          S.outcomeProbability
            ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) = 1
    simp_rw [Fintype.sum_prod_type]
    calc
      (∑ x : X, ∑ y : Y, ∑ a : A, ∑ b : B,
        G.questionWeight x y *
          S.outcomeProbability x y a b) =
        ∑ x : X, ∑ y : Y,
          G.questionWeight x y *
            (∑ a : A, ∑ b : B,
              S.outcomeProbability x y a b) := by
                apply Finset.sum_congr rfl
                intro x _
                apply Finset.sum_congr rfl
                intro y _
                simp only [Finset.mul_sum]
      _ = ∑ x : X, ∑ y : Y,
          G.questionWeight x y * 1 := by
            apply Finset.sum_congr rfl
            intro x _
            apply Finset.sum_congr rfl
            intro y _
            rw [S.outcomeProbability_normalized x y]
      _ = 1 := by
            simpa using G.weight_normalized

def strategyWinEvent (G : Game X Y A B) :
    Finset (StrategyOutcome X Y A B) :=
  Finset.univ.filter
    (fun ω =>
      G.predicate ω.1 ω.2.1 ω.2.2.1 ω.2.2.2 = true)

def repeatedCoordinateWin (G : Game X Y A B) (n : ℕ)
    (i : Fin n)
    (ω : StrategyOutcome
      (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B)) : Bool :=
  G.predicate (ω.1 i) (ω.2.1 i)
    (ω.2.2.1 i) (ω.2.2.2 i)

end StrategyEventLaw

end

noncomputable section

open scoped BigOperators

variable {ι : Type*}

end

noncomputable section

open scoped BigOperators

end

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder

theorem weighted_positive_matrix_mean
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (weight : ι → ℝ) (F : ι → Matrix d d ℂ)
    (nonnegative : ∀ i, 0 ≤ weight i)
    (positive : ∀ i, (F i).PosSemidef) :
    (∑ i : ι, weight i • F i).PosSemidef := by
  exact Matrix.posSemidef_sum Finset.univ
    (fun i _ => (positive i).smul (nonnegative i))

end

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Topology

end

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def diagonalPurificationGram
    {d : Type*} [Fintype d] [DecidableEq d]
    (eigenvalue : d → ℝ) (s : ℝ) : Matrix d d ℂ :=
  Matrix.diagonal fun i =>
    (((eigenvalue i / (eigenvalue i + s)) ^ 2 : ℝ) : ℂ)

def spectralConjugationCLM
    {d : Type*} [Fintype d] [DecidableEq d]
    (U : Matrix.unitaryGroup d ℂ) :
    Matrix d d ℂ →L[ℝ] Matrix d d ℂ :=
  LinearMap.toContinuousLinearMap
    (Unitary.conjStarAlgAut ℝ (Matrix d d ℂ) U).toAlgEquiv.toLinearEquiv.toLinearMap

@[simp] theorem spectralConjugationCLM_apply
    {d : Type*} [Fintype d] [DecidableEq d]
    (U : Matrix.unitaryGroup d ℂ) (A : Matrix d d ℂ) :
    spectralConjugationCLM U A =
      (U : Matrix d d ℂ) * A * star (U : Matrix d d ℂ) := by
  rfl

def spectralPurificationGram
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) (s : ℝ) :
    Matrix d d ℂ :=
  spectralConjugationCLM hF.isHermitian.eigenvectorUnitary
    (diagonalPurificationGram hF.isHermitian.eigenvalues s)

end

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Kronecker Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def spectralPurificationFilter
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) (s : ℝ) : Matrix d d ℂ :=
  spectralConjugationCLM hF.isHermitian.eigenvectorUnitary
    (Matrix.diagonal fun i =>
      ((hF.isHermitian.eigenvalues i /
        (hF.isHermitian.eigenvalues i + s) : ℝ) : ℂ))

def bornTracePairing
    {dA dB : Type*} [Fintype dA] [Fintype dB]
    (ρ : Matrix (dA × dB) (dA × dB) ℂ) :
    Matrix dA dA ℂ →ₗ[ℝ] Matrix dB dB ℂ →ₗ[ℝ] ℝ where
  toFun F :=
    { toFun := fun G => (Matrix.trace (ρ * (F ⊗ₖ G))).re
      map_add' := by
        intro G H
        simp [Matrix.kronecker_add, Matrix.mul_add, Matrix.trace_add]
      map_smul' := by
        intro r G
        simp [Matrix.kronecker_smul, mul_smul_comm, Matrix.trace_smul] }
  map_add' := by
    intro F H
    ext G
    simp [Matrix.add_kronecker, Matrix.mul_add, Matrix.trace_add]
  map_smul' := by
    intro r F
    ext G
    simp [Matrix.smul_kronecker, mul_smul_comm, Matrix.trace_smul]

end

noncomputable section

open scoped BigOperators Kronecker

namespace Game

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def conditionalYGivenX (G : Game X Y A B) (x : X) (y : Y) : ℝ :=
  G.questionWeight x y / G.marginalX x

def conditionalXGivenY (G : Game X Y A B) (y : Y) (x : X) : ℝ :=
  G.questionWeight x y / G.marginalY y

end Game

section MixedHistories

variable {X Y A B U V : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [AddCommGroup U] [Module ℝ U]
variable [AddCommGroup V] [Module ℝ V]

def conditionalBobAverage
    (G : Game X Y A B) (K : Y → V) (x : X) : V :=
  ∑ y : Y, G.conditionalYGivenX x y • K y

def conditionalAliceAverage
    (G : Game X Y A B) (H : X → U) (y : Y) : U :=
  ∑ x : X, G.conditionalXGivenY y x • H x

end MixedHistories

section RepeatedQuantumFilters

open scoped ComplexOrder MatrixOrder

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def conditionedAliceEffect
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (α : {i : Fin n // i ∈ D} → A)
    (xs : Fin n → X) :
    Matrix S.Alice S.Alice ℂ := by
  classical
  exact
    ∑ answers : Fin n → A,
      if ∀ (i : Fin n) (hi : i ∈ D),
        answers i = α ⟨i, hi⟩
      then (S.aliceMeasurement xs).effect answers
      else 0

def conditionedBobEffect
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (β : {i : Fin n // i ∈ D} → B)
    (ys : Fin n → Y) :
    Matrix S.Bob S.Bob ℂ := by
  classical
  exact
    ∑ answers : Fin n → B,
      if ∀ (i : Fin n) (hi : i ∈ D),
        answers i = β ⟨i, hi⟩
      then (S.bobMeasurement ys).effect answers
      else 0

end RepeatedQuantumFilters

end

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder

def spectralSupportFunctional
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (f : ℝ → ℝ) : Matrix d d ℂ :=
  (Unitary.conjStarAlgAut ℂ (Matrix d d ℂ)
    hF.isHermitian.eigenvectorUnitary)
      (Matrix.diagonal fun i => (f (hF.isHermitian.eigenvalues i) : ℂ))

theorem spectralSupportFunctional_mul
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (f g : ℝ → ℝ) :
    spectralSupportFunctional F hF f *
        spectralSupportFunctional F hF g =
      spectralSupportFunctional F hF (fun x => f x * g x) := by
  classical
  let e := Unitary.conjStarAlgAut ℂ (Matrix d d ℂ)
    hF.isHermitian.eigenvectorUnitary
  change e _ * e _ = e _
  rw [← map_mul, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  push_cast
  rfl

theorem spectralSupportFunctional_id
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    spectralSupportFunctional F hF (fun x => x) = F := by
  simpa [spectralSupportFunctional, Function.comp_def] using
    hF.isHermitian.spectral_theorem.symm

theorem spectralSupportFunctional_congr
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    {f g : ℝ → ℝ}
    (h : ∀ i : d,
      f (hF.isHermitian.eigenvalues i) =
        g (hF.isHermitian.eigenvalues i)) :
    spectralSupportFunctional F hF f =
      spectralSupportFunctional F hF g := by
  unfold spectralSupportFunctional
  congr 2
  funext i
  exact_mod_cast h i

theorem spectralSupportFunctional_isHermitian
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (f : ℝ → ℝ) :
    (spectralSupportFunctional F hF f).IsHermitian := by
  classical
  let e := Unitary.conjStarAlgAut ℂ (Matrix d d ℂ)
    hF.isHermitian.eigenvectorUnitary
  let D : Matrix d d ℂ :=
    Matrix.diagonal fun i => (f (hF.isHermitian.eigenvalues i) : ℂ)
  have hD : D.IsHermitian := by
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro i
    change star (f (hF.isHermitian.eigenvalues i) : ℂ) = _
    simp
  have hDstar : star D = D := by
    simpa only [Matrix.star_eq_conjTranspose] using hD.eq
  change Matrix.conjTranspose (e D) = e D
  simpa only [Matrix.star_eq_conjTranspose] using
    (show star (e D) = e D by rw [← map_star, hDstar])

def spectralSupportInverse
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) : Matrix d d ℂ :=
  spectralSupportFunctional F hF (fun x => x⁻¹)

def spectralSupportProjection
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) : Matrix d d ℂ :=
  spectralSupportFunctional F hF (fun x => if x = 0 then 0 else 1)

def spectralSupportSqrt
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) : Matrix d d ℂ :=
  spectralSupportFunctional F hF Real.sqrt

theorem spectralSupportInverse_isHermitian
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    (spectralSupportInverse F hF).IsHermitian :=
  spectralSupportFunctional_isHermitian F hF _

theorem spectralSupportInverse_penrose
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    spectralSupportInverse F hF * F *
        spectralSupportInverse F hF =
      spectralSupportInverse F hF := by
  change spectralSupportFunctional F hF (fun x => x⁻¹) * F *
      spectralSupportFunctional F hF (fun x => x⁻¹) =
    spectralSupportFunctional F hF (fun x => x⁻¹)
  calc
    spectralSupportFunctional F hF (fun x => x⁻¹) * F *
        spectralSupportFunctional F hF (fun x => x⁻¹) =
      (spectralSupportFunctional F hF (fun x => x⁻¹) *
        spectralSupportFunctional F hF (fun x => x)) *
          spectralSupportFunctional F hF (fun x => x⁻¹) := by
            rw [spectralSupportFunctional_id]
    _ = spectralSupportFunctional F hF
          (fun x => (x⁻¹ * x) * x⁻¹) := by
      rw [spectralSupportFunctional_mul,
        spectralSupportFunctional_mul]
    _ = _ := spectralSupportFunctional_congr F hF (by
      intro i
      by_cases hi : hF.isHermitian.eigenvalues i = 0
      · simp [hi]
      · simp [hi])

end

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

end

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

set_option maxHeartbeats 400000

def purificationRangeProjection
    {d e : Type*} [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ) : Matrix e e ℂ :=
  Γ * spectralSupportInverse F hF * Matrix.conjTranspose Γ

theorem purificationRangeProjection_isHermitian
    {d e : Type*} [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ) :
    (purificationRangeProjection F hF Γ).IsHermitian := by
  unfold purificationRangeProjection
  change Matrix.conjTranspose
    (Γ * spectralSupportInverse F hF * Matrix.conjTranspose Γ) = _
  simp [Matrix.conjTranspose_mul,
    (spectralSupportInverse_isHermitian F hF).eq, Matrix.mul_assoc]

theorem purificationRangeProjection_idempotent
    {d e : Type*} [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (hΓ : Matrix.conjTranspose Γ * Γ = F) :
    purificationRangeProjection F hF Γ *
        purificationRangeProjection F hF Γ =
      purificationRangeProjection F hF Γ := by
  unfold purificationRangeProjection
  calc
    (Γ * spectralSupportInverse F hF * Matrix.conjTranspose Γ) *
        (Γ * spectralSupportInverse F hF * Matrix.conjTranspose Γ) =
      Γ * (spectralSupportInverse F hF *
        (Matrix.conjTranspose Γ * Γ) *
          spectralSupportInverse F hF) * Matrix.conjTranspose Γ := by
            simp only [Matrix.mul_assoc]
    _ = Γ * (spectralSupportInverse F hF * F *
          spectralSupportInverse F hF) * Matrix.conjTranspose Γ := by
            rw [hΓ]
    _ = Γ * spectralSupportInverse F hF *
          Matrix.conjTranspose Γ := by
            rw [spectralSupportInverse_penrose]

theorem purificationRangeProjection_complement_posSemidef
    {d e : Type*} [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (hΓ : Matrix.conjTranspose Γ * Γ = F) :
    (1 - purificationRangeProjection F hF Γ).PosSemidef := by
  let P := purificationRangeProjection F hF Γ
  have hPstar : Matrix.conjTranspose P = P :=
    (purificationRangeProjection_isHermitian F hF Γ).eq
  have hPsq : P * P = P :=
    purificationRangeProjection_idempotent F hF Γ hΓ
  have hsquare :
      Matrix.conjTranspose (1 - P) * (1 - P) = 1 - P := by
    calc
      Matrix.conjTranspose (1 - P) * (1 - P) =
          (1 - P) * (1 - P) := by
            simp [Matrix.conjTranspose_sub, hPstar]
      _ = 1 - P - P + P * P := by noncomm_ring
      _ = 1 - P := by rw [hPsq]; noncomm_ring
  have hpositive := Matrix.posSemidef_conjTranspose_mul_self
    (1 - P)
  rw [hsquare] at hpositive
  exact hpositive

def purifiedRefinementCore
    {ι d e : Type*} [Fintype ι]
    [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (effect : ι → Matrix d d ℂ) (a : ι) : Matrix e e ℂ :=
  Γ * spectralSupportInverse F hF * effect a *
    spectralSupportInverse F hF * Matrix.conjTranspose Γ

theorem purifiedRefinementCore_posSemidef
    {ι d e : Type*} [Fintype ι]
    [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (effect : ι → Matrix d d ℂ)
    (hpositive : ∀ a, (effect a).PosSemidef)
    (a : ι) :
    (purifiedRefinementCore F hF Γ effect a).PosSemidef := by
  have h := (hpositive a).mul_mul_conjTranspose_same
    (Γ * spectralSupportInverse F hF)
  simpa [purifiedRefinementCore, Matrix.conjTranspose_mul,
    (spectralSupportInverse_isHermitian F hF).eq,
    Matrix.mul_assoc] using h

theorem purifiedRefinementCore_sum
    {ι d e : Type*} [Fintype ι]
    [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (effect : ι → Matrix d d ℂ)
    (hsum : (∑ a : ι, effect a) = F) :
    (∑ a : ι, purifiedRefinementCore F hF Γ effect a) =
      purificationRangeProjection F hF Γ := by
  unfold purifiedRefinementCore purificationRangeProjection
  calc
    (∑ a : ι,
      Γ * spectralSupportInverse F hF * effect a *
        spectralSupportInverse F hF * Matrix.conjTranspose Γ) =
      Γ * spectralSupportInverse F hF *
        (∑ a : ι, effect a) * spectralSupportInverse F hF *
          Matrix.conjTranspose Γ := by
            simp only [Matrix.mul_sum, Matrix.sum_mul]
    _ = Γ * spectralSupportInverse F hF * F *
          spectralSupportInverse F hF * Matrix.conjTranspose Γ := by
            rw [hsum]
    _ = Γ * (spectralSupportInverse F hF * F *
          spectralSupportInverse F hF) * Matrix.conjTranspose Γ := by
            simp only [Matrix.mul_assoc]
    _ = Γ * spectralSupportInverse F hF *
          Matrix.conjTranspose Γ := by
            rw [spectralSupportInverse_penrose]

def purifiedRefinedEffect
    {ι d e : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (effect : ι → Matrix d d ℂ)
    (a₀ a : ι) : Matrix e e ℂ :=
  purifiedRefinementCore F hF Γ effect a +
    if a = a₀ then 1 - purificationRangeProjection F hF Γ else 0

theorem purifiedRefinedEffect_posSemidef
    {ι d e : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (hΓ : Matrix.conjTranspose Γ * Γ = F)
    (effect : ι → Matrix d d ℂ)
    (hpositive : ∀ a, (effect a).PosSemidef)
    (a₀ a : ι) :
    (purifiedRefinedEffect F hF Γ effect a₀ a).PosSemidef := by
  change (purifiedRefinementCore F hF Γ effect a +
    if a = a₀ then 1 - purificationRangeProjection F hF Γ else 0).PosSemidef
  refine (purifiedRefinementCore_posSemidef F hF Γ effect
    hpositive a).add ?_
  split
  · exact purificationRangeProjection_complement_posSemidef F hF Γ hΓ
  · exact Matrix.PosSemidef.zero

theorem purifiedRefinedEffect_complete
    {ι d e : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (effect : ι → Matrix d d ℂ)
    (hsum : (∑ a : ι, effect a) = F)
    (a₀ : ι) :
    (∑ a : ι, purifiedRefinedEffect F hF Γ effect a₀ a) = 1 := by
  classical
  unfold purifiedRefinedEffect
  rw [Finset.sum_add_distrib]
  rw [purifiedRefinementCore_sum F hF Γ effect hsum]
  simp

def purifiedRefinedPOVM
    {ι d e : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (hΓ : Matrix.conjTranspose Γ * Γ = F)
    (effect : ι → Matrix d d ℂ)
    (hpositive : ∀ a, (effect a).PosSemidef)
    (hsum : (∑ a : ι, effect a) = F)
    (a₀ : ι) : POVM ι e where
  effect := purifiedRefinedEffect F hF Γ effect a₀
  positive a := purifiedRefinedEffect_posSemidef F hF Γ hΓ
    effect hpositive a₀ a
  complete := purifiedRefinedEffect_complete F hF Γ effect hsum a₀

end

noncomputable section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

def fullHistoryRemaining (n : ℕ)
    (D L : Finset (Fin n)) : Finset (Fin n) :=
  (Finset.univ \ D) \ L

@[ext (iff := false)] structure FullSubsetHistory
    (X Y : Type*) [Fintype X] [Fintype Y]
    (n : ℕ) (D L : Finset (Fin n)) where
  aliceConditioned : {i : Fin n // i ∈ D} → X
  bobConditioned : {i : Fin n // i ∈ D} → Y
  aliceRevealed : {i : Fin n // i ∈ L} → X
  bobRemaining : {i : Fin n // i ∈ fullHistoryRemaining n D L} → Y
  deriving Fintype

def fullHistoryAliceQuestion
    {X Y : Type*} [Fintype X] [Fintype Y]
    {n : ℕ} {D L : Finset (Fin n)}
    (h : FullSubsetHistory X Y n D L)
    (hidden : {i : Fin n // i ∈ fullHistoryRemaining n D L} → X) :
    Fin n → X := fun i =>
  if hiD : i ∈ D then h.aliceConditioned ⟨i, hiD⟩
  else if hiL : i ∈ L then h.aliceRevealed ⟨i, hiL⟩
  else hidden ⟨i, by
    simp [fullHistoryRemaining, hiD, hiL]⟩

def fullHistoryBobQuestion
    {X Y : Type*} [Fintype X] [Fintype Y]
    {n : ℕ} {D L : Finset (Fin n)}
    (h : FullSubsetHistory X Y n D L)
    (hidden : {i : Fin n // i ∈ L} → Y) :
    Fin n → Y := fun i =>
  if hiD : i ∈ D then h.bobConditioned ⟨i, hiD⟩
  else if hiL : i ∈ L then hidden ⟨i, hiL⟩
  else h.bobRemaining ⟨i, by
    simp [fullHistoryRemaining, hiD, hiL]⟩

def fullHistoryQuestionEquiv
    {X Y : Type*} [Fintype X] [Fintype Y]
    {n : ℕ} (D L : Finset (Fin n))
    (hL : L ⊆ Finset.univ \ D) :
    (FullSubsetHistory X Y n D L ×
      ({i : Fin n // i ∈ fullHistoryRemaining n D L} → X) ×
      ({i : Fin n // i ∈ L} → Y)) ≃
      ((Fin n → X) × (Fin n → Y)) where
  toFun t :=
    (fullHistoryAliceQuestion t.1 t.2.1,
      fullHistoryBobQuestion t.1 t.2.2)
  invFun q :=
    (⟨fun i => q.1 i,
      fun i => q.2 i,
      fun i => q.1 i,
      fun i => q.2 i⟩,
      (fun i => q.1 i),
      (fun i => q.2 i))
  left_inv := by
    rintro ⟨h, hx, hy⟩
    apply Prod.ext
    · apply FullSubsetHistory.ext
      · funext i
        simp [fullHistoryAliceQuestion, i.property]
      · funext i
        simp [fullHistoryBobQuestion, i.property]
      · funext i
        have hiD : (i : Fin n) ∉ D :=
          (Finset.mem_sdiff.mp (hL i.property)).2
        simp [fullHistoryAliceQuestion, hiD, i.property]
      · funext i
        have hiD : (i : Fin n) ∉ D := by
          have := i.property
          simpa [fullHistoryRemaining] using
            (Finset.mem_sdiff.mp
              (Finset.mem_sdiff.mp i.property).1).2
        have hiL : (i : Fin n) ∉ L :=
          (Finset.mem_sdiff.mp i.property).2
        simp [fullHistoryBobQuestion, hiD, hiL]
    · apply Prod.ext
      · funext i
        have hiD : (i : Fin n) ∉ D :=
          (Finset.mem_sdiff.mp
            (Finset.mem_sdiff.mp i.property).1).2
        have hiL : (i : Fin n) ∉ L :=
          (Finset.mem_sdiff.mp i.property).2
        simp [fullHistoryAliceQuestion, hiD, hiL]
      · funext i
        have hiD : (i : Fin n) ∉ D :=
          (Finset.mem_sdiff.mp (hL i.property)).2
        simp [fullHistoryBobQuestion, hiD, i.property]
  right_inv := by
    rintro ⟨xs, ys⟩
    apply Prod.ext
    · funext i
      by_cases hiD : i ∈ D
      · simp [fullHistoryAliceQuestion, hiD]
      · by_cases hiL : i ∈ L <;>
          simp [fullHistoryAliceQuestion, hiD, hiL]
    · funext i
      by_cases hiD : i ∈ D
      · simp [fullHistoryBobQuestion, hiD]
      · by_cases hiL : i ∈ L <;>
          simp [fullHistoryBobQuestion, hiD, hiL]

section ActualHistoryWeights

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def fullHistoryWeight
    (G : Game X Y A B) {n : ℕ}
    {D L : Finset (Fin n)}
    (h : FullSubsetHistory X Y n D L) : ℝ :=
  (∏ i : {i : Fin n // i ∈ D},
    G.questionWeight (h.aliceConditioned i) (h.bobConditioned i)) *
  (∏ i : {i : Fin n // i ∈ L},
    G.marginalX (h.aliceRevealed i)) *
  (∏ i : {i : Fin n // i ∈ fullHistoryRemaining n D L},
    G.marginalY (h.bobRemaining i))

def fullHistoryHiddenAliceWeight
    (G : Game X Y A B) {n : ℕ}
    {D L : Finset (Fin n)}
    (h : FullSubsetHistory X Y n D L)
    (hidden : {i : Fin n // i ∈ fullHistoryRemaining n D L} → X) : ℝ :=
  ∏ i : {i : Fin n // i ∈ fullHistoryRemaining n D L},
    G.conditionalXGivenY (h.bobRemaining i) (hidden i)

def fullHistoryHiddenBobWeight
    (G : Game X Y A B) {n : ℕ}
    {D L : Finset (Fin n)}
    (h : FullSubsetHistory X Y n D L)
    (hidden : {i : Fin n // i ∈ L} → Y) : ℝ :=
  ∏ i : {i : Fin n // i ∈ L},
    G.conditionalYGivenX (h.aliceRevealed i) (hidden i)

def fullHistoryAliceFilter
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D L : Finset (Fin n))
    (h : FullSubsetHistory X Y n D L)
    (α : {i : Fin n // i ∈ D} → A) :
    Matrix S.Alice S.Alice ℂ :=
  ∑ hidden : {i : Fin n // i ∈ fullHistoryRemaining n D L} → X,
    fullHistoryHiddenAliceWeight G h hidden •
      conditionedAliceEffect G n S D α
        (fullHistoryAliceQuestion h hidden)

def fullHistoryBobFilter
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D L : Finset (Fin n))
    (h : FullSubsetHistory X Y n D L)
    (β : {i : Fin n // i ∈ D} → B) :
    Matrix S.Bob S.Bob ℂ :=
  ∑ hidden : {i : Fin n // i ∈ L} → Y,
    fullHistoryHiddenBobWeight G h hidden •
      conditionedBobEffect G n S D β
        (fullHistoryBobQuestion h hidden)

def fullHistoryWinIndicator
    (G : Game X Y A B) {n : ℕ}
    {D L : Finset (Fin n)}
    (h : FullSubsetHistory X Y n D L)
    (α : {i : Fin n // i ∈ D} → A)
    (β : {i : Fin n // i ∈ D} → B) : ℝ := by
  classical
  exact if ∀ i : {i : Fin n // i ∈ D},
    G.predicate (h.aliceConditioned i) (h.bobConditioned i)
      (α i) (β i) = true then 1 else 0

def fullQuestionWinIndicator
    (G : Game X Y A B) {n : ℕ}
    (D : Finset (Fin n))
    (xs : Fin n → X) (ys : Fin n → Y)
    (α : {i : Fin n // i ∈ D} → A)
    (β : {i : Fin n // i ∈ D} → B) : ℝ := by
  classical
  exact if ∀ i : {i : Fin n // i ∈ D},
    G.predicate (xs i) (ys i) (α i) (β i) = true
    then 1 else 0

end ActualHistoryWeights

end

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def matrixQuadraticCLM
    {d : Type*} [Fintype d]
    (x : d → ℂ) : Matrix d d ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => star x ⬝ᵥ A.mulVec x
      map_add' := by
        intro A B
        simp [Matrix.mulVec, dotProduct, add_mul, mul_add,
          Finset.sum_add_distrib]
      map_smul' := by
        intro r A
        change
          (∑ i, star (x i) *
            ∑ j, ((r : ℂ) * A i j) * x j) =
          (r : ℂ) *
            (∑ i, star (x i) * ∑ j, A i j * x j)
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring }

def matrixAdjointCLM
    {d : Type*} [Fintype d] :
    Matrix d d ℂ →L[ℝ] Matrix d d ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => star A
      map_add' := by
        intro A B
        exact star_add A B
      map_smul' := by
        intro r A
        simp }

end

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def spectralEntropyKernel
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) (s : ℝ) :
    Matrix d d ℂ :=
  spectralConjugationCLM hF.isHermitian.eigenvectorUnitary
    (Matrix.diagonal fun i =>
      ((hF.isHermitian.eigenvalues i / (1 + s) -
        hF.isHermitian.eigenvalues i /
          (hF.isHermitian.eigenvalues i + s) : ℝ) : ℂ))

end

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def weightedSpectralFilterVariance
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (weight : ι → ℝ) (F : ι → Matrix d d ℂ)
    (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) (s : ℝ) : Matrix d d ℂ :=
  ∑ i : ι, weight i •
    (star (spectralPurificationFilter (F i) (positive i) s -
        spectralPurificationFilter M hM s) *
      (spectralPurificationFilter (F i) (positive i) s -
        spectralPurificationFilter M hM s))

def weightedSpectralEntropyJensen
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (weight : ι → ℝ) (F : ι → Matrix d d ℂ)
    (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) (s : ℝ) : Matrix d d ℂ :=
  (∑ i : ι, weight i • spectralEntropyKernel (F i) (positive i) s) -
    spectralEntropyKernel M hM s

end

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def diagonalEntropyKernel
    {d : Type*} [Fintype d] [DecidableEq d]
    (eigenvalue : d → ℝ) (s : ℝ) : Matrix d d ℂ :=
  Matrix.diagonal fun i =>
    ((eigenvalue i / (1 + s) -
      eigenvalue i / (eigenvalue i + s) : ℝ) : ℂ)

end

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end

noncomputable section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

section HistoryContractions

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def fullHistoryAliceEntropyPotential
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) : ℝ :=
  ∑ h : FullSubsetHistory X Y n D L,
    ∑ α : {i : Fin n // i ∈ D} → A,
    ∑ β : {i : Fin n // i ∈ D} → B,
      fullHistoryWeight G h * fullHistoryWinIndicator G h α β *
        bornTracePairing S.state.matrix
          (cfc (fun z : ℝ => z * Real.log z)
            (fullHistoryAliceFilter G n S D L h α))
          (fullHistoryBobFilter G n S D L h β)

end HistoryContractions

def positiveMatrixSpectralAtom
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) (i : d) :
    Matrix d d ℂ :=
  spectralConjugationCLM hF.isHermitian.eigenvectorUnitary
    (Matrix.diagonal (Pi.single i (1 : ℂ)))

theorem positiveMatrixSpectralAtom_posSemidef
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) (i : d) :
    (positiveMatrixSpectralAtom F hF i).PosSemidef := by
  classical
  have hdiag :
      (Matrix.diagonal (Pi.single i (1 : ℂ))).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  unfold positiveMatrixSpectralAtom
  rw [spectralConjugationCLM_apply]
  simpa [Matrix.star_eq_conjTranspose] using
    hdiag.mul_mul_conjTranspose_same
      (hF.isHermitian.eigenvectorUnitary : Matrix d d ℂ)

theorem positiveMatrixSpectralAtom_sum
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    (∑ i : d, positiveMatrixSpectralAtom F hF i) = 1 := by
  classical
  let U := hF.isHermitian.eigenvectorUnitary
  have hdiag :
      (∑ i : d, Matrix.diagonal (Pi.single i (1 : ℂ))) =
        (1 : Matrix d d ℂ) := by
    ext j k
    by_cases hjk : j = k
    · subst k
      simp [Matrix.sum_apply, Pi.single_apply]
    · simp [Matrix.sum_apply,         hjk]
  change
    (∑ i : d,
      spectralConjugationCLM U
        (Matrix.diagonal (Pi.single i (1 : ℂ)))) = 1
  rw [← map_sum, hdiag]
  simp [spectralConjugationCLM_apply]

def leftSpectralBornWeight
    {dA dB : Type*}
    [Fintype dA] [Fintype dB]
    [DecidableEq dA] [DecidableEq dB]
    (ρ : DensityMatrix (dA × dB))
    (F : Matrix dA dA ℂ) (hF : F.PosSemidef)
    (G : Matrix dB dB ℂ)
    (i : dA) : ℝ :=
  bornTracePairing ρ.matrix
    (positiveMatrixSpectralAtom F hF i) G

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

def rawEmbezzlementState (n : ℕ) :
    EuclideanSpace ℂ (Fin n × Fin n) :=
  toLp 2 fun q : Fin n × Fin n =>
    if q.1 = q.2 then
      (↑((Real.sqrt ((q.1.val : ℝ) + 1))⁻¹) : ℂ)
    else
      0

def harmonicNumber (n : ℕ) : ℝ :=
  ∑ j : Fin n, ((j.val : ℝ) + 1)⁻¹

def embezzlementState (n : ℕ) :
    EuclideanSpace ℂ (Fin n × Fin n) :=
  (‖rawEmbezzlementState n‖⁻¹ : ℝ) •
    rawEmbezzlementState n

abbrev BipartiteUnitVector (d : ℕ) :=
  {ξ : EuclideanSpace ℂ (Fin d × Fin d) // ‖ξ‖ = 1}

def spectralAtomOverlap
    {d : Type*} [Fintype d] [DecidableEq d]
    (F G : Matrix d d ℂ)
    (hF : F.PosSemidef) (hG : G.PosSemidef)
    (i j : d) : ℝ :=
  (Matrix.trace
    (positiveMatrixSpectralAtom F hF i *
      positiveMatrixSpectralAtom G hG j)).re

def coherentBinaryJointOutcome
    {d e : Type*}
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (P : POVM Bool d) (Q : POVM Bool e)
    (z : EuclideanSpace ℂ (d × e))
    (a b : Bool) : EuclideanSpace ℂ (d × e) :=
  toLp 2
    (((P.effect a ⊗ₖ Q.effect b)).mulVec (ofLp z))

def finiteTensorVector
    {ι d : Type*} [Fintype ι] [Fintype d]
    (v : ι → EuclideanSpace ℂ d) :
    EuclideanSpace ℂ (ι → d) :=
  toLp 2 fun q : ι → d => ∏ i : ι, v i (q i)

def binaryBornProbability
    {d e : Type*}
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (ρ : DensityMatrix (d × e))
    (P : POVM Bool d) (Q : POVM Bool e)
    (a b : Bool) : ℝ :=
  (Matrix.trace
    (ρ.matrix * (P.effect a ⊗ₖ Q.effect b))).re

def binaryContinueProbability
    {d e : Type*}
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (ρ : DensityMatrix (d × e))
    (P : POVM Bool d) (Q : POVM Bool e) : ℝ :=
  binaryBornProbability ρ P Q false false

def binaryJointSuccessProbability
    {d e : Type*}
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (ρ : DensityMatrix (d × e))
    (P : POVM Bool d) (Q : POVM Bool e) : ℝ :=
  binaryBornProbability ρ P Q true true

def binaryMismatchProbability
    {d e : Type*}
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (ρ : DensityMatrix (d × e))
    (P : POVM Bool d) (Q : POVM Bool e) : ℝ :=
  binaryBornProbability ρ P Q true false +
    binaryBornProbability ρ P Q false true

def sharedThresholdResourceRaw
    {κ d : Type*} [Fintype κ] [Fintype d]
    [DecidableEq κ] [DecidableEq d]
    (τ : κ → ℝ) :
    EuclideanSpace ℂ ((Σ _ : κ, d) × (Σ _ : κ, d)) :=
  toLp 2 fun q : (Σ _ : κ, d) × (Σ _ : κ, d) =>
    if q.1.1 = q.2.1 ∧ q.1.2 = q.2.2 then
      (τ q.1.1 : ℂ)
    else
      0

theorem sharedThresholdResourceRaw_ne_zero
    {κ d : Type*} [Fintype κ] [Fintype d]
    [DecidableEq κ] [DecidableEq d]
    (τ : κ → ℝ) (k : κ) (i : d) (hk : τ k ≠ 0) :
    sharedThresholdResourceRaw (d := d) τ ≠ 0 := by
  intro hzero
  have hentry := congrArg
    (fun z : EuclideanSpace ℂ
        ((Σ _ : κ, d) × (Σ _ : κ, d)) =>
      z (⟨k, i⟩, ⟨k, i⟩)) hzero
  have hcast : (τ k : ℂ) = 0 := by
    simpa [sharedThresholdResourceRaw] using hentry
  exact hk (by exact_mod_cast hcast)

def sharedThresholdResource
    {κ d : Type*} [Fintype κ] [Fintype d]
    [DecidableEq κ] [DecidableEq d]
    (τ : κ → ℝ) :
    EuclideanSpace ℂ ((Σ _ : κ, d) × (Σ _ : κ, d)) :=
  (‖sharedThresholdResourceRaw (d := d) τ‖⁻¹ : ℝ) •
    sharedThresholdResourceRaw (d := d) τ

theorem sharedThresholdResource_norm
    {κ d : Type*} [Fintype κ] [Fintype d]
    [DecidableEq κ] [DecidableEq d]
    (τ : κ → ℝ) (k : κ) (i : d) (hk : τ k ≠ 0) :
    ‖sharedThresholdResource (d := d) τ‖ = 1 := by
  have hnorm : ‖sharedThresholdResourceRaw (d := d) τ‖ ≠ 0 :=
    norm_ne_zero_iff.mpr
      (sharedThresholdResourceRaw_ne_zero τ k i hk)
  rw [sharedThresholdResource, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ hnorm]

def transposePOVM
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (P : POVM ι d) : POVM ι d where
  effect b := (P.effect b).transpose
  positive b := (P.positive b).transpose
  complete := by
    classical
    ext i j
    have hc := congrArg
      (fun M : Matrix d d ℂ => M j i) P.complete
    simpa [Matrix.sum_apply, Matrix.transpose_apply,
      Matrix.one_apply, eq_comm] using hc

def weightedComplexOverlapVector
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (σ : ι → ℝ) (μ : κ → ℝ)
    (L : ι → κ → ℂ) : EuclideanSpace ℂ (ι × κ) :=
  toLp 2 fun q : ι × κ =>
    (Real.sqrt (σ q.1 * μ q.2) : ℂ) * L q.1 q.2

def tensorEmbezzlementTarget
    {d n : ℕ} (ξ : BipartiteUnitVector d) :
    EuclideanSpace ℂ (Fin (d * n) × Fin (d * n)) :=
  toLp 2 fun q : Fin (d * n) × Fin (d * n) =>
    let a : Fin d × Fin n := finProdFinEquiv.symm q.1
    let b : Fin d × Fin n := finProdFinEquiv.symm q.2
    ξ.val (a.1, b.1) * embezzlementState n (a.2, b.2)

def localUnitaryAction {n : ℕ}
    (U V : Matrix.unitaryGroup (Fin n) ℂ)
    (ψ : EuclideanSpace ℂ (Fin n × Fin n)) :
    EuclideanSpace ℂ (Fin n × Fin n) :=
  toLp 2
    (((U : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ
      (V : Matrix (Fin n) (Fin n) ℂ)).mulVec (ofLp ψ))

def unitaryBasisOverlap
    {d : Type*} [Fintype d] [DecidableEq d]
    (U V : Matrix.unitaryGroup d ℂ) :
    Matrix.unitaryGroup d ℂ := U⁻¹ * V

def diagonalSchmidtState
    {d : Type*} [Fintype d] [DecidableEq d]
    (σ : d → ℝ) : EuclideanSpace ℂ (d × d) :=
  toLp 2 fun q : d × d =>
    if q.1 = q.2 then (σ q.1 : ℂ) else 0

theorem diagonalSchmidtState_norm_sq
    {d : Type*} [Fintype d] [DecidableEq d]
    (σ : d → ℝ) :
    ‖diagonalSchmidtState σ‖ ^ 2 =
      ∑ i : d, σ i ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  change
    (∑ j : d, ‖if i = j then (σ i : ℂ) else 0‖ ^ 2) =
      σ i ^ 2
  have hterm (j : d) :
      ‖if i = j then (σ i : ℂ) else 0‖ ^ 2 =
        if i = j then σ i ^ 2 else 0 := by
    split_ifs <;> simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp_rw [hterm]
  simp

def schmidtVector
    {d : ℕ}
    (σ : Fin d → ℝ)
    (U V : Matrix.unitaryGroup (Fin d) ℂ) :
    EuclideanSpace ℂ (Fin d × Fin d) :=
  localUnitaryAction U V
    (diagonalSchmidtState σ)

@[simp] theorem unitaryBasisOverlap_apply
    {d : Type*} [Fintype d] [DecidableEq d]
    (U V : Matrix.unitaryGroup d ℂ) (i j : d) :
    unitaryBasisOverlap U V i j =
      (((U : Matrix d d ℂ).conjTranspose *
        (V : Matrix d d ℂ)) i j) := by
  rfl

end

noncomputable section

open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset

end

open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset

noncomputable section

def orthonormalBasisUnitary
    {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℂ
      (EuclideanSpace ℂ (Fin d))) :
    Matrix.unitaryGroup (Fin d) ℂ :=
  ⟨(EuclideanSpace.basisFun (Fin d) ℂ).toBasis.toMatrix b.toBasis,
    (EuclideanSpace.basisFun (Fin d) ℂ).toMatrix_orthonormalBasis_mem_unitary b⟩

@[simp] theorem orthonormalBasisUnitary_apply
    {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℂ
      (EuclideanSpace ℂ (Fin d)))
    (i j : Fin d) :
    orthonormalBasisUnitary b i j = b j i := by
  rfl

def conjugateUnitary
    {d : ℕ}
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    Matrix.unitaryGroup (Fin d) ℂ := by
  refine ⟨(U.val.conjTranspose).transpose, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff']
  change
    ((U.val.conjTranspose).transpose).conjTranspose *
      (U.val.conjTranspose).transpose = 1
  have htranspose :
      ((U.val.conjTranspose).transpose).conjTranspose =
        U.val.transpose := by
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  rw [htranspose]
  have h := congrArg Matrix.transpose U.property.1
  simpa [Matrix.star_eq_conjTranspose, Matrix.transpose_mul] using h

@[simp] theorem conjugateUnitary_apply
    {d : ℕ}
    (U : Matrix.unitaryGroup (Fin d) ℂ)
    (i j : Fin d) :
    conjugateUnitary U i j = star (U i j) := by
  rfl

-- Vendoring compile fix (Lean v4.33): this proof needs the pre-v4.33 transparency
-- behaviour (its closing `simpa` no longer sees through `Matrix.toEuclideanLin`);
-- see README.md.

end

noncomputable section

open scoped BigOperators

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker

def ePRState (m : ℕ) :
    EuclideanSpace ℂ (Fin m × Fin m) :=
  toLp 2 fun q : Fin m × Fin m =>
    if q.1 = q.2 then
      (↑((Real.sqrt (m : ℝ))⁻¹) : ℂ)
    else
      0

theorem permutationMatrix_mem_unitary
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) :
    σ.permMatrix ℂ ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
  simp

def permutationUnitary
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) : Matrix.unitaryGroup ι ℂ :=
  ⟨σ.permMatrix ℂ, permutationMatrix_mem_unitary σ⟩

@[simp] theorem permutationUnitary_val
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) :
    (permutationUnitary σ : Matrix ι ι ℂ) =
      σ.permMatrix ℂ := rfl

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

def harmonicTensorSchmidtAmplitude
    {d n : ℕ} (σ : Fin d → ℝ) (q : Fin (d * n)) : ℝ :=
  let p : Fin d × Fin n := finProdFinEquiv.symm q
  σ p.1 * (Real.sqrt ((p.2.val : ℝ) + 1))⁻¹

def descendingHarmonicSchmidtPermutation
    {d n : ℕ} (σ : Fin d → ℝ) : Equiv.Perm (Fin (d * n)) :=
  Tuple.sort (fun q : Fin (d * n) =>
    -harmonicTensorSchmidtAmplitude (n := n) σ q)

def diagonalSchmidtUnitVector
    {d : ℕ} (σ : Fin d → ℝ)
    (hunit : (∑ i : Fin d, σ i ^ 2) = 1) :
    BipartiteUnitVector d := by
  refine ⟨diagonalSchmidtState σ, ?_⟩
  have hsquare := diagonalSchmidtState_norm_sq σ
  rw [hunit] at hsquare
  nlinarith [norm_nonneg (diagonalSchmidtState σ)]

def harmonicSchmidtPermutationUnitary
    {d n : ℕ} (σ : Fin d → ℝ) :
    Matrix.unitaryGroup (Fin (d * n)) ℂ :=
  permutationUnitary
    (descendingHarmonicSchmidtPermutation
      (n := n) σ).symm

def universalCatalystOverlapTerm
    {d n : ℕ} (σ : Fin d → ℝ)
    (k : Fin (d * n)) : ℝ :=
  ‖rawEmbezzlementState (d * n)‖⁻¹ *
    (Real.sqrt ((k.val : ℝ) + 1))⁻¹ *
    ‖rawEmbezzlementState n‖⁻¹ *
    harmonicTensorSchmidtAmplitude
      (n := n) σ
        (descendingHarmonicSchmidtPermutation
          (n := n) σ k)

def harmonicTargetLiftUnitary
    {d n : ℕ}
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    Matrix.unitaryGroup (Fin (d * n)) ℂ := by
  let e : (Fin d × Fin n) ≃ Fin (d * n) :=
    finProdFinEquiv
  let M : Matrix (Fin d × Fin n) (Fin d × Fin n) ℂ :=
    (U.val ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))
  have hM : M ∈ Matrix.unitaryGroup (Fin d × Fin n) ℂ := by
    exact Matrix.kronecker_mem_unitary U.property
      (show (1 : Matrix (Fin n) (Fin n) ℂ) ∈
        Matrix.unitaryGroup (Fin n) ℂ from
          (Matrix.unitaryGroup (Fin n) ℂ).one_mem)
  refine ⟨(Matrix.reindex e e) M, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff']
  have hstar :
      star ((Matrix.reindex e e) M) =
        (Matrix.reindex e e) (star M) := by
    ext i j
    simp [Matrix.star_eq_conjTranspose,
      Matrix.reindex_apply, Matrix.conjTranspose_apply]
  rw [hstar]
  change (Matrix.reindexRingEquiv ℂ e) (star M) *
    (Matrix.reindexRingEquiv ℂ e) M = 1
  rw [← (Matrix.reindexRingEquiv ℂ e).map_mul,
    (Matrix.mem_unitaryGroup_iff').mp hM]
  exact (Matrix.reindexRingEquiv ℂ e).map_one

@[simp] theorem harmonicTargetLiftUnitary_apply
    {d n : ℕ}
    (U : Matrix.unitaryGroup (Fin d) ℂ)
    (a b : Fin d) (i j : Fin n) :
    harmonicTargetLiftUnitary (n := n) U
      (finProdFinEquiv (a, i))
      (finProdFinEquiv (b, j)) =
        if i = j then U a b else 0 := by
  change
    (Matrix.reindex finProdFinEquiv finProdFinEquiv
      (U.val ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)))
        (finProdFinEquiv (a, i))
        (finProdFinEquiv (b, j)) = _
  simp [Matrix.reindex_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply]

def coherentSharedRandomControlledUnitary
    {Ω d : Type*}
    [Fintype Ω] [Fintype d]
    [DecidableEq Ω] [DecidableEq d]
    (U : Ω → Matrix.unitaryGroup d ℂ) :
    Matrix.unitaryGroup (Σ _ : Ω, d) ℂ := by
  refine ⟨Matrix.blockDiagonal' fun ω : Ω =>
    (U ω : Matrix d d ℂ), ?_⟩
  rw [Matrix.mem_unitaryGroup_iff',
    Matrix.star_eq_conjTranspose,
    Matrix.blockDiagonal'_conjTranspose,
    ← Matrix.blockDiagonal'_mul]
  have hblock (ω : Ω) :
      (U ω : Matrix d d ℂ).conjTranspose *
        (U ω : Matrix d d ℂ) = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff').mp (U ω).property
  simp_rw [hblock]
  ext ⟨ω, i⟩ ⟨ν, j⟩
  by_cases hων : ω = ν <;>
    by_cases hij : i = j <;>
      simp [Matrix.blockDiagonal'_apply,
        Matrix.one_apply, hων, hij]

def spectralPartitionPOVM
    {κ d : Type*}
    [Fintype κ] [Fintype d] [DecidableEq κ] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (bin : d → κ) : POVM κ d where
  effect k :=
    ∑ i ∈ Finset.univ.filter (fun i : d => bin i = k),
      positiveMatrixSpectralAtom F hF i
  positive k := by
    apply Matrix.posSemidef_sum
    intro i _
    exact positiveMatrixSpectralAtom_posSemidef F hF i
  complete := by
    classical
    calc
      (∑ k : κ,
        ∑ i ∈ Finset.univ.filter (fun i : d => bin i = k),
          positiveMatrixSpectralAtom F hF i) =
        ∑ i : d, positiveMatrixSpectralAtom F hF i := by
          simp [Finset.sum_filter, Finset.sum_comm]
      _ = 1 := positiveMatrixSpectralAtom_sum F hF

def bilateralWorkPairEquiv
    {ι d e : Type*} :
    ((ι → d) × (ι → e)) ≃ (ι → d × e) where
  toFun x i := (x.1 i, x.2 i)
  invFun x := (fun i => (x i).1, fun i => (x i).2)
  left_inv x := by
    rcases x with ⟨a, b⟩
    rfl
  right_inv x := by
    funext i
    exact Prod.eta (x i)

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 2048

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 3072

def finiteUniformThresholdGrid
    (lower upper : ℝ) (N : ℕ) (k : Fin N) : ℝ :=
  lower + (k.val : ℝ) * ((upper - lower) / (N : ℝ))

def finiteUniformThresholdCrossing
    (lower upper a b : ℝ) (N : ℕ) : ℝ :=
  ((Finset.univ.filter fun k : Fin N =>
      min a b ≤ finiteUniformThresholdGrid lower upper N k ∧
        finiteUniformThresholdGrid lower upper N k ≤ max a b).card : ℝ) /
    (N : ℝ)

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

def targetCoefficientMatrix
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    Matrix (Fin d) (Fin d) ℂ :=
  fun b a => ξ.val (a, b)

def targetReducedDensity
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    Matrix (Fin d) (Fin d) ℂ :=
  (targetCoefficientMatrix ξ).conjTranspose *
    targetCoefficientMatrix ξ

theorem targetReducedDensity_posSemidef
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    (targetReducedDensity ξ).PosSemidef := by
  exact Matrix.posSemidef_conjTranspose_mul_self
    (targetCoefficientMatrix ξ)

end

noncomputable section

open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option maxRecDepth 3072

def targetCanonicalSchmidtCoefficient
    {d : ℕ} (ξ : BipartiteUnitVector d)
    (i : Fin d) : ℝ :=
  Real.sqrt
    ((targetReducedDensity_posSemidef ξ).isHermitian.eigenvalues i)

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

def targetCanonicalSpectralEnergy
    {d : ℕ} (ξ ζ : BipartiteUnitVector d) : ℝ :=
  let F := targetReducedDensity ξ
  let G := targetReducedDensity ζ
  let hF := targetReducedDensity_posSemidef ξ
  let hG := targetReducedDensity_posSemidef ζ
  ∑ i : Fin d, ∑ j : Fin d,
    (Real.sqrt (hF.isHermitian.eigenvalues i) -
      Real.sqrt (hG.isHermitian.eigenvalues j)) ^ 2 *
      spectralAtomOverlap F G hF hG i j

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 3072

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048

def dSVCanonicalFailurePrefix
    {d : ℕ} (r : Fin (d + 1)) :
    EuclideanSpace ℂ (Fin d × Fin d) :=
  toLp 2 fun q : Fin d × Fin d =>
    if q.1 = q.2 ∧ q.1.val < r.val then 1 else 0

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
set_option maxRecDepth 3072

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 3072

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

def dSVRankControlledTargetCatalystIndexEquiv
    {ι : Type*} [Fintype ι]
    (d n : ℕ) :
    ((Fin d × ι) × Fin n) ≃
      Fin (d * (Fintype.card ι * n)) :=
  (Equiv.prodAssoc (Fin d) ι (Fin n)).trans
    ((Equiv.prodCongr (Equiv.refl (Fin d))
      ((Equiv.prodCongr (Fintype.equivFin ι)
        (Equiv.refl (Fin n))).trans finProdFinEquiv)).trans
      finProdFinEquiv)

end

end QuantumParallelRepetition

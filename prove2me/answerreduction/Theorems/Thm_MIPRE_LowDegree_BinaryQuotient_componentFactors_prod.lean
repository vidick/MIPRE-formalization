/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryQuotientFactors.lean (statement stub of MIPRE.LowDegree.BinaryQuotient.componentFactors_prod);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotient
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryLinear
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryElimination
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteReducedComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_IdempotentSplit
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientFactors

open MIPRE
open MIPRE.LowDegree
open MIPRE.LowDegree.BinaryQuotient
open Polynomial

theorem MIPRE.LowDegree.BinaryQuotient.componentFactors_prod (f : Polynomial (ZMod 2)) (hf : f.Monic)
    [Finite (AdjoinRoot f)]
    (hsq : Function.Bijective (fun x : AdjoinRoot f => x * x))
    {n : ℕ} (E : Fin n → Polynomial (ZMod 2))
    (he : ∀ i, PrimitiveBinaryComponent (AdjoinRoot.mk f (E i)))
    (horth : Pairwise (fun i j => AdjoinRoot.mk f (E i) * AdjoinRoot.mk f (E j) = 0))
    (hsum : ∑ i, AdjoinRoot.mk f (E i) = 1) :
    ∏ i, componentFactor f (E i) = f := by sorry

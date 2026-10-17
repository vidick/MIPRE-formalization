/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryQuotientFactors.lean (definition bundle: declarations the uploaded statements rest on);
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
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_eval2_polyOfBits

/-!
# Extracting polynomial factors from primitive quotient components

An idempotent represented by `E` corresponds to the factor `gcd(f,E-1)`.
Its multiples are exactly the polynomials annihilated by that component.
Primitive-component inverses therefore prove irreducibility without a Chinese
remainder construction or an enumeration of the quotient ring.
-/

noncomputable section

namespace MIPRE.LowDegree.BinaryQuotient

open Polynomial

/-- The factor supported by the component represented by `E`. -/
def componentFactor (f E : Polynomial (ZMod 2)) : Polynomial (ZMod 2) :=
  gcd f (E - 1)

/-- The quotient map reads coefficient bits by evaluation at its canonical root. -/
theorem mk_polyOfBits (f : Polynomial (ZMod 2)) (a : Cost.BitStr) :
    AdjoinRoot.mk f (polyOfBits a) = BinaryPolynomial.evalBits (AdjoinRoot.root f) a := by
  rw [← AdjoinRoot.aeval_eq]
  exact BinaryPolynomial.eval2_polyOfBits (algebraMap (ZMod 2) (AdjoinRoot f)) _ a

/-- Canonical coordinate bits give a polynomial representative of the quotient element. -/
@[simp] theorem mk_polyOfBits_toBits (f : Polynomial (ZMod 2)) (hf : f.Monic)
    (x : AdjoinRoot f) :
    AdjoinRoot.mk f (polyOfBits (toBits f hf x)) = x := by
  rw [mk_polyOfBits, evalBits_toBits]

end MIPRE.LowDegree.BinaryQuotient

end

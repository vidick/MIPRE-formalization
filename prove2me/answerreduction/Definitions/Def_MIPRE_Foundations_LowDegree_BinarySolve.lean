/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinarySolve.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
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
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryLinear
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryElimination
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasisProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasis
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_getD_vectorBits

/-! # Solving binary linear systems with certified elimination -/

namespace MIPRE.LowDegree.BinaryLinear

open Cost Cost.PolyTimeFun

variable {n t : ℕ}

@[simp] theorem pivotSpan_nil : pivotSpan ([] : List (Pivot n t)) = ⊥ := by
  simp [pivotSpan]

def vectorValue (n : ℕ) (v : BitStr) : Fin n → ZMod 2 := fun i => ofBool (v.getD i false)

@[simp] theorem vectorValue_vectorBits (v : Fin n → ZMod 2) :
    vectorValue n (vectorBits v) = v := by
  funext i
  rw [vectorValue, getD_vectorBits, ofBool_bit]

end MIPRE.LowDegree.BinaryLinear

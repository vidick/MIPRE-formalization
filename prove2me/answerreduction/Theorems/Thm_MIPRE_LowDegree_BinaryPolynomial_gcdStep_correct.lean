/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryGCD.lean (statement stub of MIPRE.LowDegree.BinaryPolynomial.gcdStep_correct);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Polynomial.Content
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryConstants
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNormalize
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDivision
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGCD

open MIPRE
open MIPRE.LowDegree
open MIPRE.LowDegree.BinaryPolynomial
open MIPRE.Cost MIPRE.Cost.PolyTimeFun Polynomial

theorem MIPRE.LowDegree.BinaryPolynomial.gcdStep_correct (s : GCDState) (b : Bool)
    (hs : s.2 = [] ∨ s.2.getLastD false = true) :
    gcd (polyOfBits (gcdStep s b).1) (polyOfBits (gcdStep s b).2) =
      gcd (polyOfBits s.1) (polyOfBits s.2) ∧
    ((gcdStep s b).2 = [] ∨ (gcdStep s b).2.getLastD false = true) := by sorry

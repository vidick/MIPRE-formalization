/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryArtinSchreierProg.lean (statement stub of MIPRE.LowDegree.BinaryPolynomial.polyOfBits_substituteArtinSchreierBits);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNormalize
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierProg

open MIPRE
open MIPRE.LowDegree
open MIPRE.LowDegree.BinaryPolynomial
open MIPRE.Cost MIPRE.Cost.PolyTimeFun Polynomial

theorem MIPRE.LowDegree.BinaryPolynomial.polyOfBits_substituteArtinSchreierBits (a : BitStr) :
    polyOfBits (substituteArtinSchreierBits a) = (polyOfBits a).comp (X ^ 2 + X) := by sorry

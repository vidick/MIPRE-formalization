/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryRepresentation.lean (statement stub of MIPRE.LowDegree.BinaryPolynomial.normalize_monic);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation

open MIPRE
open MIPRE.LowDegree
open MIPRE.Cost

theorem MIPRE.LowDegree.BinaryPolynomial.normalize_monic (l : BitStr) (h : (polyOfBits l).Monic) :
    polyOfBits (l.take (polyOfBits l).natDegree ++ [true]) = polyOfBits l := by sorry

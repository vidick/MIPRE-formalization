/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryCoprimeDegree.lean (statement stub of MIPRE.LowDegree.BinaryFiniteField.minpoly_natDegree_add_of_coprime);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.FieldTheory.Finite.Extension
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCoprimeDegree

open MIPRE
open MIPRE.LowDegree
open MIPRE.LowDegree.BinaryFiniteField
open Polynomial
variable {R : Type*} [CommRing R] [CharP R 2]
variable {L : Type*} [Field L] [Algebra (ZMod 2) L]

theorem MIPRE.LowDegree.BinaryFiniteField.minpoly_natDegree_add_of_coprime (x y : L)
    (hx : IsIntegral (ZMod 2) x) (hy : IsIntegral (ZMod 2) y)
    (hab : (minpoly (ZMod 2) x).natDegree.Coprime (minpoly (ZMod 2) y).natDegree) :
    (minpoly (ZMod 2) (x + y)).natDegree =
      (minpoly (ZMod 2) x).natDegree * (minpoly (ZMod 2) y).natDegree := by sorry

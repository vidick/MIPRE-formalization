/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryCoprimeDegree.lean (statement stub of MIPRE.LowDegree.BinaryFiniteField.frobenius_period_add_of_coprime);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.FieldTheory.Finite.Extension
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCoprimeDegree

open MIPRE
open MIPRE.LowDegree
open MIPRE.LowDegree.BinaryFiniteField
open Polynomial
variable {R : Type*} [CommRing R] [CharP R 2]

theorem MIPRE.LowDegree.BinaryFiniteField.frobenius_period_add_of_coprime (x y : R) (a b n : ℕ) (hab : a.Coprime b)
    (hx : iterateFrobenius R 2 a x = x) (hy : iterateFrobenius R 2 b y = y)
    (hs : iterateFrobenius R 2 n (x + y) = x + y) :
    iterateFrobenius R 2 n x = x ∧ iterateFrobenius R 2 n y = y := by sorry

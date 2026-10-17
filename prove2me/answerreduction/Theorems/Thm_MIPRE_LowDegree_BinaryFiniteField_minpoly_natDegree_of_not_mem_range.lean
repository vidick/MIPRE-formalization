/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryFiniteFieldDegree.lean (statement stub of MIPRE.LowDegree.BinaryFiniteField.minpoly_natDegree_of_not_mem_range);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.FieldTheory.Finite.Extension

open Polynomial

theorem MIPRE.LowDegree.BinaryFiniteField.minpoly_natDegree_of_not_mem_range {K L : Type*} [Field K] [Field L]
    [Finite K] [Algebra K L] [Algebra (ZMod 2) L] [FiniteDimensional (ZMod 2) L]
    (t : ℕ) (hK : Nat.card K = 2 ^ (2 ^ t))
    (hL : Module.finrank (ZMod 2) L = 2 ^ (t + 1)) (x : L)
    (hx : x ∉ (algebraMap K L).range) :
    (minpoly (ZMod 2) x).natDegree = 2 ^ (t + 1) := by sorry

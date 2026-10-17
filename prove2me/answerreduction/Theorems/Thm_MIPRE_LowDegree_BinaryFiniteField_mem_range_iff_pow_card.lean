/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryFiniteFieldDegree.lean (statement stub of MIPRE.LowDegree.BinaryFiniteField.mem_range_iff_pow_card);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.FieldTheory.Finite.Extension

open Polynomial

theorem MIPRE.LowDegree.BinaryFiniteField.mem_range_iff_pow_card {K L : Type*} [Field K] [Field L] [Finite K]
    [Algebra K L] (x : L) :
    x ∈ (algebraMap K L).range ↔ x ^ Nat.card K = x := by sorry

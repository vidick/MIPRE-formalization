/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/SelfDualize.lean (statement stub of MIPRE.LowDegree.add_self_injective);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_MIPRE_Foundations_LowDegree_SelfDualize

open MIPRE
open MIPRE.LowDegree
open Finset
variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem MIPRE.LowDegree.add_self_injective (hG : Odd (Fintype.card G)) :
    Function.Injective fun g : G => g + g := by sorry

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/SelfDualize.lean (statement stub of MIPRE.LowDegree.mul_self_bijective);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_MIPRE_Foundations_LowDegree_SelfDualize

open MIPRE
open MIPRE.LowDegree
open Finset
variable {G : Type*} [AddCommGroup G] [Fintype G]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq G]

theorem MIPRE.LowDegree.mul_self_bijective (hF : CharP F 2) (hG : Odd (Fintype.card G)) :
    Function.Bijective fun x : AddMonoidAlgebra F G => x * x := by sorry

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/BlockPoly.lean (statement stub of MIPRE.LIDT.LowIndDegPoly.eval_blockPoly);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Background_LIDT_BlockPoly

open MIPRE
open MIPRE.LIDT
open MIPRE.LIDT.LowIndDegPoly
open Finset
variable {F : Type*} [Field F] {n n' d : ℕ}

theorem MIPRE.LIDT.LowIndDegPoly.eval_blockPoly {idx : Fin n' → Fin n} (hinj : Function.Injective idx)
    {H : LowIndDegPoly (F := F) (m := n) (d := d)}
    (hsupp : ∀ e, H e ≠ 0 → ∀ k, (∀ j, idx j ≠ k) → e k = 0) (u : Point F n) :
    (H.blockPoly idx).eval (fun j => u (idx j)) = H.eval u := by sorry

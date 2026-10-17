/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/BlockPoly.lean (definition bundle: declarations the uploaded statements rest on);
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

/-!
# A polynomial on a block of the variables

A coefficient vector in `n` variables read on a block of them, as a coefficient vector in the
block's `n'` variables (`LowIndDegPoly.blockPoly`), and the exponent vectors that carry it
(`expandIdx`). Moved from `MIPRE/Background/QLD/Complete.lean`, where the Pauli basis test's
completion uses them, so that answer reduction can use them without importing that test.
-/

noncomputable section

/-! ## A polynomial on a block of the variables -/

namespace MIPRE.LIDT

open Finset

variable {F : Type*} [Field F] {n n' d : ℕ}

/-- The exponent vector on `Fin n` carried by the injection `idx` from one on `Fin n'`, zero off
the range. -/
def expandIdx (idx : Fin n' → Fin n) (e' : Fin n' → Fin (d + 1)) : Fin n → Fin (d + 1) :=
  fun k => if h : ∃ j, idx j = k then e' h.choose else 0

/-- **A coefficient vector read on a block of the variables**, as a coefficient vector on the
block. -/
def LowIndDegPoly.blockPoly (idx : Fin n' → Fin n) (H : LowIndDegPoly (F := F) (m := n) (d := d)) :
    LowIndDegPoly (F := F) (m := n') (d := d) :=
  fun e' => H (expandIdx idx e')

/-- **A coefficient vector in a block's variables, placed on the block**: zero on every monomial
that reads a variable off the block. -/
def LowIndDegPoly.liftIdx (idx : Fin n' → Fin n) (g : LowIndDegPoly (F := F) (m := n') (d := d)) :
    LowIndDegPoly (F := F) (m := n) (d := d) :=
  fun e => if ∀ k, (∀ j, idx j ≠ k) → e k = 0 then g (fun j => e (idx j)) else 0

end MIPRE.LIDT

end

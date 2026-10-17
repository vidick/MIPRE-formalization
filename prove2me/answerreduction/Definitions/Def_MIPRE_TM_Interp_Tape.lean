/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/Interp/Tape.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Sign.Defs
import Mathlib.Tactic
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_TM_Interp_Instr

/-!
# Tape contents

`Holds τ p l`: the tape `τ` holds the list `l` from cell `p`. The lemmas relate it to
appending, to writing a cell (`Function.update`) and to reading the cell under a head.
-/

namespace MIPRE.TM.Interp

/-- A work tape. -/
abbrev Tape := ℤ → Option Sym

/-- The tape holds `l` from cell `p`. -/
def Holds (τ : Tape) (p : ℤ) (l : List Sym) : Prop :=
  ∀ k : ℕ, (hk : k < l.length) → τ (p + k) = some l[k]

namespace Holds

variable {τ : Tape} {p : ℤ}

@[simp] theorem nil : Holds τ p [] := fun k hk => by simp at hk

end Holds

/-- The cells of `[p, p + n)` are blank. -/
def BlankFrom (τ : Tape) (p : ℤ) (n : ℕ) : Prop := ∀ q, p ≤ q → q < p + n → τ q = none

/-- The tape is blank from `p` on. -/
def BlankBeyond (τ : Tape) (p : ℤ) : Prop := ∀ q, p ≤ q → τ q = none

/-- The tape is blank before `p`. -/
def BlankBefore (τ : Tape) (p : ℤ) : Prop := ∀ q, q < p → τ q = none

/-- The bits of a bit string as symbols. -/
def bits : List Bool → List Sym := List.map fun b => if b then Sym.one else Sym.zero

@[simp] theorem bits_nil : bits [] = [] := rfl
@[simp] theorem bits_cons (b : Bool) (l : List Bool) :
    bits (b :: l) = (if b then Sym.one else Sym.zero) :: bits l := rfl
@[simp] theorem bits_append (l₁ l₂ : List Bool) : bits (l₁ ++ l₂) = bits l₁ ++ bits l₂ :=
  List.map_append ..
@[simp] theorem length_bits (l : List Bool) : (bits l).length = l.length := List.length_map ..

end MIPRE.TM.Interp

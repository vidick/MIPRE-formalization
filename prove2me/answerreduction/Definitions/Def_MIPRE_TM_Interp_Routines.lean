/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/Interp/Routines.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Computability.Language
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Sign.Defs
import Mathlib.Logic.Relation
import Mathlib.Tactic
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Cslib_Foundations_Data_RelatesInSteps
import Definitions.Def_MIPRE_Cslib_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_MIPRE_TM_MultiInput_Deterministic
import Definitions.Def_MIPRE_TM_Interp_Instr
import Definitions.Def_MIPRE_TM_Interp_Machine
import Definitions.Def_MIPRE_TM_Interp_Tape
import Definitions.Def_MIPRE_TM_Interp_Reach

/-!
# The routines: specifications of the instructions

Each instruction's specification is a reachability statement: from a configuration at
the instruction's first phase, with the tapes it reads in a stated shape, a bounded
number of steps leads to the configuration at the next instruction, with the stated
effect on the tapes it touches and none on the others (`Untouched`).
-/

namespace MIPRE.TM.Interp

open Turing MultiInputTM Phase
open MultiTapeTM (moveInputPos)

variable {input : Fin 7 → List Sym}

/-- The control at `(k, pc)`, first phase. -/
abbrev at_ (k : ProgId) (pc : Fin maxPc) : Option Ctl := some ⟨k, pc, p0⟩

/-- The control at the instruction after `(k, pc)`. -/
def next_ (k : ProgId) (pc : Fin maxPc) (h : pc.val + 1 < maxPc) : Option Ctl :=
  some ⟨k, ⟨pc.val + 1, h⟩, p0⟩

@[simp] theorem resolve_stay (k : ProgId) (pc : Fin maxPc) (ph : Phase) :
    resolve k pc (.stay ph) = some ⟨k, pc, ph⟩ := rfl

@[simp] theorem resolve_jmp (k : ProgId) (pc : Fin maxPc) (k' : ProgId) :
    resolve k pc (.jmp k') = some ⟨k', ⟨0, by decide⟩, p0⟩ := rfl

@[simp] theorem resolve_halt (k : ProgId) (pc : Fin maxPc) : resolve k pc .halt = none := rfl

/-- `c'` agrees with `c` on the input heads outside `SI` and on the work tapes outside `SW`. -/
def Untouched (c c' : Cfg input) (SI : List IT) (SW : List WT) : Prop :=
  (∀ j, j ∉ SI → c'.inputPos j = c.inputPos j) ∧
    ∀ d, d ∉ SW → c'.workTapes d = c.workTapes d ∧ c'.workTapePos d = c.workTapePos d

namespace Untouched

end Untouched

/-! ## One step of an instruction -/

/-- An action that moves only the input heads in `SI` and touches only the work tapes in
`SW`. -/
def Act.Within (a : Act) (SI : List IT) (SW : List WT) : Prop :=
  (∀ j, j ∉ SI → a.inMoves j = 0) ∧ ∀ d, d ∉ SW → a.works d = (none, 0)

/-! ## `write` -/

/-! ## `move` -/

/-! ## `toEnd` -/

/-! ## `rewind` -/

/-! ## `eraseRight` -/

/-! ## `copyUntil` -/

/-! ## `branch`, `jump`, `emit`, `halt` -/

/-! ## Scanning left -/

/-! ## `popBack` -/

/-! ## The budget and the counter -/

/-- A unary tape: `n` ones from cell `0`, blank elsewhere. -/
def Unary (τ : Tape) (n : ℕ) : Prop :=
  Holds τ 0 (List.replicate n .one) ∧ BlankBeyond τ n ∧ BlankBefore τ 0

/-! ## Input heads -/

end MIPRE.TM.Interp

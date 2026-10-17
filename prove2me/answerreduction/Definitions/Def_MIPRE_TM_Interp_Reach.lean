/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/Interp/Reach.lean (definition bundle: declarations the uploaded statements rest on);
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

/-!
# Runs of the interpreter

`Reach c n c' out`: from the configuration `c`, `n` steps of `U` lead to `c'`, emitting
`out`. It composes (`Reach.trans`), and a single step is the action of the current
instruction phase (`step_eq`, `applyAct`). The routine specifications (`Routines.lean`)
are reachability statements with step bounds.
-/

namespace MIPRE.TM.Interp

open Turing MultiInputTM
open MultiTapeTM (moveInputPos)

variable {input : Fin 7 → List Sym}

/-- Configurations of the interpreter on the inputs `input`. -/
abbrev Cfg (input : Fin 7 → List Sym) := MultiInputTM.Cfg 7 6 Sym Ctl input

/-- The configuration after the actions `a`, with the control `q'`. -/
def applyAct (a : Act) (q' : Option Ctl) (c : Cfg input) : Cfg input where
  state := q'
  inputPos j := moveInputPos (c.inputPos j) (a.inMoves j)
  workTapes d :=
    match (a.works d).1 with
    | none => c.workTapes d
    | some s => Function.update (c.workTapes d) (c.workTapePos d) s
  workTapePos d := c.workTapePos d + (a.works d).2

/-- The action of the current instruction phase. -/
def actOf (q : Ctl) (c : Cfg input) : Act :=
  execInstr (instrAt q.k q.pc) q.ph c.inputSymbols c.workTapeSymbols

/-- `n` steps from `c` lead to `c'`, emitting `out`. -/
def Reach (c : Cfg input) (n : ℕ) (c' : Cfg input) (out : List Sym) : Prop :=
  U.configs c n = c' ∧ U.outputString c n = out

namespace Reach

end Reach

/-- Halting silently: the state is `none` after `n` steps, and nothing was emitted. -/
def HaltsIn (c : Cfg input) (n : ℕ) : Prop :=
  (U.configs c n).state = none ∧ U.outputString c n = []

/-! ## Reading and writing under `applyAct` -/

section Apply

variable (a : Act) (q' : Option Ctl) (c : Cfg input)

@[simp] theorem applyAct_state : (applyAct a q' c).state = q' := rfl

@[simp] theorem applyAct_inputPos (j : IT) :
    (applyAct a q' c).inputPos j = moveInputPos (c.inputPos j) (a.inMoves j) := rfl

@[simp] theorem applyAct_workTapePos (d : WT) :
    (applyAct a q' c).workTapePos d = c.workTapePos d + (a.works d).2 := rfl

end Apply

/-! ## Evaluating actions -/

namespace Act

@[simp] theorem base_inMoves (n : Next) (j : IT) : (base n).inMoves j = 0 := rfl
@[simp] theorem base_works (n : Next) (d : WT) : (base n).works d = (none, 0) := rfl
@[simp] theorem base_out (n : Next) : (base n).out = none := rfl
@[simp] theorem base_next (n : Next) : (base n).next = n := rfl

@[simp] theorem mw_next (a : Act) (t : WT) (m : SignType) : (a.mw t m).next = a.next := rfl
@[simp] theorem ww_next (a : Act) (t : WT) (s : Option Sym) : (a.ww t s).next = a.next := rfl
@[simp] theorem mi_next (a : Act) (j : IT) (m : SignType) : (a.mi j m).next = a.next := rfl
@[simp] theorem emit_next (a : Act) (s : Sym) : (a.emit s).next = a.next := rfl

@[simp] theorem mw_out (a : Act) (t : WT) (m : SignType) : (a.mw t m).out = a.out := rfl
@[simp] theorem ww_out (a : Act) (t : WT) (s : Option Sym) : (a.ww t s).out = a.out := rfl
@[simp] theorem mi_out (a : Act) (j : IT) (m : SignType) : (a.mi j m).out = a.out := rfl
@[simp] theorem emit_out (a : Act) (s : Sym) : (a.emit s).out = some s := rfl

@[simp] theorem mw_inMoves (a : Act) (t : WT) (m : SignType) : (a.mw t m).inMoves = a.inMoves := rfl
@[simp] theorem ww_inMoves (a : Act) (t : WT) (s : Option Sym) : (a.ww t s).inMoves = a.inMoves := rfl
@[simp] theorem emit_inMoves (a : Act) (s : Sym) : (a.emit s).inMoves = a.inMoves := rfl
@[simp] theorem mi_inMoves (a : Act) (j : IT) (m : SignType) :
    (a.mi j m).inMoves = Function.update a.inMoves j m := rfl

@[simp] theorem mi_works (a : Act) (j : IT) (m : SignType) : (a.mi j m).works = a.works := rfl
@[simp] theorem emit_works (a : Act) (s : Sym) : (a.emit s).works = a.works := rfl

@[simp] theorem mw_works_self (a : Act) (t : WT) (m : SignType) :
    (a.mw t m).works t = ((a.works t).1, m) := by simp [mw]

@[simp] theorem ww_works_self (a : Act) (t : WT) (s : Option Sym) :
    (a.ww t s).works t = (some s, (a.works t).2) := by simp [ww]

end Act

end MIPRE.TM.Interp

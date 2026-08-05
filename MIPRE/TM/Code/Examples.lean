/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.TM.Code.Semantics

/-!
# Executable test machines

The Milestone B acceptance tests (`planning/tm-infrastructure.md`): concrete machine
codes whose runs are evaluated *inside the kernel* — every `example … := by decide` below
both pins the expected behaviour as a regression test and certifies that the whole
evaluation path (`Code.toTM`, `Code.actionAt`, `Turing.transitionIndex`,
`MultiInputTM.step`/`configs`/`outputString`) is genuinely executable, with no
`Fintype.elems`, choice, or `noncomputable` anywhere in it (decision D5). No
`native_decide` is used.

Machines (all at arity one, alphabet size two):

1. `defaultRejectCode i` — output `0` and halt (arity-generic; the total-decoding default
   of Milestone C);
2. `copyBit` — copy the first input bit;
3. `moveLeftTwice` — walk onto the left blank boundary and verify clamping;
4. `moveRightTwice` — walk past the last symbol and verify clamping;
5. `workTapeRoundTrip` — write a symbol, move away, come back, reread it, output it;
6. `loopForever` — a two-state machine that never halts.

The probe helpers project decidable data (states, head positions, output bits, tape
windows) out of configurations, whose tape fields are functions and therefore not
themselves comparable.
-/

namespace Turing.Code

/-! ## The default reject machine -/

/-- The action of the default reject machine: touch nothing, output `0`, halt. -/
def defaultRejectAction (i : ℕ) : RawAction where
  inputMoves := Array.replicate i .stay
  workActions := #[]
  output := some false
  nextState := none

/-- The default reject machine: two symbols, one state, no work tapes; on its first
transition it outputs `0` (i.e. `false`) and halts, regardless of the observation. This
is the total interpretation of malformed descriptions in Milestone C. -/
def defaultRejectCode (i : ℕ) : Code i where
  raw :=
    { workTapeCount := 0
      alphabetSize := 2
      stateCount := 1
      startState := 0
      table := Array.replicate (3 ^ i) (defaultRejectAction i) }
  wf := by
    refine ⟨Nat.le_refl 2, Nat.one_pos, Nat.one_pos, by simp, ?_⟩
    intro a ha
    rw [Array.mem_replicate] at ha
    obtain ⟨-, rfl⟩ := ha
    exact ⟨by simp [defaultRejectAction], by simp [defaultRejectAction],
      by simp [defaultRejectAction], by simp [defaultRejectAction]⟩

/-! ## Probe helpers -/

variable {i : ℕ}

/-- The state (as a raw number) after `t` steps on bit inputs `x`. -/
def stateAt (c : Code i) (x : Fin i → List Bool) (t : ℕ) : Option ℕ :=
  ((c.toTM.configs (c.toTM.initCfg (c.bitInputs x)) t).state).map Fin.val

/-- The position of input head `j` after `t` steps on bit inputs `x`. -/
def inputPosAt (c : Code i) (x : Fin i → List Bool) (t : ℕ) (j : Fin i) : ℕ :=
  ((c.toTM.configs (c.toTM.initCfg (c.bitInputs x)) t).inputPos j).val

/-- The symbol (as a raw number) under input head `j` after `t` steps. -/
def inputSymbolAt (c : Code i) (x : Fin i → List Bool) (t : ℕ) (j : Fin i) : Option ℕ :=
  ((c.toTM.configs (c.toTM.initCfg (c.bitInputs x)) t).inputSymbol j).map Fin.val

/-- A window of `len` cells of work tape `d`, starting at position `lo`, after `t`
steps. -/
def workWindow (c : Code i) (x : Fin i → List Bool) (t : ℕ) (d : Fin c.workTapeCount)
    (lo : ℤ) (len : ℕ) : List (Option ℕ) :=
  (List.range len).map fun k =>
    ((c.toTM.configs (c.toTM.initCfg (c.bitInputs x)) t).workTapes d (lo + k)).map Fin.val

/-- The bits output during the first `t` steps on bit inputs `x`. -/
def outBitsAt (c : Code i) (x : Fin i → List Bool) (t : ℕ) : List Bool :=
  c.decodeBitOutput (c.toTM.outputString (c.toTM.initCfg (c.bitInputs x)) t)

/-- The work-tape space used up to step `t` on bit inputs `x`. -/
def spaceAt (c : Code i) (x : Fin i → List Bool) (t : ℕ) : ℕ :=
  c.toTM.spaceUsed (c.toTM.initCfg (c.bitInputs x)) t

/-! ## 1: output `0` and halt -/

example : stateAt (defaultRejectCode 1) (fun _ => [true]) 0 = some 0 := by decide
example : stateAt (defaultRejectCode 1) (fun _ => [true]) 1 = none := by decide
example : outBitsAt (defaultRejectCode 1) (fun _ => [true]) 5 = [false] := by decide
example : (defaultRejectCode 1).toTM.haltsAtStep
    ((defaultRejectCode 1).bitInputs fun _ => [true]) 1 = true := by decide

/-! ## 2: copy the first input bit -/

/-- Copy the first input bit: one state; on reading a symbol output it and halt, on
reading the blank boundary output `0` and halt. -/
def copyBit : Code 1 :=
  ⟨{ workTapeCount := 0
     alphabetSize := 2
     stateCount := 1
     startState := 0
     table := #[
       -- observation digits: 0 = blank, 1 = symbol `0`, 2 = symbol `1`
       { inputMoves := #[.stay], workActions := #[], output := some false, nextState := none },
       { inputMoves := #[.stay], workActions := #[], output := some false, nextState := none },
       { inputMoves := #[.stay], workActions := #[], output := some true, nextState := none }] },
   by decide⟩

example : outBitsAt copyBit (fun _ => [true]) 2 = [true] := by decide
example : outBitsAt copyBit (fun _ => [false]) 2 = [false] := by decide
example : outBitsAt copyBit (fun _ => [true, false]) 2 = [true] := by decide
example : outBitsAt copyBit (fun _ => []) 2 = [false] := by decide
example : stateAt copyBit (fun _ => [true]) 1 = none := by decide
example : copyBit.toTM.haltsAtStep (copyBit.bitInputs fun _ => [true]) 1 = true := by
  decide

/-! ## 3: move left onto the blank boundary -/

/-- Move the input head left twice (the second move is clamped at the left boundary),
then halt. -/
def moveLeftTwice : Code 1 :=
  ⟨{ workTapeCount := 0
     alphabetSize := 2
     stateCount := 2
     startState := 0
     table :=
       Array.replicate 3
         { inputMoves := #[.left], workActions := #[], output := none, nextState := some 1 } ++
       Array.replicate 3
         { inputMoves := #[.left], workActions := #[], output := none, nextState := none } },
   by decide⟩

example : inputPosAt moveLeftTwice (fun _ => [true]) 0 0 = 1 := by decide
example : inputPosAt moveLeftTwice (fun _ => [true]) 1 0 = 0 := by decide
example : inputSymbolAt moveLeftTwice (fun _ => [true]) 1 0 = none := by decide
-- the second left move is clamped: the head stays on the left boundary
example : inputPosAt moveLeftTwice (fun _ => [true]) 2 0 = 0 := by decide
example : stateAt moveLeftTwice (fun _ => [true]) 2 = none := by decide

/-! ## 4: move right past the final symbol -/

/-- Move the input head right twice (the second move is clamped at the right boundary),
then halt. -/
def moveRightTwice : Code 1 :=
  ⟨{ workTapeCount := 0
     alphabetSize := 2
     stateCount := 2
     startState := 0
     table :=
       Array.replicate 3
         { inputMoves := #[.right], workActions := #[], output := none, nextState := some 1 } ++
       Array.replicate 3
         { inputMoves := #[.right], workActions := #[], output := none, nextState := none } },
   by decide⟩

example : inputPosAt moveRightTwice (fun _ => [true]) 1 0 = 2 := by decide
example : inputSymbolAt moveRightTwice (fun _ => [true]) 1 0 = none := by decide
-- the second right move is clamped: the head stays on the right boundary
example : inputPosAt moveRightTwice (fun _ => [true]) 2 0 = 2 := by decide
example : stateAt moveRightTwice (fun _ => [true]) 2 = none := by decide

/-! ## 5: write, move, return, and reread a work-tape symbol -/

/-- Write symbol `1` on the work tape, move the work head right, move it back left,
reread the written symbol, output it as a bit, and halt. Observation digits are
`inputDigit * 3 + workDigit`; in state `2` the entries with work digit `2`
(symbol `1` under the work head) output `true`. -/
def workTapeRoundTrip : Code 1 :=
  ⟨{ workTapeCount := 1
     alphabetSize := 2
     stateCount := 3
     startState := 0
     table :=
       -- state 0: write `1`, move right, go to state 1
       Array.replicate 9
         { inputMoves := #[.stay], workActions := #[⟨.symbol 1, .right⟩],
           output := none, nextState := some 1 } ++
       -- state 1: move back left, go to state 2
       Array.replicate 9
         { inputMoves := #[.stay], workActions := #[⟨.keep, .left⟩],
           output := none, nextState := some 2 } ++
       -- state 2: output whether the work head reads symbol `1`, halt
       #[
         { inputMoves := #[.stay], workActions := #[⟨.keep, .stay⟩], output := some false, nextState := none },
         { inputMoves := #[.stay], workActions := #[⟨.keep, .stay⟩], output := some false, nextState := none },
         { inputMoves := #[.stay], workActions := #[⟨.keep, .stay⟩], output := some true, nextState := none },
         { inputMoves := #[.stay], workActions := #[⟨.keep, .stay⟩], output := some false, nextState := none },
         { inputMoves := #[.stay], workActions := #[⟨.keep, .stay⟩], output := some false, nextState := none },
         { inputMoves := #[.stay], workActions := #[⟨.keep, .stay⟩], output := some true, nextState := none },
         { inputMoves := #[.stay], workActions := #[⟨.keep, .stay⟩], output := some false, nextState := none },
         { inputMoves := #[.stay], workActions := #[⟨.keep, .stay⟩], output := some false, nextState := none },
         { inputMoves := #[.stay], workActions := #[⟨.keep, .stay⟩], output := some true, nextState := none }] },
   by decide⟩

example : outBitsAt workTapeRoundTrip (fun _ => [true]) 5 = [true] := by decide
example : stateAt workTapeRoundTrip (fun _ => [true]) 3 = none := by decide
-- after the run, the work tape holds exactly one written cell, at the origin
example : workWindow workTapeRoundTrip (fun _ => [true]) 3 ⟨0, by decide⟩ (-1) 3 =
    [none, some 1, none] := by decide
-- the head visited two cells
example : spaceAt workTapeRoundTrip (fun _ => [true]) 3 = 2 := by decide

/-! ## 6: a two-state machine that never halts -/

/-- Bounce between two states forever, never halting. -/
def loopForever : Code 1 :=
  ⟨{ workTapeCount := 0
     alphabetSize := 2
     stateCount := 2
     startState := 0
     table :=
       Array.replicate 3
         { inputMoves := #[.stay], workActions := #[], output := none, nextState := some 1 } ++
       Array.replicate 3
         { inputMoves := #[.stay], workActions := #[], output := none, nextState := some 0 } },
   by decide⟩

set_option maxRecDepth 4000 in
example : stateAt loopForever (fun _ => [true]) 100 = some 0 := by decide
set_option maxRecDepth 4000 in
example : stateAt loopForever (fun _ => [true]) 101 = some 1 := by decide
example : loopForever.toTM.haltsAtStep (loopForever.bitInputs fun _ => [true]) 7 = false := by
  decide
example : outBitsAt loopForever (fun _ => [true]) 50 = [] := by decide

/-! ## Display demos (`#eval` doubles as an executability check) -/

#eval stateAt copyBit (fun _ => [true]) 1                 -- none (halted)
#eval outBitsAt workTapeRoundTrip (fun _ => [true]) 5     -- [true]
#eval workWindow workTapeRoundTrip (fun _ => [true]) 3 ⟨0, by decide⟩ (-1) 3
#eval spaceAt workTapeRoundTrip (fun _ => [true]) 3       -- 2

end Turing.Code

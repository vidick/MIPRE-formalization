/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.TM.Code.Encoding.MachineCode
public meta import MIPRE.TM.Code.Encoding.MachineCode
public import MIPRE.TM.Code.Examples
public meta import MIPRE.TM.Code.Examples

@[expose] public section

/-!
# Total decoding, description size, and the Milestone C test battery

`Turing.decodeCode` interprets *every* bit string as a machine: malformed descriptions
(and non-canonical ones — anything `decodeCodeExact` rejects) decode to the default
reject machine `Code.defaultRejectCode i`, giving the paper's total notation `[α]_i`.

`Turing.codeSize` is the description length `|α|`; `codeSize_le` bounds it explicitly in
the header data — the arithmetic later consumed by λ-boundedness bookkeeping.

The examples at the end are the Milestone C acceptance battery
(`planning/tm-infrastructure.md`, WP9), all kernel-evaluated by `decide`: encode/decode
round trips for the Milestone B machines, and one malformed description per failure mode
— zero states, alphabet of size one, wrong table length, out-of-range successor state,
out-of-range work symbol, trailing garbage, and the empty string — each pinned to
`decodeCodeExact = none` and `decodeCode = defaultRejectCode`.
-/

set_option maxRecDepth 8000

namespace Turing

/-! ## Total decoding -/

/-- Total decoding: the machine described by an arbitrary bit string — the paper's
`[α]_i`. Strings rejected by `decodeCodeExact` denote the default reject machine. -/
def decodeCode (i : ℕ) (s : List Bool) : Code i :=
  (decodeCodeExact i s).getD (Code.defaultRejectCode i)

@[simp]
theorem decodeCode_encodeCode {i : ℕ} (c : Code i) : decodeCode i (encodeCode c) = c := by
  simp [decodeCode]

/-! ## Description size -/

/-- The description size `|α|` of a machine code. -/
def codeSize {i : ℕ} (c : Code i) : ℕ := (encodeCode c).length

/-! ## Round trips (Milestone B machines) -/

example : decodeCodeExact 1 (encodeCode Code.copyBit) = some Code.copyBit := by decide
example : decodeCode 1 (encodeCode Code.copyBit) = Code.copyBit := by decide
example : decodeCode 1 (encodeCode Code.moveLeftTwice) = Code.moveLeftTwice := by decide
example : decodeCode 1 (encodeCode Code.moveRightTwice) = Code.moveRightTwice := by decide
example : decodeCode 1 (encodeCode Code.workTapeRoundTrip) = Code.workTapeRoundTrip := by
  decide
example : decodeCode 1 (encodeCode Code.loopForever) = Code.loopForever := by decide
example : decodeCode 1 (encodeCode (Code.defaultRejectCode 1))
    = Code.defaultRejectCode 1 := by decide

/-! ## The malformed battery

One raw description per failure mode; each must be rejected by `decodeCodeExact` and
decode totally to the default reject machine. -/

/-- A syntactically plausible one-input entry. -/
def dummyEntry : RawAction :=
  { inputMoves := #[.stay], workActions := #[], output := some false, nextState := none }

/-- Zero states (the empty table has the canonical size `0 · 3¹`, so this parses and is
rejected by the checker alone). -/
def badZeroStates : RawCode 1 :=
  { workTapeCount := 0, alphabetSize := 2, stateCount := 0, startState := 0, table := #[] }

/-- Alphabet of size one (table of the canonical size `1 · 2¹`). -/
def badAlphabet : RawCode 1 :=
  { workTapeCount := 0, alphabetSize := 1, stateCount := 1, startState := 0,
    table := #[dummyEntry, dummyEntry] }

/-- Wrong table length: the header demands `1 · 3¹ = 3` entries, only two are present,
so parsing itself fails. -/
def badTableLength : RawCode 1 :=
  { workTapeCount := 0, alphabetSize := 2, stateCount := 1, startState := 0,
    table := #[dummyEntry, dummyEntry] }

/-- Out-of-range successor state. -/
def badNextState : RawCode 1 :=
  { workTapeCount := 0, alphabetSize := 2, stateCount := 1, startState := 0,
    table := #[{ inputMoves := #[.stay], workActions := #[], output := none,
                 nextState := some 5 }, dummyEntry, dummyEntry] }

/-- Out-of-range work symbol (one work tape, so `1 · 3² = 9` entries). -/
def badWorkSymbol : RawCode 1 :=
  { workTapeCount := 1, alphabetSize := 2, stateCount := 1, startState := 0,
    table := Array.replicate 9
      { inputMoves := #[.stay], workActions := #[⟨.symbol 7, .stay⟩], output := none,
        nextState := none } }

example : decodeCodeExact 1 (encodeRawCode badZeroStates) = none := by decide
example : decodeCode 1 (encodeRawCode badZeroStates) = Code.defaultRejectCode 1 := by
  decide
example : decodeCodeExact 1 (encodeRawCode badAlphabet) = none := by decide
example : decodeCode 1 (encodeRawCode badAlphabet) = Code.defaultRejectCode 1 := by decide
example : decodeCodeExact 1 (encodeRawCode badTableLength) = none := by decide
example : decodeCode 1 (encodeRawCode badTableLength) = Code.defaultRejectCode 1 := by
  decide
example : decodeCodeExact 1 (encodeRawCode badNextState) = none := by decide
example : decodeCode 1 (encodeRawCode badNextState) = Code.defaultRejectCode 1 := by
  decide
example : decodeCodeExact 1 (encodeRawCode badWorkSymbol) = none := by decide
example : decodeCode 1 (encodeRawCode badWorkSymbol) = Code.defaultRejectCode 1 := by
  decide

-- the empty string
example : decodeCodeExact 1 ([] : List Bool) = none := by decide
example : decodeCode 1 ([] : List Bool) = Code.defaultRejectCode 1 := by decide

-- trailing garbage after a valid description
example : decodeCodeExact 1 (encodeCode Code.copyBit ++ [true]) = none := by decide
example : decodeCode 1 (encodeCode Code.copyBit ++ [true]) = Code.defaultRejectCode 1 := by
  decide

/-! ## Display demos -/

#eval codeSize Code.copyBit                        -- description length of the copy machine
#eval codeSize (Code.defaultRejectCode 1)
#eval (encodeCode (Code.defaultRejectCode 1)).map fun b => if b then 1 else 0

end Turing

end

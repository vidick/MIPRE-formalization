/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.TM.Code.Encoding.MachineCode
import MIPRE.TM.Code.Examples

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

theorem codeSize_eq {i : ℕ} (c : Code i) : codeSize c = (encodeCode c).length := rfl

theorem encodeMove_length_le (m : Move) : (encodeMove m).length ≤ 2 := by
  cases m <;> simp [encodeMove]

theorem encodeOutput_length_le (o : Option Bool) : (encodeOutput o).length ≤ 2 := by
  cases o <;> simp [encodeOutput]

/-- Elementwise length bound for concatenated encodings. -/
theorem encodeListWith_length_le {α : Type*} {enc : α → List Bool} {B : ℕ} :
    ∀ {l : List α}, (∀ a ∈ l, (enc a).length ≤ B) →
      (encodeListWith enc l).length ≤ l.length * B
  | [], _ => by simp
  | a :: l, h => by
    have h1 := h a (by simp)
    have h2 := encodeListWith_length_le (l := l) fun a' h' =>
      h a' (List.mem_cons_of_mem a h')
    have h3 : (l.length + 1) * B = l.length * B + B := Nat.succ_mul l.length B
    simp only [encodeListWith_cons, List.length_append, List.length_cons]
    omega

/-- Length bound for one well-formed table entry. -/
theorem encodeAction_length_le {i : ℕ} (c : Code i) {a : RawAction}
    (ha : a ∈ c.raw.table) :
    (encodeAction a).length ≤
      2 * i + c.raw.workTapeCount * (4 + (encodeNat c.raw.alphabetSize).length) + 3
        + (encodeNat c.raw.stateCount).length := by
  have hmoves : (encodeListWith encodeMove a.inputMoves.toList).length ≤ i * 2 := by
    have h := encodeListWith_length_le (l := a.inputMoves.toList)
      (fun m _ => encodeMove_length_le m)
    simpa [c.wf.inputMoves_size ha] using h
  have hwa : ∀ wa ∈ a.workActions.toList,
      (encodeWorkAction wa).length ≤ 4 + (encodeNat c.raw.alphabetSize).length := by
    intro wa hwa
    rw [Array.mem_toList_iff] at hwa
    have hwrite : (encodeWrite wa.write).length
        ≤ 2 + (encodeNat c.raw.alphabetSize).length := by
      cases hw : wa.write with
      | keep =>
        simp only [encodeWrite, List.length_cons, List.length_nil]
        omega
      | blank =>
        simp only [encodeWrite, List.length_cons, List.length_nil]
        omega
      | symbol s =>
        have hs := c.wf.write_lt ha hwa hw
        have hmono := encodeNat_length_mono (Nat.le_of_lt hs)
        simp only [encodeWrite, List.length_cons]
        omega
    have hmove := encodeMove_length_le wa.move
    simp only [encodeWorkAction, List.length_append]
    omega
  have hworks : (encodeListWith encodeWorkAction a.workActions.toList).length ≤
      c.raw.workTapeCount * (4 + (encodeNat c.raw.alphabetSize).length) := by
    have h := encodeListWith_length_le (l := a.workActions.toList) hwa
    simpa [c.wf.workActions_size ha] using h
  have hout := encodeOutput_length_le a.output
  have hnext : (encodeNextState a.nextState).length ≤
      1 + (encodeNat c.raw.stateCount).length := by
    cases hn : a.nextState with
    | none =>
      simp only [encodeNextState, List.length_cons, List.length_nil]
      omega
    | some q =>
      have hq := c.wf.nextState_lt ha (show q ∈ a.nextState by simp [hn])
      have hmono := encodeNat_length_mono (Nat.le_of_lt hq)
      simp only [encodeNextState, List.length_cons]
      omega
  simp only [encodeAction, List.length_append]
  omega

/-- Explicit size bound: header plus table-count times the per-entry bound. This is the
`|α|` arithmetic that λ-boundedness bookkeeping consumes. -/
theorem codeSize_le {i : ℕ} (c : Code i) :
    codeSize c ≤
      1 + (encodeNat c.raw.workTapeCount).length + (encodeNat c.raw.alphabetSize).length
        + 2 * (encodeNat c.raw.stateCount).length
        + c.raw.stateCount * (c.raw.alphabetSize + 1) ^ (i + c.raw.workTapeCount)
            * (2 * i + c.raw.workTapeCount * (4 + (encodeNat c.raw.alphabetSize).length)
              + 3 + (encodeNat c.raw.stateCount).length) := by
  have htable := encodeListWith_length_le (enc := encodeAction) (l := c.raw.table.toList)
    (fun a ha => encodeAction_length_le c (Array.mem_toList_iff.mp ha))
  have hlen : c.raw.table.toList.length
      = c.raw.stateCount * (c.raw.alphabetSize + 1) ^ (i + c.raw.workTapeCount) := by
    simp [c.wf.table_size]
  rw [hlen] at htable
  have hq0 := encodeNat_length_mono (Nat.le_of_lt c.wf.startState_lt)
  have h0 : (encodeNat 0).length = 1 := by simp [encodeNat_length]
  simp only [codeSize, encodeCode, encodeRawCode, List.length_append]
  omega

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
private def dummyEntry : RawAction :=
  { inputMoves := #[.stay], workActions := #[], output := some false, nextState := none }

/-- Zero states (the empty table has the canonical size `0 · 3¹`, so this parses and is
rejected by the checker alone). -/
private def badZeroStates : RawCode 1 :=
  { workTapeCount := 0, alphabetSize := 2, stateCount := 0, startState := 0, table := #[] }

/-- Alphabet of size one (table of the canonical size `1 · 2¹`). -/
private def badAlphabet : RawCode 1 :=
  { workTapeCount := 0, alphabetSize := 1, stateCount := 1, startState := 0,
    table := #[dummyEntry, dummyEntry] }

/-- Wrong table length: the header demands `1 · 3¹ = 3` entries, only two are present,
so parsing itself fails. -/
private def badTableLength : RawCode 1 :=
  { workTapeCount := 0, alphabetSize := 2, stateCount := 1, startState := 0,
    table := #[dummyEntry, dummyEntry] }

/-- Out-of-range successor state. -/
private def badNextState : RawCode 1 :=
  { workTapeCount := 0, alphabetSize := 2, stateCount := 1, startState := 0,
    table := #[{ inputMoves := #[.stay], workActions := #[], output := none,
                 nextState := some 5 }, dummyEntry, dummyEntry] }

/-- Out-of-range work symbol (one work tape, so `1 · 3² = 9` entries). -/
private def badWorkSymbol : RawCode 1 :=
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

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.TM.Code.Encoding.Nat
import MIPRE.TM.Code.WellFormed

/-!
# Binary serialization of machine codes

The normative description format (`planning/tm-infrastructure.md`, Milestone C):

`encodeCode c = encodeNat 0 (version) · workTapeCount · alphabetSize · stateCount ·
startState · table entries in `transitionIndex` order`

with every natural in the self-delimiting code of `MIPRE.TM.Code.Encoding.Nat`, and per
entry: the `i` input moves (`stay = 0`, `right = 10`, `left = 11`), the `w` work actions
(write `keep = 0`, `blank = 10`, `symbol s = 11·encodeNat s`, then the move), the output
(`none = 0`, `some b = 1·b`), and the successor (`none = 0`, `some q = 1·encodeNat q`).
The arity `i` is external, matching the paper's `[α]_i`.

`decodeCodeExact` parses, demands full consumption, and gates on the executable
well-formedness checker; the three theorems at the end are Milestone C's exact-codec
package: `decodeCodeExact_encodeCode` (round trip), `encodeCode_injective`, and
`decodeCodeExact_sound` (canonicality: every accepted string *is* the canonical encoding
of its parse). Every parser is paired with a prefix lemma and a soundness lemma, so
soundness composes field by field (decision D11); everything is structurally recursive
(decision D10).
-/

namespace Turing

/-! ## Field codecs -/

/-- Encode a head movement: `stay = 0`, `right = 10`, `left = 11`. -/
def encodeMove : Move → List Bool
  | .stay => [false]
  | .right => [true, false]
  | .left => [true, true]

/-- Parse a head movement. -/
def parseMove : List Bool → Option (Move × List Bool)
  | false :: r => some (.stay, r)
  | true :: false :: r => some (.right, r)
  | true :: true :: r => some (.left, r)
  | _ => none

@[simp]
theorem parseMove_encodeMove (m : Move) (rest : List Bool) :
    parseMove (encodeMove m ++ rest) = some (m, rest) := by
  cases m <;> rfl

theorem parseMove_sound : ∀ {s : List Bool} {m : Move} {rest : List Bool},
    parseMove s = some (m, rest) → s = encodeMove m ++ rest
  | [], _, _, h => by simp [parseMove] at h
  | false :: r, _, _, h => by
    simp only [parseMove, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | [true], _, _, h => by simp [parseMove] at h
  | true :: false :: r, _, _, h => by
    simp only [parseMove, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | true :: true :: r, _, _, h => by
    simp only [parseMove, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl

/-- Encode a write action: `keep = 0`, `blank = 10`, `symbol s = 11·encodeNat s`. -/
def encodeWrite : RawWrite → List Bool
  | .keep => [false]
  | .blank => [true, false]
  | .symbol s => true :: true :: encodeNat s

/-- Parse a write action. -/
def parseWrite : List Bool → Option (RawWrite × List Bool)
  | false :: r => some (.keep, r)
  | true :: false :: r => some (.blank, r)
  | true :: true :: r =>
    match parseNat r with
    | some (s, r') => some (.symbol s, r')
    | none => none
  | _ => none

@[simp]
theorem parseWrite_encodeWrite (w : RawWrite) (rest : List Bool) :
    parseWrite (encodeWrite w ++ rest) = some (w, rest) := by
  cases w with
  | keep => rfl
  | blank => rfl
  | symbol s => simp [encodeWrite, parseWrite]

theorem parseWrite_sound : ∀ {s : List Bool} {w : RawWrite} {rest : List Bool},
    parseWrite s = some (w, rest) → s = encodeWrite w ++ rest
  | [], _, _, h => by simp [parseWrite] at h
  | false :: r, _, _, h => by
    simp only [parseWrite, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | [true], _, _, h => by simp [parseWrite] at h
  | true :: false :: r, _, _, h => by
    simp only [parseWrite, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | true :: true :: r, _, _, h => by
    cases hp : parseNat r with
    | none => simp [parseWrite, hp] at h
    | some p =>
      obtain ⟨s', r'⟩ := p
      simp only [parseWrite, hp, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [encodeWrite, List.cons_append, List.cons_append, parseNat_sound hp]

/-- Encode an optional output bit: `none = 0`, `some b = 1·b`. -/
def encodeOutput : Option Bool → List Bool
  | none => [false]
  | some b => [true, b]

/-- Parse an optional output bit. -/
def parseOutput : List Bool → Option (Option Bool × List Bool)
  | false :: r => some (none, r)
  | true :: b :: r => some (some b, r)
  | _ => none

@[simp]
theorem parseOutput_encodeOutput (o : Option Bool) (rest : List Bool) :
    parseOutput (encodeOutput o ++ rest) = some (o, rest) := by
  cases o <;> rfl

theorem parseOutput_sound : ∀ {s : List Bool} {o : Option Bool} {rest : List Bool},
    parseOutput s = some (o, rest) → s = encodeOutput o ++ rest
  | [], _, _, h => by simp [parseOutput] at h
  | false :: r, _, _, h => by
    simp only [parseOutput, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | [true], _, _, h => by simp [parseOutput] at h
  | true :: b :: r, _, _, h => by
    simp only [parseOutput, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl

/-- Encode an optional successor state: `none = 0`, `some q = 1·encodeNat q`. -/
def encodeNextState : Option ℕ → List Bool
  | none => [false]
  | some q => true :: encodeNat q

/-- Parse an optional successor state. -/
def parseNextState : List Bool → Option (Option ℕ × List Bool)
  | false :: r => some (none, r)
  | true :: r =>
    match parseNat r with
    | some (q, r') => some (some q, r')
    | none => none
  | _ => none

@[simp]
theorem parseNextState_encodeNextState (o : Option ℕ) (rest : List Bool) :
    parseNextState (encodeNextState o ++ rest) = some (o, rest) := by
  cases o with
  | none => rfl
  | some q => simp [encodeNextState, parseNextState]

theorem parseNextState_sound : ∀ {s : List Bool} {o : Option ℕ} {rest : List Bool},
    parseNextState s = some (o, rest) → s = encodeNextState o ++ rest
  | [], _, _, h => by simp [parseNextState] at h
  | false :: r, _, _, h => by
    simp only [parseNextState, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | true :: r, _, _, h => by
    cases hp : parseNat r with
    | none => simp [parseNextState, hp] at h
    | some p =>
      obtain ⟨q, r'⟩ := p
      simp only [parseNextState, hp, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [encodeNextState, List.cons_append, parseNat_sound hp]

/-- Encode one work-tape action: the write, then the move. -/
def encodeWorkAction (wa : RawWorkAction) : List Bool :=
  encodeWrite wa.write ++ encodeMove wa.move

/-- Parse one work-tape action. -/
def parseWorkAction (s : List Bool) : Option (RawWorkAction × List Bool) :=
  match parseWrite s with
  | some (wr, s₁) =>
    match parseMove s₁ with
    | some (mv, s₂) => some (⟨wr, mv⟩, s₂)
    | none => none
  | none => none

@[simp]
theorem parseWorkAction_encodeWorkAction (wa : RawWorkAction) (rest : List Bool) :
    parseWorkAction (encodeWorkAction wa ++ rest) = some (wa, rest) := by
  simp [encodeWorkAction, parseWorkAction, List.append_assoc]

theorem parseWorkAction_sound {s : List Bool} {wa : RawWorkAction} {rest : List Bool}
    (h : parseWorkAction s = some (wa, rest)) : s = encodeWorkAction wa ++ rest := by
  cases hw : parseWrite s with
  | none => simp [parseWorkAction, hw] at h
  | some p =>
    obtain ⟨wr, s₁⟩ := p
    cases hm : parseMove s₁ with
    | none => simp [parseWorkAction, hw, hm] at h
    | some q =>
      obtain ⟨mv, s₂⟩ := q
      simp only [parseWorkAction, hw, hm, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [parseWrite_sound hw, parseMove_sound hm, encodeWorkAction]
      simp [List.append_assoc]

/-! ## Fixed-count sequences -/

variable {α : Type*}

/-- Concatenate elementwise encodings; the element count is protocol context (the parser
is told how many to read), not part of the string. -/
def encodeListWith (enc : α → List Bool) (l : List α) : List Bool :=
  l.flatMap enc

@[simp]
theorem encodeListWith_nil (enc : α → List Bool) : encodeListWith enc [] = [] := rfl

@[simp]
theorem encodeListWith_cons (enc : α → List Bool) (a : α) (l : List α) :
    encodeListWith enc (a :: l) = enc a ++ encodeListWith enc l := by
  simp [encodeListWith]

/-- Parse exactly `k` elements. -/
def parseCount (p : List Bool → Option (α × List Bool)) :
    ℕ → List Bool → Option (List α × List Bool)
  | 0, s => some ([], s)
  | k + 1, s =>
    match p s with
    | some (a, s') =>
      match parseCount p k s' with
      | some (l, s'') => some (a :: l, s'')
      | none => none
    | none => none

/-- Prefix property for fixed-count sequences; the elementwise prefix property is only
required on the members of the encoded list. -/
theorem parseCount_encodeListWith {p : List Bool → Option (α × List Bool)}
    {enc : α → List Bool} (l : List α)
    (henc : ∀ a ∈ l, ∀ rest, p (enc a ++ rest) = some (a, rest)) (rest : List Bool) :
    parseCount p l.length (encodeListWith enc l ++ rest) = some (l, rest) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ha := henc a (by simp)
    have hl : ∀ a' ∈ l, ∀ r, p (enc a' ++ r) = some (a', r) := fun a' h' =>
      henc a' (by simp [h'])
    simp only [encodeListWith_cons, List.length_cons, List.append_assoc, parseCount, ha,
      ih hl]

/-- Uniform-codec version of `parseCount_encodeListWith`. -/
theorem parseCount_encodeListWith' {p : List Bool → Option (α × List Bool)}
    {enc : α → List Bool} (henc : ∀ a rest, p (enc a ++ rest) = some (a, rest))
    (l : List α) (rest : List Bool) :
    parseCount p l.length (encodeListWith enc l ++ rest) = some (l, rest) :=
  parseCount_encodeListWith l (fun a _ rest => henc a rest) rest

/-- Soundness for fixed-count sequences. -/
theorem parseCount_sound {p : List Bool → Option (α × List Bool)} {enc : α → List Bool}
    (hp : ∀ {s a rest}, p s = some (a, rest) → s = enc a ++ rest) :
    ∀ {k : ℕ} {s : List Bool} {l : List α} {rest : List Bool},
      parseCount p k s = some (l, rest) →
        s = encodeListWith enc l ++ rest ∧ l.length = k := by
  intro k
  induction k with
  | zero =>
    intro s l rest h
    simp only [parseCount, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | succ k ih =>
    intro s l rest h
    cases hps : p s with
    | none => simp [parseCount, hps] at h
    | some q =>
      obtain ⟨a, s'⟩ := q
      cases hpc : parseCount p k s' with
      | none => simp [parseCount, hps, hpc] at h
      | some r =>
        obtain ⟨l', s''⟩ := r
        simp only [parseCount, hps, hpc, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hs', hlen⟩ := ih hpc
        refine ⟨?_, by simp [hlen]⟩
        rw [hp hps, hs']
        simp [List.append_assoc]

/-! ## Actions -/

/-- Encode one transition-table entry. -/
def encodeAction (a : RawAction) : List Bool :=
  encodeListWith encodeMove a.inputMoves.toList ++
    (encodeListWith encodeWorkAction a.workActions.toList ++
      (encodeOutput a.output ++ encodeNextState a.nextState))

/-- Parse one transition-table entry of an `i`-input, `w`-work-tape machine. -/
def parseAction (i w : ℕ) (s : List Bool) : Option (RawAction × List Bool) :=
  match parseCount parseMove i s with
  | some (mv, s₁) =>
    match parseCount parseWorkAction w s₁ with
    | some (was, s₂) =>
      match parseOutput s₂ with
      | some (out, s₃) =>
        match parseNextState s₃ with
        | some (nx, s₄) => some (⟨mv.toArray, was.toArray, out, nx⟩, s₄)
        | none => none
      | none => none
    | none => none
  | none => none

@[simp]
theorem parseAction_encodeAction {i w : ℕ} (a : RawAction)
    (hmoves : a.inputMoves.size = i) (hworks : a.workActions.size = w)
    (rest : List Bool) :
    parseAction i w (encodeAction a ++ rest) = some (a, rest) := by
  subst hmoves hworks
  rw [← Array.length_toList, ← Array.length_toList]
  simp only [encodeAction, parseAction, List.append_assoc,
    parseCount_encodeListWith' parseMove_encodeMove,
    parseCount_encodeListWith' parseWorkAction_encodeWorkAction,
    parseOutput_encodeOutput, parseNextState_encodeNextState, Array.toArray_toList]

theorem parseAction_sound {i w : ℕ} {s : List Bool} {a : RawAction} {rest : List Bool}
    (h : parseAction i w s = some (a, rest)) :
    s = encodeAction a ++ rest ∧ a.inputMoves.size = i ∧ a.workActions.size = w := by
  cases h₁ : parseCount parseMove i s with
  | none => simp [parseAction, h₁] at h
  | some p₁ =>
    obtain ⟨mv, s₁⟩ := p₁
    cases h₂ : parseCount parseWorkAction w s₁ with
    | none => simp [parseAction, h₁, h₂] at h
    | some p₂ =>
      obtain ⟨was, s₂⟩ := p₂
      cases h₃ : parseOutput s₂ with
      | none => simp [parseAction, h₁, h₂, h₃] at h
      | some p₃ =>
        obtain ⟨out, s₃⟩ := p₃
        cases h₄ : parseNextState s₃ with
        | none => simp [parseAction, h₁, h₂, h₃, h₄] at h
        | some p₄ =>
          obtain ⟨nx, s₄⟩ := p₄
          simp only [parseAction, h₁, h₂, h₃, h₄, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨hs₁, hmv⟩ := parseCount_sound (fun h => parseMove_sound h) h₁
          obtain ⟨hs₂, hwas⟩ := parseCount_sound (fun h => parseWorkAction_sound h) h₂
          have hs₃ := parseOutput_sound h₃
          have hs₄ := parseNextState_sound h₄
          refine ⟨?_, by simpa using hmv, by simpa using hwas⟩
          rw [hs₁, hs₂, hs₃, hs₄, encodeAction]
          simp [List.append_assoc]

/-! ## Machine codes -/

/-- Encode a raw machine description (version `0`, header, dense table in canonical
order). -/
def encodeRawCode {i : ℕ} (c : RawCode i) : List Bool :=
  encodeNat 0 ++
    (encodeNat c.workTapeCount ++
      (encodeNat c.alphabetSize ++
        (encodeNat c.stateCount ++
          (encodeNat c.startState ++ encodeListWith encodeAction c.table.toList))))

/-- The canonical binary description of a machine code — the paper's `α`. -/
def encodeCode {i : ℕ} (c : Code i) : List Bool := encodeRawCode c.raw

/-- Parse a raw machine description: version, header, then exactly the canonical number
of table entries. -/
def parseRawCode (i : ℕ) (s : List Bool) : Option (RawCode i × List Bool) :=
  match parseNat s with
  | some (v, s₀) =>
    if v = 0 then
      match parseNat s₀ with
      | some (w, s₁) =>
        match parseNat s₁ with
        | some (σ, s₂) =>
          match parseNat s₂ with
          | some (Q, s₃) =>
            match parseNat s₃ with
            | some (q₀, s₄) =>
              match parseCount (parseAction i w) (Q * (σ + 1) ^ (i + w)) s₄ with
              | some (entries, s₅) => some (⟨w, σ, Q, q₀, entries.toArray⟩, s₅)
              | none => none
            | none => none
          | none => none
        | none => none
      | none => none
    else none
  | none => none

/-- Exact decoding: parse, demand full consumption, and check well-formedness. -/
def decodeCodeExact (i : ℕ) (s : List Bool) : Option (Code i) :=
  match parseRawCode i s with
  | some (raw, []) =>
    if h : raw.wellFormedB = true then some ⟨raw, RawCode.wellFormedB_iff.mp h⟩
    else none
  | _ => none

/-- Prefix property at the raw level (for well-formed codes, whose entries have the
arities the parser expects). -/
theorem parseRawCode_encodeRawCode {i : ℕ} (c : RawCode i) (hwf : c.WellFormed)
    (rest : List Bool) :
    parseRawCode i (encodeRawCode c ++ rest) = some (c, rest) := by
  have htable : ∀ a ∈ c.table.toList, ∀ r,
      parseAction i c.workTapeCount (encodeAction a ++ r) = some (a, r) := by
    intro a ha r
    rw [Array.mem_toList_iff] at ha
    exact parseAction_encodeAction a (hwf.inputMoves_size ha) (hwf.workActions_size ha) r
  have hcount : c.stateCount * (c.alphabetSize + 1) ^ (i + c.workTapeCount)
      = c.table.toList.length := by
    simp [hwf.table_size]
  simp only [encodeRawCode, parseRawCode, List.append_assoc, parseNat_encodeNat, hcount,
    parseCount_encodeListWith c.table.toList htable, Array.toArray_toList, if_pos]

/-- Soundness at the raw level: every accepted prefix is the canonical encoding. -/
theorem parseRawCode_sound {i : ℕ} {s : List Bool} {c : RawCode i} {rest : List Bool}
    (h : parseRawCode i s = some (c, rest)) : s = encodeRawCode c ++ rest := by
  cases h₀ : parseNat s with
  | none => simp [parseRawCode, h₀] at h
  | some p₀ =>
    obtain ⟨v, s₀⟩ := p₀
    by_cases hv : v = 0
    · subst hv
      cases h₁ : parseNat s₀ with
      | none => simp [parseRawCode, h₀, h₁] at h
      | some p₁ =>
        obtain ⟨w, s₁⟩ := p₁
        cases h₂ : parseNat s₁ with
        | none => simp [parseRawCode, h₀, h₁, h₂] at h
        | some p₂ =>
          obtain ⟨σ, s₂⟩ := p₂
          cases h₃ : parseNat s₂ with
          | none => simp [parseRawCode, h₀, h₁, h₂, h₃] at h
          | some p₃ =>
            obtain ⟨Q, s₃⟩ := p₃
            cases h₄ : parseNat s₃ with
            | none => simp [parseRawCode, h₀, h₁, h₂, h₃, h₄] at h
            | some p₄ =>
              obtain ⟨q₀, s₄⟩ := p₄
              cases h₅ : parseCount (parseAction i w) (Q * (σ + 1) ^ (i + w)) s₄ with
              | none => simp [parseRawCode, h₀, h₁, h₂, h₃, h₄, h₅] at h
              | some p₅ =>
                obtain ⟨entries, s₅⟩ := p₅
                simp only [parseRawCode, h₀, h₁, h₂, h₃, h₄, h₅, if_pos,
                  Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                obtain ⟨hs₄, -⟩ :=
                  parseCount_sound (fun h => (parseAction_sound h).1) h₅
                rw [parseNat_sound h₀, parseNat_sound h₁, parseNat_sound h₂,
                  parseNat_sound h₃, parseNat_sound h₄, hs₄, encodeRawCode]
                simp [List.append_assoc]
    · simp [parseRawCode, h₀, hv] at h

/-- Round trip: exact decoding inverts encoding. -/
@[simp]
theorem decodeCodeExact_encodeCode {i : ℕ} (c : Code i) :
    decodeCodeExact i (encodeCode c) = some c := by
  have h := parseRawCode_encodeRawCode c.raw c.wf []
  rw [List.append_nil] at h
  simp only [decodeCodeExact, encodeCode, h]
  rw [dif_pos (RawCode.wellFormedB_iff.mpr c.wf)]

/-- Canonicality: every accepted description is exactly the canonical encoding of the
code it parses to. -/
theorem decodeCodeExact_sound {i : ℕ} {s : List Bool} {c : Code i}
    (h : decodeCodeExact i s = some c) : encodeCode c = s := by
  cases hp : parseRawCode i s with
  | none => simp [decodeCodeExact, hp] at h
  | some p =>
    obtain ⟨raw, r⟩ := p
    cases r with
    | cons b r' => simp [decodeCodeExact, hp] at h
    | nil =>
      simp only [decodeCodeExact, hp] at h
      by_cases hwf : raw.wellFormedB = true
      · rw [dif_pos hwf] at h
        obtain rfl : (⟨raw, RawCode.wellFormedB_iff.mp hwf⟩ : Code i) = c := by
          simpa using h
        have hs := parseRawCode_sound hp
        rw [List.append_nil] at hs
        exact hs.symm
      · rw [dif_neg hwf] at h
        exact absurd h (by simp)

/-- Canonical descriptions are unique. -/
theorem encodeCode_injective {i : ℕ} : Function.Injective (encodeCode (i := i)) := by
  intro a b hab
  have ha := decodeCodeExact_encodeCode a
  rw [hab, decodeCodeExact_encodeCode] at ha
  simpa using ha.symm

end Turing

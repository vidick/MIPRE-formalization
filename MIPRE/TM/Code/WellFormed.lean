/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.TM.Code.Raw
import MIPRE.TM.Code.Observation

/-!
# Well-formed machine codes

`RawCode.WellFormed` pins down when a raw description denotes a machine: alphabet of size
at least two (symbols `0`/`1` are the I/O bits), a nonempty state set containing the start
state, a dense transition table of exactly the canonical size
`stateCount * (alphabetSize + 1) ^ (i + workTapeCount)` (`Turing.transitionIndex`), and
per-entry arity and range constraints.

The predicate comes with an executable checker `RawCode.wellFormedB` and the equivalence
`RawCode.wellFormedB_iff` (decision D3 of `planning/tm-infrastructure.md`); through it,
`WellFormed` is decidable, so concrete literals can be certified by `decide`. The
Milestone C parser will run the same checker.

`Code i` bundles a raw code with its well-formedness proof; by proof irrelevance it is
just as first-order as `RawCode i` (`Code.ext`, `DecidableEq`). `Code.actionAt` is the
canonical table lookup, and the `Code.actionAt_*` lemmas expose the well-formedness facts
about the entry it returns — every later consumer of table entries (the interpretation of
Milestone B, the serialization of Milestone C, the universal machine of Milestones E–G)
goes through this single, dependency-free access point.
-/

namespace Turing

variable {i : ℕ}

/-! ## The well-formedness predicate -/

/-- Executable check that a write action only writes symbols below the alphabet size. -/
def RawWrite.checkB : RawWrite → ℕ → Bool
  | .symbol s, σ => decide (s < σ)
  | _, _ => true

theorem RawWrite.checkB_eq_true_iff {w : RawWrite} {σ : ℕ} :
    w.checkB σ = true ↔ ∀ s, w = .symbol s → s < σ := by
  cases w <;> simp [checkB]

/-- Executable check that a successor state, if any, is below the state count. -/
def nextStateCheckB (Q : ℕ) : Option ℕ → Bool
  | none => true
  | some q => decide (q < Q)

theorem nextStateCheckB_eq_true_iff {Q : ℕ} {o : Option ℕ} :
    nextStateCheckB Q o = true ↔ ∀ q ∈ o, q < Q := by
  cases o <;> simp [nextStateCheckB]

/-- A raw code denotes a machine: the alphabet has at least the two I/O symbols, there is
at least one state, the start state is in range, the transition table has exactly the
canonical dense size, and every entry has the right arities and only in-range symbols and
successor states. -/
def RawCode.WellFormed (c : RawCode i) : Prop :=
  2 ≤ c.alphabetSize ∧
  0 < c.stateCount ∧
  c.startState < c.stateCount ∧
  c.table.size = c.stateCount * (c.alphabetSize + 1) ^ (i + c.workTapeCount) ∧
  ∀ a ∈ c.table,
    a.inputMoves.size = i ∧
    a.workActions.size = c.workTapeCount ∧
    (∀ wa ∈ a.workActions, ∀ s, wa.write = .symbol s → s < c.alphabetSize) ∧
    ∀ q ∈ a.nextState, q < c.stateCount

/-- The executable well-formedness checker; `RawCode.wellFormedB_iff` proves it decides
`RawCode.WellFormed`. The Milestone C parser accepts exactly the descriptions passing this
check. -/
def RawCode.wellFormedB (c : RawCode i) : Bool :=
  decide (2 ≤ c.alphabetSize) &&
  (decide (0 < c.stateCount) &&
  (decide (c.startState < c.stateCount) &&
  (decide (c.table.size = c.stateCount * (c.alphabetSize + 1) ^ (i + c.workTapeCount)) &&
  c.table.all fun a =>
    decide (a.inputMoves.size = i) &&
    (decide (a.workActions.size = c.workTapeCount) &&
    ((a.workActions.all fun wa => wa.write.checkB c.alphabetSize) &&
    nextStateCheckB c.stateCount a.nextState)))))

/-- The executable checker decides well-formedness. -/
theorem RawCode.wellFormedB_iff {c : RawCode i} : c.wellFormedB = true ↔ c.WellFormed := by
  unfold wellFormedB WellFormed
  simp only [Bool.and_eq_true, decide_eq_true_eq, Array.all_eq_true',
    RawWrite.checkB_eq_true_iff, nextStateCheckB_eq_true_iff]

instance : DecidablePred (RawCode.WellFormed (i := i)) := fun c =>
  decidable_of_iff (c.wellFormedB = true) RawCode.wellFormedB_iff

/-! ## Named accessors for the conjuncts -/

namespace RawCode.WellFormed

variable {c : RawCode i} {a : RawAction}

theorem two_le_alphabetSize (h : c.WellFormed) : 2 ≤ c.alphabetSize := h.1

theorem stateCount_pos (h : c.WellFormed) : 0 < c.stateCount := h.2.1

theorem startState_lt (h : c.WellFormed) : c.startState < c.stateCount := h.2.2.1

theorem table_size (h : c.WellFormed) :
    c.table.size = c.stateCount * (c.alphabetSize + 1) ^ (i + c.workTapeCount) :=
  h.2.2.2.1

theorem inputMoves_size (h : c.WellFormed) (ha : a ∈ c.table) : a.inputMoves.size = i :=
  (h.2.2.2.2 a ha).1

theorem workActions_size (h : c.WellFormed) (ha : a ∈ c.table) :
    a.workActions.size = c.workTapeCount :=
  (h.2.2.2.2 a ha).2.1

theorem write_lt (h : c.WellFormed) (ha : a ∈ c.table) {wa : RawWorkAction}
    (hwa : wa ∈ a.workActions) {s : ℕ} (hs : wa.write = .symbol s) : s < c.alphabetSize :=
  (h.2.2.2.2 a ha).2.2.1 wa hwa s hs

theorem nextState_lt (h : c.WellFormed) (ha : a ∈ c.table) {q : ℕ}
    (hq : q ∈ a.nextState) : q < c.stateCount :=
  (h.2.2.2.2 a ha).2.2.2 q hq

end RawCode.WellFormed

/-! ## The type of well-formed codes -/

/-- A well-formed machine code: a raw description together with its well-formedness
proof. By proof irrelevance, `Code i` is as first-order as `RawCode i` itself. -/
structure Code (i : ℕ) : Type where
  /-- The underlying raw description. -/
  raw : RawCode i
  /-- The well-formedness certificate. -/
  wf : raw.WellFormed

/-- Codes with equal raw descriptions are equal (proof irrelevance). -/
@[ext]
theorem Code.ext : ∀ {c₁ c₂ : Code i}, c₁.raw = c₂.raw → c₁ = c₂
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

instance : DecidableEq (Code i) := fun c₁ c₂ =>
  decidable_of_iff (c₁.raw = c₂.raw) ⟨Code.ext, fun h => h ▸ rfl⟩

namespace Code

/-- The number of work tapes of a coded machine. -/
abbrev workTapeCount (c : Code i) : ℕ := c.raw.workTapeCount

/-- The alphabet size of a coded machine (at least `2`). -/
abbrev alphabetSize (c : Code i) : ℕ := c.raw.alphabetSize

/-- The number of states of a coded machine (at least `1`). -/
abbrev stateCount (c : Code i) : ℕ := c.raw.stateCount

/-- The start state of a coded machine (in range by well-formedness). -/
abbrev startState (c : Code i) : ℕ := c.raw.startState

/-- The canonical table lookup: the entry of the dense transition table at the normative
position `transitionIndex q as bs`. All later consumers of table entries go through this
single access point. -/
def actionAt (c : Code i) (q : Fin c.stateCount)
    (as : Fin i → Option (Fin c.alphabetSize))
    (bs : Fin c.workTapeCount → Option (Fin c.alphabetSize)) : RawAction :=
  c.raw.table[(transitionIndex q as bs).val]'(by
    rw [c.wf.table_size]
    exact (transitionIndex q as bs).isLt)

variable {c : Code i} {q : Fin c.stateCount} {as : Fin i → Option (Fin c.alphabetSize)}
  {bs : Fin c.workTapeCount → Option (Fin c.alphabetSize)}

theorem actionAt_mem (c : Code i) (q : Fin c.stateCount)
    (as : Fin i → Option (Fin c.alphabetSize))
    (bs : Fin c.workTapeCount → Option (Fin c.alphabetSize)) :
    c.actionAt q as bs ∈ c.raw.table :=
  Array.getElem_mem _

theorem actionAt_inputMoves_size : (c.actionAt q as bs).inputMoves.size = i :=
  c.wf.inputMoves_size (c.actionAt_mem q as bs)

theorem actionAt_workActions_size :
    (c.actionAt q as bs).workActions.size = c.workTapeCount :=
  c.wf.workActions_size (c.actionAt_mem q as bs)

theorem actionAt_write_lt {wa : RawWorkAction}
    (hwa : wa ∈ (c.actionAt q as bs).workActions) {s : ℕ} (hs : wa.write = .symbol s) :
    s < c.alphabetSize :=
  c.wf.write_lt (c.actionAt_mem q as bs) hwa hs

theorem actionAt_nextState_lt {q' : ℕ} (hq' : q' ∈ (c.actionAt q as bs).nextState) :
    q' < c.stateCount :=
  c.wf.nextState_lt (c.actionAt_mem q as bs) hq'

end Code

end Turing

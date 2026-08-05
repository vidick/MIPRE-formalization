/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import Mathlib.Data.Sign.Defs

/-!
# Raw syntax for coded multi-input Turing machines

First-order, serializable machine descriptions: plain data with no embedded functions, no
well-formedness requirements, and derivable decidable equality. A `RawCode i` describes a
multi-input machine (`MIPRE.TM.MultiInput.Deterministic`) with `i` input tapes through a
*dense* transition table: one `RawAction` per observation
(state, input symbols, work symbols), stored in the canonical order fixed by
`Turing.transitionIndex` (`MIPRE.TM.Code.Observation`).

Well-formedness is a separate predicate (`MIPRE.TM.Code.WellFormed`), and only well-formed
codes are interpreted as machines (`MIPRE.TM.Code.Semantics`). This "machine code first"
layering is what later makes descriptions serializable, measurable (`|𝒟|`) and usable for
self-reference; see `planning/tm-infrastructure.md` (Milestone B).

## Input/output conventions

* The alphabet of a coded machine is `Fin alphabetSize` with `alphabetSize ≥ 2` (enforced
  by well-formedness). Symbols `0` and `1` are reserved for binary input and output;
  symbols `≥ 2` may be used freely on the work tapes.
* A transition's `output` field is an `Option Bool`, not an optional symbol: coded
  machines emit *bits*, so decoding their output is total, while the internal alphabet may
  be larger.
* States are `Fin stateCount`; `nextState = none` halts the machine.
-/

namespace Turing

/-- A head movement of a coded machine. -/
inductive Move : Type
  /-- Move the head one cell to the left. -/
  | left
  /-- Do not move the head. -/
  | stay
  /-- Move the head one cell to the right. -/
  | right
deriving DecidableEq, Repr

/-- Interpret a `Move` as the `SignType` movement used by the operational model. -/
def Move.toSignType : Move → SignType
  | .left => .neg
  | .stay => .zero
  | .right => .pos

/-- What a coded machine writes on a work tape in one step: nothing (`keep`), the blank
symbol (`blank`), or the alphabet symbol `a` (`symbol a`; well-formedness bounds `a` by
the alphabet size). -/
inductive RawWrite : Type
  /-- Leave the cell unchanged. -/
  | keep
  /-- Write the blank symbol. -/
  | blank
  /-- Write the alphabet symbol `a`. -/
  | symbol (a : ℕ)
deriving DecidableEq, Repr

/-- The action of a coded machine on one work tape: what to write, and how to move. -/
structure RawWorkAction : Type where
  /-- What to write on the cell under the head. -/
  write : RawWrite
  /-- How to move the head. -/
  move : Move
deriving DecidableEq, Repr

/-- One entry of a transition table: the action taken on one observation. The arity and
work-tape count are not parameters of this type — well-formedness constrains
`inputMoves.size` and `workActions.size` (see `planning/tm-infrastructure.md`, decision
D2). -/
structure RawAction : Type where
  /-- The movement of each input head, in ascending tape order. -/
  inputMoves : Array Move
  /-- The action on each work tape, in ascending tape order. -/
  workActions : Array RawWorkAction
  /-- The optionally emitted output bit. -/
  output : Option Bool
  /-- The successor state, or `none` to halt. -/
  nextState : Option ℕ
deriving DecidableEq, Repr

/-- A raw description of an `i`-input machine: header data and a dense transition table in
the canonical observation order (`Turing.transitionIndex`). No well-formedness is imposed
here; see `RawCode.WellFormed`. -/
structure RawCode (i : ℕ) : Type where
  /-- The number of work tapes. -/
  workTapeCount : ℕ
  /-- The alphabet size (well-formedness requires `≥ 2`; symbols `0`/`1` are the I/O
  bits). -/
  alphabetSize : ℕ
  /-- The number of states. -/
  stateCount : ℕ
  /-- The initial state (well-formedness requires it to be `< stateCount`). -/
  startState : ℕ
  /-- The dense transition table: entry `transitionIndex q as bs` is the action taken on
  observation `(q, as, bs)`. Well-formedness requires size
  `stateCount * (alphabetSize + 1) ^ (i + workTapeCount)`. -/
  table : Array RawAction
deriving DecidableEq, Repr

end Turing

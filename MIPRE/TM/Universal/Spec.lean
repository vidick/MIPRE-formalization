/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.TM.Code.Encoding.Total
import MIPRE.TM.Code.Evaluator
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# The machine-level universal simulation theorems (specification)

The target interface of the machine-level programme (Milestones E–G of
`planning/tm-infrastructure.md`), frozen here as `sorry`-ed theorems so that later work
can be planned and verified against a fixed specification, independently of the open
interpreter-ownership decision (plan document, roadmap gate).

* `Turing.exists_universalCode` — blueprint `lem:universal-machine`, tracked by
  issue #17: a machine code `U` with `i + 1` input tapes simulating `[α]_i` on the
  remaining tapes, exactly (produces-iff) and with polynomial time and space overhead
  in `|α| + t`.
* `Turing.exists_boundedUniversalCode` — blueprint `lem:bounded-universal-machine`,
  tracked by issue #18: the budgeted variant, always halting within `P(|α| + T)` and
  outputting the canonically encoded budgeted result. This is the variant the
  pipeline-style uses (timeout simulation, bounded interpretation) need first.

Both statements are **existential** (`∃ U : Code _, …`), mirroring how
`MIPRE/Foundations/Cost/Toolkit.lean` states its ambient-model counterparts
(blueprint `lem:universal-tm`): a `sorry`-ed `def universalCode` would be poisoned data
— every consumer would inherit `sorryAx` and nothing could compute with it — so the
concrete definition, with its `#eval`-able canonical description, only arrives with the
construction in Milestone F. The specification vocabulary is entirely that of
Milestones C and D: total decoding `decodeCode`, the relational semantics
`Code.Produces`, and the budgeted evaluator `Code.evalWithin`.

`encodeBoundedResult` (the output format of the bounded machine) is the one *defined*
object here — computable, `sorry`-free — completing the Milestone F output interface
deferred from `Code/Evaluator.lean` (decision D12).
-/

namespace Turing

/-- The canonical bit encoding of a budgeted result — the output format of the bounded
universal machine: `timeout ↦ 0`, `halted y ↦ 1 · encodeNat |y| · y`. -/
def encodeBoundedResult : Code.BoundedResult → List Bool
  | .timeout => [false]
  | .halted y => true :: (encodeNat y.length ++ y)

/-- **Universal machine** (blueprint `lem:universal-machine`; specification for
Milestones E–G, tracked by issue #17).

There are a machine code `U` with `i + 1` input tapes and a polynomial `P` such that,
with a description `α` on the first input tape and source inputs `x` on the others:

* `U` produces `y` exactly when the decoded machine `[α]_i` produces `y` on `x`
  (in particular, `U` halts exactly when `[α]_i` does), and
* whenever `[α]_i` halts within `t` steps, `U` halts within `P(|α| + t)` time and
  space. -/
theorem exists_universalCode (i : ℕ) :
    ∃ (U : Code (i + 1)) (P : Polynomial ℕ),
      (∀ (α : List Bool) (x : Fin i → List Bool) (y : List Bool),
        U.Produces (Fin.cons α x) y ↔ (decodeCode i α).Produces x y) ∧
      ∀ (α : List Bool) (x : Fin i → List Bool) (y : List Bool) (t s : ℕ),
        (decodeCode i α).toTM.ComputesInTimeAndSpace ((decodeCode i α).bitInputs x)
          (y.map fun b => (decodeCode i α).bitEmbedding b) t s →
        ∃ t' s',
          U.toTM.ComputesInTimeAndSpace (U.bitInputs (Fin.cons α x))
            (y.map fun b => U.bitEmbedding b) t' s' ∧
          t' ≤ P.eval (α.length + t) ∧ s' ≤ P.eval (α.length + t) := by
  sorry -- blueprint `lem:universal-machine`; issue #17 (Milestones E–G)

/-- **Bounded universal machine** (blueprint `lem:bounded-universal-machine`;
specification for Milestones E–G, tracked by issue #18).

There are a machine code `U` with `i + 2` input tapes and a polynomial `P` such that,
with a description `α` on the first input tape, a budget `T` in binary on the second,
and source inputs `x` on the others, `U` *always* halts, within `P(|α| + T)` steps,
outputting the canonical encoding of the budgeted evaluation of `[α]_i` on `x` with
budget `T`. -/
theorem exists_boundedUniversalCode (i : ℕ) :
    ∃ (U : Code (i + 2)) (P : Polynomial ℕ),
      ∀ (α : List Bool) (T : ℕ) (x : Fin i → List Bool),
        ∃ t s,
          U.toTM.ComputesInTimeAndSpace
            (U.bitInputs (Fin.cons α (Fin.cons (encodeNat T) x)))
            ((encodeBoundedResult ((decodeCode i α).evalWithin x T)).map
              fun b => U.bitEmbedding b) t s ∧
          t ≤ P.eval (α.length + T) := by
  sorry -- blueprint `lem:bounded-universal-machine`; issue #18 (Milestones E–G)

#eval encodeBoundedResult (Code.BoundedResult.halted [true])
#eval encodeBoundedResult Code.BoundedResult.timeout

end Turing

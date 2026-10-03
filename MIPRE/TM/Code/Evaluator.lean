/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.TM.Code.Examples
public meta import MIPRE.TM.Code.Examples

@[expose] public section

-- Lean v4.33's transparency check breaks several `rw`/`simp` steps in this file
-- (the same failure Mathlib patches with this option on affected declarations).
set_option backward.isDefEq.respectTransparency false

/-!
# The reference evaluator for coded machines

Milestone D (`planning/tm-infrastructure.md`): the specification-side evaluator against
which the universal machine (Milestones E–G) will be verified, independent of its
eventual construction language. Everything is definitional over `Code.toTM` — this file
re-implements nothing:

* `Code.runFor` — the configuration after `t` steps on bit inputs;
* `Code.outputFor` — the decoded bit output after `t` steps;
* `Code.evalWithin` — total, executable, budgeted evaluation (`Code.BoundedResult`);
* `Code.Produces` — the relational input/output semantics.

The three views agree (decision D12): `evalWithin_eq_halted_iff` and
`evalWithin_eq_timeout_iff` characterize the budgeted evaluator by configurations,
`evalWithin_halted_mono` makes budgeted results stable, and
`produces_iff_exists_evalWithin` ties the relational semantics to the executable one —
via the bit-level bridge `outputString_isBit`/`map_bitEmbedding_decodeBitOutput` (coded
machines only ever emit the two reserved bit symbols, so decoding loses nothing).
`Produces.unique` records that outputs are deterministic.

The `BoundedResult` bit codec is deliberately deferred to the Milestone F interface.
-/

namespace Turing.Code

variable {i : ℕ}

/-! ## The step-indexed run -/

/-- The configuration reached by the coded machine `c` on bit inputs `x` after `t`
steps. -/
def runFor (c : Code i) (x : Fin i → List Bool) (t : ℕ) :
    MultiInputTM.Cfg i c.workTapeCount c.Symbol c.State (c.bitInputs x) :=
  c.toTM.configs (c.toTM.initCfg (c.bitInputs x)) t

/-- The bits emitted by `c` on bit inputs `x` during the first `t` steps. -/
def outputFor (c : Code i) (x : Fin i → List Bool) (t : ℕ) : List Bool :=
  c.decodeBitOutput (c.toTM.outputString (c.toTM.initCfg (c.bitInputs x)) t)

@[simp]
theorem runFor_zero (c : Code i) (x : Fin i → List Bool) :
    c.runFor x 0 = c.toTM.initCfg (c.bitInputs x) := by
  simp [runFor]

theorem runFor_succ (c : Code i) (x : Fin i → List Bool) (t : ℕ) :
    c.runFor x (t + 1) = c.toTM.step (c.runFor x t) :=
  MultiInputTM.configs_succ_eq_step'

@[simp]
theorem outputFor_zero (c : Code i) (x : Fin i → List Bool) : c.outputFor x 0 = [] := by
  simp [outputFor, MultiInputTM.outputString, decodeBitOutput]

theorem outputFor_succ (c : Code i) (x : Fin i → List Bool) (t : ℕ) :
    c.outputFor x (t + 1) =
      c.outputFor x t ++ c.decodeBitOutput (c.toTM.outputSymbol (c.runFor x t)).toList := by
  simp [outputFor, runFor, MultiInputTM.outputString_succ, decodeBitOutput]

/-! ## Budgeted evaluation -/

/-- The result of running a coded machine under a step budget. Its canonical bit codec
is deferred to the universal-machine interface (Milestone F). -/
inductive BoundedResult : Type
  /-- The machine was still running when the budget ran out. -/
  | timeout
  /-- The machine halted within the budget, with the given output bits. -/
  | halted (output : List Bool)
deriving DecidableEq, Repr

/-- Budgeted evaluation: run for `T` steps; report the output if the machine has halted
by then, and `timeout` otherwise. Total and executable. -/
def evalWithin (c : Code i) (x : Fin i → List Bool) (T : ℕ) : BoundedResult :=
  if (c.runFor x T).state.isNone then .halted (c.outputFor x T) else .timeout

/-! ## The relational semantics -/

/-- The relational input/output semantics: `c` on bit inputs `x` halts with output bits
`y`, in some time and space. -/
def Produces (c : Code i) (x : Fin i → List Bool) (y : List Bool) : Prop :=
  ∃ t s, c.toTM.ComputesInTimeAndSpace (c.bitInputs x)
    (y.map fun b => c.bitEmbedding b) t s

/-! ## The bit-level bridge -/

@[simp]
theorem bitEmbedding_val_beq_one (c : Code i) (b : Bool) :
    ((c.bitEmbedding b).val == 1) = b := by
  cases b <;> simp [bitEmbedding]

@[simp]
theorem decodeBitOutput_nil (c : Code i) : c.decodeBitOutput [] = [] := rfl

@[simp]
theorem decodeBitOutput_cons (c : Code i) (s : c.Symbol) (l : List c.Symbol) :
    c.decodeBitOutput (s :: l) = (s.val == 1) :: c.decodeBitOutput l := rfl

/-! ## Executable pins (Milestone B machines) -/

example : Code.copyBit.evalWithin (fun _ => [true]) 2 = .halted [true] := by decide
example : Code.copyBit.evalWithin (fun _ => [false]) 2 = .halted [false] := by decide
example : Code.copyBit.evalWithin (fun _ => [true]) 0 = .timeout := by decide
example : (Code.defaultRejectCode 1).evalWithin (fun _ => [true]) 1 = .halted [false] := by
  decide
example : Code.workTapeRoundTrip.evalWithin (fun _ => [true]) 3 = .halted [true] := by
  decide
example : Code.workTapeRoundTrip.evalWithin (fun _ => [true]) 2 = .timeout := by decide
set_option maxRecDepth 4000 in
example : Code.loopForever.evalWithin (fun _ => [true]) 100 = .timeout := by decide

#eval Code.copyBit.evalWithin (fun _ => [true]) 2       -- halted [true]
#eval Code.workTapeRoundTrip.evalWithin (fun _ => [true]) 5

end Turing.Code

end

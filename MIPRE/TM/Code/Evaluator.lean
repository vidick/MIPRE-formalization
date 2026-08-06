/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.TM.Code.Examples

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

theorem runFor_add (c : Code i) (x : Fin i → List Bool) (a b : ℕ) :
    c.runFor x (a + b) = c.toTM.configs (c.runFor x a) b :=
  MultiInputTM.configs_add _ a b

/-- Once halted, the run is frozen. -/
theorem runFor_of_halt {c : Code i} {x : Fin i → List Bool} {t : ℕ}
    (h : (c.runFor x t).state = none) (d : ℕ) :
    c.runFor x (t + d) = c.runFor x t := by
  rw [runFor_add, MultiInputTM.configs_of_halts _ h]

@[simp]
theorem outputFor_zero (c : Code i) (x : Fin i → List Bool) : c.outputFor x 0 = [] := by
  simp [outputFor, MultiInputTM.outputString, decodeBitOutput]

theorem outputFor_succ (c : Code i) (x : Fin i → List Bool) (t : ℕ) :
    c.outputFor x (t + 1) =
      c.outputFor x t ++ c.decodeBitOutput (c.toTM.outputSymbol (c.runFor x t)).toList := by
  simp [outputFor, runFor, MultiInputTM.outputString_succ, decodeBitOutput]

/-- The output is frozen once the machine has halted. -/
theorem outputFor_of_halt {c : Code i} {x : Fin i → List Bool} {t t' : ℕ} (hle : t ≤ t')
    (h : (c.runFor x t).state = none) :
    c.outputFor x t' = c.outputFor x t := by
  unfold outputFor
  rw [MultiInputTM.outputString_eq_of_halt _ _ hle h]

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

theorem evalWithin_eq_halted_iff {c : Code i} {x : Fin i → List Bool} {T : ℕ}
    {y : List Bool} :
    c.evalWithin x T = .halted y ↔ (c.runFor x T).state = none ∧ c.outputFor x T = y := by
  rcases hst : (c.runFor x T).state with _ | q <;> simp [evalWithin, hst]

theorem evalWithin_eq_timeout_iff {c : Code i} {x : Fin i → List Bool} {T : ℕ} :
    c.evalWithin x T = .timeout ↔ ¬(c.runFor x T).state = none := by
  rcases hst : (c.runFor x T).state with _ | q <;> simp [evalWithin, hst]

/-- Budgeted results are stable under enlarging the budget. -/
theorem evalWithin_halted_mono {c : Code i} {x : Fin i → List Bool} {T T' : ℕ}
    {y : List Bool} (hle : T ≤ T') (h : c.evalWithin x T = .halted y) :
    c.evalWithin x T' = .halted y := by
  rw [evalWithin_eq_halted_iff] at h ⊢
  obtain ⟨hhalt, hout⟩ := h
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  refine ⟨?_, ?_⟩
  · rw [runFor_of_halt hhalt]
    exact hhalt
  · rw [outputFor_of_halt (Nat.le_add_right T d) hhalt]
    exact hout

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

/-- Coded machines only ever emit the two reserved bit symbols. -/
theorem outputString_isBit (c : Code i) {input : Fin i → List c.Symbol}
    (cfg : MultiInputTM.Cfg i c.workTapeCount c.Symbol c.State input) (t : ℕ) :
    ∀ s ∈ c.toTM.outputString cfg t, ∃ b, s = c.bitEmbedding b := by
  induction t with
  | zero => simp [MultiInputTM.outputString]
  | succ t ih =>
    rw [MultiInputTM.outputString_succ]
    intro s hs
    rw [List.mem_append] at hs
    rcases hs with hs | hs
    · exact ih s hs
    · rcases c.outputSymbol_isBit (c.toTM.configs cfg t) with hnone | ⟨b, hb⟩
      · rw [hnone] at hs
        simp at hs
      · rw [hb] at hs
        simp only [Option.toList_some, List.mem_singleton] at hs
        exact ⟨b, hs⟩

/-- Decoding is a section on strings of bit symbols. -/
theorem map_bitEmbedding_decodeBitOutput (c : Code i) {l : List c.Symbol}
    (h : ∀ s ∈ l, ∃ b, s = c.bitEmbedding b) :
    (c.decodeBitOutput l).map (fun b => c.bitEmbedding b) = l := by
  induction l with
  | nil => simp
  | cons s l ih =>
    obtain ⟨b, rfl⟩ := h s (by simp)
    have ihl := ih fun s' hs' => h s' (by simp [hs'])
    rw [decodeBitOutput_cons, List.map_cons, bitEmbedding_val_beq_one, ihl]

/-- The relational and the budgeted views agree: `c` produces `y` exactly when some
budget suffices to observe it. -/
theorem produces_iff_exists_evalWithin (c : Code i) (x : Fin i → List Bool)
    (y : List Bool) :
    c.Produces x y ↔ ∃ T, c.evalWithin x T = .halted y := by
  constructor
  · rintro ⟨t, s, hhalt, hout, -⟩
    refine ⟨t, evalWithin_eq_halted_iff.mpr ⟨hhalt, ?_⟩⟩
    unfold outputFor
    rw [hout, decodeBitOutput_map_bitEmbedding]
  · rintro ⟨T, h⟩
    rw [evalWithin_eq_halted_iff] at h
    obtain ⟨hhalt, hout⟩ := h
    refine ⟨T, c.toTM.spaceUsed (c.toTM.initCfg (c.bitInputs x)) T, hhalt, ?_, rfl⟩
    rw [← hout]
    exact (map_bitEmbedding_decodeBitOutput c
      (outputString_isBit c (c.toTM.initCfg (c.bitInputs x)) T)).symm

/-- Outputs are deterministic. -/
theorem Produces.unique {c : Code i} {x : Fin i → List Bool} {y y' : List Bool}
    (h : c.Produces x y) (h' : c.Produces x y') : y = y' := by
  rw [produces_iff_exists_evalWithin] at h h'
  obtain ⟨T, hT⟩ := h
  obtain ⟨T', hT'⟩ := h'
  rcases Nat.le_total T T' with hle | hle
  · have h2 := (evalWithin_halted_mono hle hT).symm.trans hT'
    simpa using h2
  · have h2 := (evalWithin_halted_mono hle hT').symm.trans hT
    simpa using h2.symm

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

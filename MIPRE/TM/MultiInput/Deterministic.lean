/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Cslib.Computability.Machines.Turing.MultiTape.Deterministic

/-!
# Deterministic multi-input multi-tape Turing machines

Defines deterministic Turing machines with `i` two-way read-only input tapes, `w` work
tapes and one write-only output tape — the machine model of MIP* = RE's normal form
verifiers (a decider is a 5-input Turing machine; blueprint `def:decider`).

This file generalizes the vendored CSLib development
(`MIPRE.Cslib.Computability.Machines.Turing.MultiTape.Deterministic`, upstream
`Turing.MultiTapeTM`) from one input tape to `i` of them, declaration for declaration and
under the same names; `Turing.MultiTapeTM` is exactly the case `i = 1` (the exact
correspondence is proved in `MIPRE.TM.MultiInput.OneInputEquiv`). All conventions are
inherited:

* tape symbols are `Option Symbol`, with `none` the blank symbol;
* each input head moves freely on its own input, clamped one cell beyond either end
  (`Turing.moveInputPos` is reused unchanged, one input tape at a time);
* the transition can optionally write and move on every work tape, and optionally emit one
  output symbol;
* halting is the absent successor state (`none`), and halted configurations are fixed
  points of `step`;
* space usage counts the work-tape cells visited by the heads; the input and output tapes
  are ignored for space.

Native multiple input tapes (rather than packing several inputs onto one tape by
concatenation) keep the paper's per-input time bounds honest: accessing one input never
costs time proportional to the lengths of the others. See
`planning/tm-infrastructure.md` (Milestone A) for the design record.

## Important declarations

* `MultiInputTM`: the machine
* `MultiInputTM.Cfg`: configurations, relative to the tuple of inputs
* `MultiInputTM.step`, `MultiInputTM.configs`: one step, and the step-indexed run
* `MultiInputTM.outputString`: the output emitted during the first `t` steps
* `MultiInputTM.spaceUsed`: the number of work-tape cells visited up to a step
* `MultiInputTM.TransitionRelation`: the relational view of `step`, tied to the iterated
  view by `relatesInSteps_iff_configs_eq`
* `MultiInputTM.haltsAtStep`, `MultiInputTM.halting_step_unique`: the exact halting step

The resource-bound packaging (`ComputesInTimeAndSpace`, `ComputesFunWithBounds`) is in
`MIPRE.TM.MultiInput.Complexity`.
-/

namespace Turing

open Relation

variable {i w : ℕ} {State Symbol : Type*}

/-- The output of the transition function of a multi-input Turing machine. -/
@[ext]
structure MultiInputTM.TransitionOut (i w : ℕ) (Symbol State : Type*) where
  /-- The movement (attempt) of each input head. -/
  inputMoves : Fin i → SignType
  /-- Actions on the work tapes: optionally a symbol to write and the head movement. -/
  workActions : Fin w → (Option (Option Symbol)) × SignType
  /-- An optional symbol to output. -/
  outS : Option Symbol
  /-- The successor state or `none` to halt. -/
  q' : Option State

/--
A deterministic Turing machine with `i` two-way read-only input tapes and `w` work tapes
over the alphabet `Option Symbol` (where `none` is the blank symbol). Note that it is not
required that `Symbol` or `State` are finite; finiteness enters only with the canonically
coded machines of `MIPRE.TM.Code`.
-/
structure MultiInputTM (i w : ℕ) (Symbol State : Type*) where
  /-- initial state -/
  q₀ : State
  /-- transition function, mapping a state, the tuple of symbols under the input heads and
  the tuple of symbols under the work heads to a movement for each input head, actions on
  the work tapes, optionally a symbol to output and the successor state -/
  tr (q : State) (inputs : Fin i → Option Symbol) (work : Fin w → Option Symbol) :
    MultiInputTM.TransitionOut i w Symbol State

namespace MultiInputTM

-- Input-head movement is shared verbatim with the vendored one-input model.
open MultiTapeTM (moveInputPos)

variable {tm : MultiInputTM i w Symbol State}

section Cfg

/-!
## Configurations

This section defines the configurations of a multi-input Turing machine, the step function
that lets the machine transition from one configuration to the next, the resulting
sequence of configurations and the initial configuration. Input-head movement reuses
`Turing.moveInputPos` from the vendored CSLib file, one input tape at a time.
-/

/--
The configurations of a multi-input Turing machine are relative to the tuple of inputs of
the machine and consist of:
- an `Option`al state (or `none` for the halting state),
- the position of each input head (shifted by one),
- the contents of the work tapes,
- the positions of the work tape heads.
-/
@[ext]
structure Cfg (i w : ℕ) (Symbol State : Type*) (input : Fin i → List Symbol) where
  /-- the state of the machine (or `none` for the halting state) -/
  state : Option State
  /-- the position of each input head, shifted by one -/
  inputPos : (j : Fin i) → Fin ((input j).length + 2)
  /-- the work tapes -/
  workTapes : Fin w → ℤ → Option Symbol
  /-- the positions of the heads on the work tapes -/
  workTapePos : Fin w → ℤ
deriving Inhabited

variable {input : Fin i → List Symbol}

/-- The symbol currently under the head of input tape `j`. -/
def Cfg.inputSymbol (cfg : Cfg i w Symbol State input) (j : Fin i) : Option Symbol :=
  if h₁ : cfg.inputPos j = 0 then none
  else if h₂ : cfg.inputPos j = (input j).length + 1 then none
  else (input j)[(cfg.inputPos j).val - 1]'(by grind)

@[simp]
lemma inputSymbolInner {cfg : Cfg i w Symbol State input} (j : Fin i) (p : ℕ)
    (h₁ : (cfg.inputPos j).val = 1 + p)
    (h₂ : p < (input j).length) :
    cfg.inputSymbol j = some (input j)[p] := by
  grind [Cfg.inputSymbol]

/-- The tuple of symbols under the input heads. -/
def Cfg.inputSymbols (cfg : Cfg i w Symbol State input) : Fin i → Option Symbol :=
  fun j => cfg.inputSymbol j

@[simp]
lemma Cfg.inputSymbols_apply (cfg : Cfg i w Symbol State input) (j : Fin i) :
    cfg.inputSymbols j = cfg.inputSymbol j := rfl

/-- The symbol read by work tape `d`. -/
def Cfg.workTapeSymbols (cfg : Cfg i w Symbol State input) (d : Fin w) : Option Symbol :=
  cfg.workTapes d (cfg.workTapePos d)

/-- The step function corresponding to a `MultiInputTM`. -/
def step (cfg : Cfg i w Symbol State input) : Cfg i w Symbol State input :=
  match cfg.state with
  -- in the halting state, we stay at the configuration
  | none => cfg
  | some q =>
    let {inputMoves, workActions, q', ..} := tm.tr q cfg.inputSymbols cfg.workTapeSymbols
    {
      state := q',
      inputPos j := moveInputPos (cfg.inputPos j) (inputMoves j),
      workTapes d := match (workActions d).1 with
        | none => cfg.workTapes d
        | some s => Function.update (cfg.workTapes d) (cfg.workTapePos d) s
      workTapePos d := (cfg.workTapePos d) + (workActions d).2
    }

/-- The symbol (optionally) output when executing one step starting from configuration
`cfg`. -/
def outputSymbol (cfg : Cfg i w Symbol State input) : Option Symbol :=
  match cfg.state with
  | none => none
  | some q => (tm.tr q cfg.inputSymbols cfg.workTapeSymbols).outS

/-- The initial configuration corresponding to a tuple of input strings. -/
@[simp]
def initCfg (input : Fin i → List Symbol) : Cfg i w Symbol State input :=
  ⟨some tm.q₀, fun _ => 1, fun _ _ => none, fun _ => 0⟩

@[simp]
lemma step_of_halt {cfg : Cfg i w Symbol State input} (h : cfg.state = none) :
    tm.step cfg = cfg := by
  unfold step
  rw [h]

/-- The sequence of configurations of the Turing machine starting from `cfg`.
If the Turing machine halts, it will stay at the halting configuration. -/
def configs (cfg : Cfg i w Symbol State input) (t : ℕ) : Cfg i w Symbol State input :=
  tm.step^[t] cfg

@[simp]
lemma configs_zero {cfg : Cfg i w Symbol State input} :
    tm.configs cfg 0 = cfg := by
  simp [configs]

lemma configs_succ_eq_step {cfg : Cfg i w Symbol State input} {t : ℕ} :
    tm.configs cfg (t + 1) = tm.configs (tm.step cfg) t := by
  simp [configs, Function.iterate_succ_apply]

lemma configs_succ_eq_step' {cfg : Cfg i w Symbol State input} {t : ℕ} :
    tm.configs cfg (t + 1) = tm.step (tm.configs cfg t) := by
  simp [configs, Function.iterate_succ_apply']

/-- Running `a + b` steps equals running `b` steps from the configuration reached after
`a`. -/
lemma configs_add (cfg : Cfg i w Symbol State input) (a b : ℕ) :
    tm.configs cfg (a + b) = tm.configs (tm.configs cfg a) b := by
  unfold configs
  rw [Nat.add_comm, Function.iterate_add_apply]

/-- The sequence of configurations from a halting state is constant. -/
@[simp]
lemma configs_of_halts (cfg : Cfg i w Symbol State input) (h : cfg.state = none) {n : ℕ} :
    tm.configs cfg n = cfg := by
  induction n with
  | zero => rfl
  | succ d ih =>
    rw [configs_succ_eq_step', ih, step_of_halt h]

@[simp]
lemma outputSymbol_of_halt {cfg : Cfg i w Symbol State input} (h_halt : cfg.state = none) :
    tm.outputSymbol cfg = none := by
  simp [outputSymbol, h_halt]

/-- Each work-tape head moves by at most one cell in a single step. -/
lemma workTapePos_step_le (c : Cfg i w Symbol State input) (d : Fin w) :
    |(tm.step c).workTapePos d - c.workTapePos d| ≤ 1 := by
  unfold step
  cases hstate : c.state with
  | none => simp
  | some q =>
    simp only [add_sub_cancel_left, abs_le, SignType.cast]
    grind

end Cfg

section Space

/-! ## Space usage -/

variable {input : Fin i → List Symbol}

/-- The set of positions visited by the head of work tape `d` in the computation starting
from configuration `cfg` up to step `t`. -/
def visitedByTapeHead (cfg : Cfg i w Symbol State input) (t : ℕ) (d : Fin w) : Finset ℤ :=
  (Finset.range (t + 1)).image fun t' => (tm.configs cfg t').workTapePos d

/--
The number of work tape cells touched by the head of tape `d` in the computation starting
from configuration `cfg` up to step `t`.
-/
def spaceUsedByTape (cfg : Cfg i w Symbol State input) (t : ℕ) (d : Fin w) : ℕ :=
  (tm.visitedByTapeHead cfg t d).card

/--
The number of work tape cells touched by a computation starting from configuration `cfg`
up to step `t`.
-/
def spaceUsed (cfg : Cfg i w Symbol State input) (t : ℕ) : ℕ :=
  ∑ d, tm.spaceUsedByTape cfg t d

/-- A machine without work tapes uses zero space. -/
@[simp]
lemma spaceUsed_zero_tapes_eq_zero (cfg : Cfg i w Symbol State input) (t : ℕ)
    (h_zero : w = 0) :
    tm.spaceUsed cfg t = 0 := by
  unfold spaceUsed
  subst h_zero
  simp

/-- Each tape's space usage is bounded by the total space used. -/
lemma spaceUsedByTape_le_spaceUsed (cfg : Cfg i w Symbol State input) (t : ℕ) (d : Fin w) :
    tm.spaceUsedByTape cfg t d ≤ tm.spaceUsed cfg t :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ d)

end Space

open Cfg

variable {input : Fin i → List Symbol}

/--
The `TransitionRelation` corresponding to a `MultiInputTM i w Symbol State` is defined by
the `step` function, which maps a configuration to its next configuration.
-/
@[scoped grind =]
def TransitionRelation (c₁ c₂ : Cfg i w Symbol State input) : Prop := tm.step c₁ = c₂

/-- The string output by the Turing machine `tm` starting in configuration `cfg₀`,
executing for `t` steps. It is the concatenation of the symbols (optionally) emitted at
each of the first `t` steps. -/
def outputString
    (tm : MultiInputTM i w Symbol State)
    (cfg₀ : Cfg i w Symbol State input) (t : ℕ) : List Symbol :=
  (List.range t).flatMap fun t' => (tm.outputSymbol (tm.configs cfg₀ t')).toList

/-- The output produced in `t + 1` steps is the output produced in `t` steps followed by
the symbol (optionally) emitted at step `t`. -/
lemma outputString_succ
    (tm : MultiInputTM i w Symbol State)
    (cfg : Cfg i w Symbol State input) (t : ℕ) :
    tm.outputString cfg (t + 1) =
      tm.outputString cfg t ++ (tm.outputSymbol (tm.configs cfg t)).toList := by
  simp [outputString, List.range_succ, List.flatMap_append]

/-- From a halting configuration, a machine does not output anything. -/
lemma outputString_halt
    (tm : MultiInputTM i w Symbol State)
    (cfg : Cfg i w Symbol State input)
    (h_halt : cfg.state = none)
    (t : ℕ) :
    tm.outputString cfg t = [] := by
  induction t with
  | zero => simp [outputString]
  | succ t ih => simp [outputString_succ, ih, h_halt]

lemma outputString_add_eq_append
    (tm : MultiInputTM i w Symbol State)
    (cfg : Cfg i w Symbol State input) (t₁ t₂ : ℕ) :
    tm.outputString cfg (t₁ + t₂) =
      tm.outputString cfg t₁ ++ tm.outputString (tm.configs cfg t₁) t₂ := by
  induction t₂ with
  | zero => simp [outputString]
  | succ t ih =>
    rw [show (t₁ + (t + 1)) = (t₁ + t) + 1 by omega]
    simp [outputString_succ, ih, configs, ← Function.iterate_add_apply, Nat.add_comm]

/-- The output does not change after the machine has halted. -/
lemma outputString_eq_of_halt
    (tm : MultiInputTM i w Symbol State)
    (cfg : Cfg i w Symbol State input) {τ t : ℕ} (hle : τ ≤ t)
    (hhalt : (tm.configs cfg τ).state = none) :
    tm.outputString cfg t = tm.outputString cfg τ := by
  conv_lhs => rw [← Nat.sub_add_cancel hle, Nat.add_comm]
  rw [outputString_add_eq_append, outputString_halt _ _ hhalt]
  simp

/-- This lemma translates between the relational notion and the iterated step notion. The
latter can be more convenient especially for deterministic machines as we have here. -/
@[scoped grind =]
lemma relatesInSteps_iff_configs_eq
    (tm : MultiInputTM i w Symbol State)
    (cfg₁ cfg₂ : Cfg i w Symbol State input)
    (t : ℕ) :
    RelatesInSteps tm.TransitionRelation cfg₁ cfg₂ t ↔ tm.configs cfg₁ t = cfg₂ := by
  unfold configs
  induction t generalizing cfg₁ cfg₂ with
  | zero => simp
  | succ t ih =>
    rw [RelatesInSteps.succ_iff, Function.iterate_succ_apply']
    constructor
    · grind
    · intro h_configs
      use tm.step^[t] cfg₁
      grind

/-- The Turing machine `tm` halts after exactly `t` steps on input tuple `input` if its
state is `none` at step `t` and non-`none` at step `t - 1`.
Note that every Turing machine has to perform at least one step to halt. -/
def haltsAtStep (tm : MultiInputTM i w Symbol State) (input : Fin i → List Symbol)
    (t : ℕ) : Bool :=
  (tm.configs (tm.initCfg input) t).state.isNone &&
  !(tm.configs (tm.initCfg input) (t - 1)).state.isNone

/-- If a Turing machine halts, the time step is uniquely determined. -/
lemma halting_step_unique
    {tm : MultiInputTM i w Symbol State}
    {input : Fin i → List Symbol}
    {t₁ t₂ : ℕ}
    (h_halts₁ : tm.haltsAtStep input t₁)
    (h_halts₂ : tm.haltsAtStep input t₂) :
    t₁ = t₂ := by
  wlog h : t₁ ≤ t₂
  · exact (this h_halts₂ h_halts₁ (Nat.le_of_not_le h)).symm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  cases d with
  | zero => rfl
  | succ d =>
    have halts₁ : (tm.configs (tm.initCfg input) t₁).state = none := by
      simp [haltsAtStep] at h_halts₁
      exact h_halts₁.left
    have halts₂ : (tm.configs (tm.initCfg input) (d + t₁)).state ≠ none := by
      grind [haltsAtStep, configs]
    refine absurd ?_ halts₂
    rw [Nat.add_comm, configs_add, tm.configs_of_halts _ halts₁]
    exact halts₁

/-- If a deterministic machine repeats a non-halting configuration, it never halts,
because the sequence between the two configurations will loop forever.
Note that this can be applied to two arbitrary and different time steps `t` and `t + Δ`
using `tm.configs_add`. -/
lemma not_halts_of_repeat_nonhalt
    (cfg : Cfg i w Symbol State input)
    (h_not_halt : cfg.state ≠ none)
    (t : ℕ)
    (heq : tm.configs cfg (t + 1) = cfg) :
    ∀ t', (tm.configs cfg t').state ≠ none := by
  intro t'
  -- The configuration will repeat every `t + 1` steps.
  have hloop : ∀ n, tm.configs cfg (n * (t + 1)) = cfg := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show (n + 1) * (t + 1) = n * (t + 1) + (t + 1) by grind, tm.configs_add, ih, heq]
  by_contra hnh
  -- Assuming the machine halts at step `t'`, it is also halted at step `t' * (t + 1)`
  have h₁ : (tm.configs cfg (t' * (t + 1))).state = none := by
    have hle : t' ≤ t' * (t + 1) := by grind
    obtain ⟨tΔ , htΔ⟩ := Nat.exists_eq_add_of_le hle
    rw [htΔ, tm.configs_add]
    simp [hnh]
  simp [hloop t', h_not_halt] at h₁

end MultiInputTM

end Turing

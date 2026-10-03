/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.TM.MultiInput.Complexity

@[expose] public section

/-!
# Relabeling multi-input machines along equivalences

Relabeling the state type or the tape alphabet of a machine does not change its
behaviour: `MultiInputTM.congrState` and `MultiInputTM.congrSymbol` transport machines,
configurations, runs, outputs, space usage and `ComputesInTimeAndSpace` along
`State ≃ State'` and `Symbol ≃ Symbol'`. This is the canonicalization glue between
machines over arbitrary (finite) types and the `Fin`-typed shape of coded machines
(`MIPRE.TM.Code.Semantics`): coded machines are *born* over `Fin`, and outside results
about machines over other types meet them through these lemmas.

Adapted to the multi-input model from `Regular.lean` on the `finite_in_fin` branch of
Christian Reitwiessner's CSLib fork (https://github.com/crei/cslib, branch tip
`4a149e205c99d4636d3a421c8cf3526e47b00f16`, 2026-07-19; Apache 2.0), which develops the
same API for the one-input `MultiTapeTM` of an earlier model revision (its configurations
still carry an `output` field, so the file predates upstream #745 and cannot be vendored
against the current model). Two deliberate changes besides the multi-input
generalization:

* `congrState` relabels along an *equivalence*, not an embedding: the fork's
  embedding-plus-`Function.invFun` version is `noncomputable`, and its only use
  instantiates with an equivalence anyway. Everything here is executable
  (`planning/tm-infrastructure.md`, decision D5).
* The fork's DFA simulation and regular-language results are deliberately not ported;
  they concern the one-input model and can be revisited when CSLib is un-vendored.
-/

namespace Turing.MultiInputTM

variable {i w : ℕ} {State State' Symbol Symbol' : Type*}

/-! ## Relabeling the state type

None of the dependent structure of a configuration (inputs, head positions, work tapes)
mentions the state type, so this direction is straightforward. -/

section CongrState

variable {input : Fin i → List Symbol}

/-- Relabel the state of a configuration along `e : State ≃ State'`. -/
def Cfg.congrState (e : State ≃ State') (cfg : Cfg i w Symbol State input) :
    Cfg i w Symbol State' input :=
  { cfg with state := cfg.state.map e }

@[simp]
lemma Cfg.congrState_state (e : State ≃ State') (cfg : Cfg i w Symbol State input) :
    (cfg.congrState e).state = cfg.state.map e := rfl

@[simp]
lemma Cfg.congrState_inputPos (e : State ≃ State') (cfg : Cfg i w Symbol State input) :
    (cfg.congrState e).inputPos = cfg.inputPos := rfl

@[simp]
lemma Cfg.congrState_workTapes (e : State ≃ State') (cfg : Cfg i w Symbol State input) :
    (cfg.congrState e).workTapes = cfg.workTapes := rfl

@[simp]
lemma Cfg.congrState_workTapePos (e : State ≃ State') (cfg : Cfg i w Symbol State input) :
    (cfg.congrState e).workTapePos = cfg.workTapePos := rfl

@[simp]
lemma Cfg.congrState_inputSymbols (e : State ≃ State') (cfg : Cfg i w Symbol State input) :
    (cfg.congrState e).inputSymbols = cfg.inputSymbols := rfl

@[simp]
lemma Cfg.congrState_workTapeSymbols (e : State ≃ State')
    (cfg : Cfg i w Symbol State input) :
    (cfg.congrState e).workTapeSymbols = cfg.workTapeSymbols := rfl

/-- Relabel the state type of a machine along an equivalence `e : State ≃ State'`. -/
def congrState (e : State ≃ State') (tm : MultiInputTM i w Symbol State) :
    MultiInputTM i w Symbol State' where
  q₀ := e tm.q₀
  tr q inputs work :=
    let o := tm.tr (e.symm q) inputs work
    { inputMoves := o.inputMoves
      workActions := o.workActions
      outS := o.outS
      q' := o.q'.map e }

/-- The step function commutes with state relabeling. -/
@[simp]
lemma step_congrState (e : State ≃ State') (tm : MultiInputTM i w Symbol State)
    (cfg : Cfg i w Symbol State input) :
    (tm.congrState e).step (cfg.congrState e) = (tm.step cfg).congrState e := by
  cases hs : cfg.state with
  | none =>
    rw [step_of_halt (show (cfg.congrState e).state = none by simp [hs]),
      step_of_halt hs]
  | some q =>
    simp only [step, Cfg.congrState_state, hs, Option.map_some, congrState,
      Equiv.symm_apply_apply, Cfg.congrState_inputSymbols, Cfg.congrState_workTapeSymbols]
    rfl

end CongrState

/-! ## Relabeling the symbol type

This direction touches the dependent structure of a configuration: each input head
position lives in `Fin ((input j).length + 2)`, so mapping the inputs transports the
positions along `List.length_map` via `Fin.cast`. -/

section CongrSymbol

variable {input : Fin i → List Symbol}

/-- Relabel the symbols of a configuration along `e : Symbol ≃ Symbol'`. -/
def Cfg.congrSymbol (e : Symbol ≃ Symbol') (cfg : Cfg i w Symbol State input) :
    Cfg i w Symbol' State (fun j => (input j).map e) where
  state := cfg.state
  inputPos j := Fin.cast (by rw [List.length_map]) (cfg.inputPos j)
  workTapes d z := (cfg.workTapes d z).map e
  workTapePos := cfg.workTapePos

@[simp]
lemma Cfg.congrSymbol_state (e : Symbol ≃ Symbol') (cfg : Cfg i w Symbol State input) :
    (cfg.congrSymbol e).state = cfg.state := rfl

@[simp]
lemma Cfg.congrSymbol_workTapePos (e : Symbol ≃ Symbol')
    (cfg : Cfg i w Symbol State input) :
    (cfg.congrSymbol e).workTapePos = cfg.workTapePos := rfl

@[simp]
lemma Cfg.congrSymbol_inputPos_val (e : Symbol ≃ Symbol')
    (cfg : Cfg i w Symbol State input) (j : Fin i) :
    ((cfg.congrSymbol e).inputPos j).val = (cfg.inputPos j).val := rfl

@[simp]
lemma Cfg.congrSymbol_workTapeSymbols (e : Symbol ≃ Symbol')
    (cfg : Cfg i w Symbol State input) (d : Fin w) :
    (cfg.congrSymbol e).workTapeSymbols d = (cfg.workTapeSymbols d).map e := rfl

@[simp]
lemma Cfg.congrSymbol_inputSymbol (e : Symbol ≃ Symbol')
    (cfg : Cfg i w Symbol State input) (j : Fin i) :
    (cfg.congrSymbol e).inputSymbol j = (cfg.inputSymbol j).map e := by
  have hz : ((cfg.congrSymbol e).inputPos j = 0) ↔ (cfg.inputPos j = 0) := by
    simp only [Fin.ext_iff, Cfg.congrSymbol_inputPos_val, Fin.val_zero]
  have he : ((cfg.congrSymbol e).inputPos j = ((input j).map e).length + 1)
      ↔ (cfg.inputPos j = (input j).length + 1) := by
    simp only [Cfg.congrSymbol_inputPos_val, List.length_map]
  unfold Cfg.inputSymbol
  simp only [hz, he]
  split_ifs with h1 h2
  · rfl
  · rfl
  · simp [Cfg.congrSymbol, List.getElem_map]

/-- Relabel the tape alphabet of a machine along an equivalence `e : Symbol ≃ Symbol'`. -/
def congrSymbol (e : Symbol ≃ Symbol') (tm : MultiInputTM i w Symbol State) :
    MultiInputTM i w Symbol' State where
  q₀ := tm.q₀
  tr q inputs work :=
    let o := tm.tr q (fun j => (inputs j).map e.symm) (fun d => (work d).map e.symm)
    { inputMoves := o.inputMoves
      workActions := fun d => ((o.workActions d).1.map (Option.map e), (o.workActions d).2)
      outS := o.outS.map e
      q' := o.q' }

end CongrSymbol

end Turing.MultiInputTM

end

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.TM.MultiInput.Complexity

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

/-- The configuration sequence commutes with state relabeling. -/
lemma configs_congrState (e : State ≃ State') (tm : MultiInputTM i w Symbol State)
    (cfg : Cfg i w Symbol State input) (t : ℕ) :
    (tm.congrState e).configs (cfg.congrState e) t = (tm.configs cfg t).congrState e := by
  unfold configs
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, step_congrState]

lemma initCfg_congrState (e : State ≃ State') (tm : MultiInputTM i w Symbol State)
    (input : Fin i → List Symbol) :
    (tm.congrState e).initCfg input = (tm.initCfg input).congrState e := by
  simp [initCfg, Cfg.congrState, congrState]

/-- The emitted symbol is unchanged by state relabeling. -/
lemma outputSymbol_congrState (e : State ≃ State') (tm : MultiInputTM i w Symbol State)
    (cfg : Cfg i w Symbol State input) :
    (tm.congrState e).outputSymbol (cfg.congrState e) = tm.outputSymbol cfg := by
  cases hs : cfg.state with
  | none =>
    rw [outputSymbol_of_halt (show (cfg.congrState e).state = none by simp [hs]),
      outputSymbol_of_halt hs]
  | some q =>
    simp only [outputSymbol, Cfg.congrState_state, hs, Option.map_some, congrState,
      Equiv.symm_apply_apply, Cfg.congrState_inputSymbols, Cfg.congrState_workTapeSymbols]

/-- The output string is unchanged by state relabeling. -/
lemma outputString_congrState (e : State ≃ State') (tm : MultiInputTM i w Symbol State)
    (cfg : Cfg i w Symbol State input) (t : ℕ) :
    (tm.congrState e).outputString (cfg.congrState e) t = tm.outputString cfg t := by
  unfold outputString
  congr 1
  funext t'
  rw [configs_congrState, outputSymbol_congrState]

/-- The space usage is unchanged by state relabeling. -/
lemma spaceUsed_congrState (e : State ≃ State') (tm : MultiInputTM i w Symbol State)
    (cfg : Cfg i w Symbol State input) (t : ℕ) :
    (tm.congrState e).spaceUsed (cfg.congrState e) t = tm.spaceUsed cfg t := by
  unfold spaceUsed spaceUsedByTape visitedByTapeHead
  simp only [configs_congrState, Cfg.congrState_workTapePos]

/-- Relabeling the state type preserves computations: the relabeled machine computes the
same input/output pairs in the same time and space. -/
lemma computesInTimeAndSpace_congrState (e : State ≃ State')
    (tm : MultiInputTM i w Symbol State) (input : Fin i → List Symbol)
    (output : List Symbol) (t s : ℕ)
    (h : tm.ComputesInTimeAndSpace input output t s) :
    (tm.congrState e).ComputesInTimeAndSpace input output t s := by
  obtain ⟨hhalt, hout, hspace⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [initCfg_congrState, configs_congrState]
    simpa using hhalt
  · rw [initCfg_congrState, outputString_congrState, hout]
  · rw [initCfg_congrState, spaceUsed_congrState, hspace]

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

lemma Cfg.congrSymbol_inputSymbols (e : Symbol ≃ Symbol')
    (cfg : Cfg i w Symbol State input) :
    (cfg.congrSymbol e).inputSymbols = fun j => (cfg.inputSymbol j).map e := by
  funext j
  simp [Cfg.inputSymbols_apply]

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

/-- Moving an input head commutes with transporting the position along an equal tape
length. -/
lemma moveInputPos_cast {n m : ℕ} (h : n + 2 = m + 2) (pos : Fin (n + 2)) (mv : SignType) :
    MultiTapeTM.moveInputPos (Fin.cast h pos) mv
      = Fin.cast h (MultiTapeTM.moveInputPos pos mv) := by
  obtain rfl : n = m := by omega
  simp

/-- The step function commutes with symbol relabeling. -/
lemma step_congrSymbol (e : Symbol ≃ Symbol') (tm : MultiInputTM i w Symbol State)
    (cfg : Cfg i w Symbol State input) :
    (tm.congrSymbol e).step (cfg.congrSymbol e) = (tm.step cfg).congrSymbol e := by
  cases hs : cfg.state with
  | none =>
    rw [step_of_halt (show (cfg.congrSymbol e).state = none from hs),
      step_of_halt hs]
  | some q =>
    have hargs : (fun j => ((cfg.congrSymbol e).inputSymbols j).map e.symm)
        = cfg.inputSymbols := by
      funext j
      simp [Cfg.inputSymbols_apply]
    have hargs' : (fun d => ((cfg.congrSymbol e).workTapeSymbols d).map e.symm)
        = cfg.workTapeSymbols := by
      funext d
      simp
    conv_lhs => rw [step]
    conv_rhs => rw [step]
    simp only [Cfg.congrSymbol_state, hs, congrSymbol, hargs, hargs']
    refine Cfg.ext rfl ?_ ?_ rfl
    · funext j
      exact moveInputPos_cast (by simp) _ _
    · funext d z
      simp only [Cfg.congrSymbol]
      rcases hw : ((tm.tr q cfg.inputSymbols cfg.workTapeSymbols).workActions d).1
        with _ | s
      · simp
      · simp [Function.apply_update (fun _ (y : Option Symbol) => Option.map e y)]

/-- The configuration sequence commutes with symbol relabeling. -/
lemma configs_congrSymbol (e : Symbol ≃ Symbol') (tm : MultiInputTM i w Symbol State)
    (cfg : Cfg i w Symbol State input) (t : ℕ) :
    (tm.congrSymbol e).configs (cfg.congrSymbol e) t = (tm.configs cfg t).congrSymbol e := by
  unfold configs
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, step_congrSymbol]

lemma initCfg_congrSymbol (e : Symbol ≃ Symbol') (tm : MultiInputTM i w Symbol State)
    (input : Fin i → List Symbol) :
    (tm.congrSymbol e).initCfg (fun j => (input j).map e)
      = (tm.initCfg input).congrSymbol e := by
  refine Cfg.ext ?_ ?_ ?_ ?_ <;>
    simp [initCfg, Cfg.congrSymbol, congrSymbol, Fin.ext_iff, funext_iff]

/-- The emitted symbol is relabeled along with the machine. -/
lemma outputSymbol_congrSymbol (e : Symbol ≃ Symbol') (tm : MultiInputTM i w Symbol State)
    (cfg : Cfg i w Symbol State input) :
    (tm.congrSymbol e).outputSymbol (cfg.congrSymbol e)
      = (tm.outputSymbol cfg).map e := by
  cases hs : cfg.state with
  | none =>
    rw [outputSymbol_of_halt (show (cfg.congrSymbol e).state = none from hs),
      outputSymbol_of_halt hs]
    rfl
  | some q =>
    have hargs : (fun j => ((cfg.congrSymbol e).inputSymbols j).map e.symm)
        = cfg.inputSymbols := by
      funext j
      simp [Cfg.inputSymbols_apply]
    have hargs' : (fun d => ((cfg.congrSymbol e).workTapeSymbols d).map e.symm)
        = cfg.workTapeSymbols := by
      funext d
      simp
    simp only [outputSymbol, Cfg.congrSymbol_state, hs, congrSymbol, hargs, hargs']

/-- The output string is relabeled along with the machine. -/
lemma outputString_congrSymbol (e : Symbol ≃ Symbol') (tm : MultiInputTM i w Symbol State)
    (cfg : Cfg i w Symbol State input) (t : ℕ) :
    (tm.congrSymbol e).outputString (cfg.congrSymbol e) t
      = (tm.outputString cfg t).map e := by
  unfold outputString
  rw [List.map_flatMap]
  congr 1
  funext t'
  rw [configs_congrSymbol, outputSymbol_congrSymbol]
  cases tm.outputSymbol (tm.configs cfg t') <;> simp

/-- The space usage is unchanged by symbol relabeling. -/
lemma spaceUsed_congrSymbol (e : Symbol ≃ Symbol') (tm : MultiInputTM i w Symbol State)
    (cfg : Cfg i w Symbol State input) (t : ℕ) :
    (tm.congrSymbol e).spaceUsed (cfg.congrSymbol e) t = tm.spaceUsed cfg t := by
  unfold spaceUsed spaceUsedByTape visitedByTapeHead
  simp only [configs_congrSymbol, Cfg.congrSymbol_workTapePos]

/-- Relabeling the tape alphabet transports computations: the relabeled machine computes
the relabeled input/output pairs in the same time and space. -/
lemma computesInTimeAndSpace_congrSymbol (e : Symbol ≃ Symbol')
    (tm : MultiInputTM i w Symbol State) (input : Fin i → List Symbol)
    (output : List Symbol) (t s : ℕ)
    (h : tm.ComputesInTimeAndSpace input output t s) :
    (tm.congrSymbol e).ComputesInTimeAndSpace (fun j => (input j).map e)
      (output.map e) t s := by
  obtain ⟨hhalt, hout, hspace⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [initCfg_congrSymbol, configs_congrSymbol]
    simpa using hhalt
  · rw [initCfg_congrSymbol, outputString_congrSymbol, hout]
  · rw [initCfg_congrSymbol, spaceUsed_congrSymbol, hspace]

end CongrSymbol

end Turing.MultiInputTM

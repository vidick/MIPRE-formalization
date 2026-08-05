/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.TM.MultiInput.Complexity

/-!
# One-input machines are exactly CSLib's multi-tape machines

The multi-input model of `MIPRE.TM.MultiInput.Deterministic` specializes, at input arity
one, to the vendored CSLib model `Turing.MultiTapeTM` — exactly, not just up to
simulation. This file provides the two machine translations

* `MultiInputTM.toCSLib : MultiInputTM 1 w Symbol State → MultiTapeTM w Symbol State`,
* `MultiInputTM.ofCSLib : MultiTapeTM w Symbol State → MultiInputTM 1 w Symbol State`,

shows they are mutually inverse, and proves that along the configuration correspondence
`MultiInputTM.cfgEquiv` they preserve `step`, `configs`, `outputString`, `spaceUsed`, and
`ComputesInTimeAndSpace` on the nose (Milestone A acceptance criteria,
`planning/tm-infrastructure.md`).

Throughout, a one-input tuple is written `fun _ : Fin 1 => input` (never `![input]`), so
that the dependent input-head positions transport definitionally.
-/

namespace Turing.MultiInputTM

variable {w : ℕ} {State Symbol : Type*}

/-- Reinterpret a one-input machine as a CSLib multi-tape machine. -/
def toCSLib (M : MultiInputTM 1 w Symbol State) : MultiTapeTM w Symbol State where
  q₀ := M.q₀
  tr q a work :=
    let o := M.tr q (fun _ => a) work
    ⟨o.inputMoves 0, o.workActions, o.outS, o.q'⟩

/-- Reinterpret a CSLib multi-tape machine as a one-input machine. -/
def ofCSLib (N : MultiTapeTM w Symbol State) : MultiInputTM 1 w Symbol State where
  q₀ := N.q₀
  tr q inputs work :=
    let o := N.tr q (inputs 0) work
    ⟨fun _ => o.inputMove, o.workActions, o.outS, o.q'⟩

/-- Round trip on CSLib machines: `toCSLib` undoes `ofCSLib`. -/
@[simp]
theorem toCSLib_ofCSLib (N : MultiTapeTM w Symbol State) : (ofCSLib N).toCSLib = N := rfl

/-- Round trip on one-input machines: `ofCSLib` undoes `toCSLib`. -/
@[simp]
theorem ofCSLib_toCSLib (M : MultiInputTM 1 w Symbol State) : ofCSLib M.toCSLib = M := by
  obtain ⟨q₀, tr⟩ := M
  refine congrArg (MultiInputTM.mk q₀) ?_
  funext q inputs work
  have hin : (fun _ : Fin 1 => inputs 0) = inputs :=
    funext fun j => by rw [Fin.fin_one_eq_zero j]
  show (⟨fun _ => (tr q (fun _ => inputs 0) work).inputMoves 0,
          (tr q (fun _ => inputs 0) work).workActions,
          (tr q (fun _ => inputs 0) work).outS,
          (tr q (fun _ => inputs 0) work).q'⟩ : TransitionOut 1 w Symbol State) =
      tr q inputs work
  rw [hin]
  exact TransitionOut.ext (funext fun j => by rw [Fin.fin_one_eq_zero j]) rfl rfl rfl

section CfgEquiv

variable {input : List Symbol}

/-- Configurations of a CSLib machine on `input` correspond exactly to configurations of a
one-input machine on the tuple `fun _ => input`. -/
def cfgEquiv (input : List Symbol) :
    MultiTapeTM.Cfg w Symbol State input ≃ Cfg 1 w Symbol State (fun _ => input) where
  toFun c := ⟨c.state, fun _ => c.inputPos, c.workTapes, c.workTapePos⟩
  invFun c := ⟨c.state, c.inputPos 0, c.workTapes, c.workTapePos⟩
  left_inv c := rfl
  right_inv c := by
    refine Cfg.ext rfl ?_ rfl rfl
    funext j
    rw [Fin.fin_one_eq_zero j]

@[simp]
lemma cfgEquiv_state (c : MultiTapeTM.Cfg w Symbol State input) :
    (cfgEquiv input c).state = c.state := rfl

@[simp]
lemma cfgEquiv_inputPos (c : MultiTapeTM.Cfg w Symbol State input) (j : Fin 1) :
    (cfgEquiv input c).inputPos j = c.inputPos := rfl

@[simp]
lemma cfgEquiv_workTapes (c : MultiTapeTM.Cfg w Symbol State input) :
    (cfgEquiv input c).workTapes = c.workTapes := rfl

@[simp]
lemma cfgEquiv_workTapePos (c : MultiTapeTM.Cfg w Symbol State input) :
    (cfgEquiv input c).workTapePos = c.workTapePos := rfl

@[simp]
lemma cfgEquiv_symm_state (c : Cfg 1 w Symbol State (fun _ => input)) :
    ((cfgEquiv input).symm c).state = c.state := rfl

/-- The input symbol read is preserved by the configuration correspondence. -/
lemma cfgEquiv_inputSymbol (c : MultiTapeTM.Cfg w Symbol State input) (j : Fin 1) :
    (cfgEquiv input c).inputSymbol j = c.inputSymbol := rfl

/-- The tuple of input symbols of a transported configuration. -/
lemma cfgEquiv_inputSymbols (c : MultiTapeTM.Cfg w Symbol State input) :
    (cfgEquiv input c).inputSymbols = fun _ : Fin 1 => c.inputSymbol := rfl

/-- The work symbols read are preserved by the configuration correspondence. -/
lemma cfgEquiv_workTapeSymbols (c : MultiTapeTM.Cfg w Symbol State input) :
    (cfgEquiv input c).workTapeSymbols = c.workTapeSymbols := rfl

end CfgEquiv

section Transfer

variable {input : List Symbol}

/-- The step functions agree along the configuration correspondence. -/
theorem toCSLib_step (M : MultiInputTM 1 w Symbol State)
    (c : MultiTapeTM.Cfg w Symbol State input) :
    cfgEquiv input (M.toCSLib.step c) = M.step (cfgEquiv input c) := by
  cases hstate : c.state with
  | none =>
    rw [MultiTapeTM.step_of_halt hstate,
      step_of_halt (show (cfgEquiv input c).state = none from hstate)]
  | some q =>
    refine Cfg.ext ?_ ?_ ?_ ?_
    · simp only [MultiTapeTM.step, step, toCSLib, cfgEquiv_state, cfgEquiv_inputSymbols,
        cfgEquiv_workTapeSymbols, hstate]
    · funext j
      simp only [MultiTapeTM.step, step, toCSLib, cfgEquiv_state, cfgEquiv_inputSymbols,
        cfgEquiv_workTapeSymbols, cfgEquiv_inputPos, hstate]
      rw [Fin.fin_one_eq_zero j]
    · simp only [MultiTapeTM.step, step, toCSLib, cfgEquiv_state, cfgEquiv_inputSymbols,
        cfgEquiv_workTapeSymbols, cfgEquiv_workTapes, cfgEquiv_workTapePos, hstate]
      rfl
    · simp only [MultiTapeTM.step, step, toCSLib, cfgEquiv_state, cfgEquiv_inputSymbols,
        cfgEquiv_workTapeSymbols, cfgEquiv_workTapePos, hstate]

/-- The step-indexed runs agree along the configuration correspondence. -/
theorem toCSLib_configs (M : MultiInputTM 1 w Symbol State)
    (c : MultiTapeTM.Cfg w Symbol State input) (t : ℕ) :
    cfgEquiv input (M.toCSLib.configs c t) = M.configs (cfgEquiv input c) t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [MultiTapeTM.configs_succ_eq_step', configs_succ_eq_step', ← ih, toCSLib_step]

/-- The emitted symbols agree along the configuration correspondence. -/
theorem toCSLib_outputSymbol (M : MultiInputTM 1 w Symbol State)
    (c : MultiTapeTM.Cfg w Symbol State input) :
    M.toCSLib.outputSymbol c = M.outputSymbol (cfgEquiv input c) := by
  cases hstate : c.state with
  | none =>
    rw [MultiTapeTM.outputSymbol_of_halt hstate,
      outputSymbol_of_halt (show (cfgEquiv input c).state = none from hstate)]
  | some q =>
    simp only [MultiTapeTM.outputSymbol, outputSymbol, toCSLib, cfgEquiv_state,
      cfgEquiv_inputSymbols, cfgEquiv_workTapeSymbols, hstate]

/-- The output strings agree along the configuration correspondence. -/
theorem toCSLib_outputString (M : MultiInputTM 1 w Symbol State)
    (c : MultiTapeTM.Cfg w Symbol State input) (t : ℕ) :
    M.toCSLib.outputString c t = M.outputString (cfgEquiv input c) t := by
  unfold MultiTapeTM.outputString outputString
  congr 1
  funext t'
  rw [← toCSLib_configs, toCSLib_outputSymbol]

/-- The visited work-tape cells agree along the configuration correspondence. -/
theorem toCSLib_visitedByTapeHead (M : MultiInputTM 1 w Symbol State)
    (c : MultiTapeTM.Cfg w Symbol State input) (t : ℕ) (d : Fin w) :
    M.toCSLib.visitedByTapeHead c t d = M.visitedByTapeHead (cfgEquiv input c) t d := by
  unfold MultiTapeTM.visitedByTapeHead visitedByTapeHead
  congr 1
  funext t'
  rw [← toCSLib_configs]
  rfl

/-- The space usage agrees along the configuration correspondence. -/
theorem toCSLib_spaceUsed (M : MultiInputTM 1 w Symbol State)
    (c : MultiTapeTM.Cfg w Symbol State input) (t : ℕ) :
    M.toCSLib.spaceUsed c t = M.spaceUsed (cfgEquiv input c) t := by
  unfold MultiTapeTM.spaceUsed spaceUsed MultiTapeTM.spaceUsedByTape spaceUsedByTape
  exact Finset.sum_congr rfl fun d _ => by rw [toCSLib_visitedByTapeHead]

/-- The initial configurations correspond. -/
theorem toCSLib_initCfg (M : MultiInputTM 1 w Symbol State) (input : List Symbol) :
    cfgEquiv input (M.toCSLib.initCfg input) = M.initCfg (fun _ => input) := rfl

/-- A one-input machine and its CSLib avatar compute the same input/output/time/space
quadruples. -/
theorem toCSLib_computesInTimeAndSpace (M : MultiInputTM 1 w Symbol State)
    (input output : List Symbol) (t s : ℕ) :
    M.toCSLib.ComputesInTimeAndSpace input output t s ↔
      M.ComputesInTimeAndSpace (fun _ => input) output t s := by
  unfold MultiTapeTM.ComputesInTimeAndSpace ComputesInTimeAndSpace
  rw [← toCSLib_initCfg, ← toCSLib_configs, ← toCSLib_outputString, ← toCSLib_spaceUsed,
    cfgEquiv_state]

end Transfer

end Turing.MultiInputTM

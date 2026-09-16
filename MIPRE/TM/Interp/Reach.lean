/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.TM.Interp.Machine
import MIPRE.TM.Interp.Tape

/-!
# Runs of the interpreter

`Reach c n c' out`: from the configuration `c`, `n` steps of `U` lead to `c'`, emitting
`out`. It composes (`Reach.trans`), and a single step is the action of the current
instruction phase (`step_eq`, `applyAct`). The routine specifications (`Routines.lean`)
are reachability statements with step bounds.
-/

namespace MIPRE.TM.Interp

open Turing MultiInputTM
open MultiTapeTM (moveInputPos)

variable {input : Fin 7 → List Sym}

/-- Configurations of the interpreter on the inputs `input`. -/
abbrev Cfg (input : Fin 7 → List Sym) := MultiInputTM.Cfg 7 6 Sym Ctl input

/-- The configuration after the actions `a`, with the control `q'`. -/
def applyAct (a : Act) (q' : Option Ctl) (c : Cfg input) : Cfg input where
  state := q'
  inputPos j := moveInputPos (c.inputPos j) (a.inMoves j)
  workTapes d :=
    match (a.works d).1 with
    | none => c.workTapes d
    | some s => Function.update (c.workTapes d) (c.workTapePos d) s
  workTapePos d := c.workTapePos d + (a.works d).2

/-- The action of the current instruction phase. -/
def actOf (q : Ctl) (c : Cfg input) : Act :=
  execInstr (instrAt q.k q.pc) q.ph c.inputSymbols c.workTapeSymbols

/-- One step of `U` is the action of the current instruction phase. -/
theorem step_eq (c : Cfg input) {q : Ctl} (hq : c.state = some q) :
    U.step c = applyAct (actOf q c) (resolve q.k q.pc (actOf q c).next) c := by
  unfold step
  rw [hq]
  dsimp only [U, actOf, applyAct]
  refine Cfg.ext rfl rfl (funext fun d => ?_) rfl
  dsimp only
  rcases h : ((execInstr (instrAt q.k q.pc) q.ph c.inputSymbols c.workTapeSymbols).works d).1 with
    _ | s <;> rfl

theorem outputSymbol_eq (c : Cfg input) {q : Ctl} (hq : c.state = some q) :
    U.outputSymbol c = (actOf q c).out := by
  unfold outputSymbol
  rw [hq]
  rfl

/-- `n` steps from `c` lead to `c'`, emitting `out`. -/
def Reach (c : Cfg input) (n : ℕ) (c' : Cfg input) (out : List Sym) : Prop :=
  U.configs c n = c' ∧ U.outputString c n = out

namespace Reach

theorem refl (c : Cfg input) : Reach c 0 c [] := ⟨configs_zero, by simp [outputString]⟩

theorem trans {c c' c'' : Cfg input} {n m : ℕ} {out out' : List Sym} (h : Reach c n c' out)
    (h' : Reach c' m c'' out') : Reach c (n + m) c'' (out ++ out') := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  refine ⟨?_, ?_⟩
  · rw [configs_add, h1, h1']
  · rw [outputString_add_eq_append, h1, h2, h2']

theorem single (c : Cfg input) : Reach c 1 (U.step c) (U.outputSymbol c).toList := by
  refine ⟨configs_succ_eq_step'.trans (by simp), ?_⟩
  rw [outputString_succ, outputString, List.range_zero, List.flatMap_nil, List.nil_append,
    configs_zero]

/-- A single silent step. -/
theorem step {c : Cfg input} {q : Ctl} (hq : c.state = some q) (hout : (actOf q c).out = none) :
    Reach c 1 (applyAct (actOf q c) (resolve q.k q.pc (actOf q c).next) c) [] := by
  have := single c
  rwa [step_eq c hq, outputSymbol_eq c hq, hout] at this

theorem cast {c c' c'' : Cfg input} {n : ℕ} {out : List Sym} (h : Reach c n c' out)
    (e : c' = c'') : Reach c n c'' out := e ▸ h

theorem cast_n {c c' : Cfg input} {n n' : ℕ} {out : List Sym} (h : Reach c n c' out)
    (e : n = n') : Reach c n' c' out := e ▸ h

theorem cast_out {c c' : Cfg input} {n : ℕ} {out out' : List Sym} (h : Reach c n c' out)
    (e : out = out') : Reach c n c' out' := e ▸ h

/-- A silent step followed by a run. -/
theorem step_trans {c c'' : Cfg input} {q : Ctl} (hq : c.state = some q)
    (hout : (actOf q c).out = none) {m : ℕ} {out : List Sym}
    (h : Reach (applyAct (actOf q c) (resolve q.k q.pc (actOf q c).next) c) m c'' out) :
    Reach c (m + 1) c'' out := by
  have := (step hq hout).trans h
  rwa [Nat.add_comm, List.nil_append] at this

end Reach

/-- Halting: the state is `none` after `n` steps. -/
def HaltsIn (c : Cfg input) (n : ℕ) : Prop := (U.configs c n).state = none

theorem HaltsIn.of_reach {c c' : Cfg input} {n : ℕ} {out : List Sym} (h : Reach c n c' out)
    (h' : c'.state = none) : HaltsIn c n := by
  unfold HaltsIn; rw [h.1]; exact h'

theorem HaltsIn.mono {c : Cfg input} {n m : ℕ} (h : HaltsIn c n) (hnm : n ≤ m) : HaltsIn c m := by
  unfold HaltsIn at *
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [configs_add, configs_of_halts _ h]
  exact h

/-! ## Reading and writing under `applyAct` -/

section Apply

variable (a : Act) (q' : Option Ctl) (c : Cfg input)

@[simp] theorem applyAct_state : (applyAct a q' c).state = q' := rfl

@[simp] theorem applyAct_inputPos (j : IT) :
    (applyAct a q' c).inputPos j = moveInputPos (c.inputPos j) (a.inMoves j) := rfl

@[simp] theorem applyAct_workTapePos (d : WT) :
    (applyAct a q' c).workTapePos d = c.workTapePos d + (a.works d).2 := rfl

theorem applyAct_workTapes_of_none (d : WT) (h : (a.works d).1 = none) :
    (applyAct a q' c).workTapes d = c.workTapes d := by
  simp [applyAct, h]

theorem applyAct_workTapes_of_some (d : WT) {s : Option Sym} (h : (a.works d).1 = some s) :
    (applyAct a q' c).workTapes d = Function.update (c.workTapes d) (c.workTapePos d) s := by
  simp [applyAct, h]

end Apply

/-! ## Evaluating actions -/

namespace Act

@[simp] theorem base_inMoves (n : Next) (j : IT) : (base n).inMoves j = 0 := rfl
@[simp] theorem base_works (n : Next) (d : WT) : (base n).works d = (none, 0) := rfl
@[simp] theorem base_out (n : Next) : (base n).out = none := rfl
@[simp] theorem base_next (n : Next) : (base n).next = n := rfl

@[simp] theorem mw_next (a : Act) (t : WT) (m : SignType) : (a.mw t m).next = a.next := rfl
@[simp] theorem ww_next (a : Act) (t : WT) (s : Option Sym) : (a.ww t s).next = a.next := rfl
@[simp] theorem mi_next (a : Act) (j : IT) (m : SignType) : (a.mi j m).next = a.next := rfl
@[simp] theorem emit_next (a : Act) (s : Sym) : (a.emit s).next = a.next := rfl

@[simp] theorem mw_out (a : Act) (t : WT) (m : SignType) : (a.mw t m).out = a.out := rfl
@[simp] theorem ww_out (a : Act) (t : WT) (s : Option Sym) : (a.ww t s).out = a.out := rfl
@[simp] theorem mi_out (a : Act) (j : IT) (m : SignType) : (a.mi j m).out = a.out := rfl
@[simp] theorem emit_out (a : Act) (s : Sym) : (a.emit s).out = some s := rfl

@[simp] theorem mw_inMoves (a : Act) (t : WT) (m : SignType) : (a.mw t m).inMoves = a.inMoves := rfl
@[simp] theorem ww_inMoves (a : Act) (t : WT) (s : Option Sym) : (a.ww t s).inMoves = a.inMoves := rfl
@[simp] theorem emit_inMoves (a : Act) (s : Sym) : (a.emit s).inMoves = a.inMoves := rfl
@[simp] theorem mi_inMoves (a : Act) (j : IT) (m : SignType) :
    (a.mi j m).inMoves = Function.update a.inMoves j m := rfl

@[simp] theorem mi_works (a : Act) (j : IT) (m : SignType) : (a.mi j m).works = a.works := rfl
@[simp] theorem emit_works (a : Act) (s : Sym) : (a.emit s).works = a.works := rfl

@[simp] theorem mw_works_self (a : Act) (t : WT) (m : SignType) :
    (a.mw t m).works t = ((a.works t).1, m) := by simp [mw]

theorem mw_works_of_ne (a : Act) {t t' : WT} (h : t' ≠ t) (m : SignType) :
    (a.mw t m).works t' = a.works t' := by simp [mw, Function.update_of_ne h]

@[simp] theorem ww_works_self (a : Act) (t : WT) (s : Option Sym) :
    (a.ww t s).works t = (some s, (a.works t).2) := by simp [ww]

theorem ww_works_of_ne (a : Act) {t t' : WT} (h : t' ≠ t) (s : Option Sym) :
    (a.ww t s).works t' = a.works t' := by simp [ww, Function.update_of_ne h]

end Act

end MIPRE.TM.Interp

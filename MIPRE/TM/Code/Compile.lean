/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.TM.Code.Semantics

/-!
# Compiling a finite machine to a machine code

`Turing.MultiInputTM.compile` turns an operational multi-input machine over the alphabet
`Fin σ` (with `2 ≤ σ`) and the state set `Fin Q` into a machine code, by tabulating its
transition function over every observation in the canonical order
(`Turing.decodeTransitionIndex`). When the machine emits only the two bit symbols `0` and
`1` — the output convention of machine codes — the interpretation of the compiled code is
the machine itself (`MultiInputTM.toTM_compile`). This is the bridge from machines written as
programs over structured state and symbol types (relabelled to `Fin` along
`MultiInputTM.congrState` and `MultiInputTM.congrSymbol`) to the codes of
`MIPRE.TM.Code`, which is what the universal machines of `MIPRE/TM/Universal/Spec.lean`
must be.
-/

namespace Turing

variable {i w σ Q : ℕ}

/-- A head movement as a `Move`. -/
def Move.ofSignType : SignType → Move
  | .neg => .left
  | .zero => .stay
  | .pos => .right

@[simp]
theorem Move.toSignType_ofSignType (s : SignType) : (Move.ofSignType s).toSignType = s := by
  cases s <;> rfl

/-- A work-tape write as a `RawWrite`: `none` keeps the cell, `some none` writes a blank and
`some (some a)` writes `a`. -/
def RawWrite.ofOption : Option (Option (Fin σ)) → RawWrite
  | none => .keep
  | some none => .blank
  | some (some a) => .symbol a.val

/-- A transition output as a raw table entry. -/
def RawAction.ofTransitionOut (t : MultiInputTM.TransitionOut i w (Fin σ) (Fin Q)) :
    RawAction where
  inputMoves := Array.ofFn fun j => Move.ofSignType (t.inputMoves j)
  workActions := Array.ofFn fun d =>
    { write := RawWrite.ofOption (t.workActions d).1, move := Move.ofSignType (t.workActions d).2 }
  output := t.outS.map fun s => decide (s.val = 1)
  nextState := t.q'.map Fin.val

namespace MultiInputTM

/-- The dense transition table of a machine over `Fin σ` and `Fin Q`, in the canonical order. -/
def table (tm : MultiInputTM i w (Fin σ) (Fin Q)) : Array RawAction :=
  Array.ofFn fun n : Fin (Q * (σ + 1) ^ (i + w)) =>
    RawAction.ofTransitionOut
      (tm.tr (decodeTransitionIndex n).1 (decodeTransitionIndex n).2.1
        (decodeTransitionIndex n).2.2)

/-- The raw code of a machine over `Fin σ` and `Fin Q`. -/
def rawCode (tm : MultiInputTM i w (Fin σ) (Fin Q)) : RawCode i where
  workTapeCount := w
  alphabetSize := σ
  stateCount := Q
  startState := tm.q₀.val
  table := tm.table

theorem rawCode_wellFormed (tm : MultiInputTM i w (Fin σ) (Fin Q)) (hσ : 2 ≤ σ) :
    (rawCode tm).WellFormed := by
  refine ⟨hσ, Nat.lt_of_le_of_lt (Nat.zero_le _) tm.q₀.isLt, tm.q₀.isLt, ?_, ?_⟩
  · simp [rawCode, table]
  · intro a ha
    simp only [rawCode, table, Array.mem_ofFn] at ha
    obtain ⟨n, rfl⟩ := ha
    refine ⟨by simp [RawAction.ofTransitionOut], by simp [RawAction.ofTransitionOut, rawCode],
      ?_, ?_⟩
    · intro wa hwa s hs
      simp only [RawAction.ofTransitionOut, Array.mem_ofFn] at hwa
      obtain ⟨d, rfl⟩ := hwa
      revert hs
      rcases (tm.tr _ _ _).workActions d with ⟨_ | _ | a, _⟩ <;>
        simp [RawWrite.ofOption]
      rintro rfl
      exact a.isLt
    · intro q hq
      simp only [RawAction.ofTransitionOut, Option.mem_def, Option.map_eq_some_iff] at hq
      obtain ⟨q', -, rfl⟩ := hq
      exact q'.isLt

/-- **The compiled code** of a machine over `Fin σ` and `Fin Q`, for `2 ≤ σ`. -/
def compile (tm : MultiInputTM i w (Fin σ) (Fin Q)) (hσ : 2 ≤ σ) : Code i :=
  ⟨rawCode tm, rawCode_wellFormed tm hσ⟩

@[simp] theorem compile_workTapeCount (tm : MultiInputTM i w (Fin σ) (Fin Q)) (hσ : 2 ≤ σ) :
    (compile tm hσ).workTapeCount = w := rfl

@[simp] theorem compile_alphabetSize (tm : MultiInputTM i w (Fin σ) (Fin Q)) (hσ : 2 ≤ σ) :
    (compile tm hσ).alphabetSize = σ := rfl

@[simp] theorem compile_stateCount (tm : MultiInputTM i w (Fin σ) (Fin Q)) (hσ : 2 ≤ σ) :
    (compile tm hσ).stateCount = Q := rfl

/-- The table entry of the compiled code at an observation is the encoded transition. -/
theorem compile_actionAt (tm : MultiInputTM i w (Fin σ) (Fin Q)) (hσ : 2 ≤ σ) (q : Fin Q)
    (as : Fin i → Option (Fin σ)) (bs : Fin w → Option (Fin σ)) :
    (compile tm hσ).actionAt q as bs = RawAction.ofTransitionOut (tm.tr q as bs) := by
  simp [Code.actionAt, compile, rawCode, table]

/-- A machine emits only bits: every emitted symbol is `0` or `1`. -/
def EmitsBits (tm : MultiInputTM i w (Fin σ) (Fin Q)) : Prop :=
  ∀ q as bs s, (tm.tr q as bs).outS = some s → s.val < 2

/-- Interpreting an encoded transition recovers it, when it emits only bits. -/
theorem interpretAction_ofTransitionOut (tm : MultiInputTM i w (Fin σ) (Fin Q)) (hσ : 2 ≤ σ)
    (t : TransitionOut i w (Fin σ) (Fin Q)) (hbits : ∀ s, t.outS = some s → s.val < 2)
    (h₁ h₂ h₃ h₄) :
    (compile tm hσ).interpretAction (RawAction.ofTransitionOut t) h₁ h₂ h₃ h₄ = t := by
  apply MultiInputTM.TransitionOut.ext
  · funext j
    simp [Code.interpretAction, RawAction.ofTransitionOut]
  · funext d
    simp only [Code.interpretAction]
    have hd : ((RawAction.ofTransitionOut t).workActions[d.val]'(by rw [h₂]; exact d.isLt)) =
        { write := RawWrite.ofOption (t.workActions d).1,
          move := Move.ofSignType (t.workActions d).2 } := by
      simp only [RawAction.ofTransitionOut, Array.getElem_ofFn]
      rfl
    split
    next hw =>
      rw [hd] at hw
      rcases hwd : t.workActions d with ⟨_ | _ | a, m⟩ <;>
        simp_all [RawWrite.ofOption]
      rfl
    next hw =>
      rw [hd] at hw
      rcases hwd : t.workActions d with ⟨_ | _ | a, m⟩ <;>
        simp_all [RawWrite.ofOption]
      rfl
    next s' hw =>
      rw [hd] at hw
      rcases hwd : t.workActions d with ⟨_ | _ | a, m⟩ <;>
        simp_all [RawWrite.ofOption]
      subst_vars
      rfl
  · simp only [Code.interpretAction, RawAction.ofTransitionOut, Option.map_map]
    cases ho : t.outS with
    | none => rfl
    | some s =>
      have hs := hbits s ho
      simp only [Option.map_some]
      congr 1
      apply Fin.ext
      show (if decide (s.val = 1) = true then 1 else 0) = s.val
      by_cases h : s.val = 1
      · simp [h]
      · simp [h]; omega
  · simp only [Code.interpretAction, RawAction.ofTransitionOut]
    split
    next heq => exact (Option.map_eq_none_iff.mp heq).symm
    next q' heq =>
      obtain ⟨q'', hq'', rfl⟩ := Option.map_eq_some_iff.mp heq
      exact hq''.symm

/-- The compiled code's transition function is the machine's, when the machine emits only
bits. -/
theorem toTM_compile_tr (tm : MultiInputTM i w (Fin σ) (Fin Q)) (hσ : 2 ≤ σ)
    (hbits : tm.EmitsBits) (q : Fin Q) (as : Fin i → Option (Fin σ))
    (bs : Fin w → Option (Fin σ)) : (compile tm hσ).toTM.tr q as bs = tm.tr q as bs := by
  have key : ∀ (a : RawAction), a = RawAction.ofTransitionOut (tm.tr q as bs) →
      ∀ h₁ h₂ h₃ h₄, (compile tm hσ).interpretAction a h₁ h₂ h₃ h₄ = tm.tr q as bs := by
    rintro a rfl h₁ h₂ h₃ h₄
    exact interpretAction_ofTransitionOut tm hσ _ (hbits q as bs) h₁ h₂ h₃ h₄
  exact key _ (compile_actionAt tm hσ q as bs) Code.actionAt_inputMoves_size
    Code.actionAt_workActions_size (fun _ hwa _ hs => Code.actionAt_write_lt hwa hs)
    (fun _ hq' => Code.actionAt_nextState_lt hq')

/-- **The compiled code denotes the machine**, for a machine that emits only bits. -/
theorem toTM_compile (tm : MultiInputTM i w (Fin σ) (Fin Q)) (hσ : 2 ≤ σ)
    (hbits : tm.EmitsBits) : (compile tm hσ).toTM = tm := by
  have htr := toTM_compile_tr tm hσ hbits
  obtain ⟨q₀, tr⟩ := tm
  unfold Code.toTM
  congr 1
  funext q as bs
  exact htr q as bs

end MultiInputTM

end Turing

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.TM.Code.WellFormed
import MIPRE.TM.MultiInput.Complexity

/-!
# Interpretation of machine codes

`Code.toTM` interprets a well-formed machine code as an operational multi-input Turing
machine (`MIPRE.TM.MultiInput.Deterministic`) over the alphabet `Fin alphabetSize` and
state set `Fin stateCount`: the transition function looks up the dense table at the
canonical position (`Code.actionAt`) and converts the raw entry into a transition output
(`Code.interpretAction`), with every range fact supplied by well-formedness through the
`Code.actionAt_*` lemmas. `Code.toTM_tr` records that this is definitional.

The machine code is the primary object and `toTM` its interpretation — never the other
way around. Everything here is executable: no `Fintype.elems`, no choice, no
`noncomputable` (`planning/tm-infrastructure.md`, decision D5 and Milestone B).

Bit-level input/output: coded machines read and write the reserved symbols `0`/`1`
(`Code.bitEmbedding`, `Code.bitInputs`); every symbol they emit is one of the two bit
symbols (`Code.outputSymbol_isBit`), so decoding outputs as bit strings
(`Code.decodeBitOutput`) is total and faithful
(`Code.decodeBitOutput_map_bitEmbedding`).
-/

namespace Turing.Code

variable {i : ℕ}

/-- The alphabet of a coded machine. -/
protected abbrev Symbol (c : Code i) : Type := Fin c.alphabetSize

/-- The state set of a coded machine. -/
protected abbrev State (c : Code i) : Type := Fin c.stateCount

/-- The two reserved I/O symbols of a coded machine: `false ↦ 0`, `true ↦ 1` (the
alphabet has size at least two by well-formedness). -/
def bitEmbedding (c : Code i) : Bool ↪ c.Symbol where
  toFun b := ⟨if b then 1 else 0, by
    have h : 2 ≤ c.alphabetSize := c.wf.two_le_alphabetSize
    cases b <;> simp <;> omega⟩
  inj' a b h := by
    cases a <;> cases b <;> simp_all [Fin.mk.injEq]

/-- Present a tuple of bit strings as input strings over the machine alphabet. -/
def bitInputs (c : Code i) (x : Fin i → List Bool) : Fin i → List c.Symbol :=
  fun j => (x j).map fun b => c.bitEmbedding b

/-- Interpret one table entry as a transition output, given the well-formedness facts
for that entry: input moves and work actions are read off positionally, written symbols
and successor states are cast into `Fin` using their range facts, and the output bit is
embedded as a reserved I/O symbol. -/
def interpretAction (c : Code i) (a : RawAction)
    (hmoves : a.inputMoves.size = i)
    (hworks : a.workActions.size = c.workTapeCount)
    (hwrite : ∀ wa ∈ a.workActions, ∀ s, wa.write = .symbol s → s < c.alphabetSize)
    (hnext : ∀ q' ∈ a.nextState, q' < c.stateCount) :
    MultiInputTM.TransitionOut i c.workTapeCount c.Symbol c.State where
  inputMoves j := (a.inputMoves[j.val]'(by rw [hmoves]; exact j.isLt)).toSignType
  workActions d :=
    (match hw : (a.workActions[d.val]'(by rw [hworks]; exact d.isLt)).write with
      | .keep => none
      | .blank => some none
      | .symbol s => some (some ⟨s, hwrite _ (Array.getElem_mem _) s hw⟩),
     (a.workActions[d.val]'(by rw [hworks]; exact d.isLt)).move.toSignType)
  outS := a.output.map fun b => c.bitEmbedding b
  q' :=
    match hq : a.nextState with
    | none => none
    | some q' => some ⟨q', hnext q' (by simp [hq])⟩

/-- The operational machine denoted by a code: start in the coded start state, and
transition by looking up the dense table at the canonical position. -/
def toTM (c : Code i) : MultiInputTM i c.workTapeCount c.Symbol c.State where
  q₀ := ⟨c.startState, c.wf.startState_lt⟩
  tr q as bs :=
    c.interpretAction (c.actionAt q as bs)
      Code.actionAt_inputMoves_size
      Code.actionAt_workActions_size
      (fun _wa hwa _s hs => Code.actionAt_write_lt hwa hs)
      (fun _q' hq' => Code.actionAt_nextState_lt hq')

@[simp]
theorem toTM_q₀ (c : Code i) : c.toTM.q₀ = ⟨c.startState, c.wf.startState_lt⟩ := rfl

/-- The transition function of `Code.toTM` is, definitionally, the interpretation of the
canonical table entry. -/
theorem toTM_tr (c : Code i) (q : c.State) (as : Fin i → Option c.Symbol)
    (bs : Fin c.workTapeCount → Option c.Symbol) :
    c.toTM.tr q as bs =
      c.interpretAction (c.actionAt q as bs)
        Code.actionAt_inputMoves_size
        Code.actionAt_workActions_size
        (fun _wa hwa _s hs => Code.actionAt_write_lt hwa hs)
        (fun _q' hq' => Code.actionAt_nextState_lt hq') := rfl

@[simp]
theorem interpretAction_outS (c : Code i) (a : RawAction) (h₁ h₂ h₃ h₄) :
    (c.interpretAction a h₁ h₂ h₃ h₄).outS = a.output.map fun b => c.bitEmbedding b := rfl

/-- The emitted symbol of a coded transition, at the level of raw data. -/
@[simp]
theorem toTM_tr_outS (c : Code i) (q : c.State) (as : Fin i → Option c.Symbol)
    (bs : Fin c.workTapeCount → Option c.Symbol) :
    (c.toTM.tr q as bs).outS =
      (c.actionAt q as bs).output.map fun b => c.bitEmbedding b := rfl

/-- The successor state of a coded transition, at the level of raw data. -/
theorem interpretAction_q'_map_val (c : Code i) (a : RawAction) (h₁ h₂ h₃ h₄) :
    ((c.interpretAction a h₁ h₂ h₃ h₄).q').map Fin.val = a.nextState := by
  simp only [interpretAction]
  split <;> simp_all

/-- The successor state of `Code.toTM`, at the level of raw data. -/
theorem toTM_tr_q'_map_val (c : Code i) (q : c.State) (as : Fin i → Option c.Symbol)
    (bs : Fin c.workTapeCount → Option c.Symbol) :
    ((c.toTM.tr q as bs).q').map Fin.val = (c.actionAt q as bs).nextState :=
  interpretAction_q'_map_val c (c.actionAt q as bs)
    Code.actionAt_inputMoves_size
    Code.actionAt_workActions_size
    (fun _wa hwa _s hs => Code.actionAt_write_lt hwa hs)
    (fun _q' hq' => Code.actionAt_nextState_lt hq')

/-- A coded machine halts on an observation exactly when the table entry says to. -/
theorem toTM_tr_q'_eq_none_iff (c : Code i) (q : c.State) (as : Fin i → Option c.Symbol)
    (bs : Fin c.workTapeCount → Option c.Symbol) :
    (c.toTM.tr q as bs).q' = none ↔ (c.actionAt q as bs).nextState = none := by
  rw [← toTM_tr_q'_map_val]
  cases (c.toTM.tr q as bs).q' <;> simp

/-- Every symbol a coded machine emits is one of the two reserved bit symbols. -/
theorem outputSymbol_isBit (c : Code i) {input : Fin i → List c.Symbol}
    (cfg : MultiInputTM.Cfg i c.workTapeCount c.Symbol c.State input) :
    c.toTM.outputSymbol cfg = none ∨
      ∃ b : Bool, c.toTM.outputSymbol cfg = some (c.bitEmbedding b) := by
  cases hst : cfg.state with
  | none => exact Or.inl (MultiInputTM.outputSymbol_of_halt hst)
  | some q =>
    have h : c.toTM.outputSymbol cfg =
        ((c.actionAt q cfg.inputSymbols cfg.workTapeSymbols).output).map
          fun b => c.bitEmbedding b := by
      simp only [MultiInputTM.outputSymbol, hst, toTM_tr_outS]
    cases ho : (c.actionAt q cfg.inputSymbols cfg.workTapeSymbols).output with
    | none => exact Or.inl (by rw [h, ho]; rfl)
    | some b => exact Or.inr ⟨b, by rw [h, ho]; rfl⟩

/-- Decode a machine-alphabet string as a bit string: symbol `1` is `true`, every other
symbol is `false`. On outputs of coded machines this is faithful, because only the two
bit symbols are ever emitted (`Code.outputSymbol_isBit`). -/
def decodeBitOutput (c : Code i) (l : List c.Symbol) : List Bool :=
  l.map fun s => s.val == 1

@[simp]
theorem decodeBitOutput_map_bitEmbedding (c : Code i) (l : List Bool) :
    c.decodeBitOutput (l.map fun b => c.bitEmbedding b) = l := by
  have h : ∀ b : Bool, ((c.bitEmbedding b).val == 1) = b := by
    intro b
    cases b <;> simp [bitEmbedding]
  simp [decodeBitOutput, List.map_map, Function.comp_def, h]

end Turing.Code

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.TM.CookLevin.Tableau

/-!
# The windows of a run are locally consistent

`localCfgOf M acc c js` is the local configuration read off a configuration `c` and its
successor at the window `js`; its encoding is the assignment of the run on the window's
variables (`encode_localCfgOf`), and it is locally consistent
(`locallyConsistent_localCfgOf`): the completeness half of the tableau's correctness
(`planning/succinct-cook-levin.md`, S1). The proof is the case analysis of the paper's
`lem:correct-tableau` on where the heads are, with the clamping of the input heads
(`Turing.moveInputPos`) matched against the tableau's rule (`newOffset`).
-/

namespace MIPRE.TM.CookLevin

open Turing SAT MultiInputTM
open MultiTapeTM (moveInputPos)

section

variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}

/-! ## Positions -/

@[simp] theorem cellIdx_val (c : Center S) (δ : Fin 5) : ((cellIdx c δ : Pos S) : ℕ) = c + δ := rfl

@[simp] theorem center_val (c : Center S) : ((center c : Pos S) : ℕ) = c + 2 := rfl

theorem cellIdx_injective (c : Center S) : Function.Injective (cellIdx c) := by
  intro δ δ' h
  have := congrArg (fun p : Pos S => (p : ℕ)) h
  simp only [cellIdx_val] at this
  exact Fin.ext (by omega)

theorem not_isBdry_iff (p : Pos S) : ¬ p.IsBdry ↔ 2 ≤ (p : ℕ) ∧ (p : ℕ) + 2 < numCells S := by
  unfold Pos.IsBdry; omega

/-! ## The local configuration of a run -/

variable (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}

/-- The local configuration of a configuration and its successor at the window `js`. -/
def localCfgOf (c : Cfg i w Symbol State input) (js : Tape i w → Center S) :
    LocalCfg i w Symbol State where
  cellPre d δ := cellValAt (S := S) c d (cellIdx (js d) δ)
  headPre d δ := decide (headCell (S := S) c d = cellIdx (js d) δ)
  cellPost d := cellValAt (S := S) (M.step c) d (center (js d))
  headPost d := decide (headCell (S := S) (M.step c) d = center (js d))
  statePre := c.state
  statePost := (M.step c).state
  emitOne := decide (M.outputSymbol c = some acc)
  emitBad := decide (M.outputSymbol c ≠ none ∧ M.outputSymbol c ≠ some acc)

omit [Fintype Symbol] [DecidableEq Symbol] [Fintype State] [DecidableEq State] in
theorem cfgAt_succ (t : ℕ) : cfgAt M (input := input) (t + 1) = M.step (cfgAt M t) :=
  configs_succ_eq_step'

/-- The encoding of the local configuration of the run at `(t, js)` is the run's assignment
on the window's variables. -/
theorem encode_localCfgOf (G : ℕ) (t : Fin S) (js : Tape i w → Center S)
    (v : WinVar i w Symbol State) :
    (localCfgOf M acc (cfgAt M (input := input) t) js).encode v =
      baseAssign M acc (input := input) G (winVarOf (G := G) t js v) := by
  have hs : cfgAt M (input := input) ((t : ℕ) + 1) = M.step (cfgAt M t) := cfgAt_succ M t
  cases v <;> simp [LocalCfg.encode, localCfgOf, winVarOf, baseAssign, hs, Fin.val_castSucc,
    Fin.val_succ]

/-! ## Heads -/

/-- The head of tape `d` is in the window at offset `δ` iff its cell is that cell. -/
theorem headPre_localCfgOf (c : Cfg i w Symbol State input) (js : Tape i w → Center S)
    (d : Tape i w) (δ : Fin 5) :
    (localCfgOf M acc c js).headPre d δ = true ↔
      headCell (S := S) c d = ((cellIdx (js d) δ : Pos S) : ℕ) := by
  simp [localCfgOf]

theorem headAt_localCfgOf (c : Cfg i w Symbol State input) (js : Tape i w → Center S)
    (d : Tape i w) (δ : Fin 5) (h : headCell (S := S) c d = ((cellIdx (js d) δ : Pos S) : ℕ)) :
    (localCfgOf M acc c js).HeadAt d δ := by
  intro δ'
  simp only [localCfgOf, cellIdx_val, h]
  by_cases hδ : δ' = δ
  · subst hδ; simp
  · have : (js d : ℕ) + (δ : ℕ) ≠ (js d : ℕ) + (δ' : ℕ) := by
      intro e; exact hδ (Fin.ext (by omega)).symm
    simp [this, hδ]
    push_cast; omega

/-- No two heads of a tape in a window of a run. -/
theorem not_twoHeads_localCfgOf (c : Cfg i w Symbol State input) (js : Tape i w → Center S)
    (d : Tape i w) : ¬ (localCfgOf M acc c js).TwoHeads d := by
  rintro ⟨δ, δ', hne, h, h'⟩
  rw [headPre_localCfgOf] at h h'
  exact hne (cellIdx_injective (js d) (Fin.ext (by simp only [cellIdx_val] at h h' ⊢; omega)))

/-! ## The step, componentwise -/

omit [Fintype Symbol] [Fintype State] [DecidableEq State] in
theorem step_state (c : Cfg i w Symbol State input) {q : State} (hst : c.state = some q) :
    (M.step c).state = (M.tr q c.inputSymbols c.workTapeSymbols).q' := by
  unfold step; rw [hst]

omit [Fintype Symbol] [Fintype State] [DecidableEq State] in
theorem step_inputPos (c : Cfg i w Symbol State input) {q : State} (hst : c.state = some q)
    (j : Fin i) : (M.step c).inputPos j =
      moveInputPos (c.inputPos j) ((M.tr q c.inputSymbols c.workTapeSymbols).inputMoves j) := by
  unfold step; rw [hst]

omit [Fintype Symbol] [Fintype State] [DecidableEq State] in
theorem step_workTapePos (c : Cfg i w Symbol State input) {q : State} (hst : c.state = some q)
    (j : Fin w) : (M.step c).workTapePos j =
      c.workTapePos j + ((M.tr q c.inputSymbols c.workTapeSymbols).workActions j).2 := by
  unfold step; rw [hst]

omit [Fintype Symbol] [Fintype State] [DecidableEq State] in
theorem step_workTapes (c : Cfg i w Symbol State input) {q : State} (hst : c.state = some q)
    (j : Fin w) : (M.step c).workTapes j =
      match ((M.tr q c.inputSymbols c.workTapeSymbols).workActions j).1 with
      | none => c.workTapes j
      | some s => Function.update (c.workTapes j) (c.workTapePos j) s := by
  unfold step; rw [hst]; rfl

omit [Fintype Symbol] [DecidableEq Symbol] [Fintype State] [DecidableEq State] in
theorem moveInputPos_sub_le {n : ℕ} (p : Fin (n + 2)) (m : SignType) :
    -1 ≤ ((moveInputPos p m : ℕ) : ℤ) - (p : ℤ) ∧ ((moveInputPos p m : ℕ) : ℤ) - (p : ℤ) ≤ 1 := by
  have hp := p.isLt
  unfold moveInputPos
  dsimp only
  split_ifs with h <;> cases m <;> simp only [SignType.cast, Fin.val_mk] at h ⊢ <;> omega

/-- A head moves by at most one cell in a step. -/
theorem headCell_step_le (c : Cfg i w Symbol State input) (d : Tape i w) :
    -1 ≤ headCell (S := S) (M.step c) d - headCell (S := S) c d ∧
      headCell (S := S) (M.step c) d - headCell (S := S) c d ≤ 1 := by
  cases hst : c.state with
  | none => rw [step_of_halt hst]; omega
  | some q =>
    cases d with
    | inl j =>
      simp only [headCell, step_inputPos M c hst]
      have := moveInputPos_sub_le (c.inputPos j)
        ((M.tr q c.inputSymbols c.workTapeSymbols).inputMoves j)
      omega
    | inr j =>
      simp only [headCell, step_workTapePos M c hst]
      cases ((M.tr q c.inputSymbols c.workTapeSymbols).workActions j).2 <;>
        simp [SignType.cast]

/-- A tape whose head is not near the center keeps its center cell and has no head there
after the step. -/
theorem far_localCfgOf (c : Cfg i w Symbol State input) (js : Tape i w → Center S) (d : Tape i w)
    (hfar : (localCfgOf M acc c js).HeadFar d) :
    (localCfgOf M acc c js).cellPost d = (localCfgOf M acc c js).cellPre d 2 ∧
      (localCfgOf M acc c js).headPost d = false := by
  obtain ⟨h1, h2, h3⟩ := hfar
  simp only [localCfgOf, decide_eq_false_iff_not, cellIdx_val, Fin.val_one, Fin.val_two,
    show ((3 : Fin 5) : ℕ) = 3 from rfl, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at h1 h2 h3
  have hstep := headCell_step_le (S := S) M c d
  have hne : headCell (S := S) (M.step c) d ≠ ((center (js d) : Pos S) : ℕ) := by
    simp only [center_val, Nat.cast_add, Nat.cast_ofNat]; omega
  refine ⟨?_, by simpa [localCfgOf] using hne⟩
  simp only [localCfgOf, center]
  cases d with
  | inl j => rfl
  | inr j =>
    simp only [cellValAt]
    split_ifs with hb
    · rfl
    · congr 1
      cases hst : c.state with
      | none => rw [step_of_halt hst]
      | some q =>
        rw [step_workTapes M c hst]
        cases ((M.tr q c.inputSymbols c.workTapeSymbols).workActions j).1 with
        | none => rfl
        | some s =>
          simp only
          rw [Function.update_of_ne]
          simp only [headCell] at h2
          simp only [cellIdx_val, Fin.val_two, Nat.cast_add, Nat.cast_ofNat]
          omega

end

end MIPRE.TM.CookLevin

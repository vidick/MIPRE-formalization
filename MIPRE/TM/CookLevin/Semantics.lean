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
open MultiTapeTM (moveInputPos moveInputPos_zero moveInputPos_neg_of_ne_left
  moveInputPos_pos_of_ne_right)

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

/-! ## The cells under the heads -/

omit [Fintype Symbol] [Fintype State] [DecidableEq State] in
/-- An interior input cell: the symbol of the input at index `p - 3`, if any, else a blank. -/
theorem inputCellVal_eq (x : List Symbol) (p : Pos S) (hnb : ¬ p.IsBdry) :
    inputCellVal x p =
      if 3 ≤ (p : ℕ) then
        (match x[(p : ℕ) - 3]? with
          | some s => CellVal.sym s
          | none => CellVal.blank)
      else .blank := by
  unfold inputCellVal
  rw [if_neg hnb]
  by_cases h3 : 3 ≤ (p : ℕ)
  · rw [if_pos h3]
    by_cases hl : (p : ℕ) - 3 < x.length
    · rw [dif_pos ⟨h3, hl⟩, List.getElem?_eq_getElem hl]
    · rw [dif_neg (fun h => hl h.2), List.getElem?_eq_none (by omega)]
  · rw [if_neg h3, dif_neg (fun h => h3 h.1)]

omit [Fintype Symbol] [Fintype State] [DecidableEq State] in
theorem inputCellVal_ne_bdry (x : List Symbol) (p : Pos S) (hnb : ¬ p.IsBdry) :
    inputCellVal x p ≠ .bdry := by
  unfold inputCellVal
  rw [if_neg hnb]
  split_ifs <;> simp

omit [Fintype Symbol] [Fintype State] [DecidableEq State] in
theorem inputCellVal_bdry_iff (x : List Symbol) (p : Pos S) :
    inputCellVal x p = .bdry ↔ p.IsBdry := by
  unfold inputCellVal
  split_ifs <;> simp_all

omit [Fintype Symbol] [Fintype State] [DecidableEq State] in
/-- The symbol under an input head is the cell of the tableau at the head's cell. -/
theorem toOpt_inputCellVal_headCell (c : Cfg i w Symbol State input) (j : Fin i) (p : Pos S)
    (hp : (p : ℕ) = (c.inputPos j : ℕ) + 2) (hnb : ¬ p.IsBdry) :
    (inputCellVal (input j) p).toOpt = c.inputSymbol j := by
  have hlt := (c.inputPos j).isLt
  rw [inputCellVal_eq (input j) p hnb]
  unfold Cfg.inputSymbol
  by_cases h0 : c.inputPos j = 0
  · have h0' : (c.inputPos j : ℕ) = 0 := by rw [h0]; rfl
    rw [dif_pos h0, if_neg (by omega)]
    rfl
  · have h0' : (c.inputPos j : ℕ) ≠ 0 := fun h => h0 (Fin.ext h)
    rw [dif_neg h0, if_pos (by omega)]
    have hidx : (p : ℕ) - 3 = (c.inputPos j : ℕ) - 1 := by omega
    rw [hidx]
    -- `c.inputPos j = (input j).length + 1` is an equality in `ℕ`, the coercion going left
    by_cases h1 : c.inputPos j = (input j).length + 1
    · rw [dif_pos h1, List.getElem?_eq_none (by omega)]
      rfl
    · rw [dif_neg h1, List.getElem?_eq_getElem (by omega)]
      rfl

omit [Fintype Symbol] [Fintype State] [DecidableEq State] in
theorem cellValAt_inr (c : Cfg i w Symbol State input) (j : Fin w) (p : Pos S) (hnb : ¬ p.IsBdry) :
    cellValAt (S := S) c (.inr j) p = .ofOpt (c.workTapes j ((p : ℤ) - (S + 3))) := by
  simp [cellValAt, hnb]

/-! ## Head positions -/

/-- The bounds under which every head is on an interior cell; they hold at every time
`t ≤ S` of a run (`headsIn_cfgAt`), since a head moves at most one position per step. -/
structure HeadsIn (c : Cfg i w Symbol State input) (S : ℕ) : Prop where
  input_pos : ∀ j, (c.inputPos j : ℕ) ≤ 2 * S + 2
  work_pos : ∀ j, -(S : ℤ) ≤ c.workTapePos j ∧ c.workTapePos j ≤ S

omit [Fintype Symbol] [Fintype State] [DecidableEq State] in
theorem HeadsIn.headCell_bounds {c : Cfg i w Symbol State input} (h : HeadsIn c S) (d : Tape i w) :
    2 ≤ headCell (S := S) c d ∧ headCell (S := S) c d + 2 < numCells S := by
  have hnc : numCells S = 2 * S + 7 := rfl
  cases d with
  | inl j =>
    have := h.input_pos j
    simp only [headCell]; omega
  | inr j =>
    have := h.work_pos j
    simp only [headCell]; omega

/-! ## The full step -/

omit [Fintype Symbol] [DecidableEq Symbol] [Fintype State] [DecidableEq State] in
theorem moveInputPos_neg_zero {n : ℕ} : moveInputPos (0 : Fin (n + 2)) .neg = 0 := by
  apply Fin.ext
  simp [moveInputPos, SignType.cast]

omit [Fintype Symbol] [DecidableEq Symbol] [Fintype State] [DecidableEq State] in
theorem moveInputPos_pos_right {n : ℕ} (p : Fin (n + 2)) (h : (p : ℕ) = n + 1) :
    moveInputPos p .pos = p := by
  apply Fin.ext
  unfold moveInputPos
  rw [dif_neg (by simp [SignType.cast]; omega)]
  simp [h]

/-- When every head is at an offset `1..3`, the local configuration of the run satisfies the
full transition check. -/
theorem fullStep_localCfgOf (c : Cfg i w Symbol State input) (js : Tape i w → Center S)
    (hin : HeadsIn c S) (δ : Tape i w → Fin 5)
    (hδ : ∀ d, 1 ≤ (δ d : ℕ) ∧ (δ d : ℕ) ≤ 3 ∧ (localCfgOf M acc c js).HeadAt d (δ d)) :
    FullStep M acc (localCfgOf M acc c js) δ := by
  -- the head of every tape is at the cell `js d + δ d`
  have hhead : ∀ d, headCell (S := S) c d = (js d : ℤ) + (δ d : ℕ) := by
    intro d
    have h := (hδ d).2.2 (δ d)
    simp only [localCfgOf, cellIdx_val, eq_self_iff_true, decide_true] at h
    have h' := of_decide_eq_true h
    push_cast at h'
    exact h'
  have hbd := fun d => hin.headCell_bounds (S := S) d
  cases hst : c.state with
  | none =>
    simp only [FullStep, localCfgOf, hst]
    refine ⟨fun d => ?_, fun d => ?_, ?_, ?_, ?_⟩
    · rw [step_of_halt hst]; rfl
    · rw [step_of_halt hst]; rfl
    · rw [step_of_halt hst, hst]
    · simp [outputSymbol, hst]
    · simp [outputSymbol, hst]
  | some q =>
    simp only [FullStep, localCfgOf, hst]
    have hnb : ∀ d, ¬ (cellIdx (js d) (δ d) : Pos S).IsBdry := by
      intro d
      rw [not_isBdry_iff]
      have := hbd d
      have := hhead d
      simp only [cellIdx_val]; push_cast at *; omega
    -- the cells under the heads carry the symbols the machine reads
    have hcell_in : ∀ j, (cellValAt (S := S) c (.inl j) (cellIdx (js (.inl j)) (δ (.inl j)))).toOpt =
        c.inputSymbol j := by
      intro j
      have := hhead (.inl j)
      simp only [headCell] at this
      exact toOpt_inputCellVal_headCell c j _ (by simp only [cellIdx_val]; push_cast at this; omega)
        (hnb (.inl j))
    have hcell_wk : ∀ j, (cellValAt (S := S) c (.inr j) (cellIdx (js (.inr j)) (δ (.inr j)))).toOpt =
        c.workTapeSymbols j := by
      intro j
      rw [cellValAt_inr c j _ (hnb _), CellVal.toOpt_ofOpt]
      have := hhead (.inr j)
      simp only [headCell, cellIdx_val] at this
      simp only [Cfg.workTapeSymbols]
      congr 1
      simp only [cellIdx_val]
      push_cast at this ⊢; omega
    have hin' : (fun j => (cellValAt (S := S) c (.inl j) (cellIdx (js (.inl j)) (δ (.inl j)))).toOpt) =
        c.inputSymbols := funext hcell_in
    have hwk' : (fun j => (cellValAt (S := S) c (.inr j) (cellIdx (js (.inr j)) (δ (.inr j)))).toOpt) =
        c.workTapeSymbols := funext hcell_wk
    refine ⟨fun d => ?_, ?_⟩
    · -- no head on a boundary cell
      cases d with
      | inl j => exact inputCellVal_ne_bdry _ _ (hnb _)
      | inr j => rw [cellValAt_inr c j _ (hnb _)]; cases c.workTapes j _ <;> simp [CellVal.ofOpt]
    simp only [hin', hwk']
    have hcnb : ∀ d, ¬ (center (js d) : Pos S).IsBdry := by
      intro d; rw [not_isBdry_iff]; have := (js d).isLt; have hnc : numCells S = 2 * S + 7 := rfl
      simp only [center_val]; omega
    refine ⟨fun j => rfl, fun j => ?_, fun j => ?_, fun j => ?_, step_state M c hst, ?_, ?_⟩
    · -- work cells
      rw [cellValAt_inr _ j _ (hcnb _), step_workTapes M c hst,
        cellValAt_inr c j (cellIdx (js (.inr j)) 2) (hcnb (.inr j))]
      have hh := hhead (.inr j)
      simp only [headCell] at hh
      by_cases h2 : δ (.inr j) = 2
      · rw [if_pos h2]
        have hpos : ((center (js (.inr j)) : Pos S) : ℤ) - (S + 3) = c.workTapePos j := by
          simp only [center_val]; rw [h2] at hh; simp only [Fin.val_two] at hh; push_cast at hh ⊢; omega
        cases ((M.tr q c.inputSymbols c.workTapeSymbols).workActions j).1 with
        | none => rfl
        | some s =>
          simp only
          rw [hpos, Function.update_self]
      · rw [if_neg h2]
        cases ((M.tr q c.inputSymbols c.workTapeSymbols).workActions j).1 with
        | none => rfl
        | some s =>
          simp only
          have hne : ((center (js (.inr j)) : Pos S) : ℤ) - (S + 3) ≠ c.workTapePos j := by
            simp only [center_val]
            push_cast at hh ⊢
            intro he
            apply h2
            apply Fin.ext
            simp only [Fin.val_two]
            omega
          rw [Function.update_of_ne hne]
          rfl
    · -- input heads
      have hh := hhead (.inl j)
      simp only [headCell] at hh
      have hlt := (c.inputPos j).isLt
      have hlen := hin.input_pos j
      have h1 := (hδ (.inl j)).1
      have h3 := (hδ (.inl j)).2.1
      simp only [headCell, step_inputPos M c hst, center_val, newOffset, Tape.isInput, true_and]
      -- the neighbor cell and the head cell
      have hnbr : cellValAt (S := S) c (.inl j) (cellIdx (js (.inl j)) ⟨(δ (.inl j) : ℕ) - 1, by omega⟩) = .bdry ↔
          (c.inputPos j : ℕ) = 0 := by
        show inputCellVal (S := S) (input j) _ = .bdry ↔ _
        rw [inputCellVal_bdry_iff, Pos.IsBdry]
        have hnc : numCells S = 2 * S + 7 := rfl
        simp only [cellIdx_val]
        push_cast at hh; omega
      have hself : cellValAt (S := S) c (.inl j) (cellIdx (js (.inl j)) (δ (.inl j))) = .blank ↔
          ((c.inputPos j : ℕ) = 0 ∨ (c.inputPos j : ℕ) = (input j).length + 1) := by
        show inputCellVal (S := S) (input j) _ = .blank ↔ _
        rw [inputCellVal_eq _ _ (hnb (.inl j))]
        have hp : ((cellIdx (js (.inl j)) (δ (.inl j)) : Pos S) : ℕ) = (c.inputPos j : ℕ) + 2 := by
          simp only [cellIdx_val]; push_cast at hh; omega
        rw [hp]
        by_cases h0 : (c.inputPos j : ℕ) = 0
        · rw [if_neg (by omega)]; simp [h0]
        · rw [if_pos (by omega)]
          have hidx : (c.inputPos j : ℕ) + 2 - 3 = (c.inputPos j : ℕ) - 1 := by omega
          rw [hidx]
          by_cases h1 : (c.inputPos j : ℕ) = (input j).length + 1
          · rw [List.getElem?_eq_none (by omega)]; simp [h1]
          · rw [List.getElem?_eq_getElem (by omega)]; simp [h0, h1]
      cases hm : (M.tr q c.inputSymbols c.workTapeSymbols).inputMoves j with
      | zero =>
        have hz : moveInputPos (c.inputPos j) SignType.zero = c.inputPos j := moveInputPos_zero _
        rw [hz]
        apply decide_eq_decide.mpr
        push_cast at hh ⊢; omega
      | neg =>
        dsimp only
        by_cases h0 : c.inputPos j = 0
        · have h0' : (c.inputPos j : ℕ) = 0 := by rw [h0]; rfl
          rw [h0, moveInputPos_neg_zero, if_pos (hnbr.mpr h0')]
          apply decide_eq_decide.mpr
          simp only [Fin.val_zero]
          rw [h0'] at hh
          push_cast at hh ⊢; omega
        · have h0' : (c.inputPos j : ℕ) ≠ 0 := fun h => h0 (Fin.ext h)
          rw [moveInputPos_neg_of_ne_left _ h0, if_neg (fun h => h0' (hnbr.mp h))]
          apply decide_eq_decide.mpr
          push_cast at hh ⊢; omega
      | pos =>
        dsimp only
        by_cases hr : (c.inputPos j : ℕ) = (input j).length + 1
        · rw [moveInputPos_pos_right _ hr, if_pos ⟨hself.mpr (Or.inr hr), fun h => by
            have := hnbr.mp h; omega⟩]
          apply decide_eq_decide.mpr
          push_cast at hh ⊢; omega
        · rw [moveInputPos_pos_of_ne_right _ hr]
          rw [if_neg]
          · apply decide_eq_decide.mpr
            push_cast at hh ⊢; omega
          · rintro ⟨hb, hnb'⟩
            rcases hself.mp hb with h0 | h0
            · exact hnb' (hnbr.mpr h0)
            · exact hr h0
    · -- work heads
      have hh := hhead (.inr j)
      simp only [headCell] at hh
      simp only [headCell, step_workTapePos M c hst, center_val, newOffset, Tape.isInput, false_and,
        if_false]
      cases ((M.tr q c.inputSymbols c.workTapeSymbols).workActions j).2 <;>
        simp only [SignType.cast, Tape.isInput, Bool.false_eq_true, false_and, if_false] <;>
        apply decide_eq_decide.mpr <;> push_cast at hh ⊢ <;> omega
    · simp [outputSymbol, hst]
    · simp [outputSymbol, hst]

/-- **The windows of a run are locally consistent.** -/
theorem locallyConsistent_localCfgOf (c : Cfg i w Symbol State input) (js : Tape i w → Center S)
    (hin : HeadsIn c S) : LocallyConsistent M acc (localCfgOf M acc c js) := by
  classical
  refine Or.inr ⟨fun d hfar => far_localCfgOf M acc c js d hfar, ?_⟩
  by_cases hall : ∀ d, ∃ δ : Fin 5, 1 ≤ (δ : ℕ) ∧ (δ : ℕ) ≤ 3 ∧ (localCfgOf M acc c js).HeadAt d δ
  · choose δ hδ using hall
    exact Or.inl ⟨δ, hδ, fullStep_localCfgOf M acc c js hin δ hδ⟩
  · exact Or.inr hall

end

end MIPRE.TM.CookLevin

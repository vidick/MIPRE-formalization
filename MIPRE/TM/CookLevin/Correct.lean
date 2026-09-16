/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.TM.CookLevin.Semantics

/-!
# Correctness of the Cook–Levin tableau

The tableau formula of `S` steps of a machine `M` (`tableau`) is satisfiable, with the fixed
input tapes holding their strings, iff `M` accepts some completion of the free input tapes
within `S` steps (`planning/succinct-cook-levin.md`, S1; `answer_reduction.tex`
`lem:correct-tableau`). Acceptance is `AcceptsIn`: halted at time `S` with output string
exactly `[acc]`.

* **Completeness** (`tableau_sat_of_acceptsIn`): the assignment of an accepting run
  (`runAssign`) satisfies every clause; the window clauses because the windows of a run are
  locally consistent (`locallyConsistent_localCfgOf`) and the check circuit computes local
  consistency, its specification being the hypothesis `hchk`.
* **Soundness** (`acceptsIn_of_tableau_sat`): a satisfying assignment determines the free
  input strings from its time-`0` rows, and its rows encode the configurations of the run on
  those inputs, by induction on time: at each step the window clauses force, through the
  check circuit, local consistency of every window, and a locally consistent window whose
  time-`t` part is that of a configuration has the time-`t + 1` part of its successor
  (`post_of_pre`). The acceptance row and the emission bookkeeping then give acceptance.

Both directions use the head bounds `headsIn_cfgAt`: along a run, a head moves at most one
cell per step, so at every time `t ≤ S` every head is on an interior cell of the tableau.
-/

namespace MIPRE.TM.CookLevin

open Turing SAT MultiInputTM
open MultiTapeTM (moveInputPos)

section

variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
  (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}

/-- Acceptance within `S` steps: halted at time `S`, having output exactly `[acc]`. -/
def AcceptsIn (input : Fin i → List Symbol) (S : ℕ) : Prop :=
  (M.configs (M.initCfg input) S).state = none ∧ M.outputString (M.initCfg input) S = [acc]

/-! ## Head bounds along a run -/

omit [Fintype Symbol] [DecidableEq Symbol] [Fintype State] [DecidableEq State] in
theorem cfgAt_zero : cfgAt M (input := input) 0 = M.initCfg input := configs_zero

omit [Fintype Symbol] [DecidableEq Symbol] [Fintype State] [DecidableEq State] in
theorem cfgAt_zero' : cfgAt M (input := input) ((0 : Fin (S + 1)) : ℕ) = M.initCfg input :=
  configs_zero

omit [Fintype Symbol] [DecidableEq Symbol] [Fintype State] [DecidableEq State] in
theorem SignType.cast_bounds (m : SignType) : -1 ≤ (m : ℤ) ∧ (m : ℤ) ≤ 1 := by
  cases m <;> simp [SignType.cast]

omit [Fintype Symbol] [Fintype State] [DecidableEq State] [DecidableEq Symbol] in
/-- An input head is at position at most `t + 1` at time `t`. -/
theorem inputPos_cfgAt_le (t : ℕ) (j : Fin i) :
    ((cfgAt M (input := input) t).inputPos j : ℕ) ≤ t + 1 := by
  induction t with
  | zero => simp [cfgAt]
  | succ t ih =>
    rw [cfgAt_succ]
    cases hst : (cfgAt M (input := input) t).state with
    | none => rw [step_of_halt hst]; omega
    | some q =>
      rw [step_inputPos M _ hst]
      have := moveInputPos_sub_le ((cfgAt M (input := input) t).inputPos j)
        ((M.tr q (cfgAt M (input := input) t).inputSymbols (cfgAt M (input := input) t).workTapeSymbols).inputMoves j)
      omega

omit [Fintype Symbol] [Fintype State] [DecidableEq State] [DecidableEq Symbol] in
/-- A work head is at a position of absolute value at most `t` at time `t`. -/
theorem workTapePos_cfgAt_bounds (t : ℕ) (j : Fin w) :
    -(t : ℤ) ≤ (cfgAt M (input := input) t).workTapePos j ∧
      (cfgAt M (input := input) t).workTapePos j ≤ t := by
  induction t with
  | zero => simp [cfgAt]
  | succ t ih =>
    rw [cfgAt_succ]
    cases hst : (cfgAt M (input := input) t).state with
    | none => rw [step_of_halt hst]; push_cast; omega
    | some q =>
      rw [step_workTapePos M _ hst]
      have := SignType.cast_bounds
        ((M.tr q (cfgAt M (input := input) t).inputSymbols (cfgAt M (input := input) t).workTapeSymbols).workActions j).2
      push_cast; omega

omit [Fintype Symbol] [Fintype State] [DecidableEq State] [DecidableEq Symbol] in
/-- At every time `t ≤ S`, every head of the run is on an interior cell. -/
theorem headsIn_cfgAt (t : ℕ) (ht : t ≤ S) : HeadsIn (cfgAt M (input := input) t) S where
  input_pos j := by have := inputPos_cfgAt_le M (input := input) t j; omega
  work_pos j := by have := workTapePos_cfgAt_bounds M (input := input) t j; omega

/-! ## The output string of an accepting run -/

omit [Fintype Symbol] [DecidableEq Symbol] [Fintype State] [DecidableEq State] in
theorem outputString_zero (c : Cfg i w Symbol State input) : M.outputString c 0 = [] := by
  simp [outputString]

omit [Fintype Symbol] [DecidableEq Symbol] [Fintype State] [DecidableEq State] in
theorem outputString_succ' (t : ℕ) :
    M.outputString (M.initCfg input) (t + 1) =
      M.outputString (M.initCfg input) t ++ (M.outputSymbol (cfgAt M (input := input) t)).toList :=
  outputString_succ M _ t

omit [Fintype Symbol] [DecidableEq Symbol] [Fintype State] [DecidableEq State] in
/-- The output of `S` steps, split at step `t`. -/
theorem outputString_split (t : ℕ) (ht : t < S) :
    M.outputString (M.initCfg input) S =
      M.outputString (M.initCfg input) t ++ (M.outputSymbol (cfgAt M (input := input) t)).toList ++
        M.outputString (cfgAt M (input := input) (t + 1)) (S - (t + 1)) := by
  have h1 : S = (t + 1) + (S - (t + 1)) := by omega
  conv_lhs => rw [h1]
  rw [outputString_add_eq_append, outputString_succ]
  rfl

theorem singleton_eq_append₃ {α : Type*} {x : α} {A B C : List α} (h : [x] = A ++ B ++ C) :
    (B ≠ [] → A = [] ∧ B = [x] ∧ C = []) ∧ (A ≠ [] → B = []) := by
  have hl := congrArg List.length h
  simp only [List.length_singleton, List.length_append] at hl
  constructor
  · intro hB
    have hB' : 0 < B.length := List.length_pos_iff.mpr hB
    have hA : A = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hC : C = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hA hC
    exact ⟨rfl, by simpa using h.symm, rfl⟩
  · intro hA
    have := List.length_pos_iff.mpr hA
    exact List.eq_nil_of_length_eq_zero (by omega)

omit [Fintype Symbol] [DecidableEq Symbol] [Fintype State] [DecidableEq State] in
/-- In a run whose output over `S` steps is `[acc]`, a step that emits emits `acc`, and
nothing was emitted before it. -/
theorem outputSymbol_of_accepting (hacc : M.outputString (M.initCfg input) S = [acc]) (t : ℕ)
    (ht : t < S) (hne : M.outputSymbol (cfgAt M (input := input) t) ≠ none) :
    M.outputSymbol (cfgAt M (input := input) t) = some acc ∧
      M.outputString (M.initCfg input) t = [] := by
  have h := outputString_split M (input := input) t ht
  rw [hacc] at h
  have hB : (M.outputSymbol (cfgAt M (input := input) t)).toList ≠ [] := by
    cases hm : M.outputSymbol (cfgAt M (input := input) t)
    · exact absurd hm hne
    · simp
  obtain ⟨hA, hB', -⟩ := (singleton_eq_append₃ h).1 hB
  refine ⟨?_, hA⟩
  cases hm : M.outputSymbol (cfgAt M (input := input) t) with
  | none => exact absurd hm hne
  | some s => rw [hm] at hB'; simpa using hB'

/-! ## The assignment of a run, by variable -/

variable (chk : Circuit)

@[simp] theorem runAssign_cell (t : Fin (S + 1)) (d : Tape i w) (p : Pos S) (v : CellVal Symbol) :
    runAssign M acc (input := input) chk (.cell t d p v) =
      baseAssign M acc (input := input) chk.gates.length (.cell t d p v) := rfl

@[simp] theorem runAssign_head (t : Fin (S + 1)) (d : Tape i w) (p : Pos S) :
    runAssign M acc (input := input) chk (.head t d p) =
      baseAssign M acc (input := input) chk.gates.length (.head t d p) := rfl

@[simp] theorem runAssign_state (t : Fin (S + 1)) (q : Option State) :
    runAssign M acc (input := input) chk (.state t q) =
      baseAssign M acc (input := input) chk.gates.length (.state t q) := rfl

@[simp] theorem runAssign_emitOne (t : Fin S) :
    runAssign M acc (input := input) chk (.emitOne t) =
      baseAssign M acc (input := input) chk.gates.length (.emitOne t) := rfl

@[simp] theorem runAssign_emitBad (t : Fin S) :
    runAssign M acc (input := input) chk (.emitBad t) =
      baseAssign M acc (input := input) chk.gates.length (.emitBad t) := rfl

@[simp] theorem runAssign_emitted (t : Fin (S + 1)) :
    runAssign M acc (input := input) chk (.emitted t) =
      baseAssign M acc (input := input) chk.gates.length (.emitted t) := rfl

theorem runAssign_aux (t : Fin S) (js : Tape i w → Center S) (g : Fin chk.gates.length) :
    runAssign M acc (input := input) chk (.aux t js g) =
      chk.valueAt (fun n => baseAssign M acc (input := input) chk.gates.length
        (inpOf (G := chk.gates.length) t js n)) g := rfl

theorem runAssign_winVarOf (t : Fin S) (js : Tape i w → Center S) (v : WinVar i w Symbol State) :
    runAssign M acc (input := input) chk (winVarOf (G := chk.gates.length) t js v) =
      baseAssign M acc (input := input) chk.gates.length (winVarOf (G := chk.gates.length) t js v) := by
  cases v <;> rfl

theorem runAssign_inpOf (t : Fin S) (js : Tape i w → Center S) (n : ℕ) :
    runAssign M acc (input := input) chk (inpOf (G := chk.gates.length) t js n) =
      baseAssign M acc (input := input) chk.gates.length (inpOf (G := chk.gates.length) t js n) := by
  unfold inpOf
  split
  · exact runAssign_winVarOf M acc chk t js _
  · rfl

/-! ## Clause evaluation -/

variable {G : ℕ}

omit [Fintype Symbol] [Fintype State] [DecidableEq Symbol] [DecidableEq State] in
theorem unit_eval (f : TabVar i w Symbol State S G → Bool) (v : TabVar i w Symbol State S G)
    (b : Bool) : (unit v b).eval f = true ↔ f v = b := by
  cases b <;> cases h : f v <;> simp [unit, cl, Clause3.eval, Lit.eval, h]

omit [Fintype Symbol] [Fintype State] [DecidableEq Symbol] [DecidableEq State] in
theorem imp2_eval (f : TabVar i w Symbol State S G → Bool) (a b : TabVar i w Symbol State S G) :
    (imp2 a b).eval f = true ↔ (f a = true → f b = true) := by
  cases ha : f a <;> cases hb : f b <;> simp [imp2, cl, Clause3.eval, Lit.eval, ha, hb]

omit [Fintype Symbol] [Fintype State] [DecidableEq Symbol] [DecidableEq State] in
theorem nand2_eval (f : TabVar i w Symbol State S G → Bool) (a b : TabVar i w Symbol State S G) :
    (nand2 a b).eval f = true ↔ ¬ (f a = true ∧ f b = true) := by
  cases ha : f a <;> cases hb : f b <;> simp [nand2, cl, Clause3.eval, Lit.eval, ha, hb]

omit [Fintype Symbol] [Fintype State] [DecidableEq Symbol] [DecidableEq State] in
theorem cl_eval (f : TabVar i w Symbol State S G → Bool) (l₁ l₂ l₃ : Lit (TabVar i w Symbol State S G)) :
    (cl l₁ l₂ l₃).eval f = true ↔ l₁.eval f = true ∨ l₂.eval f = true ∨ l₃.eval f = true := by
  simp [cl, Clause3.eval, or_assoc]

omit [Fintype Symbol] [Fintype State] [DecidableEq Symbol] [DecidableEq State] in
@[simp] theorem lit_eval_true (f : TabVar i w Symbol State S G → Bool) (v) :
    (Lit.eval f ⟨v, true⟩) = f v := rfl

omit [Fintype Symbol] [Fintype State] [DecidableEq Symbol] [DecidableEq State] in
@[simp] theorem lit_eval_false (f : TabVar i w Symbol State S G → Bool) (v) :
    (Lit.eval f ⟨v, false⟩) = !f v := rfl

/-! ## Cells -/

omit [Fintype Symbol] [Fintype State] [DecidableEq State] [DecidableEq Symbol] in
theorem cellValAt_inl (c : Cfg i w Symbol State input) (j : Fin i) (p : Pos S) :
    cellValAt (S := S) c (.inl j) p = inputCellVal (input j) p := rfl

omit [Fintype Symbol] [Fintype State] [DecidableEq State] [DecidableEq Symbol] in
theorem cellValAt_bdry (c : Cfg i w Symbol State input) (d : Tape i w) (p : Pos S) (hb : p.IsBdry) :
    cellValAt (S := S) c d p = .bdry := by
  cases d with
  | inl j => exact (inputCellVal_bdry_iff _ _).mpr hb
  | inr j => simp [cellValAt, hb]

omit [Fintype Symbol] [Fintype State] [DecidableEq State] [DecidableEq Symbol] in
/-- An interior input cell holds a blank or a symbol of the string. -/
theorem inputCellVal_mem (x : List Symbol) (p : Pos S) (hnb : ¬ p.IsBdry) :
    inputCellVal x p = .blank ∨
      ∃ (k : ℕ) (hk : k < x.length), (p : ℕ) = k + 3 ∧ inputCellVal x p = .sym x[k] := by
  rw [inputCellVal_eq x p hnb]
  by_cases h3 : 3 ≤ (p : ℕ)
  · rw [if_pos h3]
    by_cases hl : (p : ℕ) - 3 < x.length
    · right
      refine ⟨(p : ℕ) - 3, hl, by omega, ?_⟩
      rw [List.getElem?_eq_getElem hl]
    · left
      rw [List.getElem?_eq_none (by omega)]
  · left; rw [if_neg h3]

omit [Fintype Symbol] [Fintype State] [DecidableEq State] [DecidableEq Symbol] in
/-- Cell `2` of an input tape is blank. -/
theorem inputCellVal_two (x : List Symbol) :
    inputCellVal (S := S) x ⟨2, by unfold numCells; omega⟩ = .blank := by
  have hnb : ¬ Pos.IsBdry (S := S) ⟨2, by unfold numCells; omega⟩ := by
    rw [not_isBdry_iff]; simp [numCells]
  rw [inputCellVal_eq x _ hnb, if_neg (by simp)]

omit [Fintype Symbol] [Fintype State] [DecidableEq State] [DecidableEq Symbol] in
/-- Blanks propagate to the right on an input tape. -/
theorem inputCellVal_blank_mono (x : List Symbol) (p p' : Pos S) (h2 : 2 < (p : ℕ))
    (hnb' : ¬ p'.IsBdry) (hpp' : p < p') (h : inputCellVal x p = .blank) :
    inputCellVal x p' = .blank := by
  have hnb : ¬ p.IsBdry := by
    rw [not_isBdry_iff] at hnb' ⊢
    have := Fin.lt_def.mp hpp'
    omega
  rw [inputCellVal_eq x p hnb, if_pos (by omega)] at h
  rw [inputCellVal_eq x p' hnb', if_pos (by have := Fin.lt_def.mp hpp'; omega)]
  have hnone : x[(p : ℕ) - 3]? = none := by
    cases hx : x[(p : ℕ) - 3]? with
    | none => rfl
    | some s => rw [hx] at h; exact absurd h (by simp)
  rw [List.getElem?_eq_none_iff] at hnone
  rw [List.getElem?_eq_none (by have := Fin.lt_def.mp hpp'; omega)]

/-! ## Completeness: the window clauses -/

omit [Fintype Symbol] [Fintype State] in
theorem baseAssign_emitted_zero :
    baseAssign M acc (input := input) G (.emitted (0 : Fin (S + 1))) = false := by
  simp [baseAssign, outputString_zero]

/-- The bits of the window read from `f` are the values of `f` on the circuit's inputs. -/
theorem getD_winBits (f : TabVar i w Symbol State S G → Bool) (h0 : f (.emitted 0) = false)
    (t : Fin S) (js : Tape i w → Center S) (n : ℕ) :
    (winBits fun v => f (winVarOf (G := G) t js v)).getD n false = f (inpOf (G := G) t js n) := by
  unfold winBits inpOf
  by_cases h : n < winCard i w Symbol State
  · rw [dif_pos h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h)]
    simp
  · rw [dif_neg h, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using h)]
    simp [h0]

/-- The check circuit accepts every window of the run. -/
theorem chk_eval_run (hchk : IsCheckCircuit M acc chk) (t : Fin S) (js : Tape i w → Center S) :
    chk.eval (fun n => baseAssign M acc (input := input) chk.gates.length
      (inpOf (G := chk.gates.length) t js n)) = true := by
  have := hchk (fun v => baseAssign M acc (input := input) chk.gates.length
    (winVarOf (G := chk.gates.length) t js v))
  have hfun : (fun n => (winBits fun v => baseAssign M acc (input := input) chk.gates.length
      (winVarOf (G := chk.gates.length) t js v)).getD n false) =
      fun n => baseAssign M acc (input := input) chk.gates.length
        (inpOf (G := chk.gates.length) t js n) :=
    funext (getD_winBits _ (baseAssign_emitted_zero M acc : baseAssign M acc (input := input)
      chk.gates.length (.emitted (0 : Fin (S + 1))) = false) t js)
  unfold Circuit.evalBits at this
  rw [hfun] at this
  refine this.mpr ?_
  exact ⟨localCfgOf M acc (cfgAt M (input := input) t) js, funext (encode_localCfgOf M acc _ t js),
    locallyConsistent_localCfgOf M acc _ js (headsIn_cfgAt M (input := input) t (by omega))⟩

theorem windowClauses_sat (hchk : IsCheckCircuit M acc chk) (hC : chk.RefsLt) :
    (windowClauses (S := S) (i := i) (w := w) (Symbol := Symbol) (State := State) chk).Sat
      (runAssign M acc (input := input) chk) := by
  rintro c ⟨t, js, hc⟩
  refine Circuit.tseitin_sat_of_values chk hC _ _ _ ?_ ?_ c hc
  · intro g hg
    simp only [auxOf, dif_pos hg, runAssign_aux, runAssign_inpOf]
  · simp only [runAssign_inpOf]
    exact chk_eval_run M acc chk hchk t js

/-! ## Completeness: the other clauses -/

variable (s₀ s₁ : Symbol) (fixed : Fin i → Option (List Symbol))

theorem startClauses_sat (hfix : ∀ j x, fixed j = some x → input j = x) :
    (startClauses (S := S) (G := chk.gates.length) M fixed).Sat
      (runAssign M acc (input := input) chk) := by
  rintro c (((⟨d, p, rfl⟩ | ⟨q, rfl⟩) | ⟨j, x, p, v, hx, rfl⟩) | ⟨j, p, v, rfl⟩)
  · rw [unit_eval, runAssign_head]
    simp only [baseAssign]
    rw [cfgAt_zero']
    apply decide_eq_decide.mpr
    cases d with
    | inl j =>
      simp only [headCell, initCfg, startCell, Fin.ext_iff, Fin.val_one]
      push_cast; omega
    | inr j =>
      simp only [headCell, initCfg, startCell, Fin.ext_iff]
      omega
  · rw [unit_eval, runAssign_state]
    simp only [baseAssign]
    rw [cfgAt_zero']
    apply decide_eq_decide.mpr
    exact eq_comm
  · rw [unit_eval, runAssign_cell]
    simp only [baseAssign]
    rw [cfgAt_zero', cellValAt_inl, hfix j x hx]
    apply decide_eq_decide.mpr
    exact eq_comm
  · rw [unit_eval, runAssign_cell]
    simp only [baseAssign]
    rw [cfgAt_zero']
    have : cellValAt (S := S) (M.initCfg input) (.inr j) p = workCellVal₀ p := by
      unfold cellValAt workCellVal₀
      split_ifs <;> rfl
    rw [this]
    apply decide_eq_decide.mpr
    exact eq_comm

theorem freeClauses_sat (hfree : ∀ j, fixed j = none → ∀ s ∈ input j, s = s₀ ∨ s = s₁) :
    (freeClauses (S := S) (G := chk.gates.length) s₀ s₁ fixed).Sat
      (runAssign M acc (input := input) chk) := by
  rintro c (((((⟨j, p, v, hj, hb, rfl⟩ | ⟨j, p, v, hj, hnb, h0, h1, hbl, rfl⟩) | ⟨j, v, hj, rfl⟩) |
    ⟨j, p, hj, hnb, rfl⟩) | ⟨j, p, v, v', hj, hnb, hvv', rfl⟩) | ⟨j, p, p', hj, h2, hnb', hpp', rfl⟩)
  · rw [unit_eval, runAssign_cell]
    simp only [baseAssign]
    rw [cfgAt_zero', cellValAt_inl, (inputCellVal_bdry_iff _ _).mpr hb]
    apply decide_eq_decide.mpr
    exact eq_comm
  · rw [unit_eval, runAssign_cell]
    simp only [baseAssign]
    rw [cfgAt_zero', cellValAt_inl]
    apply decide_eq_false
    intro h
    rcases inputCellVal_mem (input j) p hnb with h' | ⟨k, hk, -, h'⟩
    · exact hbl (h.symm.trans h')
    · rcases hfree j hj _ (List.getElem_mem hk) with hs | hs
      · exact h0 (by rw [← h, h', hs])
      · exact h1 (by rw [← h, h', hs])
  · rw [unit_eval, runAssign_cell]
    simp only [baseAssign]
    rw [cfgAt_zero', cellValAt_inl, inputCellVal_two]
    apply decide_eq_decide.mpr
    exact eq_comm
  · rw [cl_eval]
    simp only [lit_eval_true, runAssign_cell, baseAssign]
    rw [cfgAt_zero', cellValAt_inl]
    simp only [decide_eq_true_iff]
    rcases inputCellVal_mem (input j) p hnb with h' | ⟨k, hk, -, h'⟩
    · exact Or.inr (Or.inr h')
    · rcases hfree j hj _ (List.getElem_mem hk) with hs | hs
      · exact Or.inl (by rw [h', hs])
      · exact Or.inr (Or.inl (by rw [h', hs]))
  · rw [nand2_eval]
    simp only [runAssign_cell, baseAssign]
    rw [cfgAt_zero', cellValAt_inl]
    simp only [decide_eq_true_iff]
    rintro ⟨h, h'⟩
    exact hvv' (h.symm.trans h')
  · rw [imp2_eval]
    simp only [runAssign_cell, baseAssign]
    rw [cfgAt_zero', cellValAt_inl]
    simp only [decide_eq_true_iff]
    exact inputCellVal_blank_mono (input j) p p' h2 hnb' hpp'

theorem bdryClauses_sat :
    (bdryClauses (S := S) (G := chk.gates.length) (i := i) (w := w) (Symbol := Symbol)
      (State := State)).Sat (runAssign M acc (input := input) chk) := by
  rintro c (⟨t, d, p, v, hb, rfl⟩ | ⟨t, d, p, hb, rfl⟩)
  · rw [unit_eval, runAssign_cell]
    simp only [baseAssign]
    rw [cellValAt_bdry _ _ _ hb]
    apply decide_eq_decide.mpr
    exact eq_comm
  · rw [unit_eval, runAssign_head]
    simp only [baseAssign]
    apply decide_eq_false
    intro h
    have hbd := (headsIn_cfgAt M (input := input) t (Nat.lt_succ_iff.mp t.isLt)).headCell_bounds d
    have hnc : numCells S = 2 * S + 7 := rfl
    unfold Pos.IsBdry at hb
    omega

theorem emitClauses_sat (hacc : M.outputString (M.initCfg input) S = [acc]) :
    (emitClauses (S := S) (G := chk.gates.length) (i := i) (w := w) (Symbol := Symbol)
      (State := State)).Sat (runAssign M acc (input := input) chk) := by
  rintro c (((((rfl | ⟨t, rfl⟩) | ⟨t, rfl⟩) | ⟨t, rfl⟩) | ⟨t, rfl⟩) | ⟨t, rfl⟩)
  · rw [unit_eval, runAssign_emitted]
    exact baseAssign_emitted_zero M acc
  · rw [cl_eval]
    simp only [lit_eval_true, lit_eval_false, runAssign_emitted, runAssign_emitOne, baseAssign,
      Fin.val_succ, Fin.val_castSucc, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
      decide_eq_true_iff, not_not]
    rw [outputString_succ']
    by_cases hA : M.outputString (M.initCfg input) t = []
    · rw [hA, List.nil_append]
      by_cases ho : M.outputSymbol (cfgAt M (input := input) t) = none
      · left; rw [ho]; rfl
      · right; right; exact (outputSymbol_of_accepting M acc (input := input) hacc t t.isLt ho).1
    · right; left; exact hA
  · rw [imp2_eval]
    simp only [runAssign_emitted, baseAssign, Fin.val_succ, Fin.val_castSucc, decide_eq_true_iff]
    intro h
    rw [outputString_succ']
    exact fun h' => h (List.append_eq_nil_iff.mp h').1
  · rw [imp2_eval]
    simp only [runAssign_emitted, runAssign_emitOne, baseAssign, Fin.val_succ,
      decide_eq_true_iff]
    intro h
    rw [outputString_succ', h]
    simp
  · rw [nand2_eval]
    simp only [runAssign_emitted, runAssign_emitOne, baseAssign, Fin.val_castSucc,
      decide_eq_true_iff]
    rintro ⟨h, h'⟩
    exact h' (outputSymbol_of_accepting M acc (input := input) hacc t t.isLt (by rw [h]; simp)).2
  · rw [unit_eval, runAssign_emitBad]
    simp only [baseAssign]
    apply decide_eq_false
    rintro ⟨h, h'⟩
    exact h' (outputSymbol_of_accepting M acc (input := input) hacc t t.isLt h).1

theorem finalClauses_sat (hacc : AcceptsIn M acc input S) :
    (finalClauses (S := S) (G := chk.gates.length) (i := i) (w := w) (Symbol := Symbol)
      (State := State)).Sat (runAssign M acc (input := input) chk) := by
  rintro c (rfl | rfl)
  · rw [unit_eval, runAssign_state]
    simp only [baseAssign, Fin.val_last]
    exact decide_eq_true hacc.1
  · rw [unit_eval, runAssign_emitted]
    simp only [baseAssign, Fin.val_last]
    apply decide_eq_true
    rw [hacc.2]
    simp

/-- **Completeness of the tableau.** The assignment of an accepting run satisfies the tableau
formula. -/
theorem tableau_sat_of_acceptsIn (hchk : IsCheckCircuit M acc chk) (hC : chk.RefsLt)
    (hfix : ∀ j x, fixed j = some x → input j = x)
    (hfree : ∀ j, fixed j = none → ∀ s ∈ input j, s = s₀ ∨ s = s₁)
    (hacc : AcceptsIn M acc input S) :
    (tableau M s₀ s₁ S fixed chk).Sat (runAssign M acc (input := input) chk) := by
  rintro c (((((hc | hc) | hc) | hc) | hc) | hc)
  · exact startClauses_sat M acc chk fixed hfix c hc
  · exact freeClauses_sat M acc chk s₀ s₁ fixed hfree c hc
  · exact bdryClauses_sat M acc chk c hc
  · exact emitClauses_sat M acc chk hacc.2 c hc
  · exact finalClauses_sat M acc chk hacc c hc
  · exact windowClauses_sat M acc chk hchk hC c hc

end

end MIPRE.TM.CookLevin

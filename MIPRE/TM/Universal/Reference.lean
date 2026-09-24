/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.TM.Code.Evaluator
import MIPRE.TM.MultiInput.Truncate
import Mathlib.Tactic.Ring

/-!
# A reference simulator for machine codes, over lists

Milestone M3 of `planning/universal-machine.md`: a simulator for coded machines written over
lists and natural numbers only — zipper tapes, head positions and states as numbers, the table
as a list, the observation index by Horner's rule — and proved to agree with the operational
semantics `Code.toTM` (`Universal.refEval_ofCode`). It is the function the universal machine's
ambient program computes (milestone M5), so it is written the way that program is: every
piece is a fold, a map, a lookup or a small arithmetic function.

Numbers stand for symbols, states and positions, so nothing here depends on the types
`Fin σ`, `Fin Q` or `Fin (len + 2)` of `MIPRE.TM.Code`; the relation `Universal.Rel` is where
the two views meet.
-/

namespace Turing.Universal

/-! ## Codes as lists -/

/-- A table entry, with lists in place of arrays. -/
structure RefAction where
  /-- The input-head moves, in tape order. -/
  moves : List Move
  /-- The work-tape actions, in tape order. -/
  works : List RawWorkAction
  /-- The emitted bit, if any. -/
  out : Option Bool
  /-- The successor state, or `none` to halt. -/
  next : Option ℕ
deriving Inhabited

/-- A raw table entry as a list-based one. -/
def RefAction.ofRaw (a : RawAction) : RefAction :=
  ⟨a.inputMoves.toList, a.workActions.toList, a.output, a.nextState⟩

/-- A machine code with its table as a list. -/
structure RefCode where
  /-- The number of work tapes. -/
  w : ℕ
  /-- The alphabet size. -/
  σ : ℕ
  /-- The start state. -/
  q₀ : ℕ
  /-- The dense table, in the canonical order. -/
  table : List RefAction

/-- A code as a list-based one. -/
def RefCode.ofCode {i : ℕ} (c : Code i) : RefCode :=
  ⟨c.workTapeCount, c.alphabetSize, c.startState, c.raw.table.toList.map RefAction.ofRaw⟩

/-! ## Tapes as zippers -/

/-- A two-way infinite tape: the cells left of the head (nearest first), the cell under the
head, and the cells right of it (nearest first). Cells beyond the lists are blank. Symbols are
numbers. -/
structure Zip where
  /-- The cells left of the head, nearest first. -/
  left : List (Option ℕ)
  /-- The cell under the head. -/
  cur : Option ℕ
  /-- The cells right of the head, nearest first. -/
  right : List (Option ℕ)

/-- The blank tape. -/
def Zip.blank : Zip := ⟨[], none, []⟩

/-- Write on the cell under the head. -/
def Zip.write (z : Zip) : RawWrite → Zip
  | .keep => z
  | .blank => { z with cur := none }
  | .symbol s => { z with cur := some s }

/-- Move the head. -/
def Zip.move (z : Zip) : Move → Zip
  | .stay => z
  | .left => ⟨z.left.tail, z.left.headD none, z.cur :: z.right⟩
  | .right => ⟨z.cur :: z.left, z.right.headD none, z.right.tail⟩

/-- One work-tape action: write, then move. -/
def Zip.act (z : Zip) (wa : RawWorkAction) : Zip := (z.write wa.write).move wa.move

/-! ## Configurations and one step -/

/-- A configuration of the reference simulator. -/
structure RefCfg where
  /-- The state, or `none` once halted. -/
  state : Option ℕ
  /-- The input-head positions (shifted by one, as in `MultiInputTM.Cfg`). -/
  inPos : List ℕ
  /-- The work tapes. -/
  tapes : List Zip
  /-- The bits emitted so far. -/
  out : List Bool

/-- The symbol under an input head at position `p` on the bit string `xs`, as a number. -/
def readInput (xs : List Bool) (p : ℕ) : Option ℕ :=
  if p = 0 then none else (xs[p - 1]?).map fun b => if b then 1 else 0

/-- An input-head move on a tape of length `len`, clamped to `[0, len + 1]`. -/
def moveIn (len p : ℕ) : Move → ℕ
  | .stay => p
  | .left => p - 1
  | .right => min (p + 1) (len + 1)

/-- The digit of an optional symbol. -/
def digit : Option ℕ → ℕ
  | none => 0
  | some s => s + 1

/-- Horner evaluation in radix `r`, first digit most significant. -/
def horner (r : ℕ) (ds : List ℕ) : ℕ := ds.foldl (fun acc d => acc * r + d) 0

/-- The table position of an observation. -/
def refIndex (rc : RefCode) (q : ℕ) (as bs : List (Option ℕ)) : ℕ :=
  horner (rc.σ + 1) (q :: (as ++ bs).map digit)

/-- One step of the reference simulator on bit inputs `x`. -/
def refStep (rc : RefCode) (x : List (List Bool)) (c : RefCfg) : RefCfg :=
  match c.state with
  | none => c
  | some q =>
    let as := (x.zip c.inPos).map fun p => readInput p.1 p.2
    let a := rc.table.getD (refIndex rc q as (c.tapes.map Zip.cur)) default
    { state := a.next
      inPos := (x.zip (c.inPos.zip a.moves)).map fun p => moveIn p.1.length p.2.1 p.2.2
      tapes := (c.tapes.zip a.works).map fun p => p.1.act p.2
      out := c.out ++ a.out.toList }

/-- The initial configuration on `i` inputs. -/
def refInit (rc : RefCode) (i : ℕ) : RefCfg :=
  ⟨some rc.q₀, List.replicate i 1, List.replicate rc.w Zip.blank, []⟩

/-- The reference budgeted evaluation. -/
def refEval (rc : RefCode) (x : List (List Bool)) (T : ℕ) : Code.BoundedResult :=
  let c := (refStep rc x)^[T] (refInit rc x.length)
  if c.state.isNone then .halted c.out else .timeout

/-! ## Lists of functions -/

theorem zip_ofFn {α β : Type*} {n : ℕ} (f : Fin n → α) (g : Fin n → β) :
    (List.ofFn f).zip (List.ofFn g) = List.ofFn fun k => (f k, g k) := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.ofFn_succ, ih]

theorem toList_eq_ofFn {α : Type*} (a : Array α) {n : ℕ} (h : a.size = n) :
    a.toList = List.ofFn fun k : Fin n => a[k.val]'(h ▸ k.isLt) := by
  subst h
  apply List.ext_getElem <;> simp

/-! ## Horner's rule -/

theorem foldl_horner (r a : ℕ) (l : List ℕ) :
    l.foldl (fun acc d => acc * r + d) a = a * r ^ l.length + horner r l := by
  induction l generalizing a with
  | nil => simp [horner]
  | cons d l ih =>
    simp only [List.foldl_cons, horner, List.length_cons]
    rw [ih, ih (0 * r + d)]
    ring

theorem horner_cons (r d : ℕ) (l : List ℕ) :
    horner r (d :: l) = d * r ^ l.length + horner r l := by
  simp only [horner, List.foldl_cons]
  rw [foldl_horner]
  simp [horner]

theorem encodeDigits_eq_horner {r : ℕ} (l : List (Fin (r + 1))) :
    encodeDigits l = horner (r + 1) (l.map Fin.val) := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [encodeDigits_cons, List.map_cons, horner_cons, ih, List.length_map]

theorem digit_map_val {σ : ℕ} (a : Option (Fin σ)) :
    digit (a.map Fin.val) = (encodeSymbol? a).val := by
  cases a <;> simp [digit, encodeSymbol?]

/-- **The reference index is the canonical transition index.** -/
theorem refIndex_eq {i w σ Q : ℕ} (rc : RefCode) (hσ : rc.σ = σ) (q : Fin Q)
    (as : Fin i → Option (Fin σ)) (bs : Fin w → Option (Fin σ)) :
    refIndex rc q (List.ofFn fun j => (as j).map Fin.val)
        (List.ofFn fun d => (bs d).map Fin.val) = (transitionIndex q as bs).val := by
  subst hσ
  simp only [refIndex, horner_cons, transitionIndex, encodeObservation, encodeDigits_eq_horner,
    observationDigits, List.map_append, List.map_ofFn, List.length_append, List.length_ofFn]
  simp [Function.comp_def, digit_map_val]

/-! ## Tapes -/

/-- A zipper represents the tape `f` with its head at `p`. -/
def Zip.Rep {σ : ℕ} (z : Zip) (f : ℤ → Option (Fin σ)) (p : ℤ) : Prop :=
  z.cur = (f p).map Fin.val ∧ (∀ k : ℕ, z.left.getD k none = (f (p - 1 - k)).map Fin.val) ∧
    ∀ k : ℕ, z.right.getD k none = (f (p + 1 + k)).map Fin.val

theorem Zip.rep_blank {σ : ℕ} (p : ℤ) : Zip.blank.Rep (fun _ => (none : Option (Fin σ))) p :=
  ⟨rfl, fun _ => by simp [Zip.blank], fun _ => by simp [Zip.blank]⟩

theorem Zip.rep_update {σ : ℕ} {z : Zip} {f : ℤ → Option (Fin σ)} {p : ℤ} (h : z.Rep f p)
    (o : Option (Fin σ)) : ({ z with cur := o.map Fin.val } : Zip).Rep (Function.update f p o) p := by
  obtain ⟨_, hl, hr⟩ := h
  refine ⟨by simp, fun k => ?_, fun k => ?_⟩
  · rw [hl k, Function.update_of_ne (by omega)]
  · rw [hr k, Function.update_of_ne (by omega)]

theorem cast_toSignType_left : ((Move.toSignType .left : SignType) : ℤ) = -1 := rfl
theorem cast_toSignType_right : ((Move.toSignType .right : SignType) : ℤ) = 1 := rfl
theorem cast_toSignType_stay : ((Move.toSignType .stay : SignType) : ℤ) = 0 := rfl

theorem getD_tail {α : Type*} (l : List α) (d : α) (k : ℕ) :
    l.tail.getD k d = l.getD (k + 1) d := by
  cases l <;> simp

theorem headD_eq_getD {α : Type*} (l : List α) (d : α) : l.headD d = l.getD 0 d := by
  cases l <;> simp

theorem Zip.rep_move {σ : ℕ} {z : Zip} {f : ℤ → Option (Fin σ)} {p : ℤ} (h : z.Rep f p)
    (m : Move) : (z.move m).Rep f (p + m.toSignType) := by
  obtain ⟨hc, hl, hr⟩ := h
  cases m with
  | stay =>
    rw [cast_toSignType_stay, add_zero]
    exact ⟨hc, hl, hr⟩
  | left =>
    rw [cast_toSignType_left]
    refine ⟨?_, fun k => ?_, fun k => ?_⟩
    · simp only [Zip.move, headD_eq_getD, hl 0]
      congr 2
      omega
    · simp only [Zip.move, getD_tail, hl (k + 1)]
      congr 2
      push_cast
      omega
    · rcases k with _ | k
      · simp only [Zip.move, List.getD_cons_zero, hc]
        congr 2
        omega
      · simp only [Zip.move, List.getD_cons_succ, hr k]
        congr 2
        push_cast
        omega
  | right =>
    rw [cast_toSignType_right]
    refine ⟨?_, fun k => ?_, fun k => ?_⟩
    · simp only [Zip.move, headD_eq_getD, hr 0]
      congr 2
      omega
    · rcases k with _ | k
      · simp only [Zip.move, List.getD_cons_zero, hc]
        congr 2
        omega
      · simp only [Zip.move, List.getD_cons_succ, hl k]
        congr 2
        push_cast
        omega
    · simp only [Zip.move, getD_tail, hr (k + 1)]
      congr 2
      push_cast
      omega

/-! ## Inputs -/

theorem readInput_eq {i : ℕ} (c : Code i) {x : Fin i → List Bool} {w : ℕ} {State : Type*}
    (cfg : MultiInputTM.Cfg i w c.Symbol State (c.bitInputs x)) (j : Fin i) :
    readInput (x j) (cfg.inputPos j).val = (cfg.inputSymbol j).map Fin.val := by
  rw [MultiInputTM.Cfg.inputSymbol_eq_getElem?]
  unfold readInput
  split_ifs with h
  · rfl
  · simp only [Code.bitInputs, List.getElem?_map, Option.map_map]
    congr 1

theorem moveIn_eq {n : ℕ} (pos : Fin (n + 2)) (m : Move) :
    moveIn n pos.val m = (MultiTapeTM.moveInputPos pos m.toSignType).val := by
  have := pos.isLt
  cases m with
  | stay =>
    unfold moveIn MultiTapeTM.moveInputPos
    rw [cast_toSignType_stay, dif_pos (by omega)]
    simp
  | left =>
    unfold moveIn MultiTapeTM.moveInputPos
    rw [cast_toSignType_left, dif_pos (by omega)]
    simp only
    omega
  | right =>
    unfold moveIn MultiTapeTM.moveInputPos
    rw [cast_toSignType_right]
    simp only
    by_cases h : ((pos.val : ℤ) + 1).toNat < n + 2
    · rw [dif_pos h]
      simp only
      omega
    · rw [dif_neg h]
      simp only
      omega

/-! ## One machine step, field by field -/

section StepFields

variable {i w : ℕ} {Symbol State : Type*} (tm : MultiInputTM i w Symbol State)
  {input : Fin i → List Symbol} {cfg : MultiInputTM.Cfg i w Symbol State input} {q : State}

theorem workTapes_step (hq : cfg.state = some q) (d : Fin w) :
    (tm.step cfg).workTapes d =
      ((tm.tr q cfg.inputSymbols cfg.workTapeSymbols).workActions d).1.elim (cfg.workTapes d)
        (Function.update (cfg.workTapes d) (cfg.workTapePos d)) := by
  simp only [MultiInputTM.step, hq]
  split <;> simp_all

theorem workTapePos_step (hq : cfg.state = some q) (d : Fin w) :
    (tm.step cfg).workTapePos d =
      cfg.workTapePos d + ((tm.tr q cfg.inputSymbols cfg.workTapeSymbols).workActions d).2 := by
  simp only [MultiInputTM.step, hq]

end StepFields

/-! ## Writes -/

/-- What a raw write puts on a tape, at the level of numbers. -/
def writeVal : RawWrite → Option (Option ℕ)
  | .keep => none
  | .blank => some none
  | .symbol s => some (some s)

theorem Zip.rep_write {σ : ℕ} {z : Zip} {f : ℤ → Option (Fin σ)} {p : ℤ} (h : z.Rep f p)
    (wr : RawWrite) (wo : Option (Option (Fin σ)))
    (hwo : wo.map (Option.map Fin.val) = writeVal wr) :
    (z.write wr).Rep (wo.elim f (Function.update f p)) p := by
  cases wo with
  | none =>
    cases wr <;> simp_all [writeVal, Zip.write]
  | some o =>
    simp only [Option.elim_some]
    have hz : z.write wr = { z with cur := o.map Fin.val } := by
      cases wr <;> simp_all [writeVal, Zip.write]
    rw [hz]
    exact Zip.rep_update h o

theorem interpretAction_write {i : ℕ} (c : Code i) (a : RawAction) (h₁ h₂ h₃ h₄)
    (d : Fin c.workTapeCount) :
    ((c.interpretAction a h₁ h₂ h₃ h₄).workActions d).1.map (Option.map Fin.val) =
      writeVal (a.workActions[d.val]'(by rw [h₂]; exact d.isLt)).write := by
  simp only [Code.interpretAction]
  split <;> simp_all [writeVal]

theorem interpretAction_move {i : ℕ} (c : Code i) (a : RawAction) (h₁ h₂ h₃ h₄)
    (d : Fin c.workTapeCount) :
    ((c.interpretAction a h₁ h₂ h₃ h₄).workActions d).2 =
      (a.workActions[d.val]'(by rw [h₂]; exact d.isLt)).move.toSignType := rfl

/-! ## The simulation -/

/-- A reference configuration represents a configuration of the coded machine: the same
state, the same input-head positions, and a zipper for each work tape. -/
structure Rel {i : ℕ} (c : Code i) (x : Fin i → List Bool)
    (cfg : MultiInputTM.Cfg i c.workTapeCount c.Symbol c.State (c.bitInputs x))
    (r : RefCfg) : Prop where
  state : r.state = cfg.state.map Fin.val
  inPos : r.inPos = List.ofFn fun j => (cfg.inputPos j).val
  tapes : ∃ zs : Fin c.workTapeCount → Zip, r.tapes = List.ofFn zs ∧
    ∀ d, (zs d).Rep (cfg.workTapes d) (cfg.workTapePos d)

theorem rel_init {i : ℕ} (c : Code i) (x : Fin i → List Bool) :
    Rel c x (c.toTM.initCfg (c.bitInputs x)) (refInit (RefCode.ofCode c) i) where
  state := rfl
  inPos := by simp [refInit, List.ofFn_const]
  tapes := ⟨fun _ => Zip.blank, by simp [refInit, RefCode.ofCode, List.ofFn_const],
    fun _ => Zip.rep_blank _⟩

theorem table_getD {i : ℕ} (c : Code i) (q : c.State) (as : Fin i → Option c.Symbol)
    (bs : Fin c.workTapeCount → Option c.Symbol) :
    (RefCode.ofCode c).table.getD (transitionIndex q as bs).val default =
      RefAction.ofRaw (c.actionAt q as bs) := by
  have hlt : (transitionIndex q as bs).val < c.raw.table.size := by
    rw [c.wf.table_size]; exact (transitionIndex q as bs).isLt
  simp only [RefCode.ofCode, Code.actionAt]
  simp [List.getD_eq_getElem?_getD, hlt]

/-- **One step of the reference simulator follows one step of the machine.** -/
theorem rel_step {i : ℕ} (c : Code i) (x : Fin i → List Bool)
    {cfg : MultiInputTM.Cfg i c.workTapeCount c.Symbol c.State (c.bitInputs x)} {r : RefCfg}
    (h : Rel c x cfg r) :
    Rel c x (c.toTM.step cfg) (refStep (RefCode.ofCode c) (List.ofFn x) r) ∧
      (refStep (RefCode.ofCode c) (List.ofFn x) r).out =
        r.out ++ c.decodeBitOutput (c.toTM.outputSymbol cfg).toList := by
  obtain ⟨hs, hp, zs, hz, hzr⟩ := h
  cases hq : cfg.state with
  | none =>
    have hr : r.state = none := by rw [hs, hq]; rfl
    rw [MultiInputTM.step_of_halt hq]
    simp only [refStep, hr, MultiInputTM.outputSymbol, hq, Option.toList_none,
      Code.decodeBitOutput_nil, List.append_nil]
    exact ⟨⟨hs, hp, zs, hz, hzr⟩, trivial⟩
  | some q =>
    have hr : r.state = some q.val := by rw [hs, hq]; rfl
    set act := c.actionAt q cfg.inputSymbols cfg.workTapeSymbols with hact
    have has : ((List.ofFn x).zip r.inPos).map (fun p => readInput p.1 p.2) =
        List.ofFn fun j => (cfg.inputSymbols j).map Fin.val := by
      rw [hp, zip_ofFn, List.map_ofFn]
      congr 1
      funext j
      exact readInput_eq c cfg j
    have hbs : r.tapes.map Zip.cur = List.ofFn fun d => (cfg.workTapeSymbols d).map Fin.val := by
      rw [hz, List.map_ofFn]
      congr 1
      funext d
      exact (hzr d).1
    have hidx : refIndex (RefCode.ofCode c) q.val
        (((List.ofFn x).zip r.inPos).map fun p => readInput p.1 p.2) (r.tapes.map Zip.cur) =
        (transitionIndex q cfg.inputSymbols cfg.workTapeSymbols).val := by
      rw [has, hbs]
      exact refIndex_eq _ rfl q _ _
    have hA : (RefCode.ofCode c).table.getD (refIndex (RefCode.ofCode c) q.val
        (((List.ofFn x).zip r.inPos).map fun p => readInput p.1 p.2) (r.tapes.map Zip.cur))
        default = RefAction.ofRaw act := by
      rw [hidx, table_getD]
    have hmoves := toList_eq_ofFn act.inputMoves Code.actionAt_inputMoves_size
    have hworks := toList_eq_ofFn act.workActions Code.actionAt_workActions_size
    have hstep : refStep (RefCode.ofCode c) (List.ofFn x) r =
        { state := act.nextState
          inPos := ((List.ofFn x).zip (r.inPos.zip act.inputMoves.toList)).map
            fun p => moveIn p.1.length p.2.1 p.2.2
          tapes := (r.tapes.zip act.workActions.toList).map fun p => p.1.act p.2
          out := r.out ++ act.output.toList } := by
      simp only [refStep, hr]
      rw [hA]
      rfl
    rw [hstep]
    refine ⟨⟨?_, ?_, ⟨fun d => (zs d).act (act.workActions[d.val]'(by
        rw [Code.actionAt_workActions_size]; exact d.isLt)), ?_, fun d => ?_⟩⟩, ?_⟩
    · -- state
      simp only [MultiInputTM.step, hq]
      exact (Code.toTM_tr_q'_map_val c q _ _).symm
    · -- input heads
      simp only [MultiInputTM.step, hq]
      rw [hp, hmoves, zip_ofFn, zip_ofFn, List.map_ofFn]
      congr 1
      funext j
      simp only [Function.comp]
      have hlen : (x j).length = (c.bitInputs x j).length := by simp [Code.bitInputs]
      rw [hlen, moveIn_eq]
      rfl
    · -- work tapes
      rw [hz, hworks, zip_ofFn, List.map_ofFn]
      rfl
    · have e : c.toTM.tr q cfg.inputSymbols cfg.workTapeSymbols =
          c.interpretAction act Code.actionAt_inputMoves_size Code.actionAt_workActions_size
            (fun _ hwa _ hs => Code.actionAt_write_lt hwa hs)
            (fun _ hq' => Code.actionAt_nextState_lt hq') := Code.toTM_tr c q _ _
      rw [workTapes_step c.toTM hq, workTapePos_step c.toTM hq, e, interpretAction_move]
      exact Zip.rep_move (Zip.rep_write (hzr d) _ _ (interpretAction_write c act _ _ _ _ d)) _
    · -- output
      simp only [MultiInputTM.outputSymbol, hq, Code.toTM_tr_outS]
      cases act.output with
      | none => rfl
      | some b => simp

/-- The reference run follows the machine's run, and has the same output. -/
theorem rel_runFor {i : ℕ} (c : Code i) (x : Fin i → List Bool) (T : ℕ) :
    Rel c x (c.runFor x T) ((refStep (RefCode.ofCode c) (List.ofFn x))^[T]
        (refInit (RefCode.ofCode c) i)) ∧
      ((refStep (RefCode.ofCode c) (List.ofFn x))^[T] (refInit (RefCode.ofCode c) i)).out =
        c.outputFor x T := by
  induction T with
  | zero => exact ⟨by simpa using rel_init c x, by simp [refInit]⟩
  | succ T ih =>
    obtain ⟨h, ho⟩ := ih
    obtain ⟨h', ho'⟩ := rel_step c x h
    rw [Function.iterate_succ_apply', Code.runFor_succ, Code.outputFor_succ]
    exact ⟨h', by rw [ho', ho]⟩

/-- **The reference simulator computes the budgeted evaluation.** -/
theorem refEval_ofCode {i : ℕ} (c : Code i) (x : Fin i → List Bool) (T : ℕ) :
    refEval (RefCode.ofCode c) (List.ofFn x) T = c.evalWithin x T := by
  obtain ⟨h, ho⟩ := rel_runFor c x T
  unfold refEval Code.evalWithin
  simp only [List.length_ofFn, h.state, ho, Option.isNone_map]

end Turing.Universal

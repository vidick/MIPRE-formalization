/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.TM.Interp.Reach

/-!
# The routines: specifications of the instructions

Each instruction's specification is a reachability statement: from a configuration at
the instruction's first phase, with the tapes it reads in a stated shape, a bounded
number of steps leads to the configuration at the next instruction, with the stated
effect on the tapes it touches and none on the others (`Untouched`).
-/

namespace MIPRE.TM.Interp

open Turing MultiInputTM Phase
open MultiTapeTM (moveInputPos)

variable {input : Fin 7 → List Sym}

/-- The control at `(k, pc)`, first phase. -/
abbrev at_ (k : ProgId) (pc : Fin maxPc) : Option Ctl := some ⟨k, pc, p0⟩

/-- The control at the instruction after `(k, pc)`. -/
def next_ (k : ProgId) (pc : Fin maxPc) (h : pc.val + 1 < maxPc) : Option Ctl :=
  some ⟨k, ⟨pc.val + 1, h⟩, p0⟩

theorem resolve_adv (k : ProgId) (pc : Fin maxPc) (h : pc.val + 1 < maxPc) :
    resolve k pc .adv = next_ k pc h := by
  simp [resolve, next_, h]

@[simp] theorem resolve_stay (k : ProgId) (pc : Fin maxPc) (ph : Phase) :
    resolve k pc (.stay ph) = some ⟨k, pc, ph⟩ := rfl

@[simp] theorem resolve_jmp (k : ProgId) (pc : Fin maxPc) (k' : ProgId) :
    resolve k pc (.jmp k') = some ⟨k', ⟨0, by decide⟩, p0⟩ := rfl

@[simp] theorem resolve_halt (k : ProgId) (pc : Fin maxPc) : resolve k pc .halt = none := rfl

/-- `c'` agrees with `c` on the input heads and on the work tapes outside `S`. -/
def Untouched (c c' : Cfg input) (S : List WT) : Prop :=
  c'.inputPos = c.inputPos ∧
    ∀ d, d ∉ S → c'.workTapes d = c.workTapes d ∧ c'.workTapePos d = c.workTapePos d

namespace Untouched

theorem refl (c : Cfg input) (S : List WT) : Untouched c c S := ⟨rfl, fun _ _ => ⟨rfl, rfl⟩⟩

theorem trans {c c' c'' : Cfg input} {S S' : List WT} (h : Untouched c c' S)
    (h' : Untouched c' c'' S') : Untouched c c'' (S ++ S') := by
  refine ⟨h'.1.trans h.1, fun d hd => ?_⟩
  rw [List.mem_append, not_or] at hd
  obtain ⟨h1, h2⟩ := h.2 d hd.1
  obtain ⟨h1', h2'⟩ := h'.2 d hd.2
  exact ⟨h1'.trans h1, h2'.trans h2⟩

theorem mono {c c' : Cfg input} {S S' : List WT} (h : Untouched c c' S) (hS : ∀ d ∈ S, d ∈ S') :
    Untouched c c' S' :=
  ⟨h.1, fun d hd => h.2 d fun hmem => hd (hS d hmem)⟩

theorem tapes {c c' : Cfg input} {S : List WT} (h : Untouched c c' S) {d : WT} (hd : d ∉ S) :
    c'.workTapes d = c.workTapes d := (h.2 d hd).1

theorem pos {c c' : Cfg input} {S : List WT} (h : Untouched c c' S) {d : WT} (hd : d ∉ S) :
    c'.workTapePos d = c.workTapePos d := (h.2 d hd).2

end Untouched

/-! ## One step of an instruction -/

/-- The symbol under the head of work tape `t`. -/
theorem workTapeSymbols_eq (c : Cfg input) (t : WT) :
    c.workTapeSymbols t = c.workTapes t (c.workTapePos t) := rfl

/-- One step at `(k, pc, ph)` executing the instruction `ins` there. -/
theorem step_instr {c : Cfg input} {k : ProgId} {pc : Fin maxPc} {ph : Phase}
    (hq : c.state = some ⟨k, pc, ph⟩) {ins : Instr} (hins : instrAt k pc = ins) :
    let a := execInstr ins ph c.inputSymbols c.workTapeSymbols
    Reach c 1 (applyAct a (resolve k pc a.next) c) a.out.toList := by
  have := Reach.single c
  rwa [step_eq c hq, outputSymbol_eq c hq, actOf, hins] at this

/-- An action that touches only the work tapes in `S`, and no input head. -/
def Act.Within (a : Act) (S : List WT) : Prop :=
  (∀ j, a.inMoves j = 0) ∧ ∀ d, d ∉ S → a.works d = (none, 0)

theorem untouched_applyAct {a : Act} {S : List WT} (h : a.Within S) (q' : Option Ctl)
    (c : Cfg input) : Untouched c (applyAct a q' c) S := by
  refine ⟨funext fun j => ?_, fun d hd => ?_⟩
  · simp [applyAct, h.1 j]
  · have := h.2 d hd
    refine ⟨?_, ?_⟩
    · rw [applyAct_workTapes_of_none _ _ _ _ (by rw [this])]
    · rw [applyAct_workTapePos, this]; simp

/-! ## `write` -/

theorem exec_write {k : ProgId} {pc : Fin maxPc} {t : WT} {s : Sym}
    (hins : instrAt k pc = .write t s) (hpc : pc.val + 1 < maxPc) (c : Cfg input)
    (hq : c.state = at_ k pc) :
    ∃ c', Reach c 1 c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [t] ∧
      c'.workTapes t = Function.update (c.workTapes t) (c.workTapePos t) (some s) ∧
      c'.workTapePos t = c.workTapePos t + 1 := by
  have h := step_instr hq hins
  simp only [execInstr] at h
  refine ⟨_, h, ?_, ?_, ?_, ?_⟩
  · simp [resolve_adv k pc hpc]
  · refine untouched_applyAct ⟨fun j => rfl, fun d hd => ?_⟩ _ _
    have : d ≠ t := by simpa using hd
    simp [Act.mw_works_of_ne _ this, Act.ww_works_of_ne _ this]
  · rw [applyAct_workTapes_of_some _ _ _ t (s := some s) (by simp)]
  · simp

/-! ## `move` -/

theorem exec_move {k : ProgId} {pc : Fin maxPc} {t : WT} {dir : Bool}
    (hins : instrAt k pc = .move t dir) (hpc : pc.val + 1 < maxPc) (c : Cfg input)
    (hq : c.state = at_ k pc) :
    ∃ c', Reach c 1 c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [t] ∧
      c'.workTapes t = c.workTapes t ∧
      c'.workTapePos t = c.workTapePos t + (if dir then 1 else -1) := by
  have h := step_instr hq hins
  simp only [execInstr] at h
  refine ⟨_, h, ?_, ?_, ?_, ?_⟩
  · simp [resolve_adv k pc hpc]
  · refine untouched_applyAct ⟨fun j => rfl, fun d hd => ?_⟩ _ _
    have : d ≠ t := by simpa using hd
    simp [Act.mw_works_of_ne _ this]
  · rw [applyAct_workTapes_of_none _ _ _ t (by simp)]
  · cases dir <;> simp

/-! ## `toEnd` -/

theorem exec_toEnd {k : ProgId} {pc : Fin maxPc} {t : WT}
    (hins : instrAt k pc = .toEnd t) (hpc : pc.val + 1 < maxPc) (l : List Sym) :
    ∀ (c : Cfg input), c.state = at_ k pc → Holds (c.workTapes t) (c.workTapePos t) l →
      c.workTapes t (c.workTapePos t + l.length) = none →
    ∃ c', Reach c (l.length + 1) c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [t] ∧
      c'.workTapes t = c.workTapes t ∧ c'.workTapePos t = c.workTapePos t + l.length := by
  induction l with
  | nil =>
    intro c hq _ hend
    have h := step_instr hq hins
    simp only [execInstr, workTapeSymbols_eq] at h
    simp only [List.length_nil, Nat.cast_zero, add_zero] at hend
    rw [hend] at h
    simp only [Act.base_out, Option.toList_none, Act.base_next] at h
    refine ⟨_, h, ?_, ?_, ?_, ?_⟩
    · simp [resolve_adv k pc hpc]
    · exact untouched_applyAct ⟨fun j => rfl, fun d _ => rfl⟩ _ _
    · rw [applyAct_workTapes_of_none _ _ _ t (by simp)]
    · simp
  | cons s l ih =>
    intro c hq hl hend
    have h := step_instr hq hins
    simp only [execInstr, workTapeSymbols_eq] at h
    rw [hl.head] at h
    simp only [Act.mw_out, Act.base_out, Option.toList_none, Act.mw_next, Act.base_next,
      resolve_stay] at h
    set c₁ := applyAct ((Act.base (.stay p0)).mw t 1) (some ⟨k, pc, p0⟩) c with hc₁
    have hu : Untouched c c₁ [t] :=
      untouched_applyAct ⟨fun j => rfl, fun d hd => by
        have : d ≠ t := by simpa using hd
        simp [Act.mw_works_of_ne _ this]⟩ _ _
    have htape : c₁.workTapes t = c.workTapes t := by
      rw [hc₁, applyAct_workTapes_of_none _ _ _ t (by simp)]
    have hpos : c₁.workTapePos t = c.workTapePos t + 1 := by simp [hc₁]
    obtain ⟨c', hr, hst, hu', htape', hpos'⟩ := ih c₁ (by simp [hc₁]) (by rw [htape, hpos]; exact hl.tail)
      (by
        rw [htape, hpos]
        simp only [List.length_cons] at hend
        convert hend using 2
        push_cast; ring)
    refine ⟨c', ?_, hst, ?_, htape'.trans htape, ?_⟩
    · exact ((h.trans hr).cast_n (by simp only [List.length_cons]; omega)).cast_out (List.nil_append _)
    · exact (hu.trans hu').mono (by simp)
    · rw [hpos', hpos]; simp only [List.length_cons]; push_cast; ring

end MIPRE.TM.Interp

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

/-- `c'` agrees with `c` on the input heads outside `SI` and on the work tapes outside `SW`. -/
def Untouched (c c' : Cfg input) (SI : List IT) (SW : List WT) : Prop :=
  (∀ j, j ∉ SI → c'.inputPos j = c.inputPos j) ∧
    ∀ d, d ∉ SW → c'.workTapes d = c.workTapes d ∧ c'.workTapePos d = c.workTapePos d

namespace Untouched

theorem refl (c : Cfg input) (SI : List IT) (SW : List WT) : Untouched c c SI SW :=
  ⟨fun _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩⟩

theorem trans {c c' c'' : Cfg input} {SI SI' : List IT} {SW SW' : List WT}
    (h : Untouched c c' SI SW) (h' : Untouched c' c'' SI' SW') :
    Untouched c c'' (SI ++ SI') (SW ++ SW') := by
  refine ⟨fun j hj => ?_, fun d hd => ?_⟩
  · rw [List.mem_append, not_or] at hj
    exact (h'.1 j hj.2).trans (h.1 j hj.1)
  · rw [List.mem_append, not_or] at hd
    obtain ⟨h1, h2⟩ := h.2 d hd.1
    obtain ⟨h1', h2'⟩ := h'.2 d hd.2
    exact ⟨h1'.trans h1, h2'.trans h2⟩

theorem mono {c c' : Cfg input} {SI SI' : List IT} {SW SW' : List WT} (h : Untouched c c' SI SW)
    (hI : ∀ j ∈ SI, j ∈ SI') (hW : ∀ d ∈ SW, d ∈ SW') : Untouched c c' SI' SW' :=
  ⟨fun j hj => h.1 j fun hmem => hj (hI j hmem), fun d hd => h.2 d fun hmem => hd (hW d hmem)⟩

theorem tapes {c c' : Cfg input} {SI : List IT} {SW : List WT} (h : Untouched c c' SI SW) {d : WT}
    (hd : d ∉ SW) : c'.workTapes d = c.workTapes d := (h.2 d hd).1

theorem pos {c c' : Cfg input} {SI : List IT} {SW : List WT} (h : Untouched c c' SI SW) {d : WT}
    (hd : d ∉ SW) : c'.workTapePos d = c.workTapePos d := (h.2 d hd).2

theorem inputPos {c c' : Cfg input} {SI : List IT} {SW : List WT} (h : Untouched c c' SI SW) {j : IT}
    (hj : j ∉ SI) : c'.inputPos j = c.inputPos j := h.1 j hj

theorem inputPos_eq {c c' : Cfg input} {SW : List WT} (h : Untouched c c' [] SW) :
    c'.inputPos = c.inputPos := funext fun j => h.1 j (by simp)

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

/-- An action that moves only the input heads in `SI` and touches only the work tapes in
`SW`. -/
def Act.Within (a : Act) (SI : List IT) (SW : List WT) : Prop :=
  (∀ j, j ∉ SI → a.inMoves j = 0) ∧ ∀ d, d ∉ SW → a.works d = (none, 0)

theorem untouched_applyAct {a : Act} {SI : List IT} {SW : List WT} (h : a.Within SI SW)
    (q' : Option Ctl) (c : Cfg input) : Untouched c (applyAct a q' c) SI SW := by
  refine ⟨fun j hj => ?_, fun d hd => ?_⟩
  · simp [applyAct, h.1 j hj]
  · have := h.2 d hd
    refine ⟨?_, ?_⟩
    · rw [applyAct_workTapes_of_none _ _ _ _ (by rw [this])]
    · rw [applyAct_workTapePos, this]; simp

/-! ## `write` -/

theorem exec_write {k : ProgId} {pc : Fin maxPc} {t : WT} {s : Sym}
    (hins : instrAt k pc = .write t s) (hpc : pc.val + 1 < maxPc) (c : Cfg input)
    (hq : c.state = at_ k pc) :
    ∃ c', Reach c 1 c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [] [t] ∧
      c'.workTapes t = Function.update (c.workTapes t) (c.workTapePos t) (some s) ∧
      c'.workTapePos t = c.workTapePos t + 1 := by
  have h := step_instr hq hins
  simp only [execInstr] at h
  refine ⟨_, h, ?_, ?_, ?_, ?_⟩
  · simp [resolve_adv k pc hpc]
  · refine untouched_applyAct ⟨fun j _ => rfl, fun d hd => ?_⟩ _ _
    have : d ≠ t := by simpa using hd
    simp [Act.mw_works_of_ne _ this, Act.ww_works_of_ne _ this]
  · rw [applyAct_workTapes_of_some _ _ _ t (s := some s) (by simp)]
  · simp

/-! ## `move` -/

theorem exec_move {k : ProgId} {pc : Fin maxPc} {t : WT} {dir : Bool}
    (hins : instrAt k pc = .move t dir) (hpc : pc.val + 1 < maxPc) (c : Cfg input)
    (hq : c.state = at_ k pc) :
    ∃ c', Reach c 1 c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [] [t] ∧
      c'.workTapes t = c.workTapes t ∧
      c'.workTapePos t = c.workTapePos t + (if dir then 1 else -1) := by
  have h := step_instr hq hins
  simp only [execInstr] at h
  refine ⟨_, h, ?_, ?_, ?_, ?_⟩
  · simp [resolve_adv k pc hpc]
  · refine untouched_applyAct ⟨fun j _ => rfl, fun d hd => ?_⟩ _ _
    have : d ≠ t := by simpa using hd
    simp [Act.mw_works_of_ne _ this]
  · rw [applyAct_workTapes_of_none _ _ _ t (by simp)]
  · cases dir <;> simp

/-! ## `toEnd` -/

theorem exec_toEnd {k : ProgId} {pc : Fin maxPc} {t : WT}
    (hins : instrAt k pc = .toEnd t) (hpc : pc.val + 1 < maxPc) (l : List Sym) :
    ∀ (c : Cfg input), c.state = at_ k pc → Holds (c.workTapes t) (c.workTapePos t) l →
      c.workTapes t (c.workTapePos t + l.length) = none →
    ∃ c', Reach c (l.length + 1) c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [] [t] ∧
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
    · exact untouched_applyAct ⟨fun j _ => rfl, fun d _ => rfl⟩ _ _
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
    have hu : Untouched c c₁ [] [t] :=
      untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
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
    · exact (hu.trans hu').mono (by simp) (by simp)
    · rw [hpos', hpos]; simp only [List.length_cons]; push_cast; ring

/-! ## `rewind` -/

/-- The scan of `rewind` from `p1`: cells `pos - n + 1 … pos` not blank, `pos - n` blank. -/
theorem scan_rewind {k : ProgId} {pc : Fin maxPc} {t : WT}
    (hins : instrAt k pc = .rewind t) (hpc : pc.val + 1 < maxPc) (n : ℕ) :
    ∀ (c : Cfg input), c.state = some ⟨k, pc, p1⟩ →
      (∀ q, c.workTapePos t - n < q → q ≤ c.workTapePos t → c.workTapes t q ≠ none) →
      c.workTapes t (c.workTapePos t - n) = none →
    ∃ c', Reach c (n + 1) c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [] [t] ∧
      c'.workTapes t = c.workTapes t ∧ c'.workTapePos t = c.workTapePos t - n + 1 := by
  induction n with
  | zero =>
    intro c hq _ hbl
    have h := step_instr hq hins
    simp only [execInstr, workTapeSymbols_eq] at h
    simp only [Nat.cast_zero, sub_zero] at hbl
    rw [hbl] at h
    simp only [Act.mw_out, Act.base_out, Option.toList_none, Act.mw_next, Act.base_next] at h
    refine ⟨_, h, ?_, ?_, ?_, ?_⟩
    · simp [resolve_adv k pc hpc]
    · exact untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
        have : d ≠ t := by simpa using hd
        simp [Act.mw_works_of_ne _ this]⟩ _ _
    · rw [applyAct_workTapes_of_none _ _ _ t (by simp)]
    · simp
  | succ n ih =>
    intro c hq hne hbl
    have h := step_instr hq hins
    simp only [execInstr, workTapeSymbols_eq] at h
    obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp (hne (c.workTapePos t) (by push_cast; omega) le_rfl)
    rw [hs] at h
    simp only [Act.mw_out, Act.base_out, Option.toList_none, Act.mw_next, Act.base_next,
      resolve_stay] at h
    set c₁ := applyAct ((Act.base (.stay p1)).mw t (-1)) (some ⟨k, pc, p1⟩) c with hc₁
    have hu : Untouched c c₁ [] [t] :=
      untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
        have : d ≠ t := by simpa using hd
        simp [Act.mw_works_of_ne _ this]⟩ _ _
    have htape : c₁.workTapes t = c.workTapes t := by
      rw [hc₁, applyAct_workTapes_of_none _ _ _ t (by simp)]
    have hpos : c₁.workTapePos t = c.workTapePos t - 1 := by simp [hc₁]; ring
    obtain ⟨c', hr, hst, hu', htape', hpos'⟩ := ih c₁ (by simp [hc₁])
      (by
        intro q h1 h2
        rw [htape]
        rw [hpos] at h1 h2
        exact hne q (by push_cast; omega) (by omega))
      (by rw [htape, hpos]; convert hbl using 2; push_cast; ring)
    refine ⟨c', ((h.trans hr).cast_n (by omega)).cast_out (List.nil_append _), hst, ?_,
      htape'.trans htape, ?_⟩
    · exact (hu.trans hu').mono (by simp) (by simp)
    · rw [hpos', hpos]; push_cast; ring

/-- From cell `p + n` with cells `p … p + n - 1` not blank and `p - 1` blank, `rewind`
reaches cell `p` (the head may start on the blank after the content). -/
theorem exec_rewind {k : ProgId} {pc : Fin maxPc} {t : WT}
    (hins : instrAt k pc = .rewind t) (hpc : pc.val + 1 < maxPc) (n : ℕ)
    (c : Cfg input) (hq : c.state = at_ k pc)
    (hne : ∀ q, c.workTapePos t - n ≤ q → q < c.workTapePos t → c.workTapes t q ≠ none)
    (hbl : c.workTapes t (c.workTapePos t - n - 1) = none) :
    ∃ c', Reach c (n + 2) c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [] [t] ∧
      c'.workTapes t = c.workTapes t ∧ c'.workTapePos t = c.workTapePos t - n := by
  have h := step_instr hq hins
  simp only [execInstr, Act.mw_out, Act.base_out, Option.toList_none, Act.mw_next, Act.base_next,
    resolve_stay] at h
  set c₁ := applyAct ((Act.base (.stay p1)).mw t (-1)) (some ⟨k, pc, p1⟩) c with hc₁
  have hu : Untouched c c₁ [] [t] :=
    untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
      have : d ≠ t := by simpa using hd
      simp [Act.mw_works_of_ne _ this]⟩ _ _
  have htape : c₁.workTapes t = c.workTapes t := by
    rw [hc₁, applyAct_workTapes_of_none _ _ _ t (by simp)]
  have hpos : c₁.workTapePos t = c.workTapePos t - 1 := by simp [hc₁]; ring
  obtain ⟨c', hr, hst, hu', htape', hpos'⟩ := scan_rewind hins hpc n c₁ (by simp [hc₁])
    (by
      intro q h1 h2
      rw [htape]
      rw [hpos] at h1 h2
      exact hne q (by omega) (by omega))
    (by rw [htape, hpos]; convert hbl using 2; ring)
  refine ⟨c', ((h.trans hr).cast_n (by omega)).cast_out (List.nil_append _), hst, ?_,
    htape'.trans htape, ?_⟩
  · exact (hu.trans hu').mono (by simp) (by simp)
  · rw [hpos', hpos]; ring

/-! ## `eraseRight` -/

/-- The erasing scan of `eraseRight` (`p1`): erase the `l` held from the head, then one
left. -/
theorem scan_erase {k : ProgId} {pc : Fin maxPc} {t : WT}
    (hins : instrAt k pc = .eraseRight t) (l : List Sym) :
    ∀ (c : Cfg input), c.state = some ⟨k, pc, p1⟩ → Holds (c.workTapes t) (c.workTapePos t) l →
      c.workTapes t (c.workTapePos t + l.length) = none →
    ∃ c', Reach c (l.length + 1) c' [] ∧ c'.state = some ⟨k, pc, p2⟩ ∧ Untouched c c' [] [t] ∧
      (∀ q, (q < c.workTapePos t ∨ c.workTapePos t + l.length ≤ q) →
        c'.workTapes t q = c.workTapes t q) ∧
      BlankFrom (c'.workTapes t) (c.workTapePos t) l.length ∧
      c'.workTapePos t = c.workTapePos t + l.length - 1 := by
  induction l with
  | nil =>
    intro c hq _ hend
    have h := step_instr hq hins
    simp only [execInstr, workTapeSymbols_eq] at h
    simp only [List.length_nil, Nat.cast_zero, add_zero] at hend
    rw [hend] at h
    simp only [Act.mw_out, Act.base_out, Option.toList_none, Act.mw_next, Act.base_next,
      resolve_stay] at h
    refine ⟨_, h, rfl, ?_, ?_, ?_, ?_⟩
    · exact untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
        have : d ≠ t := by simpa using hd
        simp [Act.mw_works_of_ne _ this]⟩ _ _
    · intro q _; rw [applyAct_workTapes_of_none _ _ _ t (by simp)]
    · intro q _ h2; simp at h2; omega
    · simp; ring
  | cons s l ih =>
    intro c hq hl hend
    have h := step_instr hq hins
    simp only [execInstr, workTapeSymbols_eq] at h
    rw [hl.head] at h
    simp only [Act.mw_out, Act.ww_out, Act.base_out, Option.toList_none, Act.mw_next, Act.ww_next,
      Act.base_next, resolve_stay] at h
    set c₁ := applyAct (((Act.base (.stay p1)).ww t none).mw t 1) (some ⟨k, pc, p1⟩) c with hc₁
    have hu : Untouched c c₁ [] [t] :=
      untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
        have : d ≠ t := by simpa using hd
        simp [Act.mw_works_of_ne _ this, Act.ww_works_of_ne _ this]⟩ _ _
    have htape : c₁.workTapes t = Function.update (c.workTapes t) (c.workTapePos t) none := by
      rw [hc₁, applyAct_workTapes_of_some _ _ _ t (s := none) (by simp)]
    have hpos : c₁.workTapePos t = c.workTapePos t + 1 := by simp [hc₁]
    obtain ⟨c', hr, hst, hu', hout, hblank, hpos'⟩ := ih c₁ (by simp [hc₁])
      (by rw [htape, hpos]; exact hl.tail.update_of_not_mem _ (Or.inl (by omega)))
      (by
        rw [htape, hpos, Function.update_of_ne (by simp only [List.length_cons] at hend; omega)]
        simp only [List.length_cons] at hend
        convert hend using 2
        push_cast; ring)
    refine ⟨c', ((h.trans hr).cast_n (by simp only [List.length_cons]; omega)).cast_out
      (List.nil_append _), hst, (hu.trans hu').mono (by simp) (by simp), ?_, ?_, ?_⟩
    · intro q hq'
      rw [hout q (by rw [hpos]; simp only [List.length_cons] at hq'; push_cast at hq' ⊢; omega),
        htape, Function.update_of_ne (by simp only [List.length_cons] at hq'; push_cast at hq'; omega)]
    · intro q h1 h2
      simp only [List.length_cons] at h2
      by_cases hq0 : q = c.workTapePos t
      · subst hq0
        rw [hout _ (Or.inl (by rw [hpos]; omega)), htape, Function.update_self]
      · exact hblank q (by rw [hpos]; omega) (by rw [hpos]; push_cast at h2 ⊢; omega)
    · rw [hpos', hpos]; simp only [List.length_cons]; push_cast; ring

/-- The return scan of `eraseRight` (`p2`): back over `n` blanks to the `$`, erase it. -/
theorem scan_eraseBack {k : ProgId} {pc : Fin maxPc} {t : WT}
    (hins : instrAt k pc = .eraseRight t) (hpc : pc.val + 1 < maxPc) (n : ℕ) :
    ∀ (c : Cfg input), c.state = some ⟨k, pc, p2⟩ →
      BlankFrom (c.workTapes t) (c.workTapePos t - n + 1) n →
      c.workTapes t (c.workTapePos t - n) = some .fr →
    ∃ c', Reach c (n + 1) c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [] [t] ∧
      c'.workTapes t = Function.update (c.workTapes t) (c.workTapePos t - n) none ∧
      c'.workTapePos t = c.workTapePos t - n := by
  induction n with
  | zero =>
    intro c hq _ hm
    have h := step_instr hq hins
    simp only [execInstr, workTapeSymbols_eq] at h
    simp only [Nat.cast_zero, sub_zero] at hm
    rw [hm] at h
    simp only [Act.ww_out, Act.base_out, Option.toList_none, Act.ww_next, Act.base_next] at h
    refine ⟨_, h, ?_, ?_, ?_, ?_⟩
    · simp [resolve_adv k pc hpc]
    · exact untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
        have : d ≠ t := by simpa using hd
        simp [Act.ww_works_of_ne _ this]⟩ _ _
    · rw [applyAct_workTapes_of_some _ _ _ t (s := none) (by simp)]; simp
    · simp
  | succ n ih =>
    intro c hq hbl hm
    have h := step_instr hq hins
    simp only [execInstr, workTapeSymbols_eq] at h
    have hread : c.workTapes t (c.workTapePos t) = none :=
      hbl _ (by push_cast; omega) (by push_cast; omega)
    rw [hread] at h
    simp only [Act.mw_out, Act.base_out, Option.toList_none, Act.mw_next, Act.base_next,
      resolve_stay] at h
    set c₁ := applyAct ((Act.base (.stay p2)).mw t (-1)) (some ⟨k, pc, p2⟩) c with hc₁
    have hu : Untouched c c₁ [] [t] :=
      untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
        have : d ≠ t := by simpa using hd
        simp [Act.mw_works_of_ne _ this]⟩ _ _
    have htape : c₁.workTapes t = c.workTapes t := by
      rw [hc₁, applyAct_workTapes_of_none _ _ _ t (by simp)]
    have hpos : c₁.workTapePos t = c.workTapePos t - 1 := by simp [hc₁]; ring
    obtain ⟨c', hr, hst, hu', htape', hpos'⟩ := ih c₁ (by simp [hc₁])
      (by
        intro q h1 h2
        rw [htape]
        rw [hpos] at h1 h2
        exact hbl q (by push_cast at h1 ⊢; omega) (by push_cast at h2 ⊢; omega))
      (by rw [htape, hpos]; convert hm using 2; push_cast; ring)
    refine ⟨c', ((h.trans hr).cast_n (by omega)).cast_out (List.nil_append _), hst, ?_, ?_, ?_⟩
    · exact (hu.trans hu').mono (by simp) (by simp)
    · rw [htape', htape, hpos]; congr 1; push_cast; ring
    · rw [hpos', hpos]; push_cast; ring

/-- Erase the `l` held from the head (no `$` among its symbols), ending where it started. -/
theorem exec_eraseRight {k : ProgId} {pc : Fin maxPc} {t : WT}
    (hins : instrAt k pc = .eraseRight t) (hpc : pc.val + 1 < maxPc) (l : List Sym)
    (c : Cfg input) (hq : c.state = at_ k pc) (hl : Holds (c.workTapes t) (c.workTapePos t) l)
    (hend : c.workTapes t (c.workTapePos t + l.length) = none) :
    ∃ c', Reach c (2 * l.length + 1) c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [] [t] ∧
      (∀ q, (q < c.workTapePos t ∨ c.workTapePos t + l.length ≤ q) →
        c'.workTapes t q = c.workTapes t q) ∧
      BlankFrom (c'.workTapes t) (c.workTapePos t) l.length ∧
      c'.workTapePos t = c.workTapePos t := by
  cases l with
  | nil =>
    have h := step_instr hq hins
    simp only [execInstr, workTapeSymbols_eq] at h
    simp only [List.length_nil, Nat.cast_zero, add_zero] at hend
    rw [hend] at h
    simp only [Act.base_out, Option.toList_none, Act.base_next] at h
    refine ⟨_, h, ?_, ?_, ?_, ?_, ?_⟩
    · simp [resolve_adv k pc hpc]
    · exact untouched_applyAct ⟨fun j _ => rfl, fun d _ => rfl⟩ _ _
    · intro q _; rw [applyAct_workTapes_of_none _ _ _ t (by simp)]
    · intro q _ h2; simp at h2; omega
    · simp
  | cons s l =>
    have h := step_instr hq hins
    simp only [execInstr, workTapeSymbols_eq] at h
    rw [hl.head] at h
    simp only [Act.mw_out, Act.ww_out, Act.base_out, Option.toList_none, Act.mw_next, Act.ww_next,
      Act.base_next, resolve_stay] at h
    set c₁ := applyAct (((Act.base (.stay p1)).ww t (some .fr)).mw t 1) (some ⟨k, pc, p1⟩) c
      with hc₁
    have hu : Untouched c c₁ [] [t] :=
      untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
        have : d ≠ t := by simpa using hd
        simp [Act.mw_works_of_ne _ this, Act.ww_works_of_ne _ this]⟩ _ _
    have htape : c₁.workTapes t = Function.update (c.workTapes t) (c.workTapePos t) (some .fr) := by
      rw [hc₁, applyAct_workTapes_of_some _ _ _ t (s := some .fr) (by simp)]
    have hpos : c₁.workTapePos t = c.workTapePos t + 1 := by simp [hc₁]
    simp only [List.length_cons] at hend
    obtain ⟨c₂, hr₂, hst₂, hu₂, hout₂, hblank₂, hpos₂⟩ := scan_erase hins l c₁ (by simp [hc₁])
      (by rw [htape, hpos]; exact hl.tail.update_of_not_mem _ (Or.inl (by omega)))
      (by
        rw [htape, hpos, Function.update_of_ne (by omega)]
        convert hend using 2
        push_cast; ring)
    have hmark : c₂.workTapes t (c.workTapePos t) = some .fr := by
      rw [hout₂ _ (Or.inl (by rw [hpos]; omega)), htape, Function.update_self]
    obtain ⟨c₃, hr₃, hst₃, hu₃, htape₃, hpos₃⟩ := scan_eraseBack hins hpc l.length c₂ hst₂
      (by
        intro q h1 h2
        rw [hpos₂, hpos] at h1 h2
        exact hblank₂ q (by rw [hpos]; omega) (by rw [hpos]; omega))
      (by rw [hpos₂, hpos]; convert hmark using 2; ring)
    have hp₀ : c₂.workTapePos t - l.length = c.workTapePos t := by rw [hpos₂, hpos]; ring
    refine ⟨c₃, (((h.trans hr₂).trans hr₃).cast_n (by simp only [List.length_cons]; omega)).cast_out
      (by simp), hst₃, ((hu.trans hu₂).trans hu₃).mono (by simp) (by simp), ?_, ?_, ?_⟩
    · intro q hq'
      simp only [List.length_cons] at hq'
      rw [htape₃, hp₀, Function.update_of_ne (by push_cast at hq'; omega),
        hout₂ q (by rw [hpos]; push_cast at hq' ⊢; omega), htape,
        Function.update_of_ne (by push_cast at hq'; omega)]
    · intro q h1 h2
      simp only [List.length_cons] at h2
      rw [htape₃, hp₀]
      by_cases hq0 : q = c.workTapePos t
      · subst hq0; simp
      · rw [Function.update_of_ne hq0]
        exact hblank₂ q (by rw [hpos]; omega) (by rw [hpos]; push_cast at h2 ⊢; omega)
    · rw [hpos₃, hp₀]

/-! ## `copyUntil` -/

/-- Copy the `l` held from the head of `src` (none of whose symbols is `m`) onto `dst`,
stopping with the `src` head on the `m` after it. -/
theorem exec_copyUntil {k : ProgId} {pc : Fin maxPc} {m : Option Sym} {src dst : WT}
    (hins : instrAt k pc = .copyUntil m src dst) (hpc : pc.val + 1 < maxPc) (hsd : src ≠ dst)
    (l : List Sym) :
    ∀ (c : Cfg input), c.state = at_ k pc → Holds (c.workTapes src) (c.workTapePos src) l →
      (∀ s ∈ l, some s ≠ m) → c.workTapes src (c.workTapePos src + l.length) = m →
    ∃ c', Reach c (l.length + 1) c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [] [src, dst] ∧
      c'.workTapes src = c.workTapes src ∧ c'.workTapePos src = c.workTapePos src + l.length ∧
      Holds (c'.workTapes dst) (c.workTapePos dst) l ∧
      (∀ q, (q < c.workTapePos dst ∨ c.workTapePos dst + l.length ≤ q) →
        c'.workTapes dst q = c.workTapes dst q) ∧
      c'.workTapePos dst = c.workTapePos dst + l.length := by
  induction l with
  | nil =>
    intro c hq _ _ hend
    have h := step_instr hq hins
    simp only [execInstr, workTapeSymbols_eq] at h
    simp only [List.length_nil, Nat.cast_zero, add_zero] at hend
    simp only [hend, eq_self_iff_true, if_true, Act.base_out, Option.toList_none, Act.base_next] at h
    refine ⟨_, h, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [resolve_adv k pc hpc]
    · exact untouched_applyAct ⟨fun j _ => rfl, fun d _ => rfl⟩ _ _
    · rw [applyAct_workTapes_of_none _ _ _ src (by simp)]
    · simp
    · simp
    · intro q _; rw [applyAct_workTapes_of_none _ _ _ dst (by simp)]
    · simp
  | cons s l ih =>
    intro c hq hl hm hend
    have h := step_instr hq hins
    simp only [execInstr, workTapeSymbols_eq] at h
    simp only [hl.head, if_neg (hm s (by simp)), Act.mw_out, Act.ww_out, Act.base_out,
      Option.toList_none, Act.mw_next, Act.ww_next, Act.base_next, resolve_stay] at h
    set c₁ := applyAct ((((Act.base (.stay p0)).ww dst (some s)).mw dst 1).mw src 1)
      (some ⟨k, pc, p0⟩) c with hc₁
    have hu : Untouched c c₁ [] [src, dst] :=
      untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
        have h1 : d ≠ src := fun e => hd (by simp [e])
        have h2 : d ≠ dst := fun e => hd (by simp [e])
        simp [Act.mw_works_of_ne _ h1, Act.mw_works_of_ne _ h2, Act.ww_works_of_ne _ h2]⟩ _ _
    have hsrc : c₁.workTapes src = c.workTapes src := by
      rw [hc₁, applyAct_workTapes_of_none _ _ _ src (by simp [Act.mw_works_of_ne _ hsd,
        Act.ww_works_of_ne _ hsd])]
    have hsrcp : c₁.workTapePos src = c.workTapePos src + 1 := by
      simp [hc₁, Act.mw_works_of_ne _ hsd, Act.ww_works_of_ne _ hsd]
    have hdst : c₁.workTapes dst = Function.update (c.workTapes dst) (c.workTapePos dst) (some s) := by
      rw [hc₁, applyAct_workTapes_of_some _ _ _ dst (s := some s)
        (by simp [Act.mw_works_of_ne _ hsd.symm])]
    have hdstp : c₁.workTapePos dst = c.workTapePos dst + 1 := by
      simp [hc₁, Act.mw_works_of_ne _ hsd.symm]
    obtain ⟨c', hr, hst, hu', hsrc', hsrcp', hhold, hout, hdstp'⟩ := ih c₁ (by simp [hc₁])
      (by rw [hsrc, hsrcp]; exact hl.tail) (fun s' hs' => hm s' (by simp [hs']))
      (by
        rw [hsrc, hsrcp]
        simp only [List.length_cons] at hend
        convert hend using 2
        push_cast; ring)
    refine ⟨c', ((h.trans hr).cast_n (by simp only [List.length_cons]; omega)).cast_out
      (List.nil_append _), hst, (hu.trans hu').mono (by simp) (by simp), hsrc'.trans hsrc, ?_, ?_, ?_, ?_⟩
    · rw [hsrcp', hsrcp]; simp only [List.length_cons]; push_cast; ring
    · refine Holds.cons ?_ ?_
      · rw [hout _ (Or.inl (by rw [hdstp]; omega)), hdst, Function.update_self]
      · rw [← hdstp]; exact hhold
    · intro q hq'
      simp only [List.length_cons] at hq'
      rw [hout q (by rw [hdstp]; push_cast at hq' ⊢; omega), hdst,
        Function.update_of_ne (by push_cast at hq'; omega)]
    · rw [hdstp', hdstp]; simp only [List.length_cons]; push_cast; ring

/-! ## `branch`, `jump`, `emit`, `halt` -/

theorem exec_branch_taken {k : ProgId} {pc : Fin maxPc} {t : WT} {s : Option Sym} {target : ProgId}
    (hins : instrAt k pc = .branch t s target) (c : Cfg input) (hq : c.state = at_ k pc)
    (hs : c.workTapes t (c.workTapePos t) = s) :
    ∃ c', Reach c 1 c' [] ∧ c'.state = at_ target ⟨0, by decide⟩ ∧ Untouched c c' [] [] ∧
      ∀ d, c'.workTapes d = c.workTapes d ∧ c'.workTapePos d = c.workTapePos d := by
  have h := step_instr hq hins
  simp only [execInstr, workTapeSymbols_eq, hs, if_true, Act.base_out, Option.toList_none,
    Act.base_next, resolve_jmp] at h
  refine ⟨_, h, rfl, untouched_applyAct ⟨fun j _ => rfl, fun d _ => rfl⟩ _ _, fun d => ?_⟩
  exact ⟨by rw [applyAct_workTapes_of_none _ _ _ d (by simp)], by simp⟩

theorem exec_branch_not {k : ProgId} {pc : Fin maxPc} {t : WT} {s : Option Sym} {target : ProgId}
    (hins : instrAt k pc = .branch t s target) (hpc : pc.val + 1 < maxPc) (c : Cfg input)
    (hq : c.state = at_ k pc) (hs : c.workTapes t (c.workTapePos t) ≠ s) :
    ∃ c', Reach c 1 c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [] [] ∧
      ∀ d, c'.workTapes d = c.workTapes d ∧ c'.workTapePos d = c.workTapePos d := by
  have h := step_instr hq hins
  simp only [execInstr, workTapeSymbols_eq, hs, if_false, Act.base_out, Option.toList_none,
    Act.base_next] at h
  refine ⟨_, h, by simp [resolve_adv k pc hpc], untouched_applyAct ⟨fun j _ => rfl, fun d _ => rfl⟩ _ _,
    fun d => ?_⟩
  exact ⟨by rw [applyAct_workTapes_of_none _ _ _ d (by simp)], by simp⟩

theorem exec_jump {k : ProgId} {pc : Fin maxPc} {target : ProgId}
    (hins : instrAt k pc = .jump target) (c : Cfg input) (hq : c.state = at_ k pc) :
    ∃ c', Reach c 1 c' [] ∧ c'.state = at_ target ⟨0, by decide⟩ ∧ Untouched c c' [] [] ∧
      ∀ d, c'.workTapes d = c.workTapes d ∧ c'.workTapePos d = c.workTapePos d := by
  have h := step_instr hq hins
  simp only [execInstr, Act.base_out, Option.toList_none, Act.base_next, resolve_jmp] at h
  refine ⟨_, h, rfl, untouched_applyAct ⟨fun j _ => rfl, fun d _ => rfl⟩ _ _, fun d => ?_⟩
  exact ⟨by rw [applyAct_workTapes_of_none _ _ _ d (by simp)], by simp⟩

theorem exec_emit {k : ProgId} {pc : Fin maxPc} {s : Sym}
    (hins : instrAt k pc = .emit s) (hpc : pc.val + 1 < maxPc) (c : Cfg input)
    (hq : c.state = at_ k pc) :
    ∃ c', Reach c 1 c' [s] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [] [] ∧
      ∀ d, c'.workTapes d = c.workTapes d ∧ c'.workTapePos d = c.workTapePos d := by
  have h := step_instr hq hins
  simp only [execInstr, Act.emit_out, Option.toList_some, Act.emit_next, Act.base_next] at h
  refine ⟨_, h, by simp [resolve_adv k pc hpc], untouched_applyAct ⟨fun j _ => rfl, fun d _ => rfl⟩ _ _,
    fun d => ?_⟩
  exact ⟨by rw [applyAct_workTapes_of_none _ _ _ d (by simp)], by simp⟩

theorem exec_halt {k : ProgId} {pc : Fin maxPc} (hins : instrAt k pc = .halt) (c : Cfg input)
    (hq : c.state = at_ k pc) : HaltsIn c 1 := by
  have h := step_instr hq hins
  simp only [execInstr, Act.base_out, Option.toList_none, Act.base_next, resolve_halt] at h
  exact HaltsIn.of_reach h rfl

/-! ## Scanning left -/

/-- The scan of `leftToMarker` (phase `p1`): over the cells `pos - n + 1 … pos`, none holding
`m`, to the marker or blank at `pos - n`, then one right. -/
theorem scan_leftToMarker {k : ProgId} {pc : Fin maxPc} {m : Sym} {t : WT}
    (hins : instrAt k pc = .leftToMarker m t) (hpc : pc.val + 1 < maxPc) (l : List Sym) :
    ∀ (c : Cfg input), c.state = some ⟨k, pc, p1⟩ →
      Holds (c.workTapes t) (c.workTapePos t + 1 - l.length) l → (∀ s ∈ l, s ≠ m) →
      (c.workTapes t (c.workTapePos t - l.length) = some m ∨
        c.workTapes t (c.workTapePos t - l.length) = none) →
    ∃ c', Reach c (l.length + 1) c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [] [t] ∧
      c'.workTapes t = c.workTapes t ∧ c'.workTapePos t = c.workTapePos t - l.length + 1 := by
  induction l using List.reverseRecOn with
  | nil =>
    intro c hq _ _ hend
    have h := step_instr hq hins
    simp only [List.length_nil, Nat.cast_zero, sub_zero] at hend
    have hact : execInstr (.leftToMarker m t) p1 c.inputSymbols c.workTapeSymbols =
        (Act.base .adv).mw t 1 := by
      simp only [execInstr, workTapeSymbols_eq]
      rcases hend with h1 | h1 <;> simp [h1]
    rw [hact] at h
    simp only [Act.mw_out, Act.base_out, Option.toList_none, Act.mw_next, Act.base_next] at h
    refine ⟨_, h, by simp [resolve_adv k pc hpc], ?_, ?_, ?_⟩
    · exact untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
        have : d ≠ t := by simpa using hd
        simp [Act.mw_works_of_ne _ this]⟩ _ _
    · rw [applyAct_workTapes_of_none _ _ _ t (by simp)]
    · simp
  | append_singleton l a ih =>
    intro c hq hl hm hend
    have hlen : ((l ++ [a]).length : ℤ) = l.length + 1 := by simp
    have ha : c.workTapes t (c.workTapePos t) = some a := by
      have := hl.of_append_right
      rw [Holds.singleton_iff] at this
      convert this using 2
      rw [hlen]; ring
    have h := step_instr hq hins
    have hact : execInstr (.leftToMarker m t) p1 c.inputSymbols c.workTapeSymbols =
        (Act.base (.stay p1)).mw t (-1) := by
      simp only [execInstr, workTapeSymbols_eq, ha]
      rw [if_neg (hm a (by simp))]
    rw [hact] at h
    simp only [Act.mw_out, Act.base_out, Option.toList_none, Act.mw_next, Act.base_next,
      resolve_stay] at h
    set c₁ := applyAct ((Act.base (.stay p1)).mw t (-1)) (some ⟨k, pc, p1⟩) c with hc₁
    have hu : Untouched c c₁ [] [t] :=
      untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
        have : d ≠ t := by simpa using hd
        simp [Act.mw_works_of_ne _ this]⟩ _ _
    have htape : c₁.workTapes t = c.workTapes t := by
      rw [hc₁, applyAct_workTapes_of_none _ _ _ t (by simp)]
    have hpos : c₁.workTapePos t = c.workTapePos t - 1 := by simp [hc₁]; ring
    have hl' : Holds (c₁.workTapes t) (c₁.workTapePos t + 1 - l.length) l := by
      rw [htape, hpos]
      have := hl.of_append_left
      convert this using 1
      rw [hlen]; ring
    have hend' : c₁.workTapes t (c₁.workTapePos t - l.length) = some m ∨
        c₁.workTapes t (c₁.workTapePos t - l.length) = none := by
      rw [htape, hpos]
      convert hend using 3 <;> (rw [hlen]; ring)
    obtain ⟨c', hr, hst, hu', htape', hpos'⟩ := ih c₁ (by simp [hc₁]) hl' (fun s hs => hm s (by simp [hs])) hend'
    refine ⟨c', ((h.trans hr).cast_n (by simp; omega)).cast_out (List.nil_append _), hst,
      (hu.trans hu').mono (by simp) (by simp), htape'.trans htape, ?_⟩
    rw [hpos', hpos, hlen]; ring

/-- `leftToMarker`: from `pos`, with `l` (no `m`) on `pos - |l| … pos - 1` and the marker or a
blank at `pos - |l| - 1`, to `pos - |l|`. -/
theorem exec_leftToMarker {k : ProgId} {pc : Fin maxPc} {m : Sym} {t : WT}
    (hins : instrAt k pc = .leftToMarker m t) (hpc : pc.val + 1 < maxPc) (l : List Sym)
    (c : Cfg input) (hq : c.state = at_ k pc)
    (hl : Holds (c.workTapes t) (c.workTapePos t - l.length) l) (hm : ∀ s ∈ l, s ≠ m)
    (hend : c.workTapes t (c.workTapePos t - l.length - 1) = some m ∨
      c.workTapes t (c.workTapePos t - l.length - 1) = none) :
    ∃ c', Reach c (l.length + 2) c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [] [t] ∧
      c'.workTapes t = c.workTapes t ∧ c'.workTapePos t = c.workTapePos t - l.length := by
  have h := step_instr hq hins
  simp only [execInstr, Act.mw_out, Act.base_out, Option.toList_none, Act.mw_next, Act.base_next,
    resolve_stay] at h
  set c₁ := applyAct ((Act.base (.stay p1)).mw t (-1)) (some ⟨k, pc, p1⟩) c with hc₁
  have hu : Untouched c c₁ [] [t] :=
    untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
      have : d ≠ t := by simpa using hd
      simp [Act.mw_works_of_ne _ this]⟩ _ _
  have htape : c₁.workTapes t = c.workTapes t := by
    rw [hc₁, applyAct_workTapes_of_none _ _ _ t (by simp)]
  have hpos : c₁.workTapePos t = c.workTapePos t - 1 := by simp [hc₁]; ring
  obtain ⟨c', hr, hst, hu', htape', hpos'⟩ := scan_leftToMarker hins hpc l c₁ (by simp [hc₁])
    (by rw [htape, hpos]; convert hl using 2; ring) hm
    (by rw [htape, hpos]; convert hend using 3 <;> ring)
  refine ⟨c', ((h.trans hr).cast_n (by omega)).cast_out (List.nil_append _), hst,
    (hu.trans hu').mono (by simp) (by simp), htape'.trans htape, ?_⟩
  rw [hpos', hpos]; ring

/-! ## `popBack` -/

/-- The scan of `popBack` (phase `p2`): erase the cells `pos - n + 1 … pos`, none holding `m`,
to the marker or blank at `pos - n`, then one right. -/
theorem scan_popBack {k : ProgId} {pc : Fin maxPc} {m : Sym} {t : WT}
    (hins : instrAt k pc = .popBack m t) (hpc : pc.val + 1 < maxPc) (l : List Sym) :
    ∀ (c : Cfg input), c.state = some ⟨k, pc, p2⟩ →
      Holds (c.workTapes t) (c.workTapePos t + 1 - l.length) l → (∀ s ∈ l, s ≠ m) →
      (c.workTapes t (c.workTapePos t - l.length) = some m ∨
        c.workTapes t (c.workTapePos t - l.length) = none) →
    ∃ c', Reach c (l.length + 1) c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [] [t] ∧
      (∀ q, (q < c.workTapePos t + 1 - l.length ∨ c.workTapePos t < q) →
        c'.workTapes t q = c.workTapes t q) ∧
      BlankFrom (c'.workTapes t) (c.workTapePos t + 1 - l.length) l.length ∧
      c'.workTapePos t = c.workTapePos t - l.length + 1 := by
  induction l using List.reverseRecOn with
  | nil =>
    intro c hq _ _ hend
    have h := step_instr hq hins
    simp only [List.length_nil, Nat.cast_zero, sub_zero] at hend
    have hact : execInstr (.popBack m t) p2 c.inputSymbols c.workTapeSymbols =
        (Act.base .adv).mw t 1 := by
      simp only [execInstr, workTapeSymbols_eq]
      rcases hend with h1 | h1 <;> simp [h1]
    rw [hact] at h
    simp only [Act.mw_out, Act.base_out, Option.toList_none, Act.mw_next, Act.base_next] at h
    refine ⟨_, h, by simp [resolve_adv k pc hpc], ?_, ?_, ?_, ?_⟩
    · exact untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
        have : d ≠ t := by simpa using hd
        simp [Act.mw_works_of_ne _ this]⟩ _ _
    · intro q _; rw [applyAct_workTapes_of_none _ _ _ t (by simp)]
    · intro q h1 h2
      simp only [List.length_nil, Nat.cast_zero, sub_zero, add_zero] at h1 h2
      omega
    · simp
  | append_singleton l a ih =>
    intro c hq hl hm hend
    have hlen : ((l ++ [a]).length : ℤ) = l.length + 1 := by simp
    have ha : c.workTapes t (c.workTapePos t) = some a := by
      have := hl.of_append_right
      rw [Holds.singleton_iff] at this
      convert this using 2
      rw [hlen]; ring
    have h := step_instr hq hins
    have hact : execInstr (.popBack m t) p2 c.inputSymbols c.workTapeSymbols =
        ((Act.base (.stay p2)).ww t none).mw t (-1) := by
      simp only [execInstr, workTapeSymbols_eq, ha]
      rw [if_neg (hm a (by simp))]
    rw [hact] at h
    simp only [Act.mw_out, Act.ww_out, Act.base_out, Option.toList_none, Act.mw_next, Act.ww_next,
      Act.base_next, resolve_stay] at h
    set c₁ := applyAct (((Act.base (.stay p2)).ww t none).mw t (-1)) (some ⟨k, pc, p2⟩) c with hc₁
    have hu : Untouched c c₁ [] [t] :=
      untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
        have : d ≠ t := by simpa using hd
        simp [Act.mw_works_of_ne _ this, Act.ww_works_of_ne _ this]⟩ _ _
    have htape : c₁.workTapes t = Function.update (c.workTapes t) (c.workTapePos t) none := by
      rw [hc₁, applyAct_workTapes_of_some _ _ _ t (s := none) (by simp)]
    have hpos : c₁.workTapePos t = c.workTapePos t - 1 := by simp [hc₁]; ring
    have hl' : Holds (c₁.workTapes t) (c₁.workTapePos t + 1 - l.length) l := by
      rw [htape, hpos]
      have := hl.of_append_left.update_of_not_mem (q := c.workTapePos t) none
        (Or.inr (by rw [hlen]; omega))
      convert this using 1
      rw [hlen]; ring
    have hend' : c₁.workTapes t (c₁.workTapePos t - l.length) = some m ∨
        c₁.workTapes t (c₁.workTapePos t - l.length) = none := by
      rw [htape, hpos, Function.update_of_ne (by omega)]
      convert hend using 3 <;> (rw [hlen]; ring)
    obtain ⟨c', hr, hst, hu', hout, hblank, hpos'⟩ := ih c₁ (by simp [hc₁]) hl'
      (fun s hs => hm s (by simp [hs])) hend'
    refine ⟨c', ((h.trans hr).cast_n (by simp; omega)).cast_out (List.nil_append _), hst,
      (hu.trans hu').mono (by simp) (by simp), ?_, ?_, ?_⟩
    · intro q hq'
      rw [hlen] at hq'
      rw [hout q (by rw [hpos]; omega), htape, Function.update_of_ne (by omega)]
    · intro q h1 h2
      rw [hlen] at h1 h2
      by_cases hq0 : q = c.workTapePos t
      · subst hq0
        rw [hout _ (Or.inr (by rw [hpos]; omega)), htape, Function.update_self]
      · exact hblank q (by rw [hpos]; omega) (by rw [hpos]; omega)
    · rw [hpos', hpos, hlen]; ring

/-- `popBack` on an empty tape: two steps, nothing. -/
theorem exec_popBack_empty {k : ProgId} {pc : Fin maxPc} {m : Sym} {t : WT}
    (hins : instrAt k pc = .popBack m t) (hpc : pc.val + 1 < maxPc) (c : Cfg input)
    (hq : c.state = at_ k pc) (hbl : c.workTapes t (c.workTapePos t - 1) = none) :
    ∃ c', Reach c 2 c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [] [t] ∧
      c'.workTapes t = c.workTapes t ∧ c'.workTapePos t = c.workTapePos t := by
  have h := step_instr hq hins
  simp only [execInstr, Act.mw_out, Act.base_out, Option.toList_none, Act.mw_next, Act.base_next,
    resolve_stay] at h
  set c₁ := applyAct ((Act.base (.stay p1)).mw t (-1)) (some ⟨k, pc, p1⟩) c with hc₁
  have hu : Untouched c c₁ [] [t] :=
    untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
      have : d ≠ t := by simpa using hd
      simp [Act.mw_works_of_ne _ this]⟩ _ _
  have htape : c₁.workTapes t = c.workTapes t := by
    rw [hc₁, applyAct_workTapes_of_none _ _ _ t (by simp)]
  have hpos : c₁.workTapePos t = c.workTapePos t - 1 := by simp [hc₁]; ring
  have h2 := step_instr (c := c₁) (k := k) (pc := pc) (ph := p1) (by simp [hc₁]) hins
  simp only [execInstr, workTapeSymbols_eq, htape, hpos, hbl, Act.mw_out, Act.base_out,
    Option.toList_none, Act.mw_next, Act.base_next] at h2
  refine ⟨_, (h.trans h2).cast_out (List.nil_append _), by simp [resolve_adv k pc hpc], ?_, ?_, ?_⟩
  · exact (hu.trans (untouched_applyAct (SI := []) (SW := [t]) ⟨fun j _ => rfl, fun d hd => by
      have : d ≠ t := by simpa using hd
      simp [Act.mw_works_of_ne _ this]⟩ _ _)).mono (by simp) (by simp)
  · rw [applyAct_workTapes_of_none _ _ _ t (by simp), htape]
  · simp [hpos]

/-- `popBack`: from the end `pos`, with `l ++ [a]` on `pos - |l| - 1 … pos - 1`, `l` free of
`m`, and the marker or a blank before: erase them, ending at `pos - |l| - 1`. -/
theorem exec_popBack {k : ProgId} {pc : Fin maxPc} {m : Sym} {t : WT}
    (hins : instrAt k pc = .popBack m t) (hpc : pc.val + 1 < maxPc) (l : List Sym) (a : Sym)
    (c : Cfg input) (hq : c.state = at_ k pc)
    (hl : Holds (c.workTapes t) (c.workTapePos t - l.length - 1) (l ++ [a])) (hm : ∀ s ∈ l, s ≠ m)
    (hend : c.workTapes t (c.workTapePos t - l.length - 2) = some m ∨
      c.workTapes t (c.workTapePos t - l.length - 2) = none) :
    ∃ c', Reach c (l.length + 3) c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [] [t] ∧
      (∀ q, (q < c.workTapePos t - l.length - 1 ∨ c.workTapePos t ≤ q) →
        c'.workTapes t q = c.workTapes t q) ∧
      BlankFrom (c'.workTapes t) (c.workTapePos t - l.length - 1) (l.length + 1) ∧
      c'.workTapePos t = c.workTapePos t - l.length - 1 := by
  have h := step_instr hq hins
  simp only [execInstr, Act.mw_out, Act.base_out, Option.toList_none, Act.mw_next, Act.base_next,
    resolve_stay] at h
  set c₁ := applyAct ((Act.base (.stay p1)).mw t (-1)) (some ⟨k, pc, p1⟩) c with hc₁
  have hu : Untouched c c₁ [] [t] :=
    untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
      have : d ≠ t := by simpa using hd
      simp [Act.mw_works_of_ne _ this]⟩ _ _
  have htape : c₁.workTapes t = c.workTapes t := by
    rw [hc₁, applyAct_workTapes_of_none _ _ _ t (by simp)]
  have hpos : c₁.workTapePos t = c.workTapePos t - 1 := by simp [hc₁]; ring
  have ha : c.workTapes t (c.workTapePos t - 1) = some a := by
    have := hl.of_append_right
    rw [Holds.singleton_iff] at this
    convert this using 2; ring
  have h2 := step_instr (c := c₁) (k := k) (pc := pc) (ph := p1) (by simp [hc₁]) hins
  simp only [execInstr, workTapeSymbols_eq, htape, hpos, ha, Act.mw_out, Act.ww_out, Act.base_out,
    Option.toList_none, Act.mw_next, Act.ww_next, Act.base_next, resolve_stay] at h2
  set c₂ := applyAct (((Act.base (.stay p2)).ww t none).mw t (-1)) (some ⟨k, pc, p2⟩) c₁ with hc₂
  have hu₂ : Untouched c₁ c₂ [] [t] :=
    untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
      have : d ≠ t := by simpa using hd
      simp [Act.mw_works_of_ne _ this, Act.ww_works_of_ne _ this]⟩ _ _
  have htape₂ : c₂.workTapes t = Function.update (c.workTapes t) (c.workTapePos t - 1) none := by
    rw [hc₂, applyAct_workTapes_of_some _ _ _ t (s := none) (by simp), htape, hpos]
  have hpos₂ : c₂.workTapePos t = c.workTapePos t - 2 := by simp [hc₂, hpos]; ring
  have hl' : Holds (c₂.workTapes t) (c₂.workTapePos t + 1 - l.length) l := by
    rw [htape₂, hpos₂]
    have := hl.of_append_left.update_of_not_mem (q := c.workTapePos t - 1) none (Or.inr (by omega))
    convert this using 1
    ring
  have hend' : c₂.workTapes t (c₂.workTapePos t - l.length) = some m ∨
      c₂.workTapes t (c₂.workTapePos t - l.length) = none := by
    rw [htape₂, hpos₂, Function.update_of_ne (by omega)]
    convert hend using 3 <;> ring
  obtain ⟨c', hr, hst, hu', hout, hblank, hpos'⟩ := scan_popBack hins hpc l c₂ (by simp [hc₂]) hl' hm hend'
  refine ⟨c', (((h.trans h2).trans hr).cast_n (by omega)).cast_out (by simp), hst,
    ((hu.trans hu₂).trans hu').mono (by simp) (by simp), ?_, ?_, ?_⟩
  · intro q hq'
    rw [hout q (by rw [hpos₂]; omega), htape₂, Function.update_of_ne (by omega)]
  · intro q h1 h2'
    by_cases hq0 : q = c.workTapePos t - 1
    · subst hq0
      rw [hout _ (Or.inr (by rw [hpos₂]; omega)), htape₂, Function.update_self]
    · exact hblank q (by rw [hpos₂]; omega) (by rw [hpos₂]; push_cast at h2' ⊢; omega)
  · rw [hpos', hpos₂]; ring

/-! ## The budget and the counter -/

/-- A unary tape: `n` ones from cell `0`, blank elsewhere. -/
def Unary (τ : Tape) (n : ℕ) : Prop :=
  Holds τ 0 (List.replicate n .one) ∧ BlankBeyond τ n ∧ BlankBefore τ 0

theorem Unary.cell {τ : Tape} {n : ℕ} (h : Unary τ n) (q : ℤ) :
    τ q = if 0 ≤ q ∧ q < n then some .one else none := by
  split_ifs with hq
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, q = k := ⟨q.toNat, by omega⟩
    have := h.1 k (by simp; omega)
    simpa using this
  · by_cases h0 : q < 0
    · exact h.2.2 q h0
    · exact h.2.1 q (by omega)

theorem Unary.pop {τ : Tape} {n : ℕ} (h : Unary τ (n + 1)) :
    Unary (Function.update τ n none) n := by
  refine ⟨fun k hk => ?_, fun q hq => ?_, fun q hq => ?_⟩
  · simp only [List.length_replicate] at hk
    rw [Function.update_of_ne (by omega)]
    have := h.1 k (by simp; omega)
    simpa using this
  · by_cases hq' : q = n
    · subst hq'; simp
    · rw [Function.update_of_ne hq']; exact h.2.1 q (by omega)
  · rw [Function.update_of_ne (by omega)]; exact h.2.2 q hq

theorem Unary.push {τ : Tape} {n : ℕ} (h : Unary τ n) :
    Unary (Function.update τ n (some .one)) (n + 1) := by
  refine ⟨fun k hk => ?_, fun q hq => ?_, fun q hq => ?_⟩
  · simp only [List.length_replicate] at hk
    by_cases hk' : k = n
    · subst hk'; simp
    · rw [Function.update_of_ne (by omega)]
      have := h.1 k (by simp; omega)
      simpa using this
  · rw [Function.update_of_ne (by omega)]; exact h.2.1 q (by omega)
  · rw [Function.update_of_ne (by omega)]; exact h.2.2 q hq

theorem Unary.zero_iff {τ : Tape} : Unary τ 0 ↔ ∀ q, τ q = none := by
  constructor
  · intro h q
    rw [h.cell q, if_neg (by omega)]
  · intro h
    exact ⟨fun k hk => by simp at hk, fun q _ => h q, fun q _ => h q⟩

/-- `charge`: one step left, then a pop per unit; halts on an exhausted budget. -/
theorem exec_charge_one {k : ProgId} {pc : Fin maxPc}
    (hins : instrAt k pc = .charge false) (hpc : pc.val + 1 < maxPc) (c : Cfg input)
    (hq : c.state = at_ k pc) {r : ℕ} (hb : Unary (c.workTapes BUD) (r + 1))
    (hpos : c.workTapePos BUD = r + 1) :
    ∃ c', Reach c 2 c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [] [BUD] ∧
      Unary (c'.workTapes BUD) r ∧ c'.workTapePos BUD = r := by
  have h := step_instr hq hins
  simp only [execInstr, Act.mw_out, Act.base_out, Option.toList_none, Act.mw_next, Act.base_next,
    resolve_stay] at h
  set c₁ := applyAct ((Act.base (.stay p1)).mw BUD (-1)) (some ⟨k, pc, p1⟩) c with hc₁
  have hu : Untouched c c₁ [] [BUD] :=
    untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
      have : d ≠ BUD := by simpa using hd
      simp [Act.mw_works_of_ne _ this]⟩ _ _
  have htape : c₁.workTapes BUD = c.workTapes BUD := by
    rw [hc₁, applyAct_workTapes_of_none _ _ _ BUD (by simp)]
  have hpos₁ : c₁.workTapePos BUD = r := by simp [hc₁, hpos]
  have hread : c₁.workTapes BUD (c₁.workTapePos BUD) = some .one := by
    rw [htape, hpos₁, hb.cell]; simp
  have h2 := step_instr (c := c₁) (k := k) (pc := pc) (ph := p1) (by simp [hc₁]) hins
  simp only [execInstr, workTapeSymbols_eq, hread, if_false, Act.ww_out, Act.base_out,
    Option.toList_none, Act.ww_next, Act.base_next, Bool.false_eq_true] at h2
  refine ⟨_, (h.trans h2).cast_out (List.nil_append _), by simp [resolve_adv k pc hpc], ?_, ?_, ?_⟩
  · exact (hu.trans (untouched_applyAct (SI := []) (SW := [BUD]) ⟨fun j _ => rfl, fun d hd => by
      have : d ≠ BUD := by simpa using hd
      simp [Act.ww_works_of_ne _ this]⟩ _ _)).mono (by simp) (by simp)
  · rw [applyAct_workTapes_of_some _ _ _ BUD (s := none) (by simp), htape, hpos₁]
    exact hb.pop
  · simp [hpos₁]

theorem exec_charge_one_fail {k : ProgId} {pc : Fin maxPc}
    (hins : instrAt k pc = .charge false) (c : Cfg input)
    (hq : c.state = at_ k pc) (hb : Unary (c.workTapes BUD) 0) : HaltsIn c 2 := by
  have h := step_instr hq hins
  simp only [execInstr, Act.mw_out, Act.base_out, Option.toList_none, Act.mw_next, Act.base_next,
    resolve_stay] at h
  set c₁ := applyAct ((Act.base (.stay p1)).mw BUD (-1)) (some ⟨k, pc, p1⟩) c with hc₁
  have htape : c₁.workTapes BUD = c.workTapes BUD := by
    rw [hc₁, applyAct_workTapes_of_none _ _ _ BUD (by simp)]
  have hread : c₁.workTapes BUD (c₁.workTapePos BUD) = none := by
    rw [htape, Unary.zero_iff.mp hb]
  have h2 := step_instr (c := c₁) (k := k) (pc := pc) (ph := p1) (by simp [hc₁]) hins
  simp only [execInstr, workTapeSymbols_eq, hread, Act.base_out, Option.toList_none, Act.base_next,
    resolve_halt] at h2
  exact HaltsIn.of_reach ((h.trans h2).cast_out (List.nil_append _)) rfl

/-! ## Input heads -/

theorem SignType.one_eq_pos : (1 : SignType) = .pos := rfl
theorem SignType.neg_one_eq_neg : (-1 : SignType) = .neg := rfl

/-- The symbol under an input head at position `q + 1`, `q < |input j|`. -/
theorem inputSymbol_of_lt (c : Cfg input) (j : IT) {q : ℕ} (hq : (c.inputPos j : ℕ) = q + 1)
    (hlt : q < (input j).length) : c.inputSymbols j = some (input j)[q] :=
  inputSymbolInner j q (by omega) hlt

theorem inputSymbol_end (c : Cfg input) (j : IT) (hq : (c.inputPos j : ℕ) = (input j).length + 1) :
    c.inputSymbols j = none := by
  simp only [Cfg.inputSymbols_apply, Cfg.inputSymbol]
  rw [dif_neg (by intro h; rw [h] at hq; simp at hq), dif_pos hq]

theorem inputSymbol_start (c : Cfg input) (j : IT) (hq : (c.inputPos j : ℕ) = 0) :
    c.inputSymbols j = none := by
  simp only [Cfg.inputSymbols_apply, Cfg.inputSymbol]
  rw [dif_pos (Fin.ext hq)]

theorem moveInputPos_val_pos {n : ℕ} (p : Fin (n + 2)) (h : (p : ℕ) < n + 1) :
    (moveInputPos p .pos : ℕ) = p + 1 := by
  rw [MultiTapeTM.moveInputPos_pos_of_ne_right p (by omega)]

theorem moveInputPos_val_neg {n : ℕ} (p : Fin (n + 2)) (h : 0 < (p : ℕ)) :
    (moveInputPos p .neg : ℕ) = p - 1 := by
  rw [MultiTapeTM.moveInputPos_neg_of_ne_left p (by intro e; rw [e] at h; simp at h)]

theorem moveInputPos_val_neg_zero {n : ℕ} (p : Fin (n + 2)) (h : (p : ℕ) = 0) :
    (moveInputPos p .neg : ℕ) = 0 := by
  have : p = 0 := Fin.ext h
  subst this
  simp [MultiTapeTM.moveInputPos, SignType.cast]

theorem exec_moveInput {k : ProgId} {pc : Fin maxPc} {j : IT} {dir : Bool}
    (hins : instrAt k pc = .moveInput j dir) (hpc : pc.val + 1 < maxPc) (c : Cfg input)
    (hq : c.state = at_ k pc) :
    ∃ c', Reach c 1 c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [j] [] ∧
      c'.inputPos j = moveInputPos (c.inputPos j) (if dir then 1 else -1) := by
  have h := step_instr hq hins
  simp only [execInstr, Act.mi_out, Act.base_out, Option.toList_none, Act.mi_next, Act.base_next] at h
  refine ⟨_, h, by simp [resolve_adv k pc hpc], ?_, ?_⟩
  · exact untouched_applyAct ⟨fun j' hj => by
      have : j' ≠ j := by simpa using hj
      simp [Act.mi, Function.update_of_ne this], fun d _ => rfl⟩ _ _
  · cases dir <;> simp [Act.mi]

/-- The scan of `rewindInput` (phase `p1`): from position `q` to position `0`. -/
theorem scan_rewindInput {k : ProgId} {pc : Fin maxPc} {j : IT}
    (hins : instrAt k pc = .rewindInput j) (hpc : pc.val + 1 < maxPc) (q : ℕ) :
    ∀ (c : Cfg input), c.state = some ⟨k, pc, p1⟩ → (c.inputPos j : ℕ) = q →
      q ≤ (input j).length →
    ∃ c', Reach c (q + 1) c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [j] [] ∧
      (c'.inputPos j : ℕ) = 0 := by
  induction q with
  | zero =>
    intro c hq hpos _
    have h := step_instr hq hins
    simp only [execInstr, inputSymbol_start c j hpos, Act.base_out, Option.toList_none,
      Act.base_next] at h
    refine ⟨_, h, by simp [resolve_adv k pc hpc], untouched_applyAct ⟨fun _ _ => rfl, fun _ _ => rfl⟩ _ _, ?_⟩
    simp [hpos]
  | succ q ih =>
    intro c hq hpos hqle
    have hsym : c.inputSymbols j ≠ none := by
      have h1 := inputSymbol_of_lt c j hpos (by omega)
      rw [h1]; simp
    obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp hsym
    have h := step_instr hq hins
    simp only [execInstr, hs, Act.mi_out, Act.base_out, Option.toList_none, Act.mi_next,
      Act.base_next, resolve_stay] at h
    set c₁ := applyAct ((Act.base (.stay p1)).mi j (-1)) (some ⟨k, pc, p1⟩) c with hc₁
    have hu : Untouched c c₁ [j] [] :=
      untouched_applyAct ⟨fun j' hj => by
        have : j' ≠ j := by simpa using hj
        simp [Act.mi, Function.update_of_ne this], fun d _ => rfl⟩ _ _
    have hpos₁ : (c₁.inputPos j : ℕ) = q := by
      simp only [hc₁, applyAct_inputPos, Act.mi_inMoves, Function.update_self, SignType.neg_one_eq_neg,
        Act.base_inMoves]
      rw [moveInputPos_val_neg _ (by omega), hpos]; rfl
    obtain ⟨c', hr, hst, hu', hpos'⟩ := ih c₁ (by simp [hc₁]) hpos₁ (by omega)
    exact ⟨c', ((h.trans hr).cast_n (by omega)).cast_out (List.nil_append _), hst,
      (hu.trans hu').mono (by simp) (by simp), hpos'⟩

theorem exec_rewindInput {k : ProgId} {pc : Fin maxPc} {j : IT}
    (hins : instrAt k pc = .rewindInput j) (hpc : pc.val + 1 < maxPc) (c : Cfg input)
    (hq : c.state = at_ k pc) :
    ∃ n ≤ (c.inputPos j : ℕ) + 2, ∃ c', Reach c n c' [] ∧ c'.state = next_ k pc hpc ∧
      Untouched c c' [j] [] ∧ (c'.inputPos j : ℕ) = 0 := by
  have h := step_instr hq hins
  simp only [execInstr, Act.mi_out, Act.base_out, Option.toList_none, Act.mi_next, Act.base_next,
    resolve_stay] at h
  set c₁ := applyAct ((Act.base (.stay p1)).mi j (-1)) (some ⟨k, pc, p1⟩) c with hc₁
  have hu : Untouched c c₁ [j] [] :=
    untouched_applyAct ⟨fun j' hj => by
      have : j' ≠ j := by simpa using hj
      simp [Act.mi, Function.update_of_ne this], fun d _ => rfl⟩ _ _
  have hpos₁ : (c₁.inputPos j : ℕ) = (c.inputPos j : ℕ) - 1 := by
    simp only [hc₁, applyAct_inputPos, Act.mi_inMoves, Function.update_self, SignType.neg_one_eq_neg,
      Act.base_inMoves]
    by_cases h0 : (c.inputPos j : ℕ) = 0
    · rw [moveInputPos_val_neg_zero _ h0, h0]
    · rw [moveInputPos_val_neg _ (by omega)]
  have hlt := (c.inputPos j).isLt
  obtain ⟨c', hr, hst, hu', hpos'⟩ := scan_rewindInput hins hpc _ c₁ (by simp [hc₁]) hpos₁
    (by omega)
  exact ⟨1 + ((c.inputPos j : ℕ) - 1 + 1), by omega, c', (h.trans hr).cast_out (List.nil_append _),
    hst, (hu.trans hu').mono (by simp) (by simp), hpos'⟩

end MIPRE.TM.Interp

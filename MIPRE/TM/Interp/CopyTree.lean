/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.TM.Interp.Routines
import MIPRE.TM.Interp.Repr

/-!
# The `copyTree` routine

Copying (or skipping) a preorder-serialized value: a scan with a unary counter of the
pending subtrees on `CNT`, one more per `1` (a node with two children, itself consumed) and
one fewer per `0` (a leaf), finishing when none is pending. The scan from `d ≥ 1` pending
subtrees over `S(v)` leaves `d - 1` pending (`copyTree_scan`), finishing when `d = 1`; the
instruction starts with one (`exec_copyTree`).
-/

namespace MIPRE.TM.Interp

open Turing MultiInputTM Phase MIPRE.Cost

variable {input : Fin 7 → List Sym}

/-- The control at `(k, pc, p1)` if `d ≠ 1`, else at the next instruction. -/
def scanExit (k : ProgId) (pc : Fin maxPc) (hpc : pc.val + 1 < maxPc) (d : ℕ) : Option Ctl :=
  if d = 1 then next_ k pc hpc else some ⟨k, pc, p1⟩

/-- The effect of writing `l` at the head of `t`: `l` held from the old head, the rest of
the tape kept, the head past `l`. -/
structure DstEff (t : WT) (c c' : Cfg input) (l : List Sym) : Prop where
  holds : Holds (c'.workTapes t) (c.workTapePos t) l
  outside : ∀ q, (q < c.workTapePos t ∨ c.workTapePos t + l.length ≤ q) →
    c'.workTapes t q = c.workTapes t q
  pos : c'.workTapePos t = c.workTapePos t + l.length

theorem DstEff.trans {t : WT} {c c' c'' : Cfg input} {l l' : List Sym} (h : DstEff t c c' l)
    (h' : DstEff t c' c'' l') : DstEff t c c'' (l ++ l') where
  holds := by
    refine Holds.append ?_ ?_
    · exact h.holds.congr fun q hq1 hq2 => h'.outside q (Or.inl (by rw [h.pos]; omega))
    · rw [← h.pos]; exact h'.holds
  outside q hq := by
    simp only [List.length_append, Nat.cast_add] at hq
    rw [h'.outside q (by rw [h.pos]; omega), h.outside q (by omega)]
  pos := by rw [h'.pos, h.pos, List.length_append]; push_cast; ring

theorem DstEff.cast {t : WT} {c c' : Cfg input} {l l' : List Sym} (h : DstEff t c c' l)
    (e : l = l') : DstEff t c c' l' := e ▸ h

theorem DstEff.nil {t : WT} {c c' : Cfg input} (htape : c'.workTapes t = c.workTapes t)
    (hpos : c'.workTapePos t = c.workTapePos t) : DstEff t c c' [] where
  holds := by simp
  outside q _ := by rw [htape]
  pos := by simp [hpos]

/-- One written symbol. -/
theorem DstEff.single {t : WT} {c c' : Cfg input} {s : Sym}
    (htape : c'.workTapes t = Function.update (c.workTapes t) (c.workTapePos t) (some s))
    (hpos : c'.workTapePos t = c.workTapePos t + 1) : DstEff t c c' [s] where
  holds := by rw [htape]; exact holds_update_self _ _ _
  outside q hq := by
    rw [htape, Function.update_of_ne]
    simp only [List.length_singleton, Nat.cast_one] at hq
    omega
  pos := by simp [hpos]

/-- The scan of `copyTree src (some t) false` over `S(v)` from `d ≥ 1` pending subtrees. -/
theorem copyTree_scan {k : ProgId} {pc : Fin maxPc} {src t : WT}
    (hins : instrAt k pc = .copyTree src (some t) false) (hpc : pc.val + 1 < maxPc)
    (hst : src ≠ t) (hsc : src ≠ CNT) (htc : t ≠ CNT) (v : Data) :
    ∀ (c : Cfg input) (d : ℕ), c.state = some ⟨k, pc, p1⟩ → 1 ≤ d →
      Unary (c.workTapes CNT) d → c.workTapePos CNT = d →
      Holds (c.workTapes src) (c.workTapePos src) (S v) →
    ∃ n ≤ 3 * v.size, ∃ c', Reach c n c' [] ∧ c'.state = scanExit k pc hpc d ∧
      Untouched c c' [] [src, CNT, t] ∧
      c'.workTapes src = c.workTapes src ∧ c'.workTapePos src = c.workTapePos src + v.size ∧
      Unary (c'.workTapes CNT) (d - 1) ∧ c'.workTapePos CNT = d - 1 ∧ DstEff t c c' (S v) := by
  induction v with
  | nil =>
    intro c d hq hd hcnt hcp hsrc
    -- step 1: the `0`
    have hread : c.workTapes src (c.workTapePos src) = some .zero := by
      simpa using hsrc.head
    have h1 := step_instr hq hins
    simp only [execInstr, workTapeSymbols_eq, hread, Bool.false_eq_true, if_false, Act.mw_out,
      Act.ww_out, Act.base_out, Option.toList_none, Act.mw_next, Act.ww_next, Act.base_next,
      resolve_stay] at h1
    set c₁ := applyAct (((((Act.base (.stay p2)).mw src 1).mw CNT (-1)).ww t (some .zero)).mw t 1)
      (some ⟨k, pc, p2⟩) c with hc₁
    have hu₁ : Untouched c c₁ [] [src, CNT, t] :=
      untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
        have h1 : d ≠ src := fun e => hd (by simp [e])
        have h2 : d ≠ CNT := fun e => hd (by simp [e])
        have h3 : d ≠ t := fun e => hd (by simp [e])
        simp [Act.mw_works_of_ne _ h1, Act.mw_works_of_ne _ h2, Act.mw_works_of_ne _ h3,
          Act.ww_works_of_ne _ h3]⟩ _ _
    have hsrc₁ : c₁.workTapes src = c.workTapes src := by
      rw [hc₁, applyAct_workTapes_of_none _ _ _ src (by
        simp [Act.mw_works_of_ne _ hst, Act.ww_works_of_ne _ hst, Act.mw_works_of_ne _ hsc])]
    have hsrcp₁ : c₁.workTapePos src = c.workTapePos src + 1 := by
      simp [hc₁, Act.mw_works_of_ne _ hst, Act.ww_works_of_ne _ hst, Act.mw_works_of_ne _ hsc]
    have hcnt₁ : c₁.workTapes CNT = c.workTapes CNT := by
      rw [hc₁, applyAct_workTapes_of_none _ _ _ CNT (by
        simp [Act.mw_works_of_ne _ htc.symm, Act.ww_works_of_ne _ htc.symm,
          Act.mw_works_of_ne _ hsc.symm])]
    have hcp₁ : c₁.workTapePos CNT = ((d - 1 : ℕ) : ℤ) := by
      simp [hc₁, Act.mw_works_of_ne _ htc.symm, Act.ww_works_of_ne _ htc.symm,
        Act.mw_works_of_ne _ hsc.symm, hcp]
      omega
    have ht₁ : c₁.workTapes t = Function.update (c.workTapes t) (c.workTapePos t) (some .zero) := by
      rw [hc₁, applyAct_workTapes_of_some _ _ _ t (s := some .zero) (by simp)]
    have htp₁ : c₁.workTapePos t = c.workTapePos t + 1 := by simp [hc₁]
    -- step 2: pop the counter
    have h2 := step_instr (c := c₁) (k := k) (pc := pc) (ph := p2) (by simp [hc₁]) hins
    simp only [execInstr, Bool.false_eq_true, if_false, Act.mw_out, Act.ww_out, Act.base_out,
      Option.toList_none, Act.mw_next, Act.ww_next, Act.base_next, resolve_stay] at h2
    set c₂ := applyAct (((Act.base (.stay p3)).ww CNT none).mw CNT (-1)) (some ⟨k, pc, p3⟩) c₁
      with hc₂
    have hu₂ : Untouched c₁ c₂ [] [CNT] :=
      untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
        have h2 : d ≠ CNT := by simpa using hd
        simp [Act.mw_works_of_ne _ h2, Act.ww_works_of_ne _ h2]⟩ _ _
    have hcnt₂ : Unary (c₂.workTapes CNT) (d - 1) := by
      rw [hc₂, applyAct_workTapes_of_some _ _ _ CNT (s := none) (by simp), hcnt₁, hcp₁]
      have := hcnt
      rw [show d = d - 1 + 1 by omega] at this
      exact this.pop
    have hcp₂ : c₂.workTapePos CNT = (d : ℤ) - 2 := by simp [hc₂, hcp₁]; omega
    -- step 3: test the counter
    have h3 := step_instr (c := c₂) (k := k) (pc := pc) (ph := p3) (by simp [hc₂]) hins
    simp only [execInstr, workTapeSymbols_eq] at h3
    rw [hcp₂, hcnt₂.cell] at h3
    have hu₃ : ∀ (n : Next) (c₀ : Cfg input) (q' : Option Ctl),
        Untouched c₀ (applyAct ((Act.base n).mw CNT 1) q' c₀) [] [CNT] := fun n c₀ q' =>
      untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
        have h2 : d ≠ CNT := by simpa using hd
        simp [Act.mw_works_of_ne _ h2]⟩ _ _
    by_cases hd1 : d = 1
    · have hcell : (if 0 ≤ (d : ℤ) - 2 ∧ (d : ℤ) - 2 < ((d - 1 : ℕ) : ℤ) then some Sym.one
          else none) = none := by
        rw [if_neg]; omega
      rw [hcell] at h3
      simp only [Act.mw_out, Act.base_out, Option.toList_none, Act.mw_next, Act.base_next] at h3
      refine ⟨3, by simp, _, ((h1.trans h2).trans h3).cast_out (by simp),
        by simp [scanExit, hd1, resolve_adv k pc hpc], ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact ((hu₁.trans hu₂).trans (hu₃ _ _ _)).mono (by simp) (by simp)
      · rw [applyAct_workTapes_of_none _ _ _ src (by simp [Act.mw_works_of_ne _ hsc]),
          hu₂.tapes (d := src) (by simp [hsc]), hsrc₁]
      · simp [Act.mw_works_of_ne _ hsc, hu₂.pos (d := src) (by simp [hsc]), hsrcp₁]
      · rw [applyAct_workTapes_of_none _ _ _ CNT (by simp)]; exact hcnt₂
      · simp [hcp₂]; omega
      · rw [S_nil]
        refine DstEff.single ?_ ?_
        · rw [applyAct_workTapes_of_none _ _ _ t (by simp [Act.mw_works_of_ne _ htc]),
            hu₂.tapes (d := t) (by simp [htc]), ht₁]
        · simp [Act.mw_works_of_ne _ htc, hu₂.pos (d := t) (by simp [htc]), htp₁]
    · have hcell : (if 0 ≤ (d : ℤ) - 2 ∧ (d : ℤ) - 2 < ((d - 1 : ℕ) : ℤ) then some Sym.one
          else none) = some Sym.one := by
        rw [if_pos]; omega
      rw [hcell] at h3
      simp only [Act.mw_out, Act.base_out, Option.toList_none, Act.mw_next, Act.base_next,
        resolve_stay] at h3
      refine ⟨3, by simp, _, ((h1.trans h2).trans h3).cast_out (by simp),
        by simp [scanExit, hd1], ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact ((hu₁.trans hu₂).trans (hu₃ _ _ _)).mono (by simp) (by simp)
      · rw [applyAct_workTapes_of_none _ _ _ src (by simp [Act.mw_works_of_ne _ hsc]),
          hu₂.tapes (d := src) (by simp [hsc]), hsrc₁]
      · simp [Act.mw_works_of_ne _ hsc, hu₂.pos (d := src) (by simp [hsc]), hsrcp₁]
      · rw [applyAct_workTapes_of_none _ _ _ CNT (by simp)]; exact hcnt₂
      · simp [hcp₂]; omega
      · rw [S_nil]
        refine DstEff.single ?_ ?_
        · rw [applyAct_workTapes_of_none _ _ _ t (by simp [Act.mw_works_of_ne _ htc]),
            hu₂.tapes (d := t) (by simp [htc]), ht₁]
        · simp [Act.mw_works_of_ne _ htc, hu₂.pos (d := t) (by simp [htc]), htp₁]
  | cons a b iha ihb =>
    intro c d hq hd hcnt hcp hsrc
    rw [S_cons] at hsrc
    have hread : c.workTapes src (c.workTapePos src) = some .one := hsrc.head
    have h1 := step_instr hq hins
    simp only [execInstr, workTapeSymbols_eq, hread, Bool.false_eq_true, if_false, Act.mw_out,
      Act.ww_out, Act.base_out, Option.toList_none, Act.mw_next, Act.ww_next, Act.base_next,
      resolve_stay] at h1
    set c₁ := applyAct ((((((Act.base (.stay p1)).mw src 1).ww CNT (some .one)).mw CNT 1).ww t
      (some .one)).mw t 1) (some ⟨k, pc, p1⟩) c with hc₁
    have hu₁ : Untouched c c₁ [] [src, CNT, t] :=
      untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
        have h1 : d ≠ src := fun e => hd (by simp [e])
        have h2 : d ≠ CNT := fun e => hd (by simp [e])
        have h3 : d ≠ t := fun e => hd (by simp [e])
        simp [Act.mw_works_of_ne _ h1, Act.mw_works_of_ne _ h2, Act.mw_works_of_ne _ h3,
          Act.ww_works_of_ne _ h3, Act.ww_works_of_ne _ h2]⟩ _ _
    have hsrc₁ : c₁.workTapes src = c.workTapes src := by
      rw [hc₁, applyAct_workTapes_of_none _ _ _ src (by
        simp [Act.mw_works_of_ne _ hst, Act.ww_works_of_ne _ hst, Act.mw_works_of_ne _ hsc,
          Act.ww_works_of_ne _ hsc])]
    have hsrcp₁ : c₁.workTapePos src = c.workTapePos src + 1 := by
      simp [hc₁, Act.mw_works_of_ne _ hst, Act.ww_works_of_ne _ hst, Act.mw_works_of_ne _ hsc,
        Act.ww_works_of_ne _ hsc]
    have hcnt₁ : Unary (c₁.workTapes CNT) (d + 1) := by
      rw [hc₁, applyAct_workTapes_of_some _ _ _ CNT (s := some .one) (by
        simp [Act.mw_works_of_ne _ htc.symm, Act.ww_works_of_ne _ htc.symm]), hcp]
      exact hcnt.push
    have hcp₁ : c₁.workTapePos CNT = d + 1 := by
      simp [hc₁, Act.mw_works_of_ne _ htc.symm, Act.ww_works_of_ne _ htc.symm, hcp]
    have ht₁ : c₁.workTapes t = Function.update (c.workTapes t) (c.workTapePos t) (some .one) := by
      rw [hc₁, applyAct_workTapes_of_some _ _ _ t (s := some .one) (by simp)]
    have htp₁ : c₁.workTapePos t = c.workTapePos t + 1 := by simp [hc₁]
    have hde₁ : DstEff t c c₁ [.one] := DstEff.single ht₁ htp₁
    -- the left subtree, from `d + 1`
    obtain ⟨na, hna, c₂, hr₂, hst₂, hu₂, hsrc₂, hsrcp₂, hcnt₂, hcp₂, hde₂⟩ :=
      iha c₁ (d + 1) (by simp [hc₁]) (by omega) hcnt₁ (by rw [hcp₁]; push_cast; ring)
        (by rw [hsrc₁, hsrcp₁]; exact hsrc.tail.of_append_left)
    have hst₂' : c₂.state = some ⟨k, pc, p1⟩ := by
      rw [hst₂, scanExit, if_neg (by omega)]
    -- the right subtree, from `d`
    obtain ⟨nb, hnb, c₃, hr₃, hst₃, hu₃, hsrc₃, hsrcp₃, hcnt₃, hcp₃, hde₃⟩ :=
      ihb c₂ d hst₂' hd (by simpa using hcnt₂) (by rw [hcp₂]; simp)
        (by
          rw [hsrc₂, hsrcp₂, hsrc₁, hsrcp₁]
          have := hsrc.tail.of_append_right
          rw [length_S] at this
          convert this using 1)
    refine ⟨1 + na + nb, by rw [Data.size_cons]; omega, c₃, ?_, hst₃, ?_, ?_, ?_, hcnt₃,
      hcp₃, ?_⟩
    · exact ((h1.trans hr₂).trans hr₃).cast_out (by simp)
    · exact ((hu₁.trans hu₂).trans hu₃).mono (by simp) (by simp)
    · rw [hsrc₃, hsrc₂, hsrc₁]
    · rw [hsrcp₃, hsrcp₂, hsrcp₁]; simp only [Data.size_cons]; push_cast; ring
    · rw [S_cons]
      exact (hde₁.trans (hde₂.trans hde₃)).cast (by simp)

/-- The scan of `copyTree src none false` (a skip) over `S(v)` from `d ≥ 1` pending
subtrees. -/
theorem skipTree_scan {k : ProgId} {pc : Fin maxPc} {src : WT}
    (hins : instrAt k pc = .copyTree src none false) (hpc : pc.val + 1 < maxPc)
    (hsc : src ≠ CNT) (v : Data) :
    ∀ (c : Cfg input) (d : ℕ), c.state = some ⟨k, pc, p1⟩ → 1 ≤ d →
      Unary (c.workTapes CNT) d → c.workTapePos CNT = d →
      Holds (c.workTapes src) (c.workTapePos src) (S v) →
    ∃ n ≤ 3 * v.size, ∃ c', Reach c n c' [] ∧ c'.state = scanExit k pc hpc d ∧
      Untouched c c' [] [src, CNT] ∧
      c'.workTapes src = c.workTapes src ∧ c'.workTapePos src = c.workTapePos src + v.size ∧
      Unary (c'.workTapes CNT) (d - 1) ∧ c'.workTapePos CNT = d - 1 := by
  induction v with
  | nil =>
    intro c d hq hd hcnt hcp hsrc
    have hread : c.workTapes src (c.workTapePos src) = some .zero := by
      simpa using hsrc.head
    have h1 := step_instr hq hins
    simp only [execInstr, workTapeSymbols_eq, hread, Bool.false_eq_true, if_false, Act.mw_out,
      Act.base_out, Option.toList_none, Act.mw_next, Act.base_next, resolve_stay] at h1
    set c₁ := applyAct (((Act.base (.stay p2)).mw src 1).mw CNT (-1)) (some ⟨k, pc, p2⟩) c with hc₁
    have hu₁ : Untouched c c₁ [] [src, CNT] :=
      untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
        have h1 : d ≠ src := fun e => hd (by simp [e])
        have h2 : d ≠ CNT := fun e => hd (by simp [e])
        simp [Act.mw_works_of_ne _ h1, Act.mw_works_of_ne _ h2]⟩ _ _
    have hsrc₁ : c₁.workTapes src = c.workTapes src := by
      rw [hc₁, applyAct_workTapes_of_none _ _ _ src (by simp [Act.mw_works_of_ne _ hsc])]
    have hsrcp₁ : c₁.workTapePos src = c.workTapePos src + 1 := by
      simp [hc₁, Act.mw_works_of_ne _ hsc]
    have hcnt₁ : c₁.workTapes CNT = c.workTapes CNT := by
      rw [hc₁, applyAct_workTapes_of_none _ _ _ CNT (by simp [Act.mw_works_of_ne _ hsc.symm])]
    have hcp₁ : c₁.workTapePos CNT = ((d - 1 : ℕ) : ℤ) := by
      simp [hc₁, Act.mw_works_of_ne _ hsc.symm, hcp]
      omega
    have h2 := step_instr (c := c₁) (k := k) (pc := pc) (ph := p2) (by simp [hc₁]) hins
    simp only [execInstr, Bool.false_eq_true, if_false, Act.mw_out, Act.ww_out, Act.base_out,
      Option.toList_none, Act.mw_next, Act.ww_next, Act.base_next, resolve_stay] at h2
    set c₂ := applyAct (((Act.base (.stay p3)).ww CNT none).mw CNT (-1)) (some ⟨k, pc, p3⟩) c₁
      with hc₂
    have hu₂ : Untouched c₁ c₂ [] [CNT] :=
      untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
        have h2 : d ≠ CNT := by simpa using hd
        simp [Act.mw_works_of_ne _ h2, Act.ww_works_of_ne _ h2]⟩ _ _
    have hcnt₂ : Unary (c₂.workTapes CNT) (d - 1) := by
      rw [hc₂, applyAct_workTapes_of_some _ _ _ CNT (s := none) (by simp), hcnt₁, hcp₁]
      have := hcnt
      rw [show d = d - 1 + 1 by omega] at this
      exact this.pop
    have hcp₂ : c₂.workTapePos CNT = (d : ℤ) - 2 := by simp [hc₂, hcp₁]; omega
    have h3 := step_instr (c := c₂) (k := k) (pc := pc) (ph := p3) (by simp [hc₂]) hins
    simp only [execInstr, workTapeSymbols_eq] at h3
    rw [hcp₂, hcnt₂.cell] at h3
    have hu₃ : ∀ (n : Next) (c₀ : Cfg input) (q' : Option Ctl),
        Untouched c₀ (applyAct ((Act.base n).mw CNT 1) q' c₀) [] [CNT] := fun n c₀ q' =>
      untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
        have h2 : d ≠ CNT := by simpa using hd
        simp [Act.mw_works_of_ne _ h2]⟩ _ _
    by_cases hd1 : d = 1
    · have hcell : (if 0 ≤ (d : ℤ) - 2 ∧ (d : ℤ) - 2 < ((d - 1 : ℕ) : ℤ) then some Sym.one
          else none) = none := by
        rw [if_neg]; omega
      rw [hcell] at h3
      simp only [Act.mw_out, Act.base_out, Option.toList_none, Act.mw_next, Act.base_next] at h3
      refine ⟨3, by simp, _, ((h1.trans h2).trans h3).cast_out (by simp),
        by simp [scanExit, hd1, resolve_adv k pc hpc], ?_, ?_, ?_, ?_, ?_⟩
      · exact ((hu₁.trans hu₂).trans (hu₃ _ _ _)).mono (by simp) (by simp)
      · rw [applyAct_workTapes_of_none _ _ _ src (by simp [Act.mw_works_of_ne _ hsc]),
          hu₂.tapes (d := src) (by simp [hsc]), hsrc₁]
      · simp [Act.mw_works_of_ne _ hsc, hu₂.pos (d := src) (by simp [hsc]), hsrcp₁]
      · rw [applyAct_workTapes_of_none _ _ _ CNT (by simp)]; exact hcnt₂
      · simp [hcp₂]; omega
    · have hcell : (if 0 ≤ (d : ℤ) - 2 ∧ (d : ℤ) - 2 < ((d - 1 : ℕ) : ℤ) then some Sym.one
          else none) = some Sym.one := by
        rw [if_pos]; omega
      rw [hcell] at h3
      simp only [Act.mw_out, Act.base_out, Option.toList_none, Act.mw_next, Act.base_next,
        resolve_stay] at h3
      refine ⟨3, by simp, _, ((h1.trans h2).trans h3).cast_out (by simp),
        by simp [scanExit, hd1], ?_, ?_, ?_, ?_, ?_⟩
      · exact ((hu₁.trans hu₂).trans (hu₃ _ _ _)).mono (by simp) (by simp)
      · rw [applyAct_workTapes_of_none _ _ _ src (by simp [Act.mw_works_of_ne _ hsc]),
          hu₂.tapes (d := src) (by simp [hsc]), hsrc₁]
      · simp [Act.mw_works_of_ne _ hsc, hu₂.pos (d := src) (by simp [hsc]), hsrcp₁]
      · rw [applyAct_workTapes_of_none _ _ _ CNT (by simp)]; exact hcnt₂
      · simp [hcp₂]; omega
  | cons a b iha ihb =>
    intro c d hq hd hcnt hcp hsrc
    rw [S_cons] at hsrc
    have hread : c.workTapes src (c.workTapePos src) = some .one := hsrc.head
    have h1 := step_instr hq hins
    simp only [execInstr, workTapeSymbols_eq, hread, Bool.false_eq_true, if_false, Act.mw_out,
      Act.ww_out, Act.base_out, Option.toList_none, Act.mw_next, Act.ww_next, Act.base_next,
      resolve_stay] at h1
    set c₁ := applyAct ((((Act.base (.stay p1)).mw src 1).ww CNT (some .one)).mw CNT 1)
      (some ⟨k, pc, p1⟩) c with hc₁
    have hu₁ : Untouched c c₁ [] [src, CNT] :=
      untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
        have h1 : d ≠ src := fun e => hd (by simp [e])
        have h2 : d ≠ CNT := fun e => hd (by simp [e])
        simp [Act.mw_works_of_ne _ h1, Act.mw_works_of_ne _ h2, Act.ww_works_of_ne _ h2]⟩ _ _
    have hsrc₁ : c₁.workTapes src = c.workTapes src := by
      rw [hc₁, applyAct_workTapes_of_none _ _ _ src (by
        simp [Act.mw_works_of_ne _ hsc, Act.ww_works_of_ne _ hsc])]
    have hsrcp₁ : c₁.workTapePos src = c.workTapePos src + 1 := by
      simp [hc₁, Act.mw_works_of_ne _ hsc, Act.ww_works_of_ne _ hsc]
    have hcnt₁ : Unary (c₁.workTapes CNT) (d + 1) := by
      rw [hc₁, applyAct_workTapes_of_some _ _ _ CNT (s := some .one) (by simp), hcp]
      exact hcnt.push
    have hcp₁ : c₁.workTapePos CNT = d + 1 := by simp [hc₁, hcp]
    obtain ⟨na, hna, c₂, hr₂, hst₂, hu₂, hsrc₂, hsrcp₂, hcnt₂, hcp₂⟩ :=
      iha c₁ (d + 1) (by simp [hc₁]) (by omega) hcnt₁ (by rw [hcp₁]; push_cast; ring)
        (by rw [hsrc₁, hsrcp₁]; exact hsrc.tail.of_append_left)
    have hst₂' : c₂.state = some ⟨k, pc, p1⟩ := by
      rw [hst₂, scanExit, if_neg (by omega)]
    obtain ⟨nb, hnb, c₃, hr₃, hst₃, hu₃, hsrc₃, hsrcp₃, hcnt₃, hcp₃⟩ :=
      ihb c₂ d hst₂' hd (by simpa using hcnt₂) (by rw [hcp₂]; simp)
        (by
          rw [hsrc₂, hsrcp₂, hsrc₁, hsrcp₁]
          have := hsrc.tail.of_append_right
          rw [length_S] at this
          convert this using 1)
    refine ⟨1 + na + nb, by rw [Data.size_cons]; omega, c₃, ?_, hst₃, ?_, ?_, ?_, hcnt₃, hcp₃⟩
    · exact ((h1.trans hr₂).trans hr₃).cast_out (by simp)
    · exact ((hu₁.trans hu₂).trans hu₃).mono (by simp) (by simp)
    · rw [hsrc₃, hsrc₂, hsrc₁]
    · rw [hsrcp₃, hsrcp₂, hsrcp₁]; simp only [Data.size_cons]; push_cast; ring

/-- The first phase of `copyTree`: one pending subtree. -/
theorem copyTree_start {k : ProgId} {pc : Fin maxPc} {src : WT} {dst : Option WT} {ch : Bool}
    (hins : instrAt k pc = .copyTree src dst ch) (c : Cfg input) (hq : c.state = at_ k pc)
    (hcnt : Unary (c.workTapes CNT) 0) (hcp : c.workTapePos CNT = 0) :
    ∃ c', Reach c 1 c' [] ∧ c'.state = some ⟨k, pc, p1⟩ ∧ Untouched c c' [] [CNT] ∧
      Unary (c'.workTapes CNT) 1 ∧ c'.workTapePos CNT = 1 := by
  have h := step_instr hq hins
  simp only [execInstr, Act.mw_out, Act.ww_out, Act.base_out, Option.toList_none, Act.mw_next,
    Act.ww_next, Act.base_next, resolve_stay] at h
  refine ⟨_, h, rfl, ?_, ?_, ?_⟩
  · exact untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
      have h2 : d ≠ CNT := by simpa using hd
      simp [Act.mw_works_of_ne _ h2, Act.ww_works_of_ne _ h2]⟩ _ _
  · rw [applyAct_workTapes_of_some _ _ _ CNT (s := some .one) (by simp), hcp]
    simpa using hcnt.push
  · simp [hcp]

/-- **`copyTree src (some t) false`**: copy `S(v)` from the head of `src` to the head of
`t`, in at most `3 |v| + 1` steps. -/
theorem exec_copyTree {k : ProgId} {pc : Fin maxPc} {src t : WT}
    (hins : instrAt k pc = .copyTree src (some t) false) (hpc : pc.val + 1 < maxPc)
    (hst : src ≠ t) (hsc : src ≠ CNT) (htc : t ≠ CNT) (v : Data) (c : Cfg input)
    (hq : c.state = at_ k pc) (hcnt : Unary (c.workTapes CNT) 0) (hcp : c.workTapePos CNT = 0)
    (hsrc : Holds (c.workTapes src) (c.workTapePos src) (S v)) :
    ∃ n ≤ 3 * v.size + 1, ∃ c', Reach c n c' [] ∧ c'.state = next_ k pc hpc ∧
      Untouched c c' [] [src, CNT, t] ∧
      c'.workTapes src = c.workTapes src ∧ c'.workTapePos src = c.workTapePos src + v.size ∧
      Unary (c'.workTapes CNT) 0 ∧ c'.workTapePos CNT = 0 ∧ DstEff t c c' (S v) := by
  obtain ⟨c₁, hr₁, hs₁, hu₁, hcnt₁, hcp₁⟩ := copyTree_start hins c hq hcnt hcp
  obtain ⟨n, hn, c', hr, hst', hu, hsrc', hsrcp', hcnt', hcp', hde⟩ :=
    copyTree_scan hins hpc hst hsc htc v c₁ 1 hs₁ le_rfl hcnt₁ (by simp [hcp₁])
      (by rw [hu₁.tapes (d := src) (by simp [hsc]), hu₁.pos (d := src) (by simp [hsc])]; exact hsrc)
  refine ⟨1 + n, by omega, c', (hr₁.trans hr).cast_out (by simp), by simpa [scanExit] using hst',
    (hu₁.trans hu).mono (by simp) (by simp), ?_, ?_, by simpa using hcnt', by simpa using hcp', ?_⟩
  · rw [hsrc', hu₁.tapes (d := src) (by simp [hsc])]
  · rw [hsrcp', hu₁.pos (d := src) (by simp [hsc])]
  · refine ⟨?_, ?_, ?_⟩
    · rw [← hu₁.pos (d := t) (by simp [htc])]; exact hde.holds
    · intro q hq'
      rw [hde.outside q (by rw [hu₁.pos (d := t) (by simp [htc])]; exact hq'),
        hu₁.tapes (d := t) (by simp [htc])]
    · rw [hde.pos, hu₁.pos (d := t) (by simp [htc])]

/-- **`copyTree src none false`**: skip `S(v)` on `src`, in at most `3 |v| + 1` steps. -/
theorem exec_skipTree {k : ProgId} {pc : Fin maxPc} {src : WT}
    (hins : instrAt k pc = .copyTree src none false) (hpc : pc.val + 1 < maxPc)
    (hsc : src ≠ CNT) (v : Data) (c : Cfg input)
    (hq : c.state = at_ k pc) (hcnt : Unary (c.workTapes CNT) 0) (hcp : c.workTapePos CNT = 0)
    (hsrc : Holds (c.workTapes src) (c.workTapePos src) (S v)) :
    ∃ n ≤ 3 * v.size + 1, ∃ c', Reach c n c' [] ∧ c'.state = next_ k pc hpc ∧
      Untouched c c' [] [src, CNT] ∧
      c'.workTapes src = c.workTapes src ∧ c'.workTapePos src = c.workTapePos src + v.size ∧
      Unary (c'.workTapes CNT) 0 ∧ c'.workTapePos CNT = 0 := by
  obtain ⟨c₁, hr₁, hs₁, hu₁, hcnt₁, hcp₁⟩ := copyTree_start hins c hq hcnt hcp
  obtain ⟨n, hn, c', hr, hst', hu, hsrc', hsrcp', hcnt', hcp'⟩ :=
    skipTree_scan hins hpc hsc v c₁ 1 hs₁ le_rfl hcnt₁ (by simp [hcp₁])
      (by rw [hu₁.tapes (d := src) (by simp [hsc]), hu₁.pos (d := src) (by simp [hsc])]; exact hsrc)
  refine ⟨1 + n, by omega, c', (hr₁.trans hr).cast_out (by simp), by simpa [scanExit] using hst',
    (hu₁.trans hu).mono (by simp) (by simp), ?_, ?_, by simpa using hcnt', by simpa using hcp'⟩
  · rw [hsrc', hu₁.tapes (d := src) (by simp [hsc])]
  · rw [hsrcp', hu₁.pos (d := src) (by simp [hsc])]

end MIPRE.TM.Interp

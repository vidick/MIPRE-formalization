/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.TM.Interp.CopyTree

/-!
# The charged `copyTree`

`copyTree src (some t) true` copies `S(v)` and pops one budget cell per bit: with a budget
of at least `|v|` it succeeds (`exec_copyTree_charge`), otherwise it halts
(`exec_copyTree_charge_fail`).
-/

namespace MIPRE.TM.Interp

open Turing MultiInputTM Phase MIPRE.Cost

variable {input : Fin 7 → List Sym}

/-- The scan of the charged copy over `S(v)` from `d ≥ 1` pending subtrees and a budget of
`r ≥ |v|`. -/
theorem copyTree_scan_charge {k : ProgId} {pc : Fin maxPc} {src t : WT}
    (hins : instrAt k pc = .copyTree src (some t) true) (hpc : pc.val + 1 < maxPc)
    (hst : src ≠ t) (hsc : src ≠ CNT) (htc : t ≠ CNT) (hsb : src ≠ BUD) (htb : t ≠ BUD) (v : Data) :
    ∀ (c : Cfg input) (d r : ℕ), c.state = some ⟨k, pc, p1⟩ → 1 ≤ d →
      Unary (c.workTapes CNT) d → c.workTapePos CNT = d →
      Unary (c.workTapes BUD) r → c.workTapePos BUD = r → v.size ≤ r →
      Holds (c.workTapes src) (c.workTapePos src) (S v) →
    ∃ n ≤ 4 * v.size, ∃ c', Reach c n c' [] ∧ c'.state = scanExit k pc hpc d ∧
      Untouched c c' [] [src, CNT, t, BUD] ∧
      c'.workTapes src = c.workTapes src ∧ c'.workTapePos src = c.workTapePos src + v.size ∧
      Unary (c'.workTapes CNT) (d - 1) ∧ c'.workTapePos CNT = d - 1 ∧
      Unary (c'.workTapes BUD) (r - v.size) ∧ c'.workTapePos BUD = ((r - v.size : ℕ) : ℤ) ∧
      DstEff t c c' (S v) := by
  have hcb : CNT ≠ BUD := by decide
  induction v with
  | nil =>
    intro c d r hq hd hcnt hcp hbud hbp hr hsrc
    simp only [Data.size_nil] at hr
    have hread : c.workTapes src (c.workTapePos src) = some .zero := by
      simpa using hsrc.head
    -- step 1
    have h1 := step_instr hq hins
    simp only [execInstr, workTapeSymbols_eq, hread, if_true, Act.mw_out, Act.ww_out, Act.base_out,
      Option.toList_none, Act.mw_next, Act.ww_next, Act.base_next, resolve_stay] at h1
    set c₁ := applyAct ((((((Act.base (.stay p2)).mw src 1).mw CNT (-1)).mw BUD (-1)).ww t
      (some .zero)).mw t 1) (some ⟨k, pc, p2⟩) c with hc₁
    have hu₁ : Untouched c c₁ [] [src, CNT, t, BUD] :=
      untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
        have h1 : d ≠ src := fun e => hd (by simp [e])
        have h2 : d ≠ CNT := fun e => hd (by simp [e])
        have h3 : d ≠ t := fun e => hd (by simp [e])
        have h4 : d ≠ BUD := fun e => hd (by simp [e])
        simp [Act.mw_works_of_ne _ h1, Act.mw_works_of_ne _ h2, Act.mw_works_of_ne _ h3,
          Act.mw_works_of_ne _ h4, Act.ww_works_of_ne _ h3]⟩ _ _
    have hsrc₁ : c₁.workTapes src = c.workTapes src := by
      rw [hc₁, applyAct_workTapes_of_none _ _ _ src (by
        simp [Act.mw_works_of_ne _ hst, Act.ww_works_of_ne _ hst, Act.mw_works_of_ne _ hsc,
          Act.mw_works_of_ne _ hsb])]
    have hsrcp₁ : c₁.workTapePos src = c.workTapePos src + 1 := by
      simp [hc₁, Act.mw_works_of_ne _ hst, Act.ww_works_of_ne _ hst, Act.mw_works_of_ne _ hsc,
        Act.mw_works_of_ne _ hsb]
    have hcnt₁ : c₁.workTapes CNT = c.workTapes CNT := by
      rw [hc₁, applyAct_workTapes_of_none _ _ _ CNT (by
        simp [Act.mw_works_of_ne _ htc.symm, Act.ww_works_of_ne _ htc.symm,
          Act.mw_works_of_ne _ hsc.symm, Act.mw_works_of_ne _ hcb])]
    have hcp₁ : c₁.workTapePos CNT = ((d - 1 : ℕ) : ℤ) := by
      simp [hc₁, Act.mw_works_of_ne _ htc.symm, Act.ww_works_of_ne _ htc.symm,
        Act.mw_works_of_ne _ hsc.symm, Act.mw_works_of_ne _ hcb, hcp]
      omega
    have hbud₁ : c₁.workTapes BUD = c.workTapes BUD := by
      rw [hc₁, applyAct_workTapes_of_none _ _ _ BUD (by
        simp [Act.mw_works_of_ne _ htb.symm, Act.ww_works_of_ne _ htb.symm,
          Act.mw_works_of_ne _ hsb.symm, Act.mw_works_of_ne _ hcb.symm,
          Act.ww_works_of_ne _ hcb.symm])]
    have hbp₁ : c₁.workTapePos BUD = ((r - 1 : ℕ) : ℤ) := by
      simp [hc₁, Act.mw_works_of_ne _ htb.symm, Act.ww_works_of_ne _ htb.symm,
        Act.mw_works_of_ne _ hsb.symm, Act.mw_works_of_ne _ hcb.symm, Act.ww_works_of_ne _ hcb.symm,
        hbp]
      omega
    have ht₁ : c₁.workTapes t = Function.update (c.workTapes t) (c.workTapePos t) (some .zero) := by
      rw [hc₁, applyAct_workTapes_of_some _ _ _ t (s := some .zero) (by simp)]
    have htp₁ : c₁.workTapePos t = c.workTapePos t + 1 := by simp [hc₁]
    -- step 2: the budget check, the counter pop
    have hbread : c₁.workTapes BUD (c₁.workTapePos BUD) = some .one := by
      rw [hbud₁, hbp₁, hbud.cell]; rw [if_pos]; omega
    have h2 := step_instr (c := c₁) (k := k) (pc := pc) (ph := p2) (by simp [hc₁]) hins
    simp only [execInstr, workTapeSymbols_eq, hbread, if_true, Act.mw_out, Act.ww_out, Act.base_out,
      Option.toList_none, Act.mw_next, Act.ww_next, Act.base_next, resolve_stay] at h2
    set c₂ := applyAct ((((Act.base (.stay p3)).ww CNT none).mw CNT (-1)).ww BUD none)
      (some ⟨k, pc, p3⟩) c₁ with hc₂
    have hu₂ : Untouched c₁ c₂ [] [CNT, BUD] :=
      untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
        have h2 : d ≠ CNT := fun e => hd (by simp [e])
        have h4 : d ≠ BUD := fun e => hd (by simp [e])
        simp [Act.mw_works_of_ne _ h2, Act.ww_works_of_ne _ h2, Act.ww_works_of_ne _ h4]⟩ _ _
    have hcnt₂ : Unary (c₂.workTapes CNT) (d - 1) := by
      rw [hc₂, applyAct_workTapes_of_some _ _ _ CNT (s := none) (by simp [Act.ww_works_of_ne _ hcb]),
        hcnt₁, hcp₁]
      have := hcnt
      rw [show d = d - 1 + 1 by omega] at this
      exact this.pop
    have hcp₂ : c₂.workTapePos CNT = (d : ℤ) - 2 := by
      simp [hc₂, hcp₁, Act.ww_works_of_ne _ hcb]; omega
    have hbud₂ : Unary (c₂.workTapes BUD) (r - 1) := by
      rw [hc₂, applyAct_workTapes_of_some _ _ _ BUD (s := none) (by simp), hbud₁, hbp₁]
      have := hbud
      rw [show r = r - 1 + 1 by omega] at this
      exact this.pop
    have hbp₂ : c₂.workTapePos BUD = ((r - 1 : ℕ) : ℤ) := by
      simp [hc₂, hbp₁, Act.mw_works_of_ne _ hcb.symm, Act.ww_works_of_ne _ hcb.symm]
    -- step 3
    have h3 := step_instr (c := c₂) (k := k) (pc := pc) (ph := p3) (by simp [hc₂]) hins
    simp only [execInstr, workTapeSymbols_eq] at h3
    rw [hcp₂, hcnt₂.cell] at h3
    have hu₃ : ∀ (n : Next) (c₀ : Cfg input) (q' : Option Ctl),
        Untouched c₀ (applyAct ((Act.base n).mw CNT 1) q' c₀) [] [CNT] := fun n c₀ q' =>
      untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
        have h2 : d ≠ CNT := by simpa using hd
        simp [Act.mw_works_of_ne _ h2]⟩ _ _
    have hfin : ∀ (n : Next) (q' : Option Ctl),
        let c' := applyAct ((Act.base n).mw CNT 1) q' c₂
        Untouched c c' [] [src, CNT, t, BUD] ∧ c'.workTapes src = c.workTapes src ∧
        c'.workTapePos src = c.workTapePos src + (1 : ℕ) ∧ Unary (c'.workTapes CNT) (d - 1) ∧
        c'.workTapePos CNT = (d : ℤ) - 2 + 1 ∧ Unary (c'.workTapes BUD) (r - 1) ∧
        c'.workTapePos BUD = ((r - 1 : ℕ) : ℤ) ∧ DstEff t c c' [.zero] := by
      intro n q'
      refine ⟨((hu₁.trans hu₂).trans (hu₃ _ _ _)).mono (by simp) (by simp), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [applyAct_workTapes_of_none _ _ _ src (by simp [Act.mw_works_of_ne _ hsc]),
          hu₂.tapes (d := src) (by simp [hsc, hsb]), hsrc₁]
      · simp [Act.mw_works_of_ne _ hsc, hu₂.pos (d := src) (by simp [hsc, hsb]), hsrcp₁]
      · rw [applyAct_workTapes_of_none _ _ _ CNT (by simp)]; exact hcnt₂
      · simp [hcp₂]
      · rw [applyAct_workTapes_of_none _ _ _ BUD (by simp [Act.mw_works_of_ne _ hcb.symm])]
        exact hbud₂
      · simp [Act.mw_works_of_ne _ hcb.symm, hbp₂]
      · refine DstEff.single ?_ ?_
        · rw [applyAct_workTapes_of_none _ _ _ t (by simp [Act.mw_works_of_ne _ htc]),
            hu₂.tapes (d := t) (by simp [htc, htb]), ht₁]
        · simp [Act.mw_works_of_ne _ htc, hu₂.pos (d := t) (by simp [htc, htb]), htp₁]
    by_cases hd1 : d = 1
    · have hcell : (if 0 ≤ (d : ℤ) - 2 ∧ (d : ℤ) - 2 < ((d - 1 : ℕ) : ℤ) then some Sym.one
          else none) = none := by
        rw [if_neg]; omega
      rw [hcell] at h3
      simp only [Act.mw_out, Act.base_out, Option.toList_none, Act.mw_next, Act.base_next] at h3
      obtain ⟨hu, hs, hsp, hc, hcp', hb, hbp', hde⟩ := hfin .adv (resolve k pc .adv)
      refine ⟨3, by simp, _, ((h1.trans h2).trans h3).cast_out (by simp),
        by simp [scanExit, hd1, resolve_adv k pc hpc], hu, hs, by rw [hsp]; simp, hc,
        by rw [hcp']; omega, by simpa using hb, by simpa using hbp', by rw [S_nil]; exact hde⟩
    · have hcell : (if 0 ≤ (d : ℤ) - 2 ∧ (d : ℤ) - 2 < ((d - 1 : ℕ) : ℤ) then some Sym.one
          else none) = some Sym.one := by
        rw [if_pos]; omega
      rw [hcell] at h3
      simp only [Act.mw_out, Act.base_out, Option.toList_none, Act.mw_next, Act.base_next,
        resolve_stay] at h3
      obtain ⟨hu, hs, hsp, hc, hcp', hb, hbp', hde⟩ := hfin (.stay p1) (some ⟨k, pc, p1⟩)
      refine ⟨3, by simp, _, ((h1.trans h2).trans h3).cast_out (by simp),
        by simp [scanExit, hd1], hu, hs, by rw [hsp]; simp, hc,
        by rw [hcp']; omega, by simpa using hb, by simpa using hbp', by rw [S_nil]; exact hde⟩
  | cons a b iha ihb =>
    intro c d r hq hd hcnt hcp hbud hbp hr hsrc
    simp only [Data.size_cons] at hr
    rw [S_cons] at hsrc
    have hread : c.workTapes src (c.workTapePos src) = some .one := hsrc.head
    -- step 1: the `1`
    have h1 := step_instr hq hins
    simp only [execInstr, workTapeSymbols_eq, hread, if_true, Act.mw_out, Act.ww_out, Act.base_out,
      Option.toList_none, Act.mw_next, Act.ww_next, Act.base_next, resolve_stay] at h1
    set c₁ := applyAct (((((((Act.base (.stay p4)).mw src 1).ww CNT (some .one)).mw CNT 1).mw BUD
      (-1)).ww t (some .one)).mw t 1) (some ⟨k, pc, p4⟩) c with hc₁
    have hu₁ : Untouched c c₁ [] [src, CNT, t, BUD] :=
      untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
        have h1 : d ≠ src := fun e => hd (by simp [e])
        have h2 : d ≠ CNT := fun e => hd (by simp [e])
        have h3 : d ≠ t := fun e => hd (by simp [e])
        have h4 : d ≠ BUD := fun e => hd (by simp [e])
        simp [Act.mw_works_of_ne _ h1, Act.mw_works_of_ne _ h2, Act.mw_works_of_ne _ h3,
          Act.mw_works_of_ne _ h4, Act.ww_works_of_ne _ h3, Act.ww_works_of_ne _ h2]⟩ _ _
    have hsrc₁ : c₁.workTapes src = c.workTapes src := by
      rw [hc₁, applyAct_workTapes_of_none _ _ _ src (by
        simp [Act.mw_works_of_ne _ hst, Act.ww_works_of_ne _ hst, Act.mw_works_of_ne _ hsc,
          Act.ww_works_of_ne _ hsc, Act.mw_works_of_ne _ hsb])]
    have hsrcp₁ : c₁.workTapePos src = c.workTapePos src + 1 := by
      simp [hc₁, Act.mw_works_of_ne _ hst, Act.ww_works_of_ne _ hst, Act.mw_works_of_ne _ hsc,
        Act.ww_works_of_ne _ hsc, Act.mw_works_of_ne _ hsb]
    have hcnt₁ : Unary (c₁.workTapes CNT) (d + 1) := by
      rw [hc₁, applyAct_workTapes_of_some _ _ _ CNT (s := some .one) (by
        simp [Act.mw_works_of_ne _ htc.symm, Act.ww_works_of_ne _ htc.symm,
          Act.mw_works_of_ne _ hcb]), hcp]
      exact hcnt.push
    have hcp₁ : c₁.workTapePos CNT = d + 1 := by
      simp [hc₁, Act.mw_works_of_ne _ htc.symm, Act.ww_works_of_ne _ htc.symm,
        Act.mw_works_of_ne _ hcb, hcp]
    have hbud₁ : c₁.workTapes BUD = c.workTapes BUD := by
      rw [hc₁, applyAct_workTapes_of_none _ _ _ BUD (by
        simp [Act.mw_works_of_ne _ htb.symm, Act.ww_works_of_ne _ htb.symm,
          Act.mw_works_of_ne _ hsb.symm, Act.mw_works_of_ne _ hcb.symm,
          Act.ww_works_of_ne _ hcb.symm])]
    have hbp₁ : c₁.workTapePos BUD = ((r - 1 : ℕ) : ℤ) := by
      simp [hc₁, Act.mw_works_of_ne _ htb.symm, Act.ww_works_of_ne _ htb.symm,
        Act.mw_works_of_ne _ hsb.symm, Act.mw_works_of_ne _ hcb.symm, Act.ww_works_of_ne _ hcb.symm,
        hbp]
      omega
    have ht₁ : c₁.workTapes t = Function.update (c.workTapes t) (c.workTapePos t) (some .one) := by
      rw [hc₁, applyAct_workTapes_of_some _ _ _ t (s := some .one) (by simp)]
    have htp₁ : c₁.workTapePos t = c.workTapePos t + 1 := by simp [hc₁]
    have hde₁ : DstEff t c c₁ [.one] := DstEff.single ht₁ htp₁
    -- step 2: the budget check
    have hbread : c₁.workTapes BUD (c₁.workTapePos BUD) = some .one := by
      rw [hbud₁, hbp₁, hbud.cell]; rw [if_pos]; omega
    have h2 := step_instr (c := c₁) (k := k) (pc := pc) (ph := p4) (by simp [hc₁]) hins
    simp only [execInstr, workTapeSymbols_eq, hbread, Act.ww_out, Act.base_out, Option.toList_none,
      Act.ww_next, Act.base_next, resolve_stay] at h2
    set c₂ := applyAct ((Act.base (.stay p1)).ww BUD none) (some ⟨k, pc, p1⟩) c₁ with hc₂
    have hu₂ : Untouched c₁ c₂ [] [BUD] :=
      untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
        have h4 : d ≠ BUD := by simpa using hd
        simp [Act.ww_works_of_ne _ h4]⟩ _ _
    have hbud₂ : Unary (c₂.workTapes BUD) (r - 1) := by
      rw [hc₂, applyAct_workTapes_of_some _ _ _ BUD (s := none) (by simp), hbud₁, hbp₁]
      have := hbud
      rw [show r = r - 1 + 1 by omega] at this
      exact this.pop
    have hbp₂ : c₂.workTapePos BUD = ((r - 1 : ℕ) : ℤ) := by simp [hc₂, hbp₁]
    -- the left subtree
    obtain ⟨na, hna, c₃, hr₃, hst₃, hu₃, hsrc₃, hsrcp₃, hcnt₃, hcp₃, hbud₃, hbp₃, hde₃⟩ :=
      iha c₂ (d + 1) (r - 1) (by simp [hc₂]) (by omega)
        (by rw [hu₂.tapes (d := CNT) (by simp [hcb])]; exact hcnt₁)
        (by rw [hu₂.pos (d := CNT) (by simp [hcb]), hcp₁]; push_cast; ring) hbud₂ hbp₂ (by omega)
        (by rw [hu₂.tapes (d := src) (by simp [hsb]), hu₂.pos (d := src) (by simp [hsb]), hsrc₁,
          hsrcp₁]; exact hsrc.tail.of_append_left)
    have hst₃' : c₃.state = some ⟨k, pc, p1⟩ := by
      rw [hst₃, scanExit, if_neg (by omega)]
    -- the right subtree
    obtain ⟨nb, hnb, c₄, hr₄, hst₄, hu₄, hsrc₄, hsrcp₄, hcnt₄, hcp₄, hbud₄, hbp₄, hde₄⟩ :=
      ihb c₃ d (r - 1 - a.size) hst₃' hd (by simpa using hcnt₃) (by rw [hcp₃]; simp) hbud₃ hbp₃
        (by omega)
        (by
          rw [hsrc₃, hsrcp₃, hu₂.tapes (d := src) (by simp [hsb]), hu₂.pos (d := src) (by simp [hsb]),
            hsrc₁, hsrcp₁]
          have := hsrc.tail.of_append_right
          rw [length_S] at this
          convert this using 1)
    refine ⟨2 + na + nb, by rw [Data.size_cons]; omega, c₄, ?_, hst₄, ?_, ?_, ?_, hcnt₄, hcp₄,
      ?_, ?_, ?_⟩
    · exact (((h1.trans h2).trans hr₃).trans hr₄).cast_out (by simp)
    · exact (((hu₁.trans hu₂).trans hu₃).trans hu₄).mono (by simp) (by simp)
    · rw [hsrc₄, hsrc₃, hu₂.tapes (d := src) (by simp [hsb]), hsrc₁]
    · rw [hsrcp₄, hsrcp₃, hu₂.pos (d := src) (by simp [hsb]), hsrcp₁]
      simp only [Data.size_cons]; push_cast; ring
    · have e : r - (Data.cons a b).size = r - 1 - a.size - b.size := by
        rw [Data.size_cons]; omega
      rw [e]; exact hbud₄
    · have e : r - (Data.cons a b).size = r - 1 - a.size - b.size := by
        rw [Data.size_cons]; omega
      rw [hbp₄, e]
    · rw [S_cons]
      refine (hde₁.trans (?_ : DstEff t c₁ c₄ (S a ++ S b))).cast (by simp)
      refine DstEff.trans ?_ hde₄
      refine ⟨?_, ?_, ?_⟩
      · rw [← hu₂.pos (d := t) (by simp [htb])]; exact hde₃.holds
      · intro q hq'
        rw [hde₃.outside q (by rw [hu₂.pos (d := t) (by simp [htb])]; exact hq'),
          hu₂.tapes (d := t) (by simp [htb])]
      · rw [hde₃.pos, hu₂.pos (d := t) (by simp [htb])]

/-- **`copyTree src (some t) true`** with a sufficient budget. -/
theorem exec_copyTree_charge {k : ProgId} {pc : Fin maxPc} {src t : WT}
    (hins : instrAt k pc = .copyTree src (some t) true) (hpc : pc.val + 1 < maxPc)
    (hst : src ≠ t) (hsc : src ≠ CNT) (htc : t ≠ CNT) (hsb : src ≠ BUD) (htb : t ≠ BUD) (v : Data)
    (c : Cfg input) (hq : c.state = at_ k pc) (hcnt : Unary (c.workTapes CNT) 0)
    (hcp : c.workTapePos CNT = 0) {r : ℕ} (hbud : Unary (c.workTapes BUD) r)
    (hbp : c.workTapePos BUD = r) (hr : v.size ≤ r)
    (hsrc : Holds (c.workTapes src) (c.workTapePos src) (S v)) :
    ∃ n ≤ 4 * v.size + 1, ∃ c', Reach c n c' [] ∧ c'.state = next_ k pc hpc ∧
      Untouched c c' [] [src, CNT, t, BUD] ∧
      c'.workTapes src = c.workTapes src ∧ c'.workTapePos src = c.workTapePos src + v.size ∧
      Unary (c'.workTapes CNT) 0 ∧ c'.workTapePos CNT = 0 ∧
      Unary (c'.workTapes BUD) (r - v.size) ∧ c'.workTapePos BUD = ((r - v.size : ℕ) : ℤ) ∧
      DstEff t c c' (S v) := by
  have hcb : CNT ≠ BUD := by decide
  obtain ⟨c₁, hr₁, hs₁, hu₁, hcnt₁, hcp₁⟩ := copyTree_start hins c hq hcnt hcp
  obtain ⟨n, hn, c', hr', hst', hu, hsrc', hsrcp', hcnt', hcp', hbud', hbp', hde⟩ :=
    copyTree_scan_charge hins hpc hst hsc htc hsb htb v c₁ 1 r hs₁ le_rfl hcnt₁ (by simp [hcp₁])
      (by rw [hu₁.tapes (d := BUD) (by decide)]; exact hbud)
      (by rw [hu₁.pos (d := BUD) (by decide)]; exact hbp) hr
      (by rw [hu₁.tapes (d := src) (by simp [hsc]), hu₁.pos (d := src) (by simp [hsc])]; exact hsrc)
  refine ⟨1 + n, by omega, c', (hr₁.trans hr').cast_out (by simp), by simpa [scanExit] using hst',
    (hu₁.trans hu).mono (by simp) (by simp), ?_, ?_, by simpa using hcnt', by simpa using hcp',
    hbud', hbp', ?_⟩
  · rw [hsrc', hu₁.tapes (d := src) (by simp [hsc])]
  · rw [hsrcp', hu₁.pos (d := src) (by simp [hsc])]
  · refine ⟨?_, ?_, ?_⟩
    · rw [← hu₁.pos (d := t) (by simp [htc])]; exact hde.holds
    · intro q hq'
      rw [hde.outside q (by rw [hu₁.pos (d := t) (by simp [htc])]; exact hq'),
        hu₁.tapes (d := t) (by simp [htc])]
    · rw [hde.pos, hu₁.pos (d := t) (by simp [htc])]


/-- The scan of the charged copy over `S(v)` with a budget `r < |v|` halts silently. -/
theorem copyTree_scan_fail {k : ProgId} {pc : Fin maxPc} {src t : WT}
    (hins : instrAt k pc = .copyTree src (some t) true) (hpc : pc.val + 1 < maxPc)
    (hst : src ≠ t) (hsc : src ≠ CNT) (htc : t ≠ CNT) (hsb : src ≠ BUD) (htb : t ≠ BUD) (v : Data) :
    ∀ (c : Cfg input) (d r : ℕ), c.state = some ⟨k, pc, p1⟩ → 1 ≤ d →
      Unary (c.workTapes CNT) d → c.workTapePos CNT = d →
      Unary (c.workTapes BUD) r → c.workTapePos BUD = r → r < v.size →
      Holds (c.workTapes src) (c.workTapePos src) (S v) →
    HaltsIn c (4 * v.size) := by
  have hcb : CNT ≠ BUD := by decide
  induction v with
  | nil =>
    intro c d r hq hd hcnt hcp hbud hbp hr hsrc
    simp only [Data.size_nil] at hr
    have hr0 : r = 0 := by omega
    subst hr0
    have hread : c.workTapes src (c.workTapePos src) = some .zero := by
      simpa using hsrc.head
    have h1 := step_instr hq hins
    simp only [execInstr, workTapeSymbols_eq, hread, if_true, Act.mw_out, Act.ww_out, Act.base_out,
      Option.toList_none, Act.mw_next, Act.ww_next, Act.base_next, resolve_stay] at h1
    set c₁ := applyAct ((((((Act.base (.stay p2)).mw src 1).mw CNT (-1)).mw BUD (-1)).ww t
      (some .zero)).mw t 1) (some ⟨k, pc, p2⟩) c with hc₁
    have hbud₁ : c₁.workTapes BUD = c.workTapes BUD := by
      rw [hc₁, applyAct_workTapes_of_none _ _ _ BUD (by
        simp [Act.mw_works_of_ne _ htb.symm, Act.ww_works_of_ne _ htb.symm,
          Act.mw_works_of_ne _ hsb.symm, Act.mw_works_of_ne _ hcb.symm])]
    have hbread : c₁.workTapes BUD (c₁.workTapePos BUD) = none := by
      rw [hbud₁, Unary.zero_iff.mp hbud]
    have h2 := step_instr (c := c₁) (k := k) (pc := pc) (ph := p2) (by simp [hc₁]) hins
    simp only [execInstr, workTapeSymbols_eq, hbread, if_true, Act.base_out, Option.toList_none,
      Act.base_next, resolve_halt] at h2
    exact (HaltsIn.of_reach ((h1.trans h2).cast_out (by simp)) rfl).mono (by simp)
  | cons a b iha ihb =>
    intro c d r hq hd hcnt hcp hbud hbp hr hsrc
    simp only [Data.size_cons] at hr
    rw [S_cons] at hsrc
    have hread : c.workTapes src (c.workTapePos src) = some .one := hsrc.head
    -- step 1: the `1`
    have h1 := step_instr hq hins
    simp only [execInstr, workTapeSymbols_eq, hread, if_true, Act.mw_out, Act.ww_out, Act.base_out,
      Option.toList_none, Act.mw_next, Act.ww_next, Act.base_next, resolve_stay] at h1
    set c₁ := applyAct (((((((Act.base (.stay p4)).mw src 1).ww CNT (some .one)).mw CNT 1).mw BUD
      (-1)).ww t (some .one)).mw t 1) (some ⟨k, pc, p4⟩) c with hc₁
    have hu₁ : Untouched c c₁ [] [src, CNT, t, BUD] :=
      untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
        have h1 : d ≠ src := fun e => hd (by simp [e])
        have h2 : d ≠ CNT := fun e => hd (by simp [e])
        have h3 : d ≠ t := fun e => hd (by simp [e])
        have h4 : d ≠ BUD := fun e => hd (by simp [e])
        simp [Act.mw_works_of_ne _ h1, Act.mw_works_of_ne _ h2, Act.mw_works_of_ne _ h3,
          Act.mw_works_of_ne _ h4, Act.ww_works_of_ne _ h3, Act.ww_works_of_ne _ h2]⟩ _ _
    have hsrc₁ : c₁.workTapes src = c.workTapes src := by
      rw [hc₁, applyAct_workTapes_of_none _ _ _ src (by
        simp [Act.mw_works_of_ne _ hst, Act.ww_works_of_ne _ hst, Act.mw_works_of_ne _ hsc,
          Act.ww_works_of_ne _ hsc, Act.mw_works_of_ne _ hsb])]
    have hsrcp₁ : c₁.workTapePos src = c.workTapePos src + 1 := by
      simp [hc₁, Act.mw_works_of_ne _ hst, Act.ww_works_of_ne _ hst, Act.mw_works_of_ne _ hsc,
        Act.ww_works_of_ne _ hsc, Act.mw_works_of_ne _ hsb]
    have hcnt₁ : Unary (c₁.workTapes CNT) (d + 1) := by
      rw [hc₁, applyAct_workTapes_of_some _ _ _ CNT (s := some .one) (by
        simp [Act.mw_works_of_ne _ htc.symm, Act.ww_works_of_ne _ htc.symm,
          Act.mw_works_of_ne _ hcb]), hcp]
      exact hcnt.push
    have hcp₁ : c₁.workTapePos CNT = d + 1 := by
      simp [hc₁, Act.mw_works_of_ne _ htc.symm, Act.ww_works_of_ne _ htc.symm,
        Act.mw_works_of_ne _ hcb, hcp]
    have hbud₁ : c₁.workTapes BUD = c.workTapes BUD := by
      rw [hc₁, applyAct_workTapes_of_none _ _ _ BUD (by
        simp [Act.mw_works_of_ne _ htb.symm, Act.ww_works_of_ne _ htb.symm,
          Act.mw_works_of_ne _ hsb.symm, Act.mw_works_of_ne _ hcb.symm,
          Act.ww_works_of_ne _ hcb.symm])]
    -- step 2: the budget check
    have h2 := step_instr (c := c₁) (k := k) (pc := pc) (ph := p4) (by simp [hc₁]) hins
    rcases Nat.eq_zero_or_pos r with hr0 | hr0
    · -- no budget: halt
      subst hr0
      have hbread : c₁.workTapes BUD (c₁.workTapePos BUD) = none := by
        rw [hbud₁, Unary.zero_iff.mp hbud]
      simp only [execInstr, workTapeSymbols_eq, hbread, Act.base_out, Option.toList_none,
        Act.base_next, resolve_halt] at h2
      exact (HaltsIn.of_reach ((h1.trans h2).cast_out (by simp)) rfl).mono (by
        rw [Data.size_cons]; omega)
    have hbp₁ : c₁.workTapePos BUD = ((r - 1 : ℕ) : ℤ) := by
      simp [hc₁, Act.mw_works_of_ne _ htb.symm, Act.ww_works_of_ne _ htb.symm,
        Act.mw_works_of_ne _ hsb.symm, Act.mw_works_of_ne _ hcb.symm, Act.ww_works_of_ne _ hcb.symm,
        hbp]
      omega
    have hbread : c₁.workTapes BUD (c₁.workTapePos BUD) = some .one := by
      rw [hbud₁, hbp₁, hbud.cell]; rw [if_pos]; omega
    simp only [execInstr, workTapeSymbols_eq, hbread, Act.ww_out, Act.base_out, Option.toList_none,
      Act.ww_next, Act.base_next, resolve_stay] at h2
    set c₂ := applyAct ((Act.base (.stay p1)).ww BUD none) (some ⟨k, pc, p1⟩) c₁ with hc₂
    have hu₂ : Untouched c₁ c₂ [] [BUD] :=
      untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
        have h4 : d ≠ BUD := by simpa using hd
        simp [Act.ww_works_of_ne _ h4]⟩ _ _
    have hbud₂ : Unary (c₂.workTapes BUD) (r - 1) := by
      rw [hc₂, applyAct_workTapes_of_some _ _ _ BUD (s := none) (by simp), hbud₁, hbp₁]
      have := hbud
      rw [show r = r - 1 + 1 by omega] at this
      exact this.pop
    have hbp₂ : c₂.workTapePos BUD = ((r - 1 : ℕ) : ℤ) := by simp [hc₂, hbp₁]
    have hsrc₂ : Holds (c₂.workTapes src) (c₂.workTapePos src) (S a ++ S b) := by
      rw [hu₂.tapes (d := src) (by simp [hsb]), hu₂.pos (d := src) (by simp [hsb]), hsrc₁, hsrcp₁]
      exact hsrc.tail
    have hs₂ : c₂.state = some ⟨k, pc, p1⟩ := by simp [hc₂]
    have hcnt₂ : Unary (c₂.workTapes CNT) (d + 1) := by
      rw [hu₂.tapes (d := CNT) (by simp [hcb])]; exact hcnt₁
    have hcp₂ : c₂.workTapePos CNT = ((d + 1 : ℕ) : ℤ) := by
      rw [hu₂.pos (d := CNT) (by simp [hcb]), hcp₁]; push_cast; ring
    have h12 : Reach c 2 c₂ [] := (h1.trans h2).cast_out (by simp)
    rcases Nat.lt_or_ge (r - 1) a.size with hra | hra
    · -- the left subtree exhausts the budget
      have := iha c₂ (d + 1) (r - 1) hs₂ (by omega) hcnt₂ hcp₂ hbud₂ hbp₂ hra hsrc₂.of_append_left
      exact (HaltsIn.after h12 this).mono (by rw [Data.size_cons]; omega)
    · -- the left subtree goes through; the right one exhausts the budget
      obtain ⟨na, hna, c₃, hr₃, hst₃, hu₃, hsrc₃, hsrcp₃, hcnt₃, hcp₃, hbud₃, hbp₃, hde₃⟩ :=
        copyTree_scan_charge hins hpc hst hsc htc hsb htb a c₂ (d + 1) (r - 1) hs₂ (by omega)
          hcnt₂ hcp₂ hbud₂ hbp₂ hra hsrc₂.of_append_left
      have hst₃' : c₃.state = some ⟨k, pc, p1⟩ := by
        rw [hst₃, scanExit, if_neg (by omega)]
      have hsrc₃' : Holds (c₃.workTapes src) (c₃.workTapePos src) (S b) := by
        rw [hsrc₃, hsrcp₃]
        have := hsrc₂.of_append_right
        rw [length_S] at this
        convert this using 1
      have := ihb c₃ d (r - 1 - a.size) hst₃' hd (by simpa using hcnt₃) (by rw [hcp₃]; simp)
        hbud₃ hbp₃ (by omega) hsrc₃'
      exact (HaltsIn.after ((h12.trans hr₃).cast_out (by simp)) this).mono (by rw [Data.size_cons]; omega)

/-- **`copyTree src (some t) true`** with an insufficient budget halts silently. -/
theorem exec_copyTree_charge_fail {k : ProgId} {pc : Fin maxPc} {src t : WT}
    (hins : instrAt k pc = .copyTree src (some t) true) (hpc : pc.val + 1 < maxPc)
    (hst : src ≠ t) (hsc : src ≠ CNT) (htc : t ≠ CNT) (hsb : src ≠ BUD) (htb : t ≠ BUD) (v : Data)
    (c : Cfg input) (hq : c.state = at_ k pc) (hcnt : Unary (c.workTapes CNT) 0)
    (hcp : c.workTapePos CNT = 0) {r : ℕ} (hbud : Unary (c.workTapes BUD) r)
    (hbp : c.workTapePos BUD = r) (hr : r < v.size)
    (hsrc : Holds (c.workTapes src) (c.workTapePos src) (S v)) :
    HaltsIn c (4 * v.size + 1) := by
  obtain ⟨c₁, hr₁, hs₁, hu₁, hcnt₁, hcp₁⟩ := copyTree_start hins c hq hcnt hcp
  have := copyTree_scan_fail hins hpc hst hsc htc hsb htb v c₁ 1 r hs₁ le_rfl hcnt₁ (by simp [hcp₁])
    (by rw [hu₁.tapes (d := BUD) (by decide)]; exact hbud)
    (by rw [hu₁.pos (d := BUD) (by decide)]; exact hbp) hr
    (by rw [hu₁.tapes (d := src) (by simp [hsc]), hu₁.pos (d := src) (by simp [hsc])]; exact hsrc)
  rw [Nat.add_comm]
  exact HaltsIn.after hr₁ this

end MIPRE.TM.Interp

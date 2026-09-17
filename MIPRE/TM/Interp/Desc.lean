/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.TM.Interp.GetEnv
import MIPRE.TM.Interp.CopyTreeCharge

/-!
# Tape descriptions

A work tape is described by the list it holds from cell `0` (blank elsewhere) and its head
position; a configuration by its control and the six descriptions (`Desc`). Every routine
becomes a transformation of descriptions (`D_write`, `D_copyTree`, …), so that the
correctness of a step of the evaluation machine is a chain of such transformations followed
by list algebra (`overwrite`).
-/

namespace MIPRE.TM.Interp

open Turing MultiInputTM Phase MIPRE.Cost

variable {input : Fin 7 → List Sym}

/-! ## One tape -/

/-- A tape holding exactly `l` from cell `0`, its head at cell `p`. -/
@[ext] structure TapeSt where
  l : List Sym
  p : ℕ

/-- The tape `τ` with head `pos` is as described by `s`. -/
def TapeIs (τ : Tape) (pos : ℤ) (s : TapeSt) : Prop :=
  Holds τ 0 s.l ∧ (∀ q : ℤ, q < 0 → τ q = none) ∧ (∀ q : ℤ, (s.l.length : ℤ) ≤ q → τ q = none) ∧
    pos = s.p

/-- Writing `w` over `l` from position `p` (no gap: `p ≤ l.length`). -/
def overwrite (l : List Sym) (p : ℕ) (w : List Sym) : List Sym :=
  l.take p ++ w ++ l.drop (p + w.length)

@[simp] theorem overwrite_zero (l w : List Sym) : overwrite l 0 w = w ++ l.drop w.length := by
  simp [overwrite]

theorem overwrite_append (a l w : List Sym) :
    overwrite (a ++ l) a.length w = a ++ w ++ l.drop w.length := by
  simp only [overwrite, List.take_left]
  rw [← List.drop_drop, List.drop_left]

theorem overwrite_append' (a l w : List Sym) {p : ℕ} (hp : p = a.length) :
    overwrite (a ++ l) p w = a ++ w ++ l.drop w.length := by
  subst hp; exact overwrite_append a l w

theorem overwrite_append_nil (a w : List Sym) {p : ℕ} (hp : p = a.length) :
    overwrite a p w = a ++ w := by
  have := overwrite_append' a [] w hp
  simpa using this

theorem length_overwrite {l : List Sym} {p : ℕ} (hp : p ≤ l.length) (w : List Sym) :
    (overwrite l p w).length = max l.length (p + w.length) := by
  simp [overwrite]; omega

theorem overwrite_nil (l : List Sym) (p : ℕ) : overwrite l p [] = l := by
  simp [overwrite]

@[simp] theorem overwrite_cons_succ (a : Sym) (l : List Sym) (p : ℕ) (w : List Sym) :
    overwrite (a :: l) (p + 1) w = a :: overwrite l p w := by
  simp only [overwrite, List.take_succ_cons, List.cons_append, List.cons.injEq, true_and]
  rw [show p + 1 + w.length = (p + w.length) + 1 by omega, List.drop_succ_cons]

namespace TapeIs

variable {τ : Tape} {pos : ℤ} {s : TapeSt}

theorem holds (h : TapeIs τ pos s) : Holds τ 0 s.l := h.1
theorem before (h : TapeIs τ pos s) (q : ℤ) (hq : q < 0) : τ q = none := h.2.1 q hq
theorem beyond (h : TapeIs τ pos s) (q : ℤ) (hq : (s.l.length : ℤ) ≤ q) : τ q = none := h.2.2.1 q hq
theorem pos_eq (h : TapeIs τ pos s) : pos = s.p := h.2.2.2

/-- The cell `n`. -/
theorem read (h : TapeIs τ pos s) (n : ℕ) : τ n = s.l[n]? := by
  by_cases hn : n < s.l.length
  · rw [List.getElem?_eq_getElem hn]
    have := h.holds n hn
    rwa [zero_add] at this
  · rw [List.getElem?_eq_none (by omega)]
    exact h.beyond n (by omega)

/-- The cell under the head. -/
theorem read_pos (h : TapeIs τ pos s) : τ pos = s.l[s.p]? := by
  rw [h.pos_eq]; exact h.read s.p

theorem read_at (h : TapeIs τ pos s) {p : ℕ} (hp : pos = p) : τ pos = s.l[p]? := by
  rw [hp]; exact h.read p

/-- A middle segment is held at its offset. -/
theorem holds_sub (h : TapeIs τ pos s) {l₁ l₂ l₃ : List Sym} (e : s.l = l₁ ++ l₂ ++ l₃) :
    Holds τ l₁.length l₂ := by
  have := h.holds
  rw [e] at this
  have := this.of_append_left.of_append_right
  rwa [zero_add] at this

/-- The tail from `n`. -/
theorem holds_drop (h : TapeIs τ pos s) (n : ℕ) : Holds τ n (s.l.drop n) := by
  have := h.holds
  rw [← List.take_append_drop n s.l] at this
  have := this.of_append_right
  by_cases hn : n ≤ s.l.length
  · rwa [zero_add, List.length_take, min_eq_left hn] at this
  · rw [List.drop_of_length_le (by omega)]; exact Holds.nil

theorem blank_after_drop (h : TapeIs τ pos s) (n : ℕ) :
    τ (n + (s.l.drop n).length) = none := by
  apply h.beyond
  simp only [List.length_drop]; omega

/-- Same tape, another head position. -/
theorem of_same {l : List Sym} {p : ℕ} (h : TapeIs τ pos ⟨l, p⟩) {τ' : Tape} {pos' : ℤ} {p' : ℕ}
    (hτ : τ' = τ) (hpos : pos' = p') : TapeIs τ' pos' ⟨l, p'⟩ :=
  ⟨hτ ▸ h.holds, fun q hq => hτ ▸ h.before q hq, fun q hq => hτ ▸ h.beyond q hq, hpos⟩

/-- `w` written from `p`, the rest as before. -/
theorem of_overwrite {l : List Sym} {p : ℕ} (h : TapeIs τ pos ⟨l, p⟩) (hp : p ≤ l.length)
    {τ' : Tape} {pos' : ℤ} {p' : ℕ} {w : List Sym} (hw : Holds τ' p w)
    (hout : ∀ q : ℤ, (q < p ∨ (p : ℤ) + w.length ≤ q) → τ' q = τ q) (hpos : pos' = p') :
    TapeIs τ' pos' ⟨overwrite l p w, p'⟩ := by
  have hh : Holds τ 0 l := h.holds
  have hbf : ∀ q : ℤ, q < 0 → τ q = none := h.before
  have hby : ∀ q : ℤ, (l.length : ℤ) ≤ q → τ q = none := h.beyond
  refine ⟨?_, ?_, ?_, hpos⟩
  · show Holds τ' 0 (l.take p ++ w ++ l.drop (p + w.length))
    refine Holds.append (Holds.append ?_ ?_) ?_
    · intro k hk
      rw [List.length_take] at hk
      rw [zero_add, hout k (Or.inl (by omega)), List.getElem_take]
      have := hh k (by omega)
      rwa [zero_add] at this
    · rw [zero_add, List.length_take, min_eq_left hp]; exact hw
    · intro k hk
      rw [List.length_drop] at hk
      rw [List.length_append, List.length_take, min_eq_left hp, List.getElem_drop]
      have := hh (p + w.length + k) (by omega)
      rw [zero_add] at this
      rw [hout _ (Or.inr (by push_cast; omega))]
      convert this using 2
      push_cast; ring
  · intro q hq
    rw [hout q (Or.inl (by omega))]
    exact hbf q hq
  · intro q hq
    show τ' q = none
    rw [length_overwrite hp] at hq
    rw [hout q (Or.inr (by push_cast at hq ⊢; omega))]
    exact hby q (by push_cast at hq ⊢; omega)

/-- Erased from `n` to the end. -/
theorem of_truncate {l : List Sym} {p : ℕ} (h : TapeIs τ pos ⟨l, p⟩) {n : ℕ} (hn : n ≤ l.length)
    {τ' : Tape} {pos' : ℤ} {p' : ℕ}
    (hout : ∀ q : ℤ, (q < n ∨ (l.length : ℤ) ≤ q) → τ' q = τ q)
    (hbl : BlankFrom τ' n (l.length - n)) (hpos : pos' = p') :
    TapeIs τ' pos' ⟨l.take n, p'⟩ := by
  have hh : Holds τ 0 l := h.holds
  have hbf : ∀ q : ℤ, q < 0 → τ q = none := h.before
  have hby : ∀ q : ℤ, (l.length : ℤ) ≤ q → τ q = none := h.beyond
  refine ⟨?_, ?_, ?_, hpos⟩
  · show Holds τ' 0 (l.take n)
    intro k hk
    rw [List.length_take] at hk
    rw [zero_add, hout k (Or.inl (by omega)), List.getElem_take]
    have := hh k (by omega)
    rwa [zero_add] at this
  · intro q hq
    rw [hout q (Or.inl (by omega))]
    exact hbf q hq
  · intro q hq
    show τ' q = none
    simp only [List.length_take, min_eq_left hn] at hq
    by_cases hq' : q < l.length
    · exact hbl q hq (by push_cast; omega)
    · rw [hout q (Or.inr (by omega))]
      exact hby q (by omega)

theorem of_unary {n : ℕ} (hu : Unary τ n) (hpos : pos = n) :
    TapeIs τ pos ⟨List.replicate n .one, n⟩ :=
  ⟨hu.1, fun q hq => hu.2.2 q hq, fun q hq => hu.2.1 q (by simpa using hq), hpos⟩

theorem unary {n : ℕ} (h : TapeIs τ pos ⟨List.replicate n .one, n⟩) : Unary τ n :=
  ⟨h.holds, fun q hq => h.beyond q (by simpa using hq), fun q hq => h.before q hq⟩

theorem of_envTape {env : Env} (h : EnvTape τ env) {p : ℕ} (hpos : pos = p) :
    TapeIs τ pos ⟨envRepr env, p⟩ :=
  ⟨h.holds, fun q hq => h.before q hq, fun q hq => h.beyond q hq, hpos⟩

theorem envTape {env : Env} {p : ℕ} (h : TapeIs τ pos ⟨envRepr env, p⟩) : EnvTape τ env :=
  ⟨h.holds, fun q hq => h.before q hq, fun q hq => h.beyond q hq⟩

end TapeIs

/-! ## A configuration -/

/-- The configuration `c` has control `q` and its work tapes are as described by `ds`. -/
def Desc (c : Cfg input) (q : Option Ctl) (ds : WT → TapeSt) : Prop :=
  c.state = q ∧ ∀ t, TapeIs (c.workTapes t) (c.workTapePos t) (ds t)

namespace Desc

variable {c : Cfg input} {q : Option Ctl} {ds : WT → TapeSt}

theorem state (h : Desc c q ds) : c.state = q := h.1
theorem tape (h : Desc c q ds) (t : WT) : TapeIs (c.workTapes t) (c.workTapePos t) (ds t) := h.2 t
theorem pos (h : Desc c q ds) (t : WT) : c.workTapePos t = (ds t).p := (h.2 t).pos_eq
theorem read (h : Desc c q ds) (t : WT) : c.workTapes t (c.workTapePos t) = (ds t).l[(ds t).p]? :=
  (h.2 t).read_pos

theorem cast (h : Desc c q ds) {q' : Option Ctl} {ds' : WT → TapeSt} (hq : q = q')
    (hds : ds = ds') : Desc c q' ds' := hq ▸ hds ▸ h

theorem cast_ds (h : Desc c q ds) {ds' : WT → TapeSt} (hds : ∀ t, ds t = ds' t) : Desc c q ds' :=
  h.cast rfl (funext hds)

/-- A run touching only the tapes in `SW`, whose new descriptions are given. -/
theorem of_untouched (h : Desc c q ds) {c' : Cfg input} {SW : List WT}
    (hu : Untouched c c' [] SW) {q' : Option Ctl} (hq' : c'.state = q') {ds' : WT → TapeSt}
    (hT : ∀ t ∈ SW, TapeIs (c'.workTapes t) (c'.workTapePos t) (ds' t))
    (hS : ∀ t, t ∉ SW → ds' t = ds t) : Desc c' q' ds' := by
  refine ⟨hq', fun t => ?_⟩
  by_cases ht : t ∈ SW
  · exact hT t ht
  · rw [hS t ht, (hu.tapes ht), (hu.pos ht)]
    exact h.tape t

end Desc

theorem not_mem_of_ne {t : WT} {SW : List WT} (h : ∀ t' ∈ SW, t ≠ t') : t ∉ SW :=
  fun hm => h t hm rfl

/-! ## The routines on descriptions -/

section Routines

variable {k : ProgId} {pc : Fin maxPc} {c : Cfg input} {ds : WT → TapeSt}

theorem D_write {t : WT} {s : Sym} (hins : instrAt k pc = .write t s) (hpc : pc.val + 1 < maxPc)
    (hd : Desc c (at_ k pc) ds) (hp : (ds t).p ≤ (ds t).l.length) :
    ∃ c', Reach c 1 c' [] ∧
      Desc c' (next_ k pc hpc) (Function.update ds t ⟨overwrite (ds t).l (ds t).p [s], (ds t).p + 1⟩) := by
  obtain ⟨c', hr, hs, hu, htape, hpos⟩ := exec_write hins hpc c hd.state
  refine ⟨c', hr, hd.of_untouched hu hs ?_ ?_⟩
  · intro t' ht'
    simp only [List.mem_singleton] at ht'
    subst ht'
    rw [Function.update_self]
    refine (hd.tape t').of_overwrite hp ?_ ?_ ?_
    · rw [Holds.singleton_iff, htape, ← hd.pos, Function.update_self]
    · intro q hq
      rw [htape, hd.pos, Function.update_of_ne (by simp only [List.length_singleton] at hq; omega)]
    · rw [hpos, hd.pos]; push_cast; ring
  · intro t' ht'
    exact Function.update_of_ne (by simpa using ht') _ _

theorem D_move_right {t : WT} (hins : instrAt k pc = .move t true) (hpc : pc.val + 1 < maxPc)
    (hd : Desc c (at_ k pc) ds) :
    ∃ c', Reach c 1 c' [] ∧ Desc c' (next_ k pc hpc) (Function.update ds t ⟨(ds t).l, (ds t).p + 1⟩) := by
  obtain ⟨c', hr, hs, hu, htape, hpos⟩ := exec_move hins hpc c hd.state
  refine ⟨c', hr, hd.of_untouched hu hs ?_ ?_⟩
  · intro t' ht'
    simp only [List.mem_singleton] at ht'
    subst ht'
    rw [Function.update_self]
    exact (hd.tape t').of_same htape (by rw [hpos, hd.pos]; simp)
  · intro t' ht'
    exact Function.update_of_ne (by simpa using ht') _ _

theorem D_move_left {t : WT} (hins : instrAt k pc = .move t false) (hpc : pc.val + 1 < maxPc)
    (hd : Desc c (at_ k pc) ds) (hp : 1 ≤ (ds t).p) :
    ∃ c', Reach c 1 c' [] ∧ Desc c' (next_ k pc hpc) (Function.update ds t ⟨(ds t).l, (ds t).p - 1⟩) := by
  obtain ⟨c', hr, hs, hu, htape, hpos⟩ := exec_move hins hpc c hd.state
  refine ⟨c', hr, hd.of_untouched hu hs ?_ ?_⟩
  · intro t' ht'
    simp only [List.mem_singleton] at ht'
    subst ht'
    rw [Function.update_self]
    exact (hd.tape t').of_same htape (by rw [hpos, hd.pos]; simp; omega)
  · intro t' ht'
    exact Function.update_of_ne (by simpa using ht') _ _

theorem D_rewind {t : WT} (hins : instrAt k pc = .rewind t) (hpc : pc.val + 1 < maxPc)
    (hd : Desc c (at_ k pc) ds) (hp : (ds t).p ≤ (ds t).l.length) :
    ∃ c', Reach c ((ds t).p + 2) c' [] ∧ Desc c' (next_ k pc hpc) (Function.update ds t ⟨(ds t).l, 0⟩) := by
  have hT := hd.tape t
  obtain ⟨c', hr, hs, hu, htape, hpos⟩ := exec_rewind hins hpc (ds t).p c hd.state
    (by
      intro q h1 h2
      rw [hd.pos] at h1 h2
      obtain ⟨n, rfl⟩ : ∃ n : ℕ, q = n := ⟨q.toNat, by omega⟩
      rw [hT.read, List.getElem?_eq_getElem (by omega)]
      simp)
    (by rw [hd.pos]; exact hT.before _ (by omega))
  refine ⟨c', hr, hd.of_untouched hu hs ?_ ?_⟩
  · intro t' ht'
    simp only [List.mem_singleton] at ht'
    subst ht'
    rw [Function.update_self]
    exact hT.of_same htape (by rw [hpos, hd.pos]; simp)
  · intro t' ht'
    exact Function.update_of_ne (by simpa using ht') _ _

theorem D_toEnd {t : WT} (hins : instrAt k pc = .toEnd t) (hpc : pc.val + 1 < maxPc)
    (hd : Desc c (at_ k pc) ds) (hp : (ds t).p ≤ (ds t).l.length) :
    ∃ c', Reach c ((ds t).l.length - (ds t).p + 1) c' [] ∧
      Desc c' (next_ k pc hpc) (Function.update ds t ⟨(ds t).l, (ds t).l.length⟩) := by
  have hT := hd.tape t
  obtain ⟨c', hr, hs, hu, htape, hpos⟩ := exec_toEnd hins hpc ((ds t).l.drop (ds t).p) c hd.state
    (by rw [hd.pos]; exact hT.holds_drop _) (by rw [hd.pos]; exact hT.blank_after_drop _)
  refine ⟨c', hr.cast_n (by simp), hd.of_untouched hu hs ?_ ?_⟩
  · intro t' ht'
    simp only [List.mem_singleton] at ht'
    subst ht'
    rw [Function.update_self]
    exact hT.of_same htape (by rw [hpos, hd.pos]; simp; omega)
  · intro t' ht'
    exact Function.update_of_ne (by simpa using ht') _ _

theorem D_eraseRight {t : WT} (hins : instrAt k pc = .eraseRight t) (hpc : pc.val + 1 < maxPc)
    (hd : Desc c (at_ k pc) ds) (hp : (ds t).p ≤ (ds t).l.length)
    (hfr : ∀ s ∈ (ds t).l.drop (ds t).p, s ≠ .fr) :
    ∃ c', Reach c (2 * ((ds t).l.length - (ds t).p) + 1) c' [] ∧
      Desc c' (next_ k pc hpc) (Function.update ds t ⟨(ds t).l.take (ds t).p, (ds t).p⟩) := by
  have hT := hd.tape t
  obtain ⟨c', hr, hs, hu, hout, hbl, hpos⟩ := exec_eraseRight hins hpc ((ds t).l.drop (ds t).p) c
    hd.state (by rw [hd.pos]; exact hT.holds_drop _) (by rw [hd.pos]; exact hT.blank_after_drop _)
  refine ⟨c', hr.cast_n (by simp), hd.of_untouched hu hs ?_ ?_⟩
  · intro t' ht'
    simp only [List.mem_singleton] at ht'
    subst ht'
    rw [Function.update_self]
    refine hT.of_truncate (n := (ds t').p) hp ?_ ?_ (by rw [hpos, hd.pos])
    · intro q hq
      apply hout
      rw [hd.pos]
      simp only [List.length_drop]
      rcases hq with hq | hq
      · exact Or.inl hq
      · right; push_cast; omega
    · rw [hd.pos] at hbl
      simpa using hbl
  · intro t' ht'
    exact Function.update_of_ne (by simpa using ht') _ _

theorem D_copyUntil {m : Option Sym} {src dst : WT} (hins : instrAt k pc = .copyUntil m src dst)
    (hpc : pc.val + 1 < maxPc) (hsd : src ≠ dst) (hd : Desc c (at_ k pc) ds)
    {l₁ w l₂ : List Sym} (hsrc : (ds src).l = l₁ ++ w ++ l₂) (hsp : (ds src).p = l₁.length)
    (hm : ∀ s ∈ w, some s ≠ m) (hend : l₂[0]? = m) (hdp : (ds dst).p ≤ (ds dst).l.length) :
    ∃ c', Reach c (w.length + 1) c' [] ∧
      Desc c' (next_ k pc hpc)
        (Function.update (Function.update ds src ⟨(ds src).l, l₁.length + w.length⟩) dst
          ⟨overwrite (ds dst).l (ds dst).p w, (ds dst).p + w.length⟩) := by
  have hS := hd.tape src
  have hD := hd.tape dst
  obtain ⟨c', hr, hs, hu, hstape, hspos, hdh, hdout, hdpos⟩ := exec_copyUntil hins hpc hsd w c
    hd.state (by rw [hd.pos, hsp]; exact hS.holds_sub hsrc) hm
    (by
      have := hS.read (l₁.length + w.length)
      rw [hsrc, List.getElem?_append_right (by simp), List.length_append, Nat.sub_self] at this
      rw [hd.pos, hsp, ← Nat.cast_add, this, hend])
  refine ⟨c', hr, hd.of_untouched hu hs ?_ ?_⟩
  · intro t' ht'
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht'
    rcases ht' with rfl | rfl
    · rw [Function.update_of_ne hsd, Function.update_self]
      exact hS.of_same hstape (by rw [hspos, hd.pos, hsp]; push_cast; ring)
    · rw [Function.update_self]
      refine hD.of_overwrite hdp ?_ ?_ ?_
      · rw [← hd.pos]; exact hdh
      · intro q hq; exact hdout q (by rw [hd.pos]; exact hq)
      · rw [hdpos, hd.pos]; push_cast; ring
  · intro t' ht'
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or] at ht'
    rw [Function.update_of_ne ht'.2, Function.update_of_ne ht'.1]

theorem D_branch_taken {t : WT} {s : Option Sym} {target : ProgId}
    (hins : instrAt k pc = .branch t s target) (hd : Desc c (at_ k pc) ds)
    (hs : (ds t).l[(ds t).p]? = s) :
    ∃ c', Reach c 1 c' [] ∧ Desc c' (at_ target ⟨0, by decide⟩) ds := by
  obtain ⟨c', hr, hst, hu, hall⟩ := exec_branch_taken hins c hd.state (by rw [hd.read]; exact hs)
  exact ⟨c', hr, hd.of_untouched (SW := []) (hu.mono (by simp) (by simp)) hst (by simp)
    (fun _ _ => rfl)⟩

theorem D_branch_not {t : WT} {s : Option Sym} {target : ProgId}
    (hins : instrAt k pc = .branch t s target) (hpc : pc.val + 1 < maxPc)
    (hd : Desc c (at_ k pc) ds) (hs : (ds t).l[(ds t).p]? ≠ s) :
    ∃ c', Reach c 1 c' [] ∧ Desc c' (next_ k pc hpc) ds := by
  obtain ⟨c', hr, hst, hu, hall⟩ := exec_branch_not hins hpc c hd.state (by rw [hd.read]; exact hs)
  exact ⟨c', hr, hd.of_untouched (SW := []) (hu.mono (by simp) (by simp)) hst (by simp)
    (fun _ _ => rfl)⟩

theorem D_jump {target : ProgId} (hins : instrAt k pc = .jump target) (hd : Desc c (at_ k pc) ds) :
    ∃ c', Reach c 1 c' [] ∧ Desc c' (at_ target ⟨0, by decide⟩) ds := by
  obtain ⟨c', hr, hst, hu, hall⟩ := exec_jump hins c hd.state
  exact ⟨c', hr, hd.of_untouched (SW := []) (hu.mono (by simp) (by simp)) hst (by simp)
    (fun _ _ => rfl)⟩

theorem D_halt (hins : instrAt k pc = .halt) (hd : Desc c (at_ k pc) ds) : HaltsIn c 1 :=
  exec_halt hins c hd.state

theorem D_emit {s : Sym} (hins : instrAt k pc = .emit s) (hpc : pc.val + 1 < maxPc)
    (hd : Desc c (at_ k pc) ds) : ∃ c', Reach c 1 c' [s] ∧ Desc c' (next_ k pc hpc) ds := by
  obtain ⟨c', hr, hst, hu, hall⟩ := exec_emit hins hpc c hd.state
  exact ⟨c', hr, hd.of_untouched (SW := []) (hu.mono (by simp) (by simp)) hst (by simp)
    (fun _ _ => rfl)⟩

theorem D_leftToMarker {m : Sym} {t : WT} (hins : instrAt k pc = .leftToMarker m t)
    (hpc : pc.val + 1 < maxPc) (hd : Desc c (at_ k pc) ds) {l₁ w l₂ : List Sym}
    (hl : (ds t).l = l₁ ++ w ++ l₂) (hp : (ds t).p = l₁.length + w.length)
    (hm : ∀ s ∈ w, s ≠ m) (hl₁ : l₁ = [] ∨ ∃ l₀, l₁ = l₀ ++ [m]) :
    ∃ c', Reach c (w.length + 2) c' [] ∧ Desc c' (next_ k pc hpc) (Function.update ds t ⟨(ds t).l, l₁.length⟩) := by
  have hT := hd.tape t
  obtain ⟨c', hr, hs, hu, htape, hpos⟩ := exec_leftToMarker hins hpc w c hd.state
    (by
      rw [hd.pos, hp]
      have := hT.holds_sub hl
      convert this using 2; push_cast; ring)
    hm
    (by
      rw [hd.pos, hp]
      rcases hl₁ with rfl | ⟨l₀, rfl⟩
      · right; exact hT.before _ (by simp)
      · left
        have := hT.read l₀.length
        rw [hl, List.append_assoc, List.append_assoc, List.getElem?_append_right le_rfl,
          Nat.sub_self, List.singleton_append, List.getElem?_cons_zero] at this
        convert this using 2
        simp only [List.length_append, List.length_singleton]; push_cast; ring)
  refine ⟨c', hr, hd.of_untouched hu hs ?_ ?_⟩
  · intro t' ht'
    simp only [List.mem_singleton] at ht'
    subst ht'
    rw [Function.update_self]
    exact hT.of_same htape (by rw [hpos, hd.pos, hp]; push_cast; ring)
  · intro t' ht'
    exact Function.update_of_ne (by simpa using ht') _ _

theorem D_popBack {m : Sym} {t : WT} (hins : instrAt k pc = .popBack m t)
    (hpc : pc.val + 1 < maxPc) (hd : Desc c (at_ k pc) ds) {l₁ w : List Sym} {a : Sym}
    (hl : (ds t).l = l₁ ++ w ++ [a]) (hp : (ds t).p = (ds t).l.length)
    (hm : ∀ s ∈ w, s ≠ m) (hl₁ : l₁ = [] ∨ ∃ l₀, l₁ = l₀ ++ [m]) :
    ∃ c', Reach c (w.length + 3) c' [] ∧ Desc c' (next_ k pc hpc) (Function.update ds t ⟨l₁, l₁.length⟩) := by
  have hT := hd.tape t
  have hlen : (ds t).l.length = l₁.length + w.length + 1 := by rw [hl]; simp; omega
  obtain ⟨c', hr, hs, hu, hout, hbl, hpos⟩ := exec_popBack hins hpc w a c hd.state
    (by
      rw [hd.pos, hp, hlen]
      have := hT.holds_sub (l₁ := l₁) (l₂ := w ++ [a]) (l₃ := [])
        (by rw [hl, List.append_nil, List.append_assoc])
      convert this using 2; push_cast; ring)
    hm
    (by
      rw [hd.pos, hp, hlen]
      rcases hl₁ with rfl | ⟨l₀, rfl⟩
      · right; exact hT.before _ (by simp)
      · left
        have := hT.read l₀.length
        rw [hl, List.append_assoc, List.append_assoc, List.getElem?_append_right le_rfl,
          Nat.sub_self, List.singleton_append, List.getElem?_cons_zero] at this
        convert this using 2
        simp only [List.length_append, List.length_singleton]; push_cast; ring)
  refine ⟨c', hr, hd.of_untouched hu hs ?_ ?_⟩
  · intro t' ht'
    simp only [List.mem_singleton] at ht'
    subst ht'
    rw [Function.update_self]
    have hpre : (ds t').l.take l₁.length = l₁ := by rw [hl, List.append_assoc, List.take_left]
    have := hT.of_truncate (n := l₁.length) (p' := l₁.length) (pos' := c'.workTapePos t')
      (by omega) (τ' := c'.workTapes t')
      (by
        intro q hq
        apply hout
        rw [hd.pos, hp, hlen]
        rcases hq with hq | hq
        · left; push_cast; omega
        · right; push_cast at hq ⊢; omega)
      (by
        intro q h1 h2
        apply hbl
        · rw [hd.pos, hp, hlen]; push_cast; omega
        · rw [hd.pos, hp, hlen]; push_cast at h2 ⊢; omega)
      (by rw [hpos, hd.pos, hp, hlen]; push_cast; ring)
    rwa [hpre] at this
  · intro t' ht'
    exact Function.update_of_ne (by simpa using ht') _ _

theorem D_popBack_empty {m : Sym} {t : WT} (hins : instrAt k pc = .popBack m t)
    (hpc : pc.val + 1 < maxPc) (hd : Desc c (at_ k pc) ds) (hl : (ds t).l = [])
    (hp : (ds t).p = 0) :
    ∃ c', Reach c 2 c' [] ∧ Desc c' (next_ k pc hpc) ds := by
  have hT := hd.tape t
  obtain ⟨c', hr, hs, hu, htape, hpos⟩ := exec_popBack_empty hins hpc c hd.state
    (by rw [hd.pos, hp]; exact hT.before _ (by norm_num))
  refine ⟨c', hr, hd.of_untouched hu hs ?_ ?_⟩
  · intro t' ht'
    simp only [List.mem_singleton] at ht'
    subst ht'
    have e : ds t' = ⟨[], 0⟩ := TapeSt.ext hl hp
    have := hT
    rw [e] at this ⊢
    exact this.of_same htape (by rw [hpos, hd.pos, hp])
  · intro _ _; rfl

theorem D_charge (hins : instrAt k pc = .charge false) (hpc : pc.val + 1 < maxPc)
    (hd : Desc c (at_ k pc) ds) {r : ℕ} (hb : ds BUD = ⟨List.replicate (r + 1) .one, r + 1⟩) :
    ∃ c', Reach c 2 c' [] ∧ Desc c' (next_ k pc hpc) (Function.update ds BUD ⟨List.replicate r .one, r⟩) := by
  have hT := hd.tape BUD
  rw [hb] at hT
  obtain ⟨c', hr, hs, hu, hun, hpos⟩ := exec_charge_one hins hpc c hd.state hT.unary
    (by rw [hd.pos, hb]; simp)
  refine ⟨c', hr, hd.of_untouched hu hs ?_ ?_⟩
  · intro t' ht'
    simp only [List.mem_singleton] at ht'
    subst ht'
    rw [Function.update_self]
    exact TapeIs.of_unary hun hpos
  · intro t' ht'
    exact Function.update_of_ne (by simpa using ht') _ _

theorem D_charge_fail (hins : instrAt k pc = .charge false) (hd : Desc c (at_ k pc) ds)
    (hb : ds BUD = ⟨[], 0⟩) : HaltsIn c 2 := by
  have hT := hd.tape BUD
  rw [hb] at hT
  exact exec_charge_one_fail hins c hd.state (by simpa using (TapeIs.unary (n := 0) hT))

theorem D_getEnv (hins : instrAt k pc = .getEnv) (hpc : pc.val + 1 < maxPc)
    (hd : Desc c (at_ k pc) ds) {env : Env} (hE : ds E = ⟨envRepr env, (envRepr env).length⟩)
    {i : ℕ} {l₁ l₂ : List Sym} (hC : (ds C).l = l₁ ++ S (Data.ofNat i) ++ l₂)
    (hCp : (ds C).p = l₁.length) (hX : (ds X).p ≤ (ds X).l.length) :
    ∃ n ≤ 3 * i + 3 * (envRepr env).length + 9, ∃ c', Reach c n c' [] ∧
      Desc c' (next_ k pc hpc)
        (Function.update (Function.update ds C ⟨(ds C).l, l₁.length + (2 * i + 1)⟩) X
          ⟨overwrite (ds X).l (ds X).p (S (Env.get env i)), (ds X).p + (S (Env.get env i)).length⟩) := by
  have hTE := hd.tape E
  rw [hE] at hTE
  have hTC := hd.tape C
  have hTX := hd.tape X
  obtain ⟨n, hn, c', hr, hs, hu, hCt, hCp', hEt, hEp', hde⟩ := exec_getEnv hins hpc env i c hd.state
    hTE.envTape (by rw [hd.pos, hE]) (by rw [hd.pos, hCp]; exact hTC.holds_sub hC)
  refine ⟨n, hn, c', hr, hd.of_untouched hu hs ?_ ?_⟩
  · intro t' ht'
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht'
    rcases ht' with rfl | rfl | rfl
    · rw [Function.update_of_ne (by decide), Function.update_self]
      exact hTC.of_same hCt (by rw [hCp', hd.pos, hCp]; push_cast; ring)
    · rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hE]
      exact hTE.of_same hEt (by rw [hEp'])
    · rw [Function.update_self]
      refine hTX.of_overwrite hX ?_ ?_ ?_
      · rw [← hd.pos]; exact hde.holds
      · intro q hq; exact hde.outside q (by rw [hd.pos]; exact hq)
      · rw [hde.pos, hd.pos]; push_cast; ring
  · intro t' ht'
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or] at ht'
    rw [Function.update_of_ne ht'.2.2, Function.update_of_ne ht'.1]

theorem D_copyTree {src t : WT} (hins : instrAt k pc = .copyTree src (some t) false)
    (hpc : pc.val + 1 < maxPc) (hst : src ≠ t) (hsc : src ≠ CNT) (htc : t ≠ CNT)
    (hd : Desc c (at_ k pc) ds) (hcnt : ds CNT = ⟨[], 0⟩) {v : Data} {l₁ l₂ : List Sym}
    (hsrc : (ds src).l = l₁ ++ S v ++ l₂) (hsp : (ds src).p = l₁.length)
    (htp : (ds t).p ≤ (ds t).l.length) :
    ∃ n ≤ 3 * v.size + 1, ∃ c', Reach c n c' [] ∧
      Desc c' (next_ k pc hpc)
        (Function.update (Function.update ds src ⟨(ds src).l, l₁.length + v.size⟩) t
          ⟨overwrite (ds t).l (ds t).p (S v), (ds t).p + v.size⟩) := by
  have hS := hd.tape src
  have hT := hd.tape t
  have hN := hd.tape CNT
  rw [hcnt] at hN
  obtain ⟨n, hn, c', hr, hs, hu, hst', hsp', hcnt', hcp', hde⟩ := exec_copyTree hins hpc hst hsc htc v
    c hd.state (by simpa using (TapeIs.unary (n := 0) hN)) (by rw [hd.pos, hcnt]; simp)
    (by rw [hd.pos, hsp]; exact hS.holds_sub hsrc)
  refine ⟨n, hn, c', hr, hd.of_untouched hu hs ?_ ?_⟩
  · intro t' ht'
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht'
    rcases ht' with rfl | rfl | rfl
    · rw [Function.update_of_ne hst, Function.update_self]
      exact hS.of_same hst' (by rw [hsp', hd.pos, hsp]; push_cast; ring)
    · rw [Function.update_of_ne htc.symm, Function.update_of_ne hsc.symm, hcnt]
      have := TapeIs.of_unary hcnt' hcp'
      simpa using this
    · rw [Function.update_self]
      refine hT.of_overwrite htp ?_ ?_ ?_
      · rw [← hd.pos]; exact hde.holds
      · intro q hq; exact hde.outside q (by rw [hd.pos]; exact hq)
      · rw [hde.pos, hd.pos, length_S]; push_cast; ring
  · intro t' ht'
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or] at ht'
    rw [Function.update_of_ne ht'.2.2, Function.update_of_ne ht'.1]

theorem D_skipTree {src : WT} (hins : instrAt k pc = .copyTree src none false)
    (hpc : pc.val + 1 < maxPc) (hsc : src ≠ CNT) (hd : Desc c (at_ k pc) ds)
    (hcnt : ds CNT = ⟨[], 0⟩) {v : Data} {l₁ l₂ : List Sym}
    (hsrc : (ds src).l = l₁ ++ S v ++ l₂) (hsp : (ds src).p = l₁.length) :
    ∃ n ≤ 3 * v.size + 1, ∃ c', Reach c n c' [] ∧
      Desc c' (next_ k pc hpc) (Function.update ds src ⟨(ds src).l, l₁.length + v.size⟩) := by
  have hS := hd.tape src
  have hN := hd.tape CNT
  rw [hcnt] at hN
  obtain ⟨n, hn, c', hr, hs, hu, hst', hsp', hcnt', hcp'⟩ := exec_skipTree hins hpc hsc v
    c hd.state (by simpa using (TapeIs.unary (n := 0) hN)) (by rw [hd.pos, hcnt]; simp)
    (by rw [hd.pos, hsp]; exact hS.holds_sub hsrc)
  refine ⟨n, hn, c', hr, hd.of_untouched hu hs ?_ ?_⟩
  · intro t' ht'
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht'
    rcases ht' with rfl | rfl
    · rw [Function.update_self]
      exact hS.of_same hst' (by rw [hsp', hd.pos, hsp]; push_cast; ring)
    · rw [Function.update_of_ne hsc.symm, hcnt]
      have := TapeIs.of_unary hcnt' hcp'
      simpa using this
  · intro t' ht'
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or] at ht'
    rw [Function.update_of_ne ht'.1]

theorem D_copyTree_charge {src t : WT} (hins : instrAt k pc = .copyTree src (some t) true)
    (hpc : pc.val + 1 < maxPc) (hst : src ≠ t) (hsc : src ≠ CNT) (htc : t ≠ CNT) (hsb : src ≠ BUD)
    (htb : t ≠ BUD) (hd : Desc c (at_ k pc) ds) (hcnt : ds CNT = ⟨[], 0⟩) {r : ℕ}
    (hbud : ds BUD = ⟨List.replicate r .one, r⟩) {v : Data} {l₁ l₂ : List Sym}
    (hsrc : (ds src).l = l₁ ++ S v ++ l₂) (hsp : (ds src).p = l₁.length)
    (htp : (ds t).p ≤ (ds t).l.length) (hr : v.size ≤ r) :
    ∃ n ≤ 4 * v.size + 1, ∃ c', Reach c n c' [] ∧
      Desc c' (next_ k pc hpc)
        (Function.update (Function.update (Function.update ds src ⟨(ds src).l, l₁.length + v.size⟩) t
          ⟨overwrite (ds t).l (ds t).p (S v), (ds t).p + v.size⟩) BUD
          ⟨List.replicate (r - v.size) .one, r - v.size⟩) := by
  have hS := hd.tape src
  have hT := hd.tape t
  have hN := hd.tape CNT
  rw [hcnt] at hN
  have hB := hd.tape BUD
  rw [hbud] at hB
  obtain ⟨n, hn, c', hr', hs, hu, hst', hsp', hcnt', hcp', hbud', hbp', hde⟩ :=
    exec_copyTree_charge hins hpc hst hsc htc hsb htb v c hd.state
      (by simpa using (TapeIs.unary (n := 0) hN)) (by rw [hd.pos, hcnt]; simp) hB.unary
      (by rw [hd.pos, hbud]) hr (by rw [hd.pos, hsp]; exact hS.holds_sub hsrc)
  refine ⟨n, hn, c', hr', hd.of_untouched hu hs ?_ ?_⟩
  · intro t' ht'
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht'
    rcases ht' with rfl | rfl | rfl | rfl
    · rw [Function.update_of_ne hsb, Function.update_of_ne hst, Function.update_self]
      exact hS.of_same hst' (by rw [hsp', hd.pos, hsp]; push_cast; ring)
    · have hcb : CNT ≠ BUD := by decide
      rw [Function.update_of_ne hcb, Function.update_of_ne htc.symm, Function.update_of_ne hsc.symm,
        hcnt]
      have := TapeIs.of_unary hcnt' hcp'
      simpa using this
    · rw [Function.update_of_ne htb, Function.update_self]
      refine hT.of_overwrite htp ?_ ?_ ?_
      · rw [← hd.pos]; exact hde.holds
      · intro q hq; exact hde.outside q (by rw [hd.pos]; exact hq)
      · rw [hde.pos, hd.pos, length_S]; push_cast; ring
    · rw [Function.update_self]
      exact TapeIs.of_unary hbud' hbp'
  · intro t' ht'
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or] at ht'
    rw [Function.update_of_ne ht'.2.2.2, Function.update_of_ne ht'.2.2.1, Function.update_of_ne ht'.1]

theorem D_copyTree_charge_fail {src t : WT} (hins : instrAt k pc = .copyTree src (some t) true)
    (hpc : pc.val + 1 < maxPc) (hst : src ≠ t) (hsc : src ≠ CNT) (htc : t ≠ CNT) (hsb : src ≠ BUD)
    (htb : t ≠ BUD) (hd : Desc c (at_ k pc) ds) (hcnt : ds CNT = ⟨[], 0⟩) {r : ℕ}
    (hbud : ds BUD = ⟨List.replicate r .one, r⟩) {v : Data} {l₁ l₂ : List Sym}
    (hsrc : (ds src).l = l₁ ++ S v ++ l₂) (hsp : (ds src).p = l₁.length) (hr : r < v.size) :
    HaltsIn c (4 * v.size + 1) := by
  have hS := hd.tape src
  have hN := hd.tape CNT
  rw [hcnt] at hN
  have hB := hd.tape BUD
  rw [hbud] at hB
  exact exec_copyTree_charge_fail hins hpc hst hsc htc hsb htb v c hd.state
    (by simpa using (TapeIs.unary (n := 0) hN)) (by rw [hd.pos, hcnt]; simp) hB.unary
    (by rw [hd.pos, hbud]) hr (by rw [hd.pos, hsp]; exact hS.holds_sub hsrc)

end Routines

end MIPRE.TM.Interp

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.TM.Interp.Instr
import Mathlib.Tactic

/-!
# Tape contents

`Holds τ p l`: the tape `τ` holds the list `l` from cell `p`. The lemmas relate it to
appending, to writing a cell (`Function.update`) and to reading the cell under a head.
-/

namespace MIPRE.TM.Interp

/-- A work tape. -/
abbrev Tape := ℤ → Option Sym

/-- The tape holds `l` from cell `p`. -/
def Holds (τ : Tape) (p : ℤ) (l : List Sym) : Prop :=
  ∀ k : ℕ, (hk : k < l.length) → τ (p + k) = some l[k]

namespace Holds

variable {τ : Tape} {p : ℤ}

@[simp] theorem nil : Holds τ p [] := fun k hk => by simp at hk

theorem cons_iff {s : Sym} {l : List Sym} :
    Holds τ p (s :: l) ↔ τ p = some s ∧ Holds τ (p + 1) l := by
  constructor
  · intro h
    refine ⟨?_, fun k hk => ?_⟩
    · have h0 := h 0 (by simp)
      rw [Nat.cast_zero, add_zero] at h0
      exact h0
    · have := h (k + 1) (by simp; omega)
      rw [List.getElem_cons_succ] at this
      convert this using 2
      push_cast; ring
  · rintro ⟨h0, h⟩ k hk
    cases k with
    | zero => rw [Nat.cast_zero, add_zero]; exact h0
    | succ k =>
      have := h k (by simpa using hk)
      rw [List.getElem_cons_succ]
      convert this using 2
      push_cast; ring

theorem cons {s : Sym} {l : List Sym} (h0 : τ p = some s) (h : Holds τ (p + 1) l) :
    Holds τ p (s :: l) := cons_iff.mpr ⟨h0, h⟩

theorem head {s : Sym} {l : List Sym} (h : Holds τ p (s :: l)) : τ p = some s := (cons_iff.mp h).1

theorem tail {s : Sym} {l : List Sym} (h : Holds τ p (s :: l)) : Holds τ (p + 1) l :=
  (cons_iff.mp h).2

theorem append_iff {l₁ l₂ : List Sym} :
    Holds τ p (l₁ ++ l₂) ↔ Holds τ p l₁ ∧ Holds τ (p + l₁.length) l₂ := by
  induction l₁ generalizing p with
  | nil => simp
  | cons s l ih =>
    have e : p + ((l.length + 1 : ℕ) : ℤ) = p + 1 + (l.length : ℤ) := by push_cast; ring
    simp only [List.cons_append, cons_iff, ih, List.length_cons, e]
    tauto

theorem append {l₁ l₂ : List Sym} (h₁ : Holds τ p l₁) (h₂ : Holds τ (p + l₁.length) l₂) :
    Holds τ p (l₁ ++ l₂) := append_iff.mpr ⟨h₁, h₂⟩

theorem of_append_left {l₁ l₂ : List Sym} (h : Holds τ p (l₁ ++ l₂)) : Holds τ p l₁ :=
  (append_iff.mp h).1

theorem of_append_right {l₁ l₂ : List Sym} (h : Holds τ p (l₁ ++ l₂)) :
    Holds τ (p + l₁.length) l₂ := (append_iff.mp h).2

/-- Writing outside the held region keeps it. -/
theorem update_of_not_mem {l : List Sym} (h : Holds τ p l) {q : ℤ} (s : Option Sym)
    (hq : q < p ∨ p + l.length ≤ q) : Holds (Function.update τ q s) p l := by
  intro k hk
  rw [Function.update_of_ne (by omega)]
  exact h k hk

/-- Two tapes agreeing on the held region hold the same. -/
theorem congr {τ' : Tape} {l : List Sym} (h : Holds τ p l)
    (hagree : ∀ q, p ≤ q → q < p + l.length → τ' q = τ q) : Holds τ' p l := by
  intro k hk
  rw [hagree _ (by omega) (by omega)]
  exact h k hk

theorem singleton_iff {s : Sym} : Holds τ p [s] ↔ τ p = some s := by
  simp [cons_iff]

end Holds

/-- Writing a symbol at the head, then holding it: `Holds (update τ p (some s)) p [s]`. -/
theorem holds_update_self (τ : Tape) (p : ℤ) (s : Sym) :
    Holds (Function.update τ p (some s)) p [s] := by
  rw [Holds.singleton_iff, Function.update_self]

/-- The cells of `[p, p + n)` are blank. -/
def BlankFrom (τ : Tape) (p : ℤ) (n : ℕ) : Prop := ∀ q, p ≤ q → q < p + n → τ q = none

/-- The tape is blank from `p` on. -/
def BlankBeyond (τ : Tape) (p : ℤ) : Prop := ∀ q, p ≤ q → τ q = none

/-- The tape is blank before `p`. -/
def BlankBefore (τ : Tape) (p : ℤ) : Prop := ∀ q, q < p → τ q = none

theorem BlankBeyond.update_of_lt {τ : Tape} {p : ℤ} (h : BlankBeyond τ p) {q : ℤ} (hq : q < p)
    (s : Option Sym) : BlankBeyond (Function.update τ q s) p := by
  intro r hr
  rw [Function.update_of_ne (by omega)]
  exact h r hr

theorem BlankBefore.update_of_le {τ : Tape} {p : ℤ} (h : BlankBefore τ p) {q : ℤ} (hq : p ≤ q)
    (s : Option Sym) : BlankBefore (Function.update τ q s) p := by
  intro r hr
  rw [Function.update_of_ne (by omega)]
  exact h r hr

theorem BlankBeyond.mono {τ : Tape} {p p' : ℤ} (h : BlankBeyond τ p) (hp : p ≤ p') :
    BlankBeyond τ p' := fun q hq => h q (by omega)

theorem BlankBefore.mono {τ : Tape} {p p' : ℤ} (h : BlankBefore τ p) (hp : p' ≤ p) :
    BlankBefore τ p' := fun q hq => h q (by omega)

/-- The bits of a bit string as symbols. -/
def bits : List Bool → List Sym := List.map fun b => if b then Sym.one else Sym.zero

@[simp] theorem bits_nil : bits [] = [] := rfl
@[simp] theorem bits_cons (b : Bool) (l : List Bool) :
    bits (b :: l) = (if b then Sym.one else Sym.zero) :: bits l := rfl
@[simp] theorem bits_append (l₁ l₂ : List Bool) : bits (l₁ ++ l₂) = bits l₁ ++ bits l₂ :=
  List.map_append ..
@[simp] theorem length_bits (l : List Bool) : (bits l).length = l.length := List.length_map ..

end MIPRE.TM.Interp

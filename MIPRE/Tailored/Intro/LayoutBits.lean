/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Intro.Layout

@[expose] public section

/-!
# The bits of the padded answer layout

The ZPC strategy of the tailored introspection verifier has one observable per bit of the padded
re-encoding `MIPRE.Tailored.Intro.enc` of an answer. This file says what each bit is, as a
function of the parts of the answer (`getD_enc_pair`, `getD_enc_read`, `getD_enc_hide`): a bit
of the register `y`, of the dual register `y'` or of the `X` tail; a bit of the input's answer
`α` in its readable block (`α_j` when `j` is below the input's readable length, `0` above); or a
bit of its linear block (`α_{s + j}`, `s` the input's readable length). Padding is invisible to
`List.getD _ _ false`, so no hypothesis on `α` is needed.
-/

namespace MIPRE.Tailored.Intro

open Cost MIPRE.Introspection MIPRE.Introspection.AnswerParser

theorem getD_pad (R : ℕ) (l : BitStr) (j : ℕ) : (pad R l).getD j false = l.getD j false := by
  unfold pad
  by_cases h : j < l.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_of_not_lt h)]
    rw [List.getElem?_eq_none (Nat.le_of_not_lt h)]
    simp [List.getElem?_replicate]
    split_ifs <;> rfl

theorem getD_take (l : BitStr) (s j : ℕ) :
    (l.take s).getD j false = if j < s then l.getD j false else false := by
  split_ifs with h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_take, h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_take, h]

theorem getD_drop (l : BitStr) (s j : ℕ) : (l.drop s).getD j false = l.getD (s + j) false := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_append_of_length {l : BitStr} (l' : BitStr) {k : ℕ} (h : l.length = k) (j : ℕ) :
    (l ++ l').getD j false = if j < k then l.getD j false else l'.getD (j - k) false := by
  subst h
  split_ifs with hj
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_of_not_lt hj)]

variable {P : Type*} {ℓ : ℕ} {Q R : ℕ} {splitR : AuxType ℓ × Bool → BitStr → ℕ}

theorem length_pad_take {α : BitStr} {s : ℕ} (hs : s ≤ R) : (pad R (α.take s)).length = R :=
  length_pad (by simp; omega)

/-- **The bits of an Introspect or Sample answer.** -/
theorem getD_enc_pair {t : AuxType ℓ × Bool} (ht : t.1 = .introspect ∨ t.1 = .sample)
    {y α : BitStr} (hy : y.length = Q) (hs : splitR t y ≤ R) (i : ℕ) :
    (enc Q R splitR (P := P) (.inr t) (pairBits y α)).getD i false =
      if i < Q then y.getD i false
      else if i - Q < R then (if i - Q < splitR t y then α.getD (i - Q) false else false)
      else α.getD (splitR t y + (i - Q - R)) false := by
  rw [enc_pair ht hy, List.append_assoc, getD_append_of_length _ hy]
  split_ifs with h1 h2 h3 h3
  · rfl
  · rw [getD_append_of_length _ (length_pad_take hs), if_pos h2, getD_pad, getD_take, if_pos h3]
  · rw [getD_append_of_length _ (length_pad_take hs), if_pos h2, getD_pad, getD_take, if_neg h3]
  · rw [getD_append_of_length _ (length_pad_take hs), if_neg h2, getD_pad, getD_drop]

/-- **The bits of a Read answer.** -/
theorem getD_enc_read {w : Bool} {y yp α : BitStr} (hy : y.length = Q) (hyp : yp.length = Q)
    (hs : splitR (.read, w) y ≤ R) (i : ℕ) :
    (enc Q R splitR (P := P) (.inr (.read, w)) (tripleBits y yp α)).getD i false =
      if i < Q then y.getD i false
      else if i - Q < R then
        (if i - Q < splitR (.read, w) y then α.getD (i - Q) false else false)
      else if i - Q - R < Q then yp.getD (i - Q - R) false
      else α.getD (splitR (.read, w) y + (i - Q - R - Q)) false := by
  simp only [enc, tripleParts_tripleBits Q y yp α hy hyp]
  rw [List.append_assoc, getD_append_of_length _ hy]
  split_ifs with h1 h2 h3 h4 h4
  · rfl
  · rw [getD_append_of_length _ (length_pad_take hs), if_pos h2, getD_pad, getD_take, if_pos h3]
  · rw [getD_append_of_length _ (length_pad_take hs), if_pos h2, getD_pad, getD_take, if_neg h3]
  · rw [getD_append_of_length _ (length_pad_take hs), if_neg h2, getD_append_of_length _ hyp,
      if_pos h4]
  · rw [getD_append_of_length _ (length_pad_take hs), if_neg h2, getD_append_of_length _ hyp,
      if_neg h4, getD_pad, getD_drop]

/-- **The bits of a Hide answer.** -/
theorem getD_enc_hide {k : Fin ℓ} {w : Bool} {y yp x : BitStr} (hy : y.length = Q)
    (hyp : yp.length = Q) (i : ℕ) :
    (enc Q R splitR (P := P) (.inr (.hide k, w)) (tripleBits y yp x)).getD i false =
      if i < Q then y.getD i false
      else if i - Q < Q then yp.getD (i - Q) false
      else x.getD (i - Q - Q) false := by
  simp only [enc, tripleParts_tripleBits Q y yp x hy hyp]
  rw [getD_append_of_length _ hy]
  split_ifs with h1 h2
  · rfl
  · rw [getD_append_of_length _ hyp, if_pos h2]
  · rw [getD_append_of_length _ hyp, if_neg h2]

end MIPRE.Tailored.Intro

end

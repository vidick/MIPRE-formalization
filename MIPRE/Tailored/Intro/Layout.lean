/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.Introspection.AuxiliaryAnswerCoding

@[expose] public section

/-!
# The padded answer layout of the tailored introspection verifier

The introspection verifier's answers are byte strings of variable length: an auxiliary answer is
a tuple of self-delimiting fields (`AnswerParser.pairBits`, `tripleBits`), the last of which may be
the input's answer, of any length up to the original cutoff `R`. A tailored game has, at each
question, a fixed number of readable and of linear answer bits. This file fixes the re-encoding,
by the question's label (`QuestionType P ℓ`):

* a Pauli label `p` keeps its bytes, `plen p` of them, all readable when `pread p` (the `Z`-basis
  answers) and all linear otherwise;
* Introspect and Sample, `(y, α)`: readable `y` and the input's readable answer bits padded to
  `R`, linear the input's linear answer bits padded to `R`;
* Read, `(y, y', α)`: readable `y` and the padded readable bits of `α`, linear `y'` and the padded
  linear bits of `α`;
* Hide, `(y, y', x)`: readable `y`, linear `y'` and `x`.

The input's answer at the question read off `y` has `splitR t y` readable and `splitL t y` linear
bits, the two functions being parameters here; the instance runs the input's answer-length
calculator. `enc` re-encodes, `dec` decodes, and `dec_enc` is the round trip on well-formed
answers whose input answer has the input's lengths; `length_enc` says that `enc` has the
label's lengths.
-/

namespace MIPRE.Tailored.Intro

open Cost MIPRE.Introspection MIPRE.Introspection.AnswerParser

/-- Pad with zeros to length `R`. -/
def pad (R : ℕ) (l : BitStr) : BitStr := l ++ List.replicate (R - l.length) false

@[simp] theorem length_pad {R : ℕ} {l : BitStr} (h : l.length ≤ R) : (pad R l).length = R := by
  simp [pad]; omega

theorem take_pad {R : ℕ} (l : BitStr) : (pad R l).take l.length = l := by
  simp [pad]

variable {P : Type*} {ℓ : ℕ} (Q R : ℕ) (plen : P → ℕ) (pread : P → Bool)
  (splitR splitL : AuxType ℓ × Bool → BitStr → ℕ)

/-- The number of readable answer bits of a label. -/
def lenR : QuestionType P ℓ → ℕ
  | .inl p => if pread p then plen p else 0
  | .inr (.introspect, _) => Q + R
  | .inr (.sample, _) => Q + R
  | .inr (.read, _) => Q + R
  | .inr (.hide _, _) => Q

/-- The number of linear answer bits of a label. -/
def lenL : QuestionType P ℓ → ℕ
  | .inl p => if pread p then 0 else plen p
  | .inr (.introspect, _) => R
  | .inr (.sample, _) => R
  | .inr (.read, _) => Q + R
  | .inr (.hide _, _) => 2 * Q

/-- The re-encoding of a byte answer, readable bits first. -/
def enc : QuestionType P ℓ → BitStr → BitStr
  | .inl _, bs => bs
  | .inr (.introspect, w), bs =>
    (pairParts Q bs).1 ++ pad R ((pairParts Q bs).2.take (splitR (.introspect, w) (pairParts Q bs).1))
      ++ pad R ((pairParts Q bs).2.drop (splitR (.introspect, w) (pairParts Q bs).1))
  | .inr (.sample, w), bs =>
    (pairParts Q bs).1 ++ pad R ((pairParts Q bs).2.take (splitR (.sample, w) (pairParts Q bs).1))
      ++ pad R ((pairParts Q bs).2.drop (splitR (.sample, w) (pairParts Q bs).1))
  | .inr (.read, w), bs =>
    (tripleParts Q bs).1 ++
      pad R ((tripleParts Q bs).2.2.take (splitR (.read, w) (tripleParts Q bs).1)) ++
      ((tripleParts Q bs).2.1 ++
        pad R ((tripleParts Q bs).2.2.drop (splitR (.read, w) (tripleParts Q bs).1)))
  | .inr (.hide _, _), bs => (tripleParts Q bs).1 ++ ((tripleParts Q bs).2.1 ++ (tripleParts Q bs).2.2)

/-- The input's answer, from its two padded blocks. -/
def unpad (t : AuxType ℓ × Bool) (y rb lb : BitStr) : BitStr :=
  (rb.take R).take (splitR t y) ++ (lb.take R).take (splitL t y)

/-- The decoding of a re-encoded answer. -/
def dec : QuestionType P ℓ → BitStr → BitStr
  | .inl _, tb => tb
  | .inr (.introspect, w), tb =>
    pairBits (tb.take Q) (unpad R splitR splitL (.introspect, w) (tb.take Q) (tb.drop Q)
      (tb.drop (Q + R)))
  | .inr (.sample, w), tb =>
    pairBits (tb.take Q) (unpad R splitR splitL (.sample, w) (tb.take Q) (tb.drop Q)
      (tb.drop (Q + R)))
  | .inr (.read, w), tb =>
    tripleBits (tb.take Q) ((tb.drop (Q + R)).take Q)
      (unpad R splitR splitL (.read, w) (tb.take Q) (tb.drop Q) (tb.drop (2 * Q + R)))
  | .inr (.hide _, _), tb =>
    tripleBits (tb.take Q) ((tb.drop Q).take Q) ((tb.drop (2 * Q)).take Q)

/-! ## The round trip -/

/-- The input's answer fits its two blocks. -/
def Fits (t : AuxType ℓ × Bool) (y α : BitStr) : Prop :=
  α.length = splitR t y + splitL t y ∧ splitR t y ≤ R ∧ splitL t y ≤ R

theorem take_take_pad {R : ℕ} {l : BitStr} (h : l.length ≤ R) (rest : BitStr) :
    ((pad R l ++ rest).take R).take l.length = l := by
  have hp : (pad R l).length = R := length_pad h
  rw [List.take_append_of_le_length hp.ge, List.take_of_length_le hp.le, take_pad]

variable {Q R splitR splitL} in
theorem unpad_pad {t : AuxType ℓ × Bool} {y α : BitStr} (h : Fits R splitR splitL t y α)
    (rest : BitStr) :
    unpad R splitR splitL t y (pad R (α.take (splitR t y)) ++ rest)
      (pad R (α.drop (splitR t y))) = α := by
  obtain ⟨hl, hr, hl'⟩ := h
  have h1 : (α.take (splitR t y)).length = splitR t y := by simp; omega
  have h2 : (α.drop (splitR t y)).length = splitL t y := by simp; omega
  unfold unpad
  have e1 := take_take_pad (R := R) (h1 ▸ hr) rest
  have e2 := take_take_pad (R := R) (h2 ▸ hl') []
  rw [List.append_nil] at e2
  rw [h1] at e1
  rw [h2] at e2
  rw [e1, e2, List.take_append_drop]

variable {Q R splitR splitL} in
theorem enc_pair {t : AuxType ℓ × Bool} (ht : t.1 = .introspect ∨ t.1 = .sample) {y α : BitStr}
    (hy : y.length = Q) :
    enc Q R splitR (P := P) (.inr t) (pairBits y α) =
      y ++ pad R (α.take (splitR t y)) ++ pad R (α.drop (splitR t y)) := by
  obtain ⟨t, w⟩ := t
  rcases ht with rfl | rfl <;> simp [enc, pairParts_pairBits Q y α hy]

variable {Q R splitR splitL} in
theorem dec_enc_pair {t : AuxType ℓ × Bool} (ht : t.1 = .introspect ∨ t.1 = .sample)
    {y α : BitStr} (hy : y.length = Q) (h : Fits R splitR splitL t y α) :
    dec Q R splitR splitL (.inr t : QuestionType P ℓ)
      (enc Q R splitR (.inr t : QuestionType P ℓ) (pairBits y α)) = pairBits y α := by
  rw [enc_pair ht hy]
  obtain ⟨h1, h2, h3⟩ := h
  have hrl : (pad R (α.take (splitR t y))).length = R := length_pad (by simp; omega)
  have hll : (pad R (α.drop (splitR t y))).length = R := length_pad (by simp; omega)
  have hty : (y ++ pad R (α.take (splitR t y)) ++ pad R (α.drop (splitR t y))).take Q = y := by
    rw [List.append_assoc, ← hy, List.take_left]
  have hdq : (y ++ pad R (α.take (splitR t y)) ++ pad R (α.drop (splitR t y))).drop Q =
      pad R (α.take (splitR t y)) ++ pad R (α.drop (splitR t y)) := by
    rw [List.append_assoc, ← hy, List.drop_left]
  have hdqr : (y ++ pad R (α.take (splitR t y)) ++ pad R (α.drop (splitR t y))).drop (Q + R) =
      pad R (α.drop (splitR t y)) := by
    rw [← List.drop_drop, hdq]
    exact List.drop_left' hrl
  obtain ⟨t, w⟩ := t
  rcases ht with rfl | rfl <;>
    simp only [dec, hty, hdq, hdqr, unpad_pad (R := R) (splitL := splitL) ⟨h1, h2, h3⟩ _]

variable {Q R splitR splitL} in
theorem dec_enc_read {w : Bool} {y yp α : BitStr} (hy : y.length = Q) (hyp : yp.length = Q)
    (h : Fits R splitR splitL (.read, w) y α) :
    dec Q R splitR splitL (.inr (.read, w) : QuestionType P ℓ)
      (enc Q R splitR (.inr (.read, w) : QuestionType P ℓ) (tripleBits y yp α)) =
        tripleBits y yp α := by
  obtain ⟨h1, h2, h3⟩ := h
  set αR := α.take (splitR (.read, w) y)
  set αL := α.drop (splitR (.read, w) y)
  have hrl : (pad R αR).length = R := length_pad (by simp [αR]; omega)
  have he : enc Q R splitR (.inr (.read, w) : QuestionType P ℓ) (tripleBits y yp α) =
      y ++ (pad R αR ++ (yp ++ pad R αL)) := by
    simp [enc, tripleParts_tripleBits Q y yp α hy hyp, αR, αL]
  rw [he]
  have hty : (y ++ (pad R αR ++ (yp ++ pad R αL))).take Q = y := by rw [← hy, List.take_left]
  have hdq : (y ++ (pad R αR ++ (yp ++ pad R αL))).drop Q = pad R αR ++ (yp ++ pad R αL) := by
    rw [← hy, List.drop_left]
  have hdqr : (y ++ (pad R αR ++ (yp ++ pad R αL))).drop (Q + R) = yp ++ pad R αL := by
    rw [← List.drop_drop, hdq]
    exact List.drop_left' hrl
  have hyp' : ((y ++ (pad R αR ++ (yp ++ pad R αL))).drop (Q + R)).take Q = yp := by
    rw [hdqr, ← hyp, List.take_left]
  have hd2 : (y ++ (pad R αR ++ (yp ++ pad R αL))).drop (2 * Q + R) = pad R αL := by
    rw [show 2 * Q + R = (Q + R) + Q by omega, ← List.drop_drop, hdqr, List.drop_left' hyp]
  simp only [dec, hty, hyp', hdq, hd2]
  rw [unpad_pad (R := R) (splitL := splitL) ⟨h1, h2, h3⟩]

variable {Q R splitR splitL} in
theorem dec_enc_hide {k : Fin ℓ} {w : Bool} {y yp x : BitStr} (hy : y.length = Q)
    (hyp : yp.length = Q) (hx : x.length = Q) :
    dec Q R splitR splitL (.inr (.hide k, w) : QuestionType P ℓ)
      (enc Q R splitR (.inr (.hide k, w) : QuestionType P ℓ) (tripleBits y yp x)) =
        tripleBits y yp x := by
  have he : enc Q R splitR (.inr (.hide k, w) : QuestionType P ℓ) (tripleBits y yp x) =
      y ++ (yp ++ x) := by
    simp [enc, tripleParts_tripleBits Q y yp x hy hyp]
  rw [he]
  have h1 : (y ++ (yp ++ x)).take Q = y := by rw [← hy, List.take_left]
  have h2 : ((y ++ (yp ++ x)).drop Q).take Q = yp := by
    rw [List.drop_left' hy, List.take_left' hyp]
  have h3 : ((y ++ (yp ++ x)).drop (2 * Q)).take Q = x := by
    rw [show 2 * Q = Q + Q by omega, ← List.drop_drop, List.drop_left' hy, List.drop_left' hyp,
      List.take_of_length_le hx.le]
  simp only [dec, h1, h2, h3]

/-! ## The lengths -/

variable {Q R splitR splitL} in
theorem length_enc_pair {t : AuxType ℓ × Bool} (ht : t.1 = .introspect ∨ t.1 = .sample)
    {y α : BitStr} (hy : y.length = Q) (h : Fits R splitR splitL t y α) :
    (enc Q R splitR (.inr t : QuestionType P ℓ) (pairBits y α)).length =
      lenR Q R plen pread (.inr t : QuestionType P ℓ) + lenL Q R plen pread (.inr t) := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [enc_pair ht hy]
  have e : (y ++ pad R (α.take (splitR t y)) ++ pad R (α.drop (splitR t y))).length =
      Q + R + R := by
    simp only [List.length_append, hy, length_pad (show (α.take (splitR t y)).length ≤ R by
      simp; omega), length_pad (show (α.drop (splitR t y)).length ≤ R by simp; omega)]
  rw [e]
  obtain ⟨t, w⟩ := t
  rcases ht with rfl | rfl <;> rfl

variable {Q R splitR splitL} in
theorem length_enc_read {w : Bool} {y yp α : BitStr} (hy : y.length = Q) (hyp : yp.length = Q)
    (h : Fits R splitR splitL (.read, w) y α) :
    (enc Q R splitR (.inr (.read, w) : QuestionType P ℓ) (tripleBits y yp α)).length =
      lenR Q R plen pread (.inr (.read, w) : QuestionType P ℓ) +
        lenL Q R plen pread (.inr (.read, w) : QuestionType P ℓ) := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [enc, tripleParts_tripleBits Q y yp α hy hyp, List.length_append, hy, hyp,
    length_pad (show (α.take (splitR (.read, w) y)).length ≤ R by simp; omega),
    length_pad (show (α.drop (splitR (.read, w) y)).length ≤ R by simp; omega), lenR, lenL]

variable {Q R splitR} in
theorem length_enc_hide {k : Fin ℓ} {w : Bool} {y yp x : BitStr} (hy : y.length = Q)
    (hyp : yp.length = Q) (hx : x.length = Q) :
    (enc Q R splitR (.inr (.hide k, w) : QuestionType P ℓ) (tripleBits y yp x)).length =
      lenR Q R plen pread (.inr (.hide k, w) : QuestionType P ℓ) +
        lenL Q R plen pread (.inr (.hide k, w) : QuestionType P ℓ) := by
  simp only [enc, tripleParts_tripleBits Q y yp x hy hyp, List.length_append, hy, hyp, hx, lenR,
    lenL]
  omega

theorem length_enc_pauli (p : P) (bs : BitStr) (h : bs.length = plen p) :
    (enc Q R splitR (.inl p : QuestionType P ℓ) bs).length =
      lenR Q R plen pread (.inl p : QuestionType P ℓ) +
        lenL Q R plen pread (.inl p : QuestionType P ℓ) := by
  simp only [enc, lenR, lenL, h]
  split_ifs <;> simp

theorem dec_enc_pauli (p : P) (bs : BitStr) :
    dec Q R splitR splitL (.inl p : QuestionType P ℓ) (enc Q R splitR (.inl p) bs) = bs := rfl

end MIPRE.Tailored.Intro

end

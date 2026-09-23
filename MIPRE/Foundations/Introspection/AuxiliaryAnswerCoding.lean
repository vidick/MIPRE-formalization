/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.DynamicParser
import MIPRE.Foundations.Introspection.TypedPredicate

/-! # Canonical auxiliary answer coding

Pauli payloads are left as bytes for the separate field-aware parser. The
other three answer shapes use full-register binary vectors and the existing
canonical tuple syntax. Valid raw tuples re-encode exactly, so same-type byte
consistency is exactly consistency of parsed answers.
-/

namespace MIPRE.Introspection.AuxiliaryAnswer
open Cost
variable {P : Type*} {Q ℓ : ℕ}

/-- Encode full register coordinates and preserve the original answer bytes. -/
def bits : ParsedAnswer (Fin Q → CL.𝔽₂) BitStr BitStr → BitStr
  | .pauli a => a
  | .pair y a => AnswerParser.pairBits (CL.toBits y) a
  | .read y yp a => AnswerParser.tripleBits (CL.toBits y) (CL.toBits yp) a
  | .hide y yp x => AnswerParser.tripleBits (CL.toBits y) (CL.toBits yp) (CL.toBits x)

/-- Total type-directed decoding; the caller checks canonical format first. -/
def decode (Q : ℕ) : QuestionType P ℓ → BitStr →
    ParsedAnswer (Fin Q → CL.𝔽₂) BitStr BitStr
  | .inl _, bs => .pauli bs
  | .inr (.introspect, _), bs | .inr (.sample, _), bs =>
      .pair (CL.ofBits Q (AnswerParser.pairParts Q bs).1) (AnswerParser.pairParts Q bs).2
  | .inr (.read, _), bs =>
      .read (CL.ofBits Q (AnswerParser.tripleParts Q bs).1)
        (CL.ofBits Q (AnswerParser.tripleParts Q bs).2.1) (AnswerParser.tripleParts Q bs).2.2
  | .inr (.hide _, _), bs =>
      .hide (CL.ofBits Q (AnswerParser.tripleParts Q bs).1)
        (CL.ofBits Q (AnswerParser.tripleParts Q bs).2.1)
        (CL.ofBits Q (AnswerParser.tripleParts Q bs).2.2)

/-- Decoding chooses exactly the constructor required by the question. -/
theorem decode_fits (t : QuestionType P ℓ) (bs : BitStr) :
    TypedPredicate.fits t (decode Q t bs) = true := by
  rcases t with p | ⟨t,w⟩
  · rfl
  · cases t <;> rfl

/-- Every correctly tagged parsed answer survives the byte round trip. -/
theorem decode_bits (t : QuestionType P ℓ)
    (a : ParsedAnswer (Fin Q → CL.𝔽₂) BitStr BitStr)
    (h : TypedPredicate.fits t a = true) : decode Q t (bits a) = a := by
  rcases t with p | ⟨t,w⟩
  · cases a <;> simp_all [TypedPredicate.fits, decode, bits]
  · cases t <;> cases a <;>
      simp_all [TypedPredicate.fits, decode, bits,
        AnswerParser.pairParts_pairBits _ _ _ (CL.length_toBits _),
        AnswerParser.tripleParts_tripleBits _ _ _ _ (CL.length_toBits _) (CL.length_toBits _),
        CL.ofBits_toBits]

/-- Canonical syntax and register lengths, with the separate original-answer cutoff. -/
def Valid (Q R : ℕ) : QuestionType P ℓ → BitStr → Prop
  | .inl _, _ => True
  | .inr (.introspect, _), bs | .inr (.sample, _), bs => AnswerParser.pairValid Q R bs
  | .inr (.read, _), bs => AnswerParser.tripleValid Q R false bs
  | .inr (.hide _, _), bs => AnswerParser.tripleValid Q Q true bs

/-- A parser-accepted auxiliary payload is the exact canonical encoding of
its decoded answer, including the full third register of a Hide answer. -/
theorem bits_decode (R : ℕ) (t : QuestionType P ℓ) (bs : BitStr)
    (h : Valid Q R t bs) : bits (decode Q t bs) = bs := by
  rcases t with p | ⟨t,w⟩
  · rfl
  · cases t with
    | introspect | sample =>
      change AnswerParser.pairValid Q R bs at h
      simp only [decode, bits, CL.toBits_ofBits h.2.1]
      exact h.1.symm
    | read =>
      change AnswerParser.tripleValid Q R false bs at h
      simp only [decode, bits, CL.toBits_ofBits h.2.1, CL.toBits_ofBits h.2.2.1]
      exact h.1.symm
    | hide k =>
      change AnswerParser.tripleValid Q Q true bs at h
      have hl : (AnswerParser.tripleParts Q bs).2.2.length = Q := h.2.2.2
      simp only [decode, bits, CL.toBits_ofBits h.2.1, CL.toBits_ofBits h.2.2.1,
        CL.toBits_ofBits hl]
      exact h.1.symm

/-- For a fixed type, byte equality and parsed equality coincide. -/
theorem bits_eq_iff (t : QuestionType P ℓ)
    (a b : ParsedAnswer (Fin Q → CL.𝔽₂) BitStr BitStr)
    (ha : TypedPredicate.fits t a = true) (hb : TypedPredicate.fits t b = true) :
    bits a = bits b ↔ a = b := by
  constructor
  · intro h
    have he := congrArg (decode Q t) h
    simpa only [decode_bits t a ha, decode_bits t b hb] using he
  · rintro rfl
    rfl

end MIPRE.Introspection.AuxiliaryAnswer

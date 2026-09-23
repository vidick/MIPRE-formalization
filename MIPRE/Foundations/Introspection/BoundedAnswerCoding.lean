/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.ParsedPauliTransport
import MIPRE.Foundations.Introspection.AuxiliaryAnswerCoding
import MIPRE.Foundations.Verifier

/-! # Finite original-answer payloads for the compiled introspection game -/

namespace MIPRE.Introspection.AuxiliaryAnswer
open Cost
variable {P PA V : Type*} {Q ℓ : ℕ}

/-- A total decoder into the finite verifier alphabet. The format check makes
the default branch irrelevant on every accepted pair or Read endpoint. -/
def bounded (R : ℕ) (bs : BitStr) : Verifier.Answers R :=
  if h : bs.length ≤ R then ⟨bs,h⟩ else ⟨[],by simp⟩

@[simp] theorem bounded_val {R : ℕ} (bs : BitStr) (h : bs.length ≤ R) :
    (bounded R bs).val = bs := by simp [bounded, h]

@[simp] theorem bounded_subtype (R : ℕ) (a : Verifier.Answers R) :
    bounded R a.val = a := Subtype.ext (bounded_val _ a.property)

/-- The internal bound applies exactly to payloads carrying an original answer. -/
def payloadBound (R : ℕ) : ParsedAnswer V BitStr PA → Prop
  | .pair _ a | .read _ _ a => a.length ≤ R
  | _ => True

theorem payloadBound_decode (R : ℕ) (t : QuestionType P ℓ) (bs : BitStr)
    (h : Valid Q R t bs) : payloadBound R (decode Q t bs) := by
  rcases t with p | ⟨t,w⟩
  · trivial
  · cases t with
    | introspect | sample => exact h.2.2
    | read => exact h.2.2.2
    | hide k => trivial

/-- Every accepted auxiliary payload already contains one full register. -/
theorem valid_aux_length (R : ℕ) (t : AuxType ℓ) (w : Bool) (bs : BitStr)
    (h : Valid Q R (.inr (t,w) : QuestionType P ℓ) bs) : Q ≤ bs.length := by
  cases t with
  | introspect | sample =>
    rw [h.1, AnswerParser.pairBits_length]
    have hw := h.2.1
    omega
  | read | hide k =>
    rw [h.1, AnswerParser.tripleBits_length]
    have hw := h.2.1
    omega

theorem mapAnswer_bounded_val (R : ℕ) (a : ParsedAnswer V BitStr PA)
    (h : payloadBound R a) :
    ParsedAnswer.mapAnswer Subtype.val (ParsedAnswer.mapAnswer (bounded R) a) = a := by
  cases a <;> simp_all only [payloadBound, ParsedAnswer.mapAnswer, bounded_val]

theorem mapAnswer_val_bounded (R : ℕ) (a : ParsedAnswer V (Verifier.Answers R) PA) :
    ParsedAnswer.mapAnswer (bounded R) (ParsedAnswer.mapAnswer Subtype.val a) = a := by
  cases a <;> simp only [ParsedAnswer.mapAnswer, bounded_subtype]

theorem payloadBound_mapAnswer_val (R : ℕ) (a : ParsedAnswer V (Verifier.Answers R) PA) :
    payloadBound R (ParsedAnswer.mapAnswer Subtype.val a) := by
  cases a with
  | pauli a | hide y yp x => trivial
  | pair y a | read y yp a => exact a.property

end MIPRE.Introspection.AuxiliaryAnswer

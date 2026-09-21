/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.DynamicParserSlice

/-! # Uniform introspection tuple parsing with binary bounds

One fixed program reads its register length and original-answer cutoff in
binary. All format and cutoff specifications are exactly those of the fixed
parser, but no parameter value is embedded as a unary program constant.
-/

noncomputable section

namespace MIPRE.Introspection.DynamicParser

open Cost Cost.PolyTimeFun CL.Detyping.Program
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)

def fieldOffset : PolyTimeFun ℕ ℕ := inc.comp (inc.comp (ap₂ natBit (const false) (PolyTimeFun.id ℕ)))

@[simp] theorem fieldOffset_apply (Q : ℕ) : fieldOffset Q = 2 * Q + 2 := by
  simp [fieldOffset, Nat.bit_val]

/-- Candidate pair fields, using the runtime binary register dimension. -/
def pairParts : PolyTimeFun (BitStr × ℕ) (BitStr × BitStr) :=
  let off := fieldOffset.comp snd
  (AnswerParser.payloadProg.comp (ap₂ takeBits fst off)).pair
    (AnswerParser.payloadProg.comp (ap₂ dropBits fst off))

@[simp] theorem pairParts_apply (bs : BitStr) (Q : ℕ) :
    pairParts (bs, Q) = AnswerParser.pairParts Q bs := by
  simp [pairParts, AnswerParser.pairParts]

def tripleParts : PolyTimeFun (BitStr × ℕ) (BitStr × BitStr × BitStr) :=
  (fst.comp pairParts).pair (pairParts.comp
    ((ap₂ dropBits fst (fieldOffset.comp snd)).pair snd))

@[simp] theorem tripleParts_apply (bs : BitStr) (Q : ℕ) :
    tripleParts (bs, Q) = AnswerParser.tripleParts Q bs := by
  simp [tripleParts, AnswerParser.tripleParts, AnswerParser.pairParts]

private theorem decide_and_if (p q : Prop) [Decidable p] [Decidable q] :
    (if p then decide q else false) = decide (p ∧ q) := by
  by_cases h : p <;> simp [h]

/-- Introspect/Sample validation, uniformly in the binary bounds `Q` and `R`. -/
def pairCheck : PolyTimeFun (BitStr × ℕ × ℕ) Bool :=
  let q : PolyTimeFun (BitStr × ℕ × ℕ) ℕ := fst.comp snd
  let r := snd.comp snd
  let parts := pairParts.comp (fst.pair q)
  ite (ap₂ treeEq (encoded.comp fst) (encoded.comp (AnswerParser.pairBitsProg.comp parts)))
    (ite (ap₂ SAT.ArrayProg.eqNat (lengthNat.comp (fst.comp parts)) q)
      (ap₂ leNat (lengthNat.comp (snd.comp parts)) r) (const false)) (const false)

theorem pairCheck_apply (bs : BitStr) (Q R : ℕ) :
    pairCheck (bs, Q, R) = decide (AnswerParser.pairValid Q R bs) := by
  simp only [pairCheck, AnswerParser.pairValid, PolyTimeFun.ite_apply, ap₂_apply,
    comp_apply, pair_apply, fst_apply, snd_apply, encoded_apply, treeEq_apply,
    AnswerParser.pairBitsProg_apply, pairParts_apply, lengthNat_apply,
    SAT.ArrayProg.eqNat_apply, leNat_apply, const_apply, encode_injective.eq_iff,
    decide_eq_true_eq]
  rw [decide_and_if, decide_and_if]
  rfl

/-- Read or Hide validation, with all numeric parameters supplied in binary. -/
def tripleCheck (exactLast : Bool) : PolyTimeFun (BitStr × ℕ × ℕ) Bool :=
  let q : PolyTimeFun (BitStr × ℕ × ℕ) ℕ := fst.comp snd
  let r := snd.comp snd
  let parts := tripleParts.comp (fst.pair q)
  let finalLength := lengthNat.comp (snd.comp (snd.comp parts))
  let lastCheck := if exactLast then ap₂ SAT.ArrayProg.eqNat finalLength r else ap₂ leNat finalLength r
  ite (ap₂ treeEq (encoded.comp fst) (encoded.comp (AnswerParser.tripleBitsProg.comp parts)))
    (ite (ap₂ SAT.ArrayProg.eqNat (lengthNat.comp (fst.comp parts)) q)
      (ite (ap₂ SAT.ArrayProg.eqNat (lengthNat.comp (fst.comp (snd.comp parts))) q)
        lastCheck (const false)) (const false)) (const false)

theorem tripleCheck_apply (bs : BitStr) (Q R : ℕ) (exactLast : Bool) :
    tripleCheck exactLast (bs, Q, R) = decide (AnswerParser.tripleValid Q R exactLast bs) := by
  cases exactLast <;>
    simp only [tripleCheck, AnswerParser.tripleValid, Bool.false_eq_true, if_false, if_true,
      PolyTimeFun.ite_apply, ap₂_apply, comp_apply, pair_apply, fst_apply, snd_apply,
      encoded_apply, treeEq_apply, AnswerParser.tripleBitsProg_apply, tripleParts_apply,
      lengthNat_apply, SAT.ArrayProg.eqNat_apply, leNat_apply, const_apply,
      encode_injective.eq_iff, decide_eq_true_eq] <;>
    rw [decide_and_if, decide_and_if, decide_and_if]

theorem pairCheck_iff (bs : BitStr) (Q R : ℕ) : pairCheck (bs, Q, R) = true ↔
    ∃ y a, y.length = Q ∧ a.length ≤ R ∧ bs = AnswerParser.pairBits y a := by
  rw [pairCheck_apply, ← AnswerParser.pairCheck_apply]
  exact AnswerParser.pairCheck_iff Q R bs

theorem tripleCheck_iff (bs : BitStr) (Q R : ℕ) (exactLast : Bool) :
    tripleCheck exactLast (bs, Q, R) = true ↔
      ∃ y yp a, y.length = Q ∧ yp.length = Q ∧
        (if exactLast then a.length = R else a.length ≤ R) ∧
        bs = AnswerParser.tripleBits y yp a := by
  rw [tripleCheck_apply, ← AnswerParser.tripleCheck_apply]
  exact AnswerParser.tripleCheck_iff Q R exactLast bs

theorem pairCheck_original_cutoff (bs : BitStr) (Q R : ℕ)
    (h : pairCheck (bs, Q, R) = true) : (pairParts (bs, Q)).2.length ≤ R := by
  rw [pairCheck_apply, decide_eq_true_eq] at h
  simpa only [pairParts_apply] using h.2.2

theorem readCheck_original_cutoff (bs : BitStr) (Q R : ℕ)
    (h : tripleCheck false (bs, Q, R) = true) : (tripleParts (bs, Q)).2.2.length ≤ R := by
  rw [tripleCheck_apply, decide_eq_true_eq] at h
  simpa only [tripleParts_apply, Bool.false_eq_true, if_false] using h.2.2.2

def pairParser : PolyTimeFun (BitStr × ℕ × ℕ) (Bool × (BitStr × BitStr)) :=
  pairCheck.pair (pairParts.comp (fst.pair (fst.comp snd)))

def tripleParser (exactLast : Bool) :
    PolyTimeFun (BitStr × ℕ × ℕ) (Bool × (BitStr × BitStr × BitStr)) :=
  (tripleCheck exactLast).pair (tripleParts.comp (fst.pair (fst.comp snd)))

end MIPRE.Introspection.DynamicParser

end

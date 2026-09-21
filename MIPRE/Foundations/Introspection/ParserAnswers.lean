/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.ParserBits

/-! # Executable introspection answer format and internal-cutoff checks

The register length `Q` and original-answer bound `R` are supplied constants.
Introspect and Sample use `pairCheck`; Read uses `tripleCheck Q R false`;
Hide uses `tripleCheck Q Q true`. Exact binary tuple re-encoding rejects all
malformed delimiters, extra fields, and trailing bits. The bound on the
original answer is checked here, independently of any outer tuple cutoff.
-/

noncomputable section

namespace MIPRE.Introspection.AnswerParser

open Cost Cost.PolyTimeFun CL.Detyping.Program
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)

def pairBits (y a : BitStr) : BitStr := field y ++ field a

def tripleBits (y yp a : BitStr) : BitStr := field y ++ (field yp ++ field a)

@[simp] theorem pairBits_length (y a : BitStr) :
    (pairBits y a).length = 2 * (y.length + a.length + 2) := by
  simp [pairBits]; omega

@[simp] theorem tripleBits_length (y yp a : BitStr) :
    (tripleBits y yp a).length = 2 * (y.length + yp.length + a.length + 3) := by
  simp [tripleBits]; omega

theorem pairBits_injective {y a z b : BitStr} (h : pairBits y a = pairBits z b) :
    y = z ∧ a = b := by
  obtain ⟨hy, ha⟩ := field_append_injective y z (field a) (field b) h
  exact ⟨hy, (field_append_injective a b [] [] (by simpa using ha)).1⟩

theorem tripleBits_injective {y yp a z zp b : BitStr}
    (h : tripleBits y yp a = tripleBits z zp b) : y = z ∧ yp = zp ∧ a = b := by
  obtain ⟨hy, hr⟩ := field_append_injective y z (pairBits yp a) (pairBits zp b) h
  exact ⟨hy, pairBits_injective hr⟩

def pairParts (Q : ℕ) (bs : BitStr) : BitStr × BitStr :=
  (payload (bs.take (2 * Q + 2)), payload (bs.drop (2 * Q + 2)))

def tripleParts (Q : ℕ) (bs : BitStr) : BitStr × BitStr × BitStr :=
  (payload (bs.take (2 * Q + 2)), pairParts Q (bs.drop (2 * Q + 2)))

@[simp] theorem pairParts_pairBits (Q : ℕ) (y a : BitStr) (hy : y.length = Q) :
    pairParts Q (pairBits y a) = (y, a) := by
  have hlen : (field y).length = 2 * Q + 2 := by simp [hy]
  simp [pairParts, pairBits, ← hlen]

@[simp] theorem tripleParts_tripleBits (Q : ℕ) (y yp a : BitStr)
    (hy : y.length = Q) (hyp : yp.length = Q) :
    tripleParts Q (tripleBits y yp a) = (y, yp, a) := by
  have hlen : (field y).length = 2 * Q + 2 := by simp [hy]
  simp only [tripleParts, tripleBits, ← hlen, List.take_left, payload_field,
    List.drop_left, Prod.mk.injEq, true_and]
  exact pairParts_pairBits Q yp a hyp

def pairPartsProg (Q : ℕ) : PolyTimeFun BitStr (BitStr × BitStr) :=
  (payloadProg.comp (ap₂ take (PolyTimeFun.id BitStr) (const (unary (2 * Q + 2))))).pair
    (payloadProg.comp (ap₂ drop (PolyTimeFun.id BitStr) (const (unary (2 * Q + 2)))))

@[simp] theorem pairPartsProg_apply (Q : ℕ) (bs : BitStr) :
    pairPartsProg Q bs = pairParts Q bs := by simp [pairPartsProg, pairParts]

def triplePartsProg (Q : ℕ) : PolyTimeFun BitStr (BitStr × BitStr × BitStr) :=
  (fst.comp (pairPartsProg Q)).pair
    ((pairPartsProg Q).comp (ap₂ drop (PolyTimeFun.id BitStr) (const (unary (2 * Q + 2)))))

@[simp] theorem triplePartsProg_apply (Q : ℕ) (bs : BitStr) :
    triplePartsProg Q bs = tripleParts Q bs := by
  simp [triplePartsProg, tripleParts, pairParts]

def pairBitsProg : PolyTimeFun (BitStr × BitStr) BitStr :=
  ap₂ append (fieldProg.comp fst) (fieldProg.comp snd)

@[simp] theorem pairBitsProg_apply (p : BitStr × BitStr) :
    pairBitsProg p = pairBits p.1 p.2 := rfl

def tripleBitsProg : PolyTimeFun (BitStr × BitStr × BitStr) BitStr :=
  ap₂ append (fieldProg.comp fst) (pairBitsProg.comp snd)

@[simp] theorem tripleBitsProg_apply (p : BitStr × BitStr × BitStr) :
    tripleBitsProg p = tripleBits p.1 p.2.1 p.2.2 := rfl

def pairValid (Q R : ℕ) (bs : BitStr) : Prop :=
  let p := pairParts Q bs
  bs = pairBits p.1 p.2 ∧ p.1.length = Q ∧ p.2.length ≤ R

def tripleValid (Q R : ℕ) (exactLast : Bool) (bs : BitStr) : Prop :=
  let p := tripleParts Q bs
  bs = tripleBits p.1 p.2.1 p.2.2 ∧ p.1.length = Q ∧ p.2.1.length = Q ∧
    (if exactLast then p.2.2.length = R else p.2.2.length ≤ R)

instance (Q R : ℕ) (bs : BitStr) : Decidable (pairValid Q R bs) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance (Q R : ℕ) (exactLast : Bool) (bs : BitStr) : Decidable (tripleValid Q R exactLast bs) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

private theorem decide_and_if (p q : Prop) [Decidable p] [Decidable q] :
    (if p then decide q else false) = decide (p ∧ q) := by
  by_cases h : p <;> simp [h]

/-- Concrete format and internal original-answer-cutoff check for Introspect/Sample. -/
def pairCheck (Q R : ℕ) : PolyTimeFun BitStr Bool :=
  let p := pairPartsProg Q
  ite (ap₂ treeEq encoded (encoded.comp (pairBitsProg.comp p)))
    (ite (ap₂ SAT.ArrayProg.eqNat (lengthNat.comp (fst.comp p)) (const Q))
      (ap₂ leNat (lengthNat.comp (snd.comp p)) (const R)) (const false)) (const false)

theorem pairCheck_apply (Q R : ℕ) (bs : BitStr) :
    pairCheck Q R bs = decide (pairValid Q R bs) := by
  simp only [pairCheck, pairValid, PolyTimeFun.ite_apply, ap₂_apply, comp_apply,
    encoded_apply, treeEq_apply, pairBitsProg_apply, pairPartsProg_apply, fst_apply,
    snd_apply, lengthNat_apply, SAT.ArrayProg.eqNat_apply, leNat_apply, const_apply,
    encode_injective.eq_iff, decide_eq_true_eq]
  rw [decide_and_if, decide_and_if]
  rfl

/-- Concrete format check for Read (`exactLast=false`) or Hide (`exactLast=true`). -/
def tripleCheck (Q R : ℕ) (exactLast : Bool) : PolyTimeFun BitStr Bool :=
  let p := triplePartsProg Q
  let finalLength := lengthNat.comp (snd.comp (snd.comp p))
  let lastCheck := if exactLast then ap₂ SAT.ArrayProg.eqNat finalLength (const R)
    else ap₂ leNat finalLength (const R)
  ite (ap₂ treeEq encoded (encoded.comp (tripleBitsProg.comp p)))
    (ite (ap₂ SAT.ArrayProg.eqNat (lengthNat.comp (fst.comp p)) (const Q))
      (ite (ap₂ SAT.ArrayProg.eqNat (lengthNat.comp (fst.comp (snd.comp p))) (const Q))
        lastCheck (const false)) (const false)) (const false)

theorem tripleCheck_apply (Q R : ℕ) (exactLast : Bool) (bs : BitStr) :
    tripleCheck Q R exactLast bs = decide (tripleValid Q R exactLast bs) := by
  cases exactLast <;>
    simp only [tripleCheck, tripleValid, Bool.false_eq_true,
      if_false, if_true, PolyTimeFun.ite_apply, ap₂_apply, comp_apply,
      encoded_apply, treeEq_apply, tripleBitsProg_apply, triplePartsProg_apply, fst_apply,
      snd_apply, lengthNat_apply, SAT.ArrayProg.eqNat_apply, leNat_apply, const_apply,
      encode_injective.eq_iff, decide_eq_true_eq] <;>
    rw [decide_and_if, decide_and_if, decide_and_if]

theorem pairCheck_iff (Q R : ℕ) (bs : BitStr) : pairCheck Q R bs = true ↔
    ∃ y a, y.length = Q ∧ a.length ≤ R ∧ bs = pairBits y a := by
  rw [pairCheck_apply, decide_eq_true_eq]
  constructor
  · rintro ⟨h, hy, ha⟩
    exact ⟨_, _, hy, ha, h⟩
  · rintro ⟨y, a, hy, ha, rfl⟩
    simp [pairValid, pairParts_pairBits Q y a hy, hy, ha]

theorem tripleCheck_iff (Q R : ℕ) (exactLast : Bool) (bs : BitStr) :
    tripleCheck Q R exactLast bs = true ↔
      ∃ y yp a, y.length = Q ∧ yp.length = Q ∧
        (if exactLast then a.length = R else a.length ≤ R) ∧ bs = tripleBits y yp a := by
  rw [tripleCheck_apply, decide_eq_true_eq]
  constructor
  · rintro ⟨h, hy, hyp, ha⟩
    exact ⟨_, _, _, hy, hyp, ha, h⟩
  · rintro ⟨y, yp, a, hy, hyp, ha, rfl⟩
    simp [tripleValid, tripleParts_tripleBits Q y yp a hy hyp, hy, hyp, ha]

/-- In particular, an encoded pair with a wrong register length or long `a` is rejected. -/
theorem pairCheck_pairBits (Q R : ℕ) (y a : BitStr) :
    pairCheck Q R (pairBits y a) = true ↔ y.length = Q ∧ a.length ≤ R := by
  rw [pairCheck_iff]
  constructor
  · rintro ⟨z, b, hz, hb, he⟩
    obtain ⟨rfl, rfl⟩ := pairBits_injective he
    exact ⟨hz, hb⟩
  · rintro ⟨hy, ha⟩
    exact ⟨y, a, hy, ha, rfl⟩

theorem tripleCheck_tripleBits (Q R : ℕ) (exactLast : Bool) (y yp a : BitStr) :
    tripleCheck Q R exactLast (tripleBits y yp a) = true ↔
      y.length = Q ∧ yp.length = Q ∧
        (if exactLast then a.length = R else a.length ≤ R) := by
  rw [tripleCheck_iff]
  constructor
  · rintro ⟨z, zp, b, hz, hzp, hb, he⟩
    obtain ⟨rfl, rfl, rfl⟩ := tripleBits_injective he
    exact ⟨hz, hzp, hb⟩
  · rintro ⟨hy, hyp, ha⟩
    exact ⟨y, yp, a, hy, hyp, ha, rfl⟩

/-- The repaired strict `8Q` outer cutoff contains every honest pair tuple. -/
theorem pairBits_lt_outer (Q R : ℕ) (hQ : 4 ≤ Q) (hR : 3 * R ≤ Q)
    (y a : BitStr) (hy : y.length = Q) (ha : a.length ≤ R) :
    (pairBits y a).length < 8 * Q := by rw [pairBits_length, hy]; omega

/-- The repaired strict `8Q` outer cutoff contains every honest Read tuple. -/
theorem readBits_lt_outer (Q R : ℕ) (hQ : 4 ≤ Q) (hR : 3 * R ≤ Q)
    (y yp a : BitStr) (hy : y.length = Q) (hyp : yp.length = Q) (ha : a.length ≤ R) :
    (tripleBits y yp a).length < 8 * Q := by rw [tripleBits_length, hy, hyp]; omega

/-- The repaired strict `8Q` outer cutoff contains every honest Hide tuple. -/
theorem hideBits_lt_outer (Q : ℕ) (hQ : 4 ≤ Q)
    (y yp x : BitStr) (hy : y.length = Q) (hyp : yp.length = Q) (hx : x.length = Q) :
    (tripleBits y yp x).length < 8 * Q := by rw [tripleBits_length, hy, hyp, hx]; omega

theorem pairCheck_original_cutoff (Q R : ℕ) (bs : BitStr)
    (h : pairCheck Q R bs = true) : (pairParts Q bs).2.length ≤ R := by
  rw [pairCheck_apply, decide_eq_true_eq] at h
  exact h.2.2

theorem readCheck_original_cutoff (Q R : ℕ) (bs : BitStr)
    (h : tripleCheck Q R false bs = true) : (tripleParts Q bs).2.2.length ≤ R := by
  rw [tripleCheck_apply, decide_eq_true_eq] at h
  exact h.2.2.2

/-- Parser output carries the validity flag and the decoded fields together. -/
def pairParser (Q R : ℕ) : PolyTimeFun BitStr (Bool × (BitStr × BitStr)) :=
  (pairCheck Q R).pair (pairPartsProg Q)

def tripleParser (Q R : ℕ) (exactLast : Bool) :
    PolyTimeFun BitStr (Bool × (BitStr × BitStr × BitStr)) :=
  (tripleCheck Q R exactLast).pair (triplePartsProg Q)

end MIPRE.Introspection.AnswerParser

end

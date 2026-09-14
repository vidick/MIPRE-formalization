/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Cost.Codable
import Mathlib.Computability.Primrec.List

/-!
# Descriptions as bit strings: the postorder serialization of data

Blueprint `rem:compression-abstract`, item 1: the strings of the compressibility criterion are
*descriptions*, pairs `(λ, decider)` of a parameter and a decider program. This file fixes how
such a pair travels as a bit string.

A pair is data (`cons (encode λ) (encode decider)`), and data is serialized in **postorder**:
`nil ↦ 0`, `cons a b ↦ a · b · 1` (`Data.toBitsPost`). Postorder, rather than the preorder
`Data.toBits`, because it is read back by a *stack machine* (`Data.stackStep`): a `0` pushes
`nil`, a `1` pops two entries and pushes their pair. A loop of the ambient model can run a stack
machine on a bit string, whereas a recursive-descent reader would need recursion; the ambient
program is in `Halting/Lists.lean`, this file has the mathematics and the primitive recursive
versions.

* `Data.toBitsPost`, `Data.stackRun`, `Data.parse`: the serialization, the stack machine and
  the total reader (the top of the final stack, `nil` for an empty stack), with the round trip
  `Data.parse_toBitsPost`.
* `Data.normBin`: a total normalization of the parameter, the identity on canonical binary
  numerals (`encode n` for `n : ℕ`) and `nil` (`encode 0`) elsewhere; `Data.natOf` reads it.
  Every string thereby names a parameter and a decider (`descLam`, `descDec`), and the
  wrapper decider of `Halting/Wrapper.lean` interprets the raw data the same way, so that no
  validity condition on strings is needed anywhere.
-/

namespace MIPRE.Cost.Data

/-! ## Postorder serialization -/

/-- Postorder serialization of data: `nil ↦ 0`, `cons a b ↦ a · b · 1`. -/
def toBitsPost : Data → BitStr
  | nil => [false]
  | cons a b => a.toBitsPost ++ b.toBitsPost ++ [true]

@[simp] theorem length_toBitsPost (d : Data) : d.toBitsPost.length = d.size := by
  induction d with
  | nil => rfl
  | cons a b iha ihb =>
    simp only [toBitsPost, List.length_append, List.length_singleton, iha, ihb, size_cons]

/-- One step of the stack machine: a `0` pushes `nil`; a `1` pops `b` then `a` and pushes
`cons a b`, and does nothing on a stack with fewer than two entries. -/
def stackStep (s : List Data) (bit : Bool) : List Data :=
  if bit then
    if 2 ≤ s.length then cons (s.tail.head?.getD nil) (s.head?.getD nil) :: s.tail.tail else s
  else nil :: s

@[simp] theorem stackStep_false (s : List Data) : stackStep s false = nil :: s := rfl

@[simp] theorem stackStep_true_cons_cons (b a : Data) (s : List Data) :
    stackStep (b :: a :: s) true = cons a b :: s := by
  simp [stackStep]

/-- Running the stack machine over a bit string from a stack. -/
def stackRun (x : BitStr) (s : List Data) : List Data := x.foldl stackStep s

@[simp] theorem stackRun_nil (s : List Data) : stackRun [] s = s := rfl

@[simp] theorem stackRun_cons (bit : Bool) (x : BitStr) (s : List Data) :
    stackRun (bit :: x) s = stackRun x (stackStep s bit) := rfl

theorem stackRun_append (x y : BitStr) (s : List Data) :
    stackRun (x ++ y) s = stackRun y (stackRun x s) :=
  List.foldl_append ..

/-- The stack machine reads a serialization by pushing the datum. -/
theorem stackRun_toBitsPost (d : Data) (rest : BitStr) (s : List Data) :
    stackRun (d.toBitsPost ++ rest) s = stackRun rest (d :: s) := by
  induction d generalizing rest s with
  | nil => rfl
  | cons a b iha ihb =>
    simp only [toBitsPost, List.append_assoc, iha, ihb, List.singleton_append, stackRun_cons,
      stackStep_true_cons_cons]

/-- The total reader: the top of the final stack, `nil` for an empty stack. -/
def parse (x : BitStr) : Data := (stackRun x []).headD nil

@[simp] theorem parse_toBitsPost (d : Data) : parse d.toBitsPost = d := by
  have := stackRun_toBitsPost d [] []
  simp only [List.append_nil, stackRun_nil] at this
  simp [parse, this]

/-! ## Primitive recursiveness -/

theorem primrec_stackStep : Primrec₂ stackStep := by
  have hlen : PrimrecPred fun p : List Data × Bool => 2 ≤ p.1.length :=
    Primrec.nat_le.comp (Primrec.const 2) (Primrec.list_length.comp Primrec.fst)
  have hhead : Primrec fun p : List Data × Bool => p.1.head?.getD nil :=
    Primrec.option_getD.comp (Primrec.list_head?.comp Primrec.fst) (Primrec.const nil)
  have htail : Primrec fun p : List Data × Bool => p.1.tail := Primrec.list_tail.comp Primrec.fst
  have hhead2 : Primrec fun p : List Data × Bool => p.1.tail.head?.getD nil :=
    Primrec.option_getD.comp (Primrec.list_head?.comp htail) (Primrec.const nil)
  have htail2 : Primrec fun p : List Data × Bool => p.1.tail.tail := Primrec.list_tail.comp htail
  have hpush : Primrec fun p : List Data × Bool =>
      cons (p.1.tail.head?.getD nil) (p.1.head?.getD nil) :: p.1.tail.tail :=
    Primrec.list_cons.comp (primrec_cons.comp hhead2 hhead) htail2
  have hnil : Primrec fun p : List Data × Bool => (nil : Data) :: p.1 :=
    Primrec.list_cons.comp (Primrec.const nil) Primrec.fst
  exact (Primrec.cond Primrec.snd (Primrec.ite hlen hpush Primrec.fst) hnil).of_eq fun p => by
    obtain ⟨s, bit⟩ := p
    cases bit <;> simp [stackStep]

theorem primrec_parse : Primrec parse := by
  have h : Primrec fun x : BitStr => stackRun x [] :=
    (Primrec.list_foldl Primrec.id (Primrec.const []) (primrec_stackStep.comp
      (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun x => rfl
  exact (Primrec.option_getD.comp (Primrec.list_head?.comp h) (Primrec.const nil)).of_eq fun x => by
    simp [parse, List.headD_eq_head?_getD]

/-! ## The parameter: canonical binary numerals -/

/-- A datum is a bit: `nil` or `cons nil nil`. -/
def isBit : Data → Bool
  | nil => true
  | cons nil nil => true
  | _ => false

@[simp] theorem isBit_ofBool (b : Bool) : isBit (ofBool b) = true := by cases b <;> rfl

theorem isBit_iff (d : Data) : isBit d = true ↔ ∃ b, d = ofBool b := by
  rcases d with _ | ⟨_ | ⟨a, b⟩, _ | ⟨c, e⟩⟩ <;> simp [isBit, ofBool]

/-- A datum is a canonical binary numeral: a list of bits, empty or ending in `true`. -/
def isCanonBin (d : Data) : Bool :=
  match (decode d : Option BitStr) with
  | some l => l = [] ∨ l.getLast? = some true
  | none => false

/-- Decoding a bit string succeeds only on its encoding. -/
theorem encode_of_decode_bitStr {d : Data} {l : BitStr}
    (h : (decode d : Option BitStr) = some l) : (encode l : Data) = d := by
  induction d generalizing l with
  | nil =>
    simp only [SizedEncoding.decode, toList?, Option.some.injEq] at h
    subst h; rfl
  | cons a b _ ihb =>
    change toList? toBool? (cons a b) = some l at h
    change ∀ {l : BitStr}, toList? toBool? b = some l → encode l = b at ihb
    simp only [toList?] at h
    rw [toBool?_eq] at h
    split_ifs at h with ha ha'
    · subst ha
      rcases hb : toList? toBool? b with _ | l'
      · rw [hb] at h; simp at h
      · rw [hb] at h
        simp at h
        subst h
        change cons (ofBool _) (encode l') = _
        rw [ihb hb]; rfl
    · subst ha'
      rcases hb : toList? toBool? b with _ | l'
      · rw [hb] at h; simp at h
      · rw [hb] at h
        simp at h
        subst h
        change cons (ofBool _) (encode l') = _
        rw [ihb hb]; rfl
    · simp at h

/-- `Nat.bits` is canonical: empty or ending in `true`. -/
theorem bits_getLast (n : ℕ) : n.bits = [] ∨ n.bits.getLast? = some true := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    right
    rcases ih with h | h
    · have hn0 : n = 0 := by
        have := Nat.foldr_bit_bits n
        rw [h] at this
        simpa using this.symm
      rw [h, hn hn0]
      rfl
    · rcases hb : n.bits with _ | ⟨c, l⟩
      · rw [hb] at h; simp at h
      · rw [hb] at h
        rw [List.getLast?_cons_cons]
        exact h

theorem isCanonBin_encode (n : ℕ) : isCanonBin (encode n) = true := by
  simp only [isCanonBin]
  show (match (decode (encode n.bits) : Option BitStr) with
    | some l => decide (l = [] ∨ l.getLast? = some true)
    | none => false) = true
  rw [SizedEncoding.decode_encode]
  simpa using bits_getLast n

/-- A canonical bit string is the binary expansion of the number it denotes. -/
theorem bits_foldr_of_canon (l : BitStr) (hl : l = [] ∨ l.getLast? = some true) :
    (l.foldr Nat.bit 0).bits = l := by
  induction l with
  | nil => simp
  | cons b l ih =>
    rcases hl with h | h
    · cases h
    · have hl' : l = [] ∨ l.getLast? = some true := by
        rcases l with _ | ⟨c, l⟩
        · exact Or.inl rfl
        · right; rw [List.getLast?_cons_cons] at h; exact h
      have h0 : l.foldr Nat.bit 0 = 0 → b = true := by
        intro hzero
        rcases hl' with hnil | hlast
        · subst hnil
          simpa using h
        · exfalso
          have := ih (Or.inr hlast)
          rw [hzero, Nat.zero_bits] at this
          rw [← this] at hlast
          simp at hlast
      rw [List.foldr_cons, Nat.bits_append_bit _ _ h0, ih hl']

/-- Total normalization of a parameter: canonical binary numerals are kept, everything else
reads as `0`. -/
def normBin (d : Data) : Data := if isCanonBin d then d else nil

/-- The parameter a datum denotes, after normalization. -/
def natOf (d : Data) : ℕ := ((decode (normBin d) : Option ℕ)).getD 0

@[simp] theorem normBin_encode (n : ℕ) : normBin (encode n) = encode n := by
  simp [normBin, isCanonBin_encode]

@[simp] theorem natOf_encode (n : ℕ) : natOf (encode n) = n := by
  simp [natOf, SizedEncoding.decode_encode]

/-- The normalized parameter is the encoding of the number it denotes. -/
theorem encode_natOf (d : Data) : (encode (natOf d) : Data) = normBin d := by
  unfold natOf normBin
  split_ifs with h
  · unfold isCanonBin at h
    rcases hdec : (decode d : Option BitStr) with _ | l
    · rw [hdec] at h; simp at h
    · rw [hdec] at h
      have hl : l = [] ∨ l.getLast? = some true := by simpa using h
      have hdn : (decode d : Option ℕ) = some (l.foldr Nat.bit 0) := by
        show ((decode d : Option BitStr).map fun l => l.foldr Nat.bit 0) = _
        rw [hdec]; rfl
      rw [hdn, Option.getD_some]
      show encode (l.foldr Nat.bit 0).bits = d
      rw [bits_foldr_of_canon l hl]
      exact encode_of_decode_bitStr hdec
  · rfl

theorem primrec_isBit : Primrec isBit := by
  refine (Primrec.ite (PrimrecRel.comp Primrec.eq Primrec.id (Primrec.const nil))
    (Primrec.const true) (Primrec.ite (PrimrecRel.comp Primrec.eq Primrec.id
      (Primrec.const (cons nil nil))) (Primrec.const true) (Primrec.const false))).of_eq
    fun d => ?_
  rcases d with _ | ⟨_ | ⟨a, b⟩, _ | ⟨c, e⟩⟩ <;> simp [isBit]

theorem primrec_isCanonBin : Primrec isCanonBin := by
  have hA : PrimrecPred fun l : BitStr => l = [] :=
    PrimrecRel.comp Primrec.eq Primrec.id (Primrec.const [])
  obtain ⟨instB, hB⟩ : PrimrecPred fun l : BitStr => l.reverse.head? = some true :=
    PrimrecRel.comp Primrec.eq (Primrec.list_head?.comp Primrec.list_reverse)
      (Primrec.const (some true))
  have h1 : Primrec fun l : BitStr => decide (l = [] ∨ l.getLast? = some true) := by
    refine (Primrec.ite hA (Primrec.const true) hB).of_eq fun l => ?_
    by_cases h : l = [] <;> by_cases h2 : l.getLast? = some true <;>
      simp [h, h2, List.head?_reverse]
  refine (Primrec.option_casesOn primrec_decode_bitStr (Primrec.const false)
    (h1.comp Primrec.snd).to₂).of_eq fun d => ?_
  simp only [isCanonBin]
  cases (decode d : Option BitStr) <;> rfl

theorem primrec_normBin : Primrec normBin := by
  have hc : PrimrecPred fun d : Data => isCanonBin d = true :=
    ⟨inferInstance, primrec_isCanonBin.of_eq fun d => by cases h : isCanonBin d <;> simp [h]⟩
  exact (Primrec.ite hc Primrec.id (Primrec.const nil)).of_eq fun d => rfl

theorem primrec_decode_nat : Primrec fun d : Data => (decode d : Option ℕ) := by
  have hbit : Primrec₂ fun (b : Bool) (n : ℕ) => Nat.bit b n := by
    refine (Primrec.cond Primrec.fst
      (Primrec.succ.comp (Primrec.nat_double.comp Primrec.snd))
      (Primrec.nat_double.comp Primrec.snd)).of_eq fun p => ?_
    obtain ⟨b, n⟩ := p
    cases b <;> simp [Nat.bit]
  have hfold : Primrec fun l : BitStr => l.foldr Nat.bit 0 :=
    (Primrec.list_foldr Primrec.id (Primrec.const 0)
      (hbit.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂).of_eq
      fun l => rfl
  exact (Primrec.option_map primrec_decode_bitStr (hfold.comp Primrec.snd).to₂).of_eq fun d => rfl

theorem primrec_natOf : Primrec natOf :=
  Primrec.option_getD.comp (primrec_decode_nat.comp primrec_normBin) (Primrec.const 0)

end MIPRE.Cost.Data

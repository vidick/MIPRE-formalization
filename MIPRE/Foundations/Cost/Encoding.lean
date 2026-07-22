/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Cost.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size

/-!
# Size-aware encodings

Interface between ordinary types and the ambient machine model: a `SizedEncoding α`
renders `a : α` as a machine value `List ℕ` over a *bounded alphabet* (bits, plus
finitely many tags/separators), so that `esize a` — the number of cells — is an
honest bit-length up to a constant factor. All polynomial-time statements
(`Cost.PolyTime`) are relative to these encodings.

This deliberately does **not** reuse Mathlib's `Encodable`/`Denumerable`/
`Primcodable`: those encode into `ℕ` via the quadratic pairing `Nat.pair`, whose
iterated use distorts lengths exponentially (a list of `k` unit-size items encodes
with `Θ(2ᵏ)` bits). Here, by contrast:

* numbers are encoded in **binary** (`esize n = Nat.size n`, up to a constant);
* pairing and list formation are **length-additive** (separator cells above the
  component alphabets), as in the paper's string conventions.

Design notes / open knobs:

* Encodings target `List ℕ` directly (rather than `List Bool` then a bit-map)
  so that separators are single cells; the `bound` field certifies the alphabet.
* Only the instances needed downstream are given here (`Bool`, `ℕ`, `List Bool`,
  products). `Turing.ToPartrec.Code` gets its instance in `Cost.Toolkit`; further
  instances (finite field elements, matrices, verifier descriptions) belong to the
  respective sections of the pipeline.
* `decode` is only required to invert `encode` (a partial-inverse spec would also
  be fine); well-formedness checking is a job for in-model programs, not for the
  meta-level interface.
-/

namespace MIPRE.Cost

open Turing.ToPartrec

/-- A size-faithful encoding of `α` as machine values: cells are bounded by
`bound` (so the number of cells measures bit-length up to a constant), and
`decode` inverts `encode`. -/
class SizedEncoding (α : Type*) where
  /-- Encoding of a value as a machine word. -/
  encode : α → List ℕ
  /-- Decoding; must invert `encode` (on well-formed words). -/
  decode : List ℕ → Option α
  decode_encode : ∀ a, decode (encode a) = some a
  /-- Alphabet bound: every cell of every encoding is `≤ bound`. -/
  bound : ℕ
  cells_le_bound : ∀ a, ∀ x ∈ encode a, x ≤ bound

export SizedEncoding (encode decode)

/-- The size of a value: its number of cells. On the instances below this is the
bit-length of the standard string encoding, up to a constant factor. -/
def esize {α : Type*} [SizedEncoding α] (a : α) : ℕ := (encode a).length

/-- The alphabet bound of an encoding, with the type explicit. -/
def encBound (α : Type*) [h : SizedEncoding α] : ℕ := h.bound

/-- Binary strings, the `{0,1}*` of the paper. -/
abbrev BitStr := List Bool

instance : SizedEncoding Bool where
  encode b := [b.toNat]
  decode l := match l with
    | [0] => some false
    | [1] => some true
    | _ => none
  decode_encode b := by cases b <;> rfl
  bound := 1
  cells_le_bound b := by cases b <;> simp

/-- Bit strings encode cell-per-bit: `esize x = x.length`. -/
instance : SizedEncoding BitStr where
  encode x := x.map Bool.toNat
  decode l := if l.all (· ≤ 1) then some (l.map (· == 1)) else none
  decode_encode x := by sorry -- routine
  bound := 1
  cells_le_bound x := by sorry -- routine

/-- Natural numbers encode in **binary** (LSB first): `esize n = Nat.size n`.
This is the encoding under which indices "`n` in binary" enter succinct
descriptions (blueprint `def:succinct`). -/
instance : SizedEncoding ℕ where
  encode n := n.bits.map Bool.toNat
  decode l := if l.all (· ≤ 1) then some ((l.map (· == 1)).foldr Nat.bit 0) else none
  decode_encode n := by sorry -- `Nat.bits` round-trip, routine
  bound := 1
  cells_le_bound n := by sorry -- routine

/-- Length-additive pairing: `encode (a, b) = encode a ++ sep :: encode b`, with a
separator cell above both alphabets. `esize (a, b) = esize a + esize b + 1`. -/
instance instSizedEncodingProd {α β : Type*} [SizedEncoding α] [SizedEncoding β] :
    SizedEncoding (α × β) where
  encode p := encode p.1 ++ (max (encBound α) (encBound β) + 1) :: encode p.2
  decode l :=
    match l.findIdx? (· == max (encBound α) (encBound β) + 1) with
    | none => none
    | some i =>
      match (decode (l.take i) : Option α), (decode (l.drop (i + 1)) : Option β) with
      | some a, some b => some (a, b)
      | _, _ => none
  decode_encode p := by sorry -- the separator does not occur in `encode p.1`; routine
  bound := max (encBound α) (encBound β) + 1
  cells_le_bound p := by sorry -- routine

@[simp] theorem esize_bitStr (x : BitStr) : esize x = x.length := by
  simp [esize, encode]

theorem esize_nat (n : ℕ) : esize n = Nat.size n := by
  sorry -- `Nat.size_eq_bits_len`

@[simp] theorem esize_prod {α β : Type*} [SizedEncoding α] [SizedEncoding β]
    (a : α) (b : β) : esize (a, b) = esize a + esize b + 1 := by
  show (encode a ++ (max (encBound α) (encBound β) + 1) :: encode b).length = _
  simp [esize]
  omega

/-- Encoded data has `vsize` proportional to `esize` (alphabet-boundedness). -/
theorem vsize_encode_le {α : Type*} [SizedEncoding α] (a : α) :
    vsize (encode a) ≤ (encBound α + 1) * esize a := by
  sorry -- routine from `cells_le_bound`

theorem esize_le_vsize_encode {α : Type*} [SizedEncoding α] (a : α) :
    esize a ≤ vsize (encode a) := by
  sorry -- routine: each cell contributes at least 1

end MIPRE.Cost

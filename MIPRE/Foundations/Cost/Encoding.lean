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

/-- Bits map to the cells `0`/`1`, which are the only cells `≤ 1`. -/
private theorem all_toNat_le (x : List Bool) : (x.map Bool.toNat).all (· ≤ 1) = true := by
  simp [List.all_eq_true, Bool.toNat_le]

/-- Reading the cells `0`/`1` back as bits inverts `Bool.toNat`. -/
private theorem map_toNat_beq_one (x : List Bool) : (x.map Bool.toNat).map (· == 1) = x := by
  induction x with
  | nil => rfl
  | cons b x ih => cases b <;> simp [ih]

/-- Bit strings encode cell-per-bit: `esize x = x.length`. -/
instance : SizedEncoding BitStr where
  encode x := x.map Bool.toNat
  decode l := if l.all (· ≤ 1) then some (l.map (· == 1)) else none
  decode_encode x := by
    show (if (x.map Bool.toNat).all (· ≤ 1) then some ((x.map Bool.toNat).map (· == 1))
      else none) = some x
    rw [if_pos (all_toNat_le x), map_toNat_beq_one]
  bound := 1
  cells_le_bound x := by
    intro y hy
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hy
    exact Bool.toNat_le b

/-- Folding `Nat.bit` over the binary digits of `n` recovers `n`. -/
theorem Nat.foldr_bit_bits (n : ℕ) : n.bits.foldr Nat.bit 0 = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [Nat.zero_bits]
  | bit b n hn ih => rw [Nat.bits_append_bit n b hn, List.foldr_cons, ih]

/-- Natural numbers encode in **binary** (LSB first): `esize n = Nat.size n`.
This is the encoding under which indices "`n` in binary" enter succinct
descriptions (blueprint `def:succinct`). -/
instance : SizedEncoding ℕ where
  encode n := n.bits.map Bool.toNat
  decode l := if l.all (· ≤ 1) then some ((l.map (· == 1)).foldr Nat.bit 0) else none
  decode_encode n := by
    show (if (n.bits.map Bool.toNat).all (· ≤ 1) then
      some (((n.bits.map Bool.toNat).map (· == 1)).foldr Nat.bit 0) else none) = some n
    rw [if_pos (all_toNat_le _), map_toNat_beq_one, Nat.foldr_bit_bits]
  bound := 1
  cells_le_bound n := by
    intro y hy
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hy
    exact Bool.toNat_le b

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
  decode_encode p := by
    obtain ⟨a, b⟩ := p
    have hsep : ∀ x ∈ encode a, (x == max (encBound α) (encBound β) + 1) = false := by
      intro x hx
      have hx' : x ≤ encBound α := SizedEncoding.cells_le_bound a x hx
      have hle : encBound α ≤ max (encBound α) (encBound β) := le_max_left _ _
      simp only [beq_eq_false_iff_ne, ne_eq]
      omega
    have hfind : (encode a ++ (max (encBound α) (encBound β) + 1) :: encode b).findIdx?
        (· == max (encBound α) (encBound β) + 1) = some (encode a).length := by
      rw [List.findIdx?_append, List.findIdx?_eq_none_iff.2 hsep, List.findIdx?_cons]
      simp
    have hsplit : encode a ++ (max (encBound α) (encBound β) + 1) :: encode b =
        (encode a ++ [max (encBound α) (encBound β) + 1]) ++ encode b := by simp
    dsimp only
    rw [hfind]
    dsimp only
    rw [List.take_left, hsplit, List.drop_left' (by simp), SizedEncoding.decode_encode,
      SizedEncoding.decode_encode]
  bound := max (encBound α) (encBound β) + 1
  cells_le_bound p := by
    obtain ⟨a, b⟩ := p
    intro x hx
    simp only [List.mem_append, List.mem_cons] at hx
    rcases hx with hx | rfl | hx
    · have hx' : x ≤ encBound α := SizedEncoding.cells_le_bound a x hx
      have hle : encBound α ≤ max (encBound α) (encBound β) := le_max_left _ _
      omega
    · exact le_rfl
    · have hx' : x ≤ encBound β := SizedEncoding.cells_le_bound b x hx
      have hle : encBound β ≤ max (encBound α) (encBound β) := le_max_right _ _
      omega

/-- The separator cell of the pairing: one above both component alphabets, so it
occurs in neither component's encoding. -/
def pairSep (α β : Type*) [SizedEncoding α] [SizedEncoding β] : ℕ :=
  max (encBound α) (encBound β) + 1

/-- The pairing convention, spelled out. -/
theorem encode_prod {α β : Type*} [SizedEncoding α] [SizedEncoding β] (a : α) (b : β) :
    encode (a, b) = encode a ++ pairSep α β :: encode b := rfl

@[simp] theorem esize_bitStr (x : BitStr) : esize x = x.length := by
  simp [esize, encode]

theorem esize_nat (n : ℕ) : esize n = Nat.size n := by
  show (n.bits.map Bool.toNat).length = _
  rw [List.length_map, Nat.size_eq_bits_len]

@[simp] theorem esize_prod {α β : Type*} [SizedEncoding α] [SizedEncoding β]
    (a : α) (b : β) : esize (a, b) = esize a + esize b + 1 := by
  show (encode a ++ (max (encBound α) (encBound β) + 1) :: encode b).length = _
  simp [esize]
  omega

/-- A word over cells `≤ B` has `vsize` at most `(B + 1)` per cell. -/
theorem vsize_le_of_forall_le {l : List ℕ} {B : ℕ} (h : ∀ x ∈ l, x ≤ B) :
    vsize l ≤ (B + 1) * l.length := by
  induction l with
  | nil => simp
  | cons n l ih =>
    have hn : n ≤ B := h n (List.mem_cons_self ..)
    have ih' := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [vsize_cons, List.length_cons, Nat.mul_succ]
    omega

/-- Encoded data has `vsize` proportional to `esize` (alphabet-boundedness). -/
theorem vsize_encode_le {α : Type*} [SizedEncoding α] (a : α) :
    vsize (encode a) ≤ (encBound α + 1) * esize a :=
  vsize_le_of_forall_le (SizedEncoding.cells_le_bound a)

theorem esize_le_vsize_encode {α : Type*} [SizedEncoding α] (a : α) :
    esize a ≤ vsize (encode a) :=
  length_le_vsize _

end MIPRE.Cost

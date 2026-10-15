/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Encoding.lean (delta bundle: declarations the new statements need that the published bundle Def_MIPRE_Foundations_Cost_Encoding does not carry);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding

/-!
# Size-aware encodings

Interface between ordinary types and the ambient model: a `SizedEncoding α` renders
`a : α` as a value `encode a : Data`, and `esize a` is its size (the length of its
preorder serialization `Data.toBits`), an honest bit-length up to a constant factor.
All polynomial-time statements (`Cost.PolyTime`) are relative to these encodings.

Conventions:

* bits are `false ↦ nil` and `true ↦ cons nil nil`;
* lists are `cons`-chains ending in `nil`, so a bit string of length `n` has size between
  `2n + 1` and `4n + 1`;
* natural numbers are encoded in **binary** (LSB first, `Nat.bits`), so
  `esize n ≤ 4 · Nat.size n + 1`;
* pairs are `cons`: `esize (a, b) = esize a + esize b + 1` — length-additive pairing, with
  no separators;
* programs are their tree encoding `Prog.toData`, a length-faithful serialization (this,
  not any numeric Gödel numbering, is how programs occur as *data*).

This deliberately does **not** reuse Mathlib's `Encodable`/`Primcodable`: those encode into
`ℕ` via the quadratic pairing `Nat.pair`, whose iterated use distorts lengths exponentially.
-/

namespace MIPRE.Cost

export SizedEncoding (encode decode)

theorem esize_pos {α : Type*} [SizedEncoding α] (a : α) : 0 < esize a := Data.size_pos _

namespace Data

theorem size_ofBool (b : Bool) : (ofBool b).size ≤ 3 := by cases b <;> simp [ofBool]

theorem size_ofList_le {α : Type*} {f : α → Data} {B : ℕ} (hf : ∀ a, (f a).size ≤ B)
    (l : List α) : (ofList f l).size ≤ (B + 1) * l.length + 1 := by
  induction l with
  | nil => simp [ofList]
  | cons a l ih =>
    have := hf a
    simp only [ofList, size_cons, List.length_cons, Nat.mul_succ]
    omega

end Data

theorem esize_bitStr_le (x : BitStr) : esize x ≤ 4 * x.length + 1 :=
  Data.size_ofList_le Data.size_ofBool x

theorem esize_nat_le (n : ℕ) : esize n ≤ 4 * Nat.size n + 1 := by
  have := esize_bitStr_le n.bits
  rw [Nat.size_eq_bits_len] at this
  exact this

theorem encode_prod {α β : Type*} [SizedEncoding α] [SizedEncoding β] (a : α) (b : β) :
    encode (a, b) = .cons (encode a) (encode b) := rfl

/-! ## Programs as data -/

namespace Prog

theorem esize_eq_size_toData (p : Prog) : esize p = p.toData.size := rfl

/-- **Every program has size at least two.** `Prog.toData` is a `Data.cons` whatever the
constructor, so no program encodes to `nil`. Small, and load-bearing: it is what forces
`2 ≤ λ` in `Verifier.IsBounded` (`Verifier.IsBounded.two_le`), and so what puts the index of
the halting reduction inside the range where `IsBounded`'s time clauses say anything. -/
theorem two_le_esize (p : Prog) : 2 ≤ esize p := by
  cases p <;>
    simp only [esize_eq_size_toData, toData, Data.size_cons, Data.size_nil, Data.size_ofNat] <;>
    omega

end Prog

end MIPRE.Cost

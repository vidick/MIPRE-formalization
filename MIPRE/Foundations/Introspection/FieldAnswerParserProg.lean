/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.BinaryBlockProg
import MIPRE.Foundations.Introspection.DynamicParserSlice
import MIPRE.Foundations.SAT.PcpFormat

/-! # Exact, bounded parsing of field-valued answer tables

The number of field elements is supplied in binary and the field width in
unary. Before allocating any list of blocks, the count is capped by the actual
answer length. The parser checks every width and exact re-encoding, including
the absence of trailing bits. Its polynomial bound therefore holds even when
a malformed short answer claims an exponentially large number of elements.

This supplies the payload parser for point, polynomial and full Pauli answers.
Question-type dispatch and the interpretation of field rows are separate.
-/

noncomputable section
namespace MIPRE.Introspection.FieldAnswerParser
open Cost Cost.PolyTimeFun Polynomial BinaryBlock DynamicParser SAT

theorem length_flatten_of_width (rows : List BitStr) (k : ℕ)
    (hw : ∀ row ∈ rows, row.length = k) : rows.flatten.length = rows.length * k := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
    have hr := hw row (by simp)
    have ht := ih (fun r h => hw r (by simp [h]))
    simp only [List.flatten_cons, List.length_append, List.length_cons, hr, ht, Nat.add_mul, one_mul]
    omega

theorem splitBlocks_exact (n k : ℕ) (bs : BitStr) (hlen : bs.length = n * k) :
    (splitBlocks n k bs).flatten = bs ∧
      ∀ row ∈ splitBlocks n k bs, row.length = k := by
  induction n generalizing bs with
  | zero =>
    have hb : bs = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
    simp [splitBlocks, hb]
  | succ n ih =>
    have hk : k ≤ bs.length := by rw [hlen, Nat.succ_mul]; omega
    have hd : (bs.drop k).length = n * k := by
      rw [List.length_drop, hlen, Nat.succ_mul]
      omega
    obtain ⟨hf, hw⟩ := ih (bs.drop k) hd
    constructor
    · simpa only [splitBlocks, List.flatten_cons, hf] using List.take_append_drop k bs
    · intro row hrow
      rcases List.mem_cons.mp hrow with rfl | hrow
      · simpa only [List.length_take] using Nat.min_eq_left hk
      · exact hw row hrow

/-- Candidate rows, with the binary count capped before the unary scan. -/
def rowsProg : PolyTimeFun (ℕ × Unary × BitStr) (List BitStr) :=
  splitBlocksProg.comp ((boundedOffset.comp ((snd.comp snd).pair fst)).pair snd)

@[simp] theorem rowsProg_apply (n : ℕ) (k : Unary) (bs : BitStr) :
    rowsProg (n, k, bs) = splitBlocks (min n bs.length) k.length bs := by
  simp [rowsProg, splitBlocksProg_apply]

/-- Validate the count, every block width, and the exact original bit string. -/
def readyProg : PolyTimeFun (ℕ × Unary × BitStr) Bool :=
  let width := unaryToBin.comp (fst.comp snd)
  let positive := ap₂ leNat (const 1) width
  let count := ap₂ ArrayProg.eqNat (unaryToBin.comp (length.comp rowsProg)) fst
  let widths := widthsProg.comp (width.pair rowsProg)
  let exactBytes := ap₂ ArrayProg.eqBits (flattenProg.comp rowsProg) (snd.comp snd)
  allBoolProg.comp (cons positive (cons count (cons widths (cons exactBytes (const [])))))

theorem readyProg_spec (n : ℕ) (k : Unary) (bs : BitStr) :
    readyProg (n, k, bs) = true ↔
      0 < k.length ∧ (rowsProg (n, k, bs)).length = n ∧
      (∀ row ∈ rowsProg (n, k, bs), row.length = k.length) ∧
      (rowsProg (n, k, bs)).flatten = bs := by
  simp [readyProg, flattenProg_apply, Nat.succ_le_iff]

theorem readyProg_iff_length (n : ℕ) (k : Unary) (bs : BitStr) :
    readyProg (n, k, bs) = true ↔ 0 < k.length ∧ bs.length = n * k.length := by
  rw [readyProg_spec]
  constructor
  · rintro ⟨hk, hn, hw, he⟩
    refine ⟨hk, ?_⟩
    rw [← he, length_flatten_of_width _ _ hw, hn]
  · rintro ⟨hk, hlen⟩
    have hn : n ≤ bs.length := by rw [hlen]; nlinarith
    have hr : rowsProg (n, k, bs) = splitBlocks n k.length bs := by
      rw [rowsProg_apply, Nat.min_eq_left hn]
    obtain ⟨he, hw⟩ := splitBlocks_exact n k.length bs hlen
    exact ⟨hk, by rw [hr, splitBlocks_length], by rwa [hr], by rwa [hr]⟩

/-- The flag must be checked before interpreting the candidate rows. -/
def parserProg : PolyTimeFun (ℕ × Unary × BitStr) (Bool × List BitStr) :=
  readyProg.pair rowsProg

theorem parserProg_flatten (rows : List BitStr) (k : ℕ) (hk : 0 < k)
    (hw : ∀ row ∈ rows, row.length = k) :
    parserProg (rows.length, unary k, rows.flatten) = (true, rows) := by
  have hn : rows.length ≤ rows.flatten.length := by
    rw [length_flatten_of_width rows k hw]
    nlinarith
  have hr : rowsProg (rows.length, unary k, rows.flatten) = rows := by
    rw [rowsProg_apply, length_unary, Nat.min_eq_left hn, splitBlocks_flatten k rows hw]
  have ready : readyProg (rows.length, unary k, rows.flatten) = true := by
    rw [readyProg_iff_length]
    exact ⟨by simpa using hk, by simpa using length_flatten_of_width rows k hw⟩
  change (readyProg _, rowsProg _) = _
  rw [ready, hr]

/-- Canonically encoded field vectors are returned exactly, without padding or loss. -/
theorem parserProg_vecBits {n k : ℕ} (E : BinField k) (hk : 0 < k)
    (v : Fin n → E.carrier) :
    parserProg (n, unary k, (E.vecBits v).flatten) = (true, E.vecBits v) := by
  simpa using parserProg_flatten (E.vecBits v) k hk (fun _ h => E.width_vecBits v h)

private theorem fold_double (u : Unary) (a : ℕ) :
    u.foldl (fun n _ => Nat.bit false n) a = a * 2 ^ u.length := by
  induction u generalizing a with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih]
    simp [Nat.bit_val, pow_succ, Nat.mul_assoc, Nat.mul_comm]

/-- Binary shifting computes an exponentially large count without unary allocation. -/
def scalePowerOfTwoProg : PolyTimeFun (ℕ × Unary) ℕ :=
  let step : PolyTimeFun (ℕ × Unit) ℕ := natBit.comp ((const false).pair fst)
  congr ((foldlAdd step (C 4) (by
    intro n u
    simpa [step] using esize_natBit_le false n)).comp (snd.pair fst))
    (fun p => p.1 * 2 ^ p.2.length) (by intro p; exact fold_double p.2 p.1)

@[simp] theorem scalePowerOfTwoProg_apply (a : ℕ) (u : Unary) :
    scalePowerOfTwoProg (a, u) = a * 2 ^ u.length := rfl

/-- Full Pauli payloads: dimension, field width, and raw answer bits. -/
def fullPauliParserProg : PolyTimeFun (Unary × Unary × BitStr) (Bool × List BitStr) :=
  parserProg.comp ((scalePowerOfTwoProg.comp ((const 1).pair fst)).pair snd)

theorem fullPauliParserProg_valid (m k : Unary) (bs : BitStr) :
    (fullPauliParserProg (m, k, bs)).1 = true ↔
      0 < k.length ∧ bs.length = 2 ^ m.length * k.length := by
  change readyProg (scalePowerOfTwoProg (1, m), k, bs) = true ↔ _
  simpa using readyProg_iff_length (scalePowerOfTwoProg (1, m)) k bs

theorem fullPauliParserProg_vecBits {m k : ℕ} (E : BinField k) (hk : 0 < k)
    (v : Fin (2 ^ m) → E.carrier) :
    fullPauliParserProg (unary m, unary k, (E.vecBits v).flatten) = (true, E.vecBits v) := by
  change parserProg (1 * 2 ^ (unary m).length, unary k, (E.vecBits v).flatten) = _
  simpa using parserProg_vecBits E hk v

/-- One ambient polynomial applies even when the declared table is enormous. -/
theorem fullPauliParserProg_runs (input : Unary × Unary × BitStr) :
    ∃ t ≤ fullPauliParserProg.timeBound.eval (esize input),
      fullPauliParserProg.code.Runs (encode input) (encode (fullPauliParserProg input)) t :=
  fullPauliParserProg.computes input

end MIPRE.Introspection.FieldAnswerParser
end

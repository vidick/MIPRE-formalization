/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.QLD.PauliAnswerCoding
import MIPRE.Foundations.SAT.QuotientField

/-! # Exact re-encoding of arbitrary valid Pauli payloads

The parser's width and count checks make every retained row canonical. For the
implemented Shoup field, decoding and re-encoding therefore recovers every
accepted raw payload, not only payloads constructed from a semantic answer.
-/

noncomputable section
namespace MIPRE.QLD.PauliAnswerProgram
open Cost SAT LowDegree LowDegree.BinaryLinear Introspection.FieldTableProgram

private theorem rows_getD {n : ℕ} (rows : List BitStr) (hn : rows.length = n) :
    List.ofFn (fun i : Fin n => rows.getD i.val []) = rows := by
  subst n
  simp [List.getD_eq_getElem?_getD]

private theorem row_getD_mem {n : ℕ} (rows : List BitStr) (hn : rows.length = n) (i : Fin n) :
    rows.getD i.val [] ∈ rows := by
  have hi : i.val < rows.length := by omega
  simp [List.getD_eq_getElem?_getD, hi]

private theorem fieldRows_roundtrip {k n : ℕ} (E : BinField k)
    (hE : ∀ bs : BitStr, bs.length = k → E.toBits (E.ofBits bs) = bs)
    (rows : List BitStr) (hn : rows.length = n) (hw : ∀ row ∈ rows, row.length = k) :
    E.vecBits (fun i : Fin n => E.ofBits (rows.getD i.val [])) = rows := by
  rw [BinField.vecBits, List.map_ofFn]
  apply Eq.trans _ (rows_getD rows hn)
  congr 1
  funext i
  exact hE _ (hw _ (row_getD_mem rows hn i))

private theorem bitRows_roundtrip {n : ℕ} (rows : List BitStr) (hn : rows.length = n)
    (hw : ∀ row ∈ rows, row.length = 1) :
    List.ofFn (fun i : Fin n => [(rows.getD i.val []).getD 0 false]) = rows := by
  apply Eq.trans _ (rows_getD rows hn)
  congr 1
  funext i
  obtain ⟨b, hb⟩ := List.length_eq_one_iff.mp (hw _ (row_getD_mem rows hn i))
  rw [hb]
  rfl

/-- Exact-width rows are recovered after semantic answer decoding. -/
theorem answerRows_decodeRows {k m d : ℕ} (E : BinField k)
    (hE : ∀ bs : BitStr, bs.length = k → E.toBits (E.ofBits bs) = bs)
    (T : Ty) (rows : List BitStr) (hn : rows.length = count T m d)
    (hw : ∀ row ∈ rows, row.length = width T k) :
    answerRows E (decodeRows E m d T rows) = rows := by
  cases T <;> simp only [count, width] at hn hw
  case point W =>
    simpa [decodeRows, answerRows, BinField.vecBits, List.ofFn_succ] using
      fieldRows_roundtrip E hE rows hn hw
  case aline W => exact fieldRows_roundtrip E hE rows hn hw
  case dline W => exact fieldRows_roundtrip E hE rows hn hw
  case pauli W =>
    simpa only [decodeRows, answerRows, Equiv.apply_symm_apply] using
      fieldRows_roundtrip E hE rows hn hw
  case pairB W =>
    simpa [decodeRows, answerRows, List.ofFn_succ] using bitRows_roundtrip rows hn hw
  case pair =>
    simpa [decodeRows, answerRows, List.ofFn_succ] using bitRows_roundtrip rows hn hw
  case con c =>
    simpa only [decodeRows, answerRows, bit_ofBool] using bitRows_roundtrip rows hn hw
  case var v =>
    simpa [decodeRows, answerRows, List.ofFn_succ] using bitRows_roundtrip rows hn hw

/-- A successful parser returns the exact count, exact row widths and the original bits. -/
theorem parser_rows_spec (T : Ty) (m k d : ℕ) (bs : BitStr)
    (h : (parser (T, unary m, unary k, unary d, bs)).1 = true) :
    let rows := (parser (T, unary m, unary k, unary d, bs)).2
    rows.length = count T m d ∧
      (∀ row ∈ rows, row.length = width T k) ∧ rows.flatten = bs := by
  have hs := (Introspection.FieldAnswerParser.readyProg_spec
    (countProg (T, unary m, unary k, unary d, bs))
    (widthProg (T, unary m, unary k, unary d, bs)) bs).mp h
  simpa only [parser, Cost.PolyTimeFun.comp_apply, Cost.PolyTimeFun.pair_apply,
    Introspection.FieldAnswerParser.parserProg, answer, Cost.PolyTimeFun.snd_apply,
    countProg_apply, widthProg_length, length_unary] using hs.2

/-- Decoding an answer always has the constructor prescribed by its actual question. -/
theorem decodeBits_format {k m d : ℕ} (E : BinField k) (q : Question E.carrier m) (bs : BitStr) :
    q.fmtOk (decodeBits E m d q.ty bs) = true :=
  decodeRows_format E q _

/-- Every accepted raw payload for the implemented field re-encodes exactly. -/
theorem answerBits_decodeBits (k : ℕ) (hk : 1 ≤ k) (m d : ℕ) (T : Ty) (bs : BitStr)
    (h : (parser (T, unary m, unary k, unary d, bs)).1 = true) :
    answerBits (shoupBinField k hk) (decodeBits (shoupBinField k hk) m d T bs) = bs := by
  obtain ⟨hn, hw, hb⟩ := parser_rows_spec T m k d bs h
  rw [answerBits, decodeBits,
    answerRows_decodeRows (shoupBinField k hk) (shoupBinField_toBits_ofBits k hk) T _ hn hw]
  exact hb

end MIPRE.QLD.PauliAnswerProgram
end

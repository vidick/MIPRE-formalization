/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.QLD.PauliAnswerPrograms
import MIPRE.Foundations.Introspection.FieldTableProg

/-! # Canonical Pauli answer payloads and their semantic decoding

Each type fixes its answer constructor. Field vectors use canonical field
blocks, polynomials use ascending coefficients, and full Pauli answers use
the same little-endian cube enumeration as the executable table evaluator.
-/

noncomputable section
namespace MIPRE.QLD.PauliAnswerProgram
open Cost SAT LowDegree LowDegree.BinaryLinear Introspection.FieldTableProgram

def answerRows {k m d : ℕ} (E : BinField k) : Answer E.carrier m d → List BitStr
  | .val a => [E.toBits a]
  | .apoly f => E.vecBits f
  | .dpoly f => E.vecBits f
  | .pauliAns h => E.vecBits (fun i => h ((cubeEnumeration m).symm i))
  | .bit b => [[bit b]]
  | .bitPair b => [[bit (b .X)], [bit (b .Z)]]
  | .bitTriple b => List.ofFn fun i => [bit (b i)]

def answerBits {k m d : ℕ} (E : BinField k) (a : Answer E.carrier m d) : BitStr :=
  (answerRows E a).flatten

def decodeRows {k : ℕ} (E : BinField k) (m d : ℕ) (T : Ty)
    (rows : List BitStr) : Answer E.carrier m d :=
  match T with
  | .point _ => .val (E.ofBits (rows.getD 0 []))
  | .aline _ => .apoly (fun i => E.ofBits (rows.getD i.val []))
  | .dline _ => .dpoly (fun i => E.ofBits (rows.getD i.val []))
  | .pauli _ => .pauliAns (fun y => E.ofBits (rows.getD (cubeEnumeration m y).val []))
  | .pairB _ | .var _ => .bit (ofBool ((rows.getD 0 []).getD 0 false))
  | .pair => .bitPair (fun W => ofBool ((rows.getD (match W with | .X => 0 | .Z => 1)
      []).getD 0 false))
  | .con _ => .bitTriple (fun i => ofBool ((rows.getD i.val []).getD 0 false))

theorem decodeRows_format {k m d : ℕ} (E : BinField k) (q : Question E.carrier m)
    (rows : List BitStr) : q.fmtOk (decodeRows E m d q.ty rows) = true := by
  cases q <;> rfl

theorem answerRows_length {k m d : ℕ} (E : BinField k) (q : Question E.carrier m)
    (a : Answer E.carrier m d) (h : q.fmtOk a = true) :
    (answerRows E a).length = count q.ty m d := by
  cases q <;> cases a <;> simp_all [Question.fmtOk, Question.ty, answerRows, count]

theorem answerRows_width {k m d : ℕ} (E : BinField k) (q : Question E.carrier m)
    (a : Answer E.carrier m d) (h : q.fmtOk a = true) :
    ∀ row ∈ answerRows E a, row.length = width q.ty k := by
  cases q <;> cases a <;> simp_all [Question.fmtOk, Question.ty, answerRows, width]
  all_goals first
    | exact E.length_toBits _
    | exact fun row hrow => E.width_vecBits _ hrow

private theorem fieldRow {k n : ℕ} (E : BinField k) (v : Fin n → E.carrier) (i : Fin n) :
    (E.vecBits v).getD i.val [] = E.toBits (v i) := by
  simp [BinField.vecBits, List.getD_eq_getElem?_getD]

theorem decodeRows_answerRows {k m d : ℕ} (E : BinField k) (q : Question E.carrier m)
    (a : Answer E.carrier m d) (h : q.fmtOk a = true) :
    decodeRows E m d q.ty (answerRows E a) = a := by
  cases q <;> cases a <;> simp_all [Question.fmtOk, Question.ty]
  all_goals simp only [decodeRows, answerRows]
  case point.val => simp [E.ofBits_toBits]
  case aline.apoly =>
    congr 1
    funext i
    rw [fieldRow, E.ofBits_toBits]
  case dline.dpoly =>
    congr 1
    funext i
    rw [fieldRow, E.ofBits_toBits]
  case pauli.pauliAns =>
    congr 1
    funext i
    rw [fieldRow, E.ofBits_toBits, Equiv.symm_apply_apply]
  case pairB.bit => simp
  case pair.bitPair =>
    congr 1
    funext W
    cases W <;> simp
  case con.bitTriple =>
    congr 1
    funext i
    fin_cases i <;> simp
  case var.bit => simp

theorem parser_answerBits {k m d : ℕ} (E : BinField k) (hk : 0 < k)
    (q : Question E.carrier m) (a : Answer E.carrier m d) (h : q.fmtOk a = true) :
    parser (q.ty, unary m, unary k, unary d, answerBits E a) =
      (true, answerRows E a) := by
  apply parser_flatten
  · cases q <;> simp_all [Question.ty, width]
  · simpa using answerRows_length E q a h
  · simpa using answerRows_width E q a h

def decodeBits {k : ℕ} (E : BinField k) (m d : ℕ) (T : Ty) (bs : BitStr) :
    Answer E.carrier m d :=
  decodeRows E m d T (parser (T, unary m, unary k, unary d, bs)).2

theorem decodeBits_answerBits {k m d : ℕ} (E : BinField k) (hk : 0 < k)
    (q : Question E.carrier m) (a : Answer E.carrier m d) (h : q.fmtOk a = true) :
    decodeBits E m d q.ty (answerBits E a) = a := by
  rw [decodeBits, parser_answerBits E hk q a h]
  exact decodeRows_answerRows E q a h

/-- Payload equality is faithful within every prescribed answer format. -/
theorem answerBits_injective_of_format {k m d : ℕ} (E : BinField k) (hk : 0 < k)
    (q : Question E.carrier m) (a b : Answer E.carrier m d)
    (ha : q.fmtOk a = true) (hb : q.fmtOk b = true) :
    answerBits E a = answerBits E b ↔ a = b := by
  constructor
  · intro h
    have he := congrArg (decodeBits E m d q.ty) h
    simpa only [decodeBits_answerBits E hk q a ha, decodeBits_answerBits E hk q b hb] using he
  · exact congrArg (answerBits E)

end MIPRE.QLD.PauliAnswerProgram
end

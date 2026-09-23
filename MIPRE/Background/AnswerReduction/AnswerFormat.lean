/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.AnswerReduction.Predicate
import MIPRE.Foundations.OracularTyped

/-!
# The answers of the answer-reduced verifier, as bit strings

Part of piece AR-3c of `planning/answer-reduction.md`: Table `tpcp` of `ld_compiler.tex`, the
answer formats of the eighteen PCP types, as bit strings.

An answer is a tuple of field elements of a length the type prescribes (`cnt`): one value, or the
`d + 1` or `md + 1` coefficients of one polynomial, for the first five copies; `m' + 6` values, or
`m' + 6` polynomials' coefficients, for the sixth. It is written as the list of the elements'
`k`-bit representations, serialized as the postorder bits of its encoding (`enc`), the format the
oracularized verifier already uses for its answer pairs (`pairEnc`). Reading an answer back
(`parse`) requires the list to decode, every block to have `k` bits and the count to be the
type's; a failed parse is rejected by the typed predicate, which is the format preamble of
`fig:decider-pcp` with its length bounds.

`parse_enc` is the round trip for an answer of the right format, and `length_enc_le` the bound
on the length of an honest answer: what completeness needs.
-/

noncomputable section

namespace MIPRE.AnswerReduction

open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT Pcp Cost

variable {P : PcpParams} {k : ℕ} (E : BinField k)

/-! ## The number of field elements of an answer -/

variable (P) in
/-- The number of field elements in an answer of the PCP type `t` (Table `tpcp`). -/
def cnt (t : PcpTy) : ℕ :=
  if (t.1 : ℕ) < 5 then
    match t.2 with
    | .point => 1
    | .aline => dPcp + 1
    | .dline => P.m * dPcp + 1
  else
    match t.2 with
    | .point => P.m' + 6
    | .aline => (P.m' + 6) * (dPcp + 1)
    | .dline => (P.m' + 6) * (P.m' * dPcp + 1)

/-- The field elements of an answer, in order: the values, or the coefficients of each
polynomial in turn. -/
def elems : Ans P E.carrier → List E.carrier
  | .inl (.values a) => [a 0]
  | .inl (.apolys f) => List.ofFn (f 0)
  | .inl (.dpolys f) => List.ofFn (f 0)
  | .inr (.values a) => List.ofFn a
  | .inr (.apolys f) => List.ofFn fun r => f (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm r).2
  | .inr (.dpolys f) => List.ofFn fun r => f (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm r).2

/-- An answer of the type `t` from a list of field elements. -/
def ofElems (t : PcpTy) (l : List E.carrier) : Ans P E.carrier :=
  if (t.1 : ℕ) < 5 then
    .inl <| match t.2 with
      | .point => .values fun _ => l.getD 0 0
      | .aline => .apolys fun _ j => l.getD j 0
      | .dline => .dpolys fun _ j => l.getD j 0
  else
    .inr <| match t.2 with
      | .point => .values fun c => l.getD c 0
      | .aline => .apolys fun c j => l.getD (finProdFinEquiv (c, j)) 0
      | .dline => .dpolys fun c j => l.getD (finProdFinEquiv (c, j)) 0

theorem getD_ofFn {n : ℕ} (g : Fin n → E.carrier) (i : Fin n) : (List.ofFn g).getD i 0 = g i := by
  simp [List.getD_eq_getElem?_getD]

theorem length_elems {t : PcpTy} {a : Ans P E.carrier} (h : ansFmt t a = true) :
    (elems E a).length = cnt P t := by
  obtain ⟨i, τ⟩ := t
  rcases a with (a | f | f) | (a | f | f) <;> cases τ <;>
    simp_all [ansFmt, tyFmt, elems, cnt] <;> first | omega | rfl

/-- **Reading the elements back** gives the answer, for an answer of the right format. -/
theorem ofElems_elems {t : PcpTy} {a : Ans P E.carrier} (h : ansFmt t a = true) :
    ofElems E t (elems E a) = a := by
  obtain ⟨i, τ⟩ := t
  rcases a with (a | f | f) | (a | f | f) <;> cases τ <;>
    simp only [ansFmt, tyFmt, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true,
      and_false] at h
  · simp only [ofElems, elems, if_pos h.1, List.getD_cons_zero]
    congr; funext c; rw [Subsingleton.elim c 0]
  · simp only [ofElems, elems, if_pos h.1]
    congr; funext c j; rw [Subsingleton.elim c 0, getD_ofFn]
  · simp only [ofElems, elems, if_pos h.1]
    congr; funext c j; rw [Subsingleton.elim c 0, getD_ofFn]
  · simp only [ofElems, elems, if_neg (by omega : ¬ (i : ℕ) < 5)]
    congr; funext c; rw [getD_ofFn]
  · simp only [ofElems, elems, if_neg (by omega : ¬ (i : ℕ) < 5)]
    congr; funext c j; rw [getD_ofFn, Equiv.symm_apply_apply]
  · simp only [ofElems, elems, if_neg (by omega : ¬ (i : ℕ) < 5)]
    congr; funext c j; rw [getD_ofFn, Equiv.symm_apply_apply]

/-! ## Bit strings -/

/-- **The honest encoding** of an answer: its elements' `k`-bit blocks, serialized. -/
def enc (a : Ans P E.carrier) : BitStr :=
  (encode ((elems E a).map E.toBits) : Data).toBitsPost

/-- **The bounded parse** of an answer of the type `t`: a serialized list of `cnt t` blocks of
`k` bits. -/
def parse (t : PcpTy) (s : BitStr) : Option (Ans P E.carrier) :=
  match (decode (Data.parse s) : Option (List BitStr)) with
  | some bs =>
    if bs.length = cnt P t ∧ ∀ b ∈ bs, b.length = k then some (ofElems E t (bs.map E.ofBits))
    else none
  | none => none

/-- **The round trip**: an answer of the right format parses back from its encoding. -/
theorem parse_enc {t : PcpTy} {a : Ans P E.carrier} (h : ansFmt t a = true) :
    parse E t (enc E a) = some a := by
  have hl := length_elems E h
  simp only [parse, enc, Data.parse_toBitsPost, SizedEncoding.decode_encode, List.length_map, hl,
    List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, E.length_toBits,
    implies_true, and_self, if_true, List.map_map]
  rw [show (E.ofBits ∘ E.toBits) = id from funext E.ofBits_toBits, List.map_id,
    ofElems_elems E h]

/-- An answer parsed at the type `t` has the right format. -/
theorem ansFmt_of_parse {t : PcpTy} {s : BitStr} {a : Ans P E.carrier}
    (h : parse E t s = some a) : ansFmt t a = true := by
  unfold parse at h
  split at h
  · split_ifs at h
    obtain ⟨i, τ⟩ := t
    cases h
    by_cases hi : (i : ℕ) < 5 <;> cases τ <;> simp [ofElems, ansFmt, tyFmt, hi] <;> omega
  · cases h

theorem length_enc_le (a : Ans P E.carrier) :
    (enc E a).length ≤ 4 * (k * (elems E a).length) + 4 * (elems E a).length + 1 := by
  rw [enc, Data.length_toBitsPost]
  have h : ∀ l : List E.carrier, esize ((l.map E.toBits : List BitStr)) ≤
      4 * (k * l.length) + 4 * l.length + 1 := by
    intro l
    induction l with
    | nil => simp
    | cons x l ih =>
      simp only [List.map_cons, esize_list_cons, List.length_cons]
      have := esize_bitStr_le (E.toBits x)
      rw [E.length_toBits] at this
      nlinarith
  exact h _

end MIPRE.AnswerReduction

end

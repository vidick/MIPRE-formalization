/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Cost.Fold
import MIPRE.Foundations.Cost.Numeric

/-!
# The closure library, part V: the binary successor, and unary to binary

The successor on binary numerals (`incProg`, `PolyTimeFun.inc`: flip the leading `1`s and the
first `0`, in two passes as `decProg`), the conversion of a unary numeral to binary
(`PolyTimeFun.unaryToBin`, a fold of the successor), data as its own encoding, the bits of a
number, and the tagging combinator (`PolyTimeFun.tagged`) for constructors of encoded
inductive types (`planning/succinct-cook-levin.md`, S3).
-/

namespace MIPRE.Cost

open Polynomial

/-! ## Data as data -/

/-- Data encode as themselves. -/
instance : SizedEncoding Data where
  encode := id
  decode := some
  decode_encode _ := rfl

@[simp] theorem encode_data (d : Data) : (encode d : Data) = d := rfl

@[simp] theorem esize_data (d : Data) : esize d = d.size := rfl

/-! ## Bit strings -/

theorem esize_bitStr_cons (b : Bool) (l : BitStr) :
    esize (b :: l) = (Data.ofBool b).size + esize l + 1 := rfl

@[simp] theorem esize_bitStr_nil : esize ([] : BitStr) = 1 := rfl

@[simp] theorem esize_true : esize true = 3 := rfl

@[simp] theorem esize_false : esize false = 1 := rfl

theorem esize_true_cons (l : BitStr) : esize (true :: l) = esize l + 4 := by
  rw [esize_bitStr_cons]; simp [Data.ofBool]; omega

theorem esize_false_cons (l : BitStr) : esize (false :: l) = esize l + 2 := by
  rw [esize_bitStr_cons]; simp [Data.ofBool]; omega

theorem esize_bitStr_append (l₁ l₂ : BitStr) : esize (l₁ ++ l₂) + 1 = esize l₁ + esize l₂ := by
  induction l₁ with
  | nil => simp only [List.nil_append, esize_bitStr_nil]; omega
  | cons b l ih => simp only [List.cons_append, esize_bitStr_cons]; omega

theorem length_le_esize_bitStr' (l : BitStr) : 2 * l.length + 1 ≤ esize l := by
  induction l with
  | nil => simp
  | cons b l ih => cases b <;> simp only [esize_true_cons, esize_false_cons, List.length_cons] <;> omega

theorem esize_replicate_true (j : ℕ) : esize (List.replicate j true) = 4 * j + 1 := by
  induction j with
  | zero => rfl
  | succ j ih => rw [List.replicate_succ, esize_true_cons, ih]; omega

theorem esize_replicate_false (j : ℕ) : esize (List.replicate j false) = 2 * j + 1 := by
  induction j with
  | zero => rfl
  | succ j ih => rw [List.replicate_succ, esize_false_cons, ih]; omega

/-- The bits of a number, as a polynomial-time function: the encoding is the same. -/
noncomputable def PolyTimeFun.natBits : PolyTimeFun ℕ BitStr :=
  PolyTimeFun.ofEncodeEq Nat.bits fun _ => rfl

@[simp] theorem PolyTimeFun.natBits_apply (n : ℕ) : PolyTimeFun.natBits n = n.bits := rfl

/-- A number as its encoding. -/
noncomputable def PolyTimeFun.natData : PolyTimeFun ℕ Data :=
  PolyTimeFun.ofEncodeEq (fun n => encode n) fun _ => rfl

/-- A program as its encoding. -/
noncomputable def PolyTimeFun.progData : PolyTimeFun Prog Data :=
  PolyTimeFun.ofEncodeEq Prog.toData fun _ => rfl

/-! ## The binary successor -/

/-- The successor of a binary numeral (least significant bit first). -/
def incBits : BitStr → BitStr
  | [] => [true]
  | false :: l => true :: l
  | true :: l => false :: incBits l

theorem incBits_bits (n : ℕ) : incBits n.bits = (n + 1).bits := by
  induction n using Nat.binaryRec' with
  | zero => rw [Nat.zero_bits, Nat.one_bits]; rfl
  | bit b m hm ih =>
    rw [Nat.bits_append_bit m b hm]
    cases b with
    | false =>
      show incBits (false :: m.bits) = (2 * m + 1).bits
      rw [Nat.bit1_bits]; rfl
    | true =>
      show incBits (true :: m.bits) = (2 * m + 1 + 1).bits
      rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring, Nat.bit0_bits _ (by omega), ← ih]
      rfl

theorem esize_incBits_le (l : BitStr) : esize (incBits l) ≤ esize l + 4 := by
  induction l with
  | nil => simp [incBits, esize_true_cons]
  | cons b l ih =>
    cases b with
    | false => simp only [incBits, esize_true_cons, esize_false_cons]; omega
    | true => simp only [incBits, esize_true_cons, esize_false_cons]; omega

theorem length_incBits_le (l : BitStr) : (incBits l).length ≤ l.length + 1 := by
  induction l with
  | nil => simp [incBits]
  | cons b l ih => cases b <;> simp only [incBits, List.length_cons] <;> omega

/-- The tail of the successor after the leading `1`s: `[]` becomes `[1]`, `0 · r` becomes `1 · r`. -/
def incTail : BitStr → BitStr
  | [] => [true]
  | _ :: r => true :: r

theorem incBits_replicate_true (j : ℕ) (rest : BitStr) (hrest : rest = [] ∨ ∃ r, rest = false :: r) :
    incBits (List.replicate j true ++ rest) = List.replicate j false ++ incTail rest := by
  induction j with
  | zero =>
    rcases hrest with rfl | ⟨r, rfl⟩ <;> rfl
  | succ j ih => simp [List.replicate_succ, incBits, ih]

theorem exists_leading_trues (l : BitStr) :
    ∃ j rest, l = List.replicate j true ++ rest ∧ (rest = [] ∨ ∃ r, rest = false :: r) := by
  induction l with
  | nil => exact ⟨0, [], rfl, Or.inl rfl⟩
  | cons b l ih =>
    cases b with
    | false => exact ⟨0, false :: l, rfl, Or.inr ⟨l, rfl⟩⟩
    | true =>
      obtain ⟨j, rest, rfl, h⟩ := ih
      exact ⟨j + 1, rest, by simp [List.replicate_succ], h⟩

namespace Prog

/-- Body of the successor loop: on `cons xs acc`, if `xs` is empty stop with `(acc, [1])`; if
its head is `0` stop with `(acc, 1 · tail)`; if its head is `1` continue with
`(tail, 0 · acc)`. Reversing the first component onto the second then gives the successor. -/
def incStop1 : Prog := .cons .nil (.cons (.var 1) (.const (.cons (.cons .nil .nil) .nil)))

/-- The stop on a head `0`: `(acc, 1 · tail)`. -/
def incStop2 : Prog := .cons .nil (.cons (.var 3) (.cons (.const (.cons .nil .nil)) (.var 1)))

/-- The continuation on a head `1`: `(tail, 0 · acc)`. -/
def incCont : Prog := .cons (.cons .nil .nil) (.cons (.var 3) (.cons .nil (.var 5)))

/-- The body of the successor loop. -/
def incBody : Prog := .elim 0 .nil (.elim 0 incStop1 (.elim 0 incStop2 incCont))

theorem incBody_wellScoped : incBody.WellScoped 1 := by
  simp [incBody, incStop1, incStop2, incCont, WellScoped]

theorem incBody_empty (acc : BitStr) :
    Eval [.cons (encode ([] : BitStr)) (encode acc)] incBody
      (.cons .nil (.cons (encode acc) (encode [true]))) (esize acc + 11) := by
  have e := Eval.elim_cons (env := [Data.cons (encode ([] : BitStr)) (encode acc)]) (i := 0)
    (n := .nil) (a := encode ([] : BitStr)) (b := encode acc) (by simp)
    (Eval.elim_nil (i := 0) (c := .elim 0 incStop2 incCont) (by simp [encode_bitStr_nil])
      (show Eval _ incStop1 _ _ from
        Eval.cons (Eval.nil _) (Eval.cons (Eval.var_of_get (i := 1) (v := encode acc) (by simp))
          (Eval.const _ (.cons (.cons .nil .nil) .nil)))))
  exact e.cast_cost (by simp only [esize, Data.size_cons, Data.size_nil]; omega)

theorem incBody_false (rest acc : BitStr) :
    Eval [.cons (encode (false :: rest)) (encode acc)] incBody
      (.cons .nil (.cons (encode acc) (encode (true :: rest)))) (esize acc + esize rest + 12) := by
  have e := Eval.elim_cons (env := [Data.cons (encode (false :: rest)) (encode acc)]) (i := 0)
    (n := .nil) (a := encode (false :: rest)) (b := encode acc) (by simp)
    (Eval.elim_cons (i := 0) (n := incStop1) (a := Data.ofBool false) (b := encode rest)
      (by simp [encode_bitStr_cons])
      (Eval.elim_nil (i := 0) (c := incCont) (by simp [Data.ofBool])
        (show Eval _ incStop2 _ _ from
          Eval.cons (Eval.nil _)
            (Eval.cons (Eval.var_of_get (i := 3) (v := encode acc) (by simp))
              (Eval.cons (Eval.const _ (.cons .nil .nil))
                (Eval.var_of_get (i := 1) (v := encode rest) (by simp)))))))
  exact e.cast_cost (by simp only [esize, Data.size_cons, Data.size_nil]; omega)

theorem incBody_true (rest acc : BitStr) :
    Eval [.cons (encode (true :: rest)) (encode acc)] incBody
      (.cons (.cons .nil .nil) (.cons (encode rest) (encode (false :: acc))))
      (esize acc + esize rest + 12) := by
  have e := Eval.elim_cons (env := [Data.cons (encode (true :: rest)) (encode acc)]) (i := 0)
    (n := .nil) (a := encode (true :: rest)) (b := encode acc) (by simp)
    (Eval.elim_cons (i := 0) (n := incStop1) (a := Data.ofBool true) (b := encode rest)
      (by simp [encode_bitStr_cons])
      (Eval.elim_cons (i := 0) (n := incStop2) (a := .nil) (b := .nil) (by simp [Data.ofBool])
        (show Eval _ incCont _ _ from
          Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
            (Eval.cons (Eval.var_of_get (i := 3) (v := encode rest) (by simp))
              (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 5) (v := encode acc) (by simp)))))))
  refine e.cast_cost ?_
  simp only [esize, Data.size_cons, Data.size_nil]; omega

/-- The successor loop on `1^j · rest` (with `rest` empty or starting with `0`) from the
accumulator `acc` stops with `(0^j · acc, incTail rest)`. -/
theorem incLoop_runs (j : ℕ) (rest : BitStr) (hrest : rest = [] ∨ ∃ r, rest = false :: r)
    (acc : BitStr) (env : Env) (S : ℕ) (hS : esize rest + esize acc + 4 * j ≤ S) :
    ∃ t ≤ (j + 1) * (S + 13),
      Eval (.cons (encode (List.replicate j true ++ rest)) (encode acc) :: env) (.loop incBody)
        (.cons (encode (List.replicate j false ++ acc)) (encode (incTail rest))) t := by
  induction j generalizing acc with
  | zero =>
    rcases hrest with rfl | ⟨r, rfl⟩
    · refine ⟨esize acc + 11 + 1, by rw [Nat.zero_add, Nat.one_mul]; omega, ?_⟩
      exact Eval.loop_stop (Eval.append_of_wellScoped (incBody_empty acc) incBody_wellScoped env)
    · refine ⟨esize acc + esize r + 12 + 1, ?_, ?_⟩
      · rw [esize_false_cons] at hS; rw [Nat.zero_add, Nat.one_mul]; omega
      · exact Eval.loop_stop (Eval.append_of_wellScoped (incBody_false r acc) incBody_wellScoped env)
  | succ j ih =>
    obtain ⟨t, ht, hrun⟩ := ih (false :: acc) (by rw [esize_false_cons]; omega)
    refine ⟨esize acc + esize (List.replicate j true ++ rest) + 12 + t + 1, ?_, ?_⟩
    · have h1 := esize_bitStr_append (List.replicate j true) rest
      have h2 := esize_replicate_true j
      have h3 : (j + 1 + 1) * (S + 13) = (j + 1) * (S + 13) + (S + 13) := Nat.succ_mul _ _
      omega
    · have hstep := Eval.append_of_wellScoped
        (incBody_true (List.replicate j true ++ rest) acc) incBody_wellScoped env
      rw [List.replicate_succ, List.cons_append]
      refine Eval.loop_step hstep ?_
      rw [List.replicate_succ', List.append_assoc, List.singleton_append]
      exact hrun

/-- The successor of a binary numeral: `incProg` on `encode l` computes `encode (incBits l)`. -/
def incProg : Prog := .let_ (.cons (.var 0) .nil) (.let_ (.loop incBody) revOntoProg)

theorem incProg_wellScoped : incProg.WellScoped 1 :=
  ⟨⟨Nat.zero_lt_one, trivial⟩, ⟨⟨Nat.zero_lt_succ 1, incBody_wellScoped.mono (by omega) _⟩,
    revOntoProg_wellScoped.mono (by omega) _⟩⟩

theorem incProg_runs (l : BitStr) :
    ∃ t ≤ (l.length + 2) * (3 * esize l + 32), incProg.Runs (encode l) (encode (incBits l)) t := by
  obtain ⟨j, rest, rfl, hrest⟩ := exists_leading_trues l
  have hL : esize (List.replicate j true ++ rest) = 4 * j + esize rest := by
    have := esize_bitStr_append (List.replicate j true) rest
    rw [esize_replicate_true] at this; omega
  have hlen : (List.replicate j true ++ rest).length = j + rest.length := by simp
  have hrl := length_le_esize_bitStr rest
  obtain ⟨t₁, ht₁, h₁⟩ := incLoop_runs j rest hrest [] [encode (List.replicate j true ++ rest)]
    (esize (List.replicate j true ++ rest) + 1) (by rw [hL]; simp only [esize_bitStr_nil]; omega)
  have htail : esize (incTail rest) ≤ esize rest + 4 := by
    rcases hrest with rfl | ⟨r, rfl⟩
    · simp [incTail, esize_true_cons]
    · simp only [incTail, esize_true_cons, esize_false_cons]; omega
  obtain ⟨t₂, ht₂, h₂⟩ := revOntoProg_runs ((List.replicate j false).map Data.ofBool)
    ((incTail rest).map Data.ofBool)
    [Data.cons (encode (List.replicate j true ++ rest)) .nil, encode (List.replicate j true ++ rest)]
    (esize (List.replicate j true ++ rest) + 6) (by
      rw [← encode_bitStr_eq_list, ← encode_bitStr_eq_list]
      change esize _ + esize _ ≤ _
      rw [esize_replicate_false, hL]
      omega)
  have h₂' : Eval (Data.cons (encode (List.replicate j false ++ [])) (encode (incTail rest)) ::
      [Data.cons (encode (List.replicate j true ++ rest)) .nil, encode (List.replicate j true ++ rest)])
      revOntoProg (encode (incBits (List.replicate j true ++ rest))) t₂ := by
    have e1 : (encode (List.replicate j false ++ []) : Data) =
        Data.list ((List.replicate j false).map Data.ofBool) := by
      rw [List.append_nil, encode_bitStr_eq_list]
    have e2 : (encode (incTail rest) : Data) = Data.list ((incTail rest).map Data.ofBool) :=
      encode_bitStr_eq_list _
    have e3 : (encode (incBits (List.replicate j true ++ rest)) : Data) =
        Data.list (((List.replicate j false).map Data.ofBool).reverse ++ (incTail rest).map Data.ofBool) := by
      rw [incBits_replicate_true j rest hrest, encode_bitStr_eq_list, List.map_append]
      simp
    rw [e1, e2, e3]
    exact h₂
  have hpre := Eval.cons (Eval.var_of_get (env := [encode (List.replicate j true ++ rest)]) (i := 0)
    (v := encode (List.replicate j true ++ rest)) (by simp))
    (Eval.nil [encode (List.replicate j true ++ rest)])
  refine ⟨esize (List.replicate j true ++ rest) + 1 + 1 + 1 + (t₁ + t₂ + 1) + 1, ?_,
    Eval.let_ hpre (Eval.let_ h₁ h₂')⟩
  simp only [List.length_map, List.length_replicate] at ht₂
  rw [hlen]
  generalize esize (List.replicate j true ++ rest) = L at *
  have hsum : t₁ + t₂ ≤ (j + 1) * (2 * L + 32) := by
    have := Nat.mul_le_mul_left (j + 1) (show L + 1 + 13 + (L + 6 + 12) ≤ 2 * L + 32 by omega)
    rw [Nat.mul_add] at this; omega
  have hfin : (j + 1) * (2 * L + 32) + (L + 6) ≤ (j + rest.length + 2) * (3 * L + 32) :=
    calc (j + 1) * (2 * L + 32) + (L + 6) ≤ (j + 1) * (2 * L + 32) + (2 * L + 32) := by omega
      _ = (j + 1 + 1) * (2 * L + 32) := (Nat.succ_mul _ _).symm
      _ ≤ (j + rest.length + 2) * (3 * L + 32) := Nat.mul_le_mul (by omega) (by omega)
  omega

end Prog

/-- The successor on binary numerals, in polynomial time. -/
noncomputable def PolyTimeFun.inc : PolyTimeFun ℕ ℕ where
  toFun n := n + 1
  code := Prog.incProg
  closed := Prog.incProg_wellScoped
  timeBound := (X + 2) * (3 * X + 32)
  computes n := by
    obtain ⟨t, ht, hrun⟩ := Prog.incProg_runs n.bits
    refine ⟨t, ?_, ?_⟩
    · refine ht.trans ?_
      have h1 : n.bits.length ≤ esize n := length_le_esize_bitStr _
      simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat]
      exact Nat.mul_le_mul (by omega) le_rfl
    · rw [show (encode (n + 1) : Data) = encode (incBits n.bits) by
        rw [incBits_bits]; rfl]
      exact hrun

@[simp] theorem PolyTimeFun.inc_apply (n : ℕ) : PolyTimeFun.inc n = n + 1 := rfl

theorem esize_succ_le (n : ℕ) : esize (n + 1) ≤ esize n + 4 := by
  show esize (n + 1).bits ≤ esize n.bits + 4
  rw [← incBits_bits]
  exact esize_incBits_le _

/-- A unary numeral to binary, by a fold of the successor. -/
noncomputable def PolyTimeFun.unaryToBin : PolyTimeFun Unary ℕ :=
  PolyTimeFun.congr ((PolyTimeFun.foldlAdd (PolyTimeFun.inc.comp PolyTimeFun.fst) (C 4) (by
      rintro s ⟨⟩
      simp only [PolyTimeFun.comp_apply, PolyTimeFun.inc_apply, PolyTimeFun.fst_apply,
        Polynomial.eval_C]
      exact esize_succ_le s)).comp ((PolyTimeFun.id _).pair (PolyTimeFun.const 0)))
    (fun u => u.length) (by
      intro u
      simp only [PolyTimeFun.comp_apply, PolyTimeFun.foldlAdd_apply, PolyTimeFun.pair_apply,
        PolyTimeFun.id_apply, PolyTimeFun.const_apply, PolyTimeFun.inc_apply, PolyTimeFun.fst_apply]
      suffices ∀ k, u.foldl (fun s (_ : Unit) => s + 1) k = k + u.length from
        (this 0).trans (Nat.zero_add _)
      induction u with
      | nil => intro k; simp
      | cons _ u ih => intro k; simp [ih]; omega)

@[simp] theorem PolyTimeFun.unaryToBin_apply (u : Unary) : PolyTimeFun.unaryToBin u = u.length := rfl

/-! ## Tagged constructors -/

/-- A constructor whose encoding pairs a unary tag with the encoding of its argument. -/
noncomputable def PolyTimeFun.tagged {α β : Type*} [SizedEncoding α] [SizedEncoding β] (k : ℕ)
    (f : α → β) (h : ∀ a, (encode (f a) : Data) = .cons (.ofNat k) (encode a)) : PolyTimeFun α β where
  toFun := f
  code := .cons (.const (.ofNat k)) (.var 0)
  closed := ⟨trivial, Nat.zero_lt_one⟩
  timeBound := X + C (2 * k + 3)
  computes a := by
    refine ⟨(2 * k + 1) + (esize a + 1) + 1, ?_, ?_⟩
    · simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]; omega
    · rw [h]
      exact Eval.cons (by simpa using Eval.const [encode a] (.ofNat k)) (Eval.var _ _)

@[simp] theorem PolyTimeFun.tagged_apply {α β : Type*} [SizedEncoding α] [SizedEncoding β] (k : ℕ)
    (f : α → β) (h : ∀ a, (encode (f a) : Data) = .cons (.ofNat k) (encode a)) (a : α) :
    PolyTimeFun.tagged k f h a = f a := rfl

end MIPRE.Cost

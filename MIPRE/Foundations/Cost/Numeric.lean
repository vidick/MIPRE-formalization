/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Cost.Unary
import Mathlib.Tactic.Ring

/-!
# The closure library, part IV: binary numbers

Programs on binary numbers presented as bit strings (LSB first, as in `Nat.bits`), used by
the bit-query program of the recursive compression argument: the zero test
(`isZeroProg`) and decrement (`decProg`). Decrement flips the leading `false`s to `true`
and the first `true` to `false`; it may leave a non-canonical representation (trailing
`false`s), which is why the specifications are in terms of the *value* `bitsVal` of a bit
string rather than `Nat.bits`.

Costs: every list walk is quadratic in this model (the loop state is rebuilt each
iteration, copying the tail), so bounds have the form `(iterations + 1) · (S + c)` with `S`
dominating the sizes involved.
-/

namespace MIPRE.Cost

/-! ## Bit strings as data -/

@[simp] theorem Data.ofBool_false : Data.ofBool false = .nil := rfl

@[simp] theorem Data.ofBool_true : Data.ofBool true = .cons .nil .nil := rfl

@[simp] theorem encode_bool (b : Bool) : encode b = Data.ofBool b := rfl

@[simp] theorem encode_bitStr_nil : encode ([] : BitStr) = Data.nil := rfl

@[simp] theorem encode_bitStr_cons (b : Bool) (l : BitStr) :
    encode (b :: l) = Data.cons (Data.ofBool b) (encode l) := rfl

theorem encode_bitStr_eq_list (l : BitStr) : encode l = Data.list (l.map Data.ofBool) :=
  Data.ofList_eq_list _ _

theorem size_encode_replicate_true (j : ℕ) :
    (encode (List.replicate j true)).size = 4 * j + 1 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [List.replicate_succ, encode_bitStr_cons, Data.size_cons, Data.ofBool_true,
      Data.size_nil, ih]
    omega

theorem size_encode_replicate_false_append (j : ℕ) (rest : BitStr) :
    (encode (List.replicate j false ++ true :: rest)).size = 2 * j + (encode rest).size + 4 := by
  induction j with
  | zero =>
    simp only [List.replicate_zero, List.nil_append, encode_bitStr_cons, Data.size_cons,
      Data.ofBool_true, Data.size_nil]
    omega
  | succ j ih =>
    simp only [List.replicate_succ, List.cons_append, encode_bitStr_cons, Data.size_cons,
      Data.ofBool_false, Data.size_nil, ih]
    omega

theorem size_encode_false_cons_replicate_true (j : ℕ) :
    (encode (false :: List.replicate j true)).size = 4 * j + 3 := by
  simp only [encode_bitStr_cons, Data.size_cons, Data.ofBool_false, Data.size_nil,
    size_encode_replicate_true]
  omega

/-- The value of a bit string (LSB first), canonical or not. -/
def bitsVal (l : BitStr) : ℕ := l.foldr Nat.bit 0

@[simp] theorem bitsVal_nil : bitsVal [] = 0 := rfl

@[simp] theorem bitsVal_cons (b : Bool) (l : BitStr) :
    bitsVal (b :: l) = Nat.bit b (bitsVal l) := rfl

theorem bitsVal_bits (n : ℕ) : bitsVal n.bits = n := Nat.foldr_bit_bits n

theorem bitsVal_eq_zero_iff (l : BitStr) : bitsVal l = 0 ↔ l.any id = false := by
  induction l with
  | nil => simp
  | cons b l ih =>
    cases b <;> simp [Nat.bit_val, ih]

theorem bitsVal_replicate_true_append (j : ℕ) (rest : BitStr) :
    bitsVal (List.replicate j true ++ false :: rest) + 1 =
      bitsVal (List.replicate j false ++ true :: rest) := by
  induction j with
  | zero => simp [Nat.bit_val]
  | succ j ih =>
    simp only [List.replicate_succ, List.cons_append, bitsVal_cons, Nat.bit_val,
      Bool.toNat_false, Bool.toNat_true]
    omega

/-- A bit string with a `true` bit splits as `false^j ++ true :: rest`. -/
theorem exists_split_of_any (l : BitStr) (h : l.any id = true) :
    ∃ j rest, l = List.replicate j false ++ true :: rest := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    cases b with
    | true => exact ⟨0, l, rfl⟩
    | false =>
      simp only [List.any_cons, id, Bool.false_or] at h
      obtain ⟨j, rest, rfl⟩ := ih h
      exact ⟨j + 1, rest, by simp [List.replicate_succ]⟩

namespace Prog

/-! ## Zero test -/

/-- Body of `isZeroProg`: walk the bits; stop with `nil` (zero) at the end, with
`cons nil nil` (nonzero) at the first `true` bit. -/
def isZeroBody : Prog :=
  .elim 0 (.cons .nil .nil)
    (.elim 0 (.cons (.cons .nil .nil) (.var 1)) (.cons .nil (.cons .nil .nil)))

/-- `isZeroProg` on a bit string computes `encode (l.any id)`: `nil` iff the value is zero. -/
def isZeroProg : Prog := .loop isZeroBody

theorem isZeroBody_wellScoped : isZeroBody.WellScoped 1 := by
  simp [isZeroBody, WellScoped]

theorem isZeroProg_wellScoped : isZeroProg.WellScoped 1 :=
  ⟨Nat.zero_lt_one, isZeroBody_wellScoped⟩

theorem isZeroBody_stop : Eval [encode ([] : BitStr)] isZeroBody (.cons .nil .nil) 4 :=
  Eval.elim_nil (env := [encode ([] : BitStr)]) (i := 0)
    (c := .elim 0 (.cons (.cons .nil .nil) (.var 1)) (.cons .nil (.cons .nil .nil))) (by simp)
    (Eval.cons (Eval.nil _) (Eval.nil _))

theorem isZeroBody_false (l : BitStr) :
    Eval [encode (false :: l)] isZeroBody (.cons (.cons .nil .nil) (encode l))
      ((encode l).size + 7) := by
  have e := Eval.elim_cons (env := [encode (false :: l)]) (i := 0) (n := .cons .nil .nil)
    (a := .nil) (b := encode l) (by simp)
    (Eval.elim_nil (i := 0) (c := .cons .nil (.cons .nil .nil)) (by simp)
      (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
        (Eval.var_of_get (i := 1) (v := encode l) (by simp))))
  exact e.cast_cost (by omega)

theorem isZeroBody_true (l : BitStr) :
    Eval [encode (true :: l)] isZeroBody (.cons .nil (.cons .nil .nil)) 7 :=
  Eval.elim_cons (env := [encode (true :: l)]) (i := 0) (n := .cons .nil .nil)
    (a := .cons .nil .nil) (b := encode l) (by simp)
    (Eval.elim_cons (i := 0) (n := .cons (.cons .nil .nil) (.var 1)) (a := .nil) (b := .nil)
      (by simp)
      (Eval.cons (Eval.nil _) (Eval.cons (Eval.nil _) (Eval.nil _))))

theorem isZeroProg_runs (l : BitStr) (env : Env) (S : ℕ) (hS : (encode l).size ≤ S) :
    ∃ t ≤ (l.length + 1) * (S + 8),
      Eval (encode l :: env) isZeroProg (encode (l.any id)) t := by
  induction l with
  | nil =>
    refine ⟨5, ?_, ?_⟩
    · simp only [List.length_nil, Nat.zero_add, Nat.one_mul]; omega
    · simpa [isZeroProg] using Eval.loop_stop
        (Eval.append_of_wellScoped isZeroBody_stop isZeroBody_wellScoped env)
  | cons b l ih =>
    cases b with
    | false =>
      have hS' : (encode l).size ≤ S := by
        simp only [encode_bitStr_cons, Data.size_cons, Data.ofBool_false, Data.size_nil] at hS
        omega
      obtain ⟨t, ht, hrun⟩ := ih hS'
      refine ⟨(encode l).size + 7 + t + 1, ?_, ?_⟩
      · have h2 : (l.length + 1 + 1) * (S + 8) = (l.length + 1) * (S + 8) + (S + 8) :=
          Nat.succ_mul _ _
        simp only [List.length_cons]
        omega
      · have hstep := Eval.append_of_wellScoped (isZeroBody_false l) isZeroBody_wellScoped env
        have := Eval.loop_step hstep hrun
        simpa [isZeroProg] using this
    | true =>
      refine ⟨8, ?_, ?_⟩
      · have h1 : S + 8 ≤ ((true :: l).length + 1) * (S + 8) :=
          Nat.le_mul_of_pos_left _ (by omega)
        omega
      · have := Eval.loop_stop
          (Eval.append_of_wellScoped (isZeroBody_true l) isZeroBody_wellScoped env)
        simpa [isZeroProg] using this

/-! ## Decrement -/

/-- Body of the first phase of `decProg`: on state `cons bits acc`, a leading `false` bit
is turned into a `true` pushed on `acc`; at the first `true` bit the loop stops with the pair
`cons (false :: acc) rest`, which the second phase (`revOntoProg`) reverses onto `rest`. -/
def decBody : Prog :=
  .elim 0 .nil (.elim 0 (.cons .nil (.cons (.var 1) .nil))
    (.elim 0 (.cons (.cons .nil .nil) (.cons (.var 1) (.cons (.cons .nil .nil) (.var 3))))
      (.cons .nil (.cons (.cons .nil (.var 5)) (.var 3)))))

/-- `decProg` on the bits of a nonzero number computes the bits of its predecessor. -/
def decProg : Prog := .let_ (.cons (.var 0) .nil) (.let_ (.loop decBody) revOntoProg)

theorem decBody_wellScoped : decBody.WellScoped 1 := by
  simp [decBody, WellScoped]

theorem decProg_wellScoped : decProg.WellScoped 1 :=
  ⟨⟨Nat.zero_lt_one, trivial⟩,
    ⟨⟨Nat.zero_lt_succ 1, decBody_wellScoped.mono (by omega) _⟩,
      revOntoProg_wellScoped.mono (by omega) _⟩⟩

theorem decBody_false (l acc : BitStr) :
    Eval [.cons (encode (false :: l)) (encode acc)] decBody
      (.cons (.cons .nil .nil) (.cons (encode l) (encode (true :: acc))))
      ((encode l).size + (encode acc).size + 14) := by
  have e := Eval.elim_cons (env := [Data.cons (encode (false :: l)) (encode acc)]) (i := 0)
    (n := .nil) (a := encode (false :: l)) (b := encode acc) (by simp)
    (Eval.elim_cons (i := 0) (n := .cons .nil (.cons (.var 1) .nil)) (a := .nil)
      (b := encode l) (by simp)
      (Eval.elim_nil (i := 0) (c := .cons .nil (.cons (.cons .nil (.var 5)) (.var 3)))
        (by simp)
        (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
          (Eval.cons (Eval.var_of_get (i := 1) (v := encode l) (by simp))
            (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
              (Eval.var_of_get (i := 3) (v := encode acc) (by simp)))))))
  exact e.cast_cost (by omega)

theorem decBody_true (l acc : BitStr) :
    Eval [.cons (encode (true :: l)) (encode acc)] decBody
      (.cons .nil (.cons (encode (false :: acc)) (encode l)))
      ((encode l).size + (encode acc).size + 10) := by
  have e := Eval.elim_cons (env := [Data.cons (encode (true :: l)) (encode acc)]) (i := 0)
    (n := .nil) (a := encode (true :: l)) (b := encode acc) (by simp)
    (Eval.elim_cons (i := 0) (n := .cons .nil (.cons (.var 1) .nil)) (a := .cons .nil .nil)
      (b := encode l) (by simp)
      (Eval.elim_cons (i := 0)
        (n := .cons (.cons .nil .nil) (.cons (.var 1) (.cons (.cons .nil .nil) (.var 3))))
        (a := .nil) (b := .nil) (by simp)
        (Eval.cons (Eval.nil _)
          (Eval.cons
            (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 5) (v := encode acc) (by simp)))
            (Eval.var_of_get (i := 3) (v := encode l) (by simp))))))
  exact e.cast_cost (by omega)

/-- The first phase of `decProg` on `false^j ++ true :: rest` with accumulator `true^i`. The
slack `S` must cover the growth of the accumulator: each converted bit adds two nodes. -/
theorem decLoop_runs (j : ℕ) (rest : BitStr) (i : ℕ) (env : Env) (S : ℕ)
    (hS : 2 * j + (encode rest).size + 4 + (4 * i + 1) + 2 * j ≤ S) :
    ∃ t ≤ (j + 1) * (S + 15),
      Eval (.cons (encode (List.replicate j false ++ true :: rest))
          (encode (List.replicate i true)) :: env) (.loop decBody)
        (.cons (encode (false :: List.replicate (i + j) true)) (encode rest)) t := by
  induction j generalizing i with
  | zero =>
    refine ⟨(encode rest).size + (encode (List.replicate i true)).size + 10 + 1, ?_, ?_⟩
    · rw [size_encode_replicate_true]
      simp only [Nat.zero_add, Nat.one_mul]
      omega
    · have := Eval.loop_stop
        (Eval.append_of_wellScoped (decBody_true rest (List.replicate i true))
          decBody_wellScoped env)
      simpa using this
  | succ j ih =>
    have hS' : 2 * j + (encode rest).size + 4 + (4 * (i + 1) + 1) + 2 * j ≤ S := by omega
    obtain ⟨t, ht, hrun⟩ := ih (i + 1) hS'
    refine ⟨(encode (List.replicate j false ++ true :: rest)).size +
        (encode (List.replicate i true)).size + 14 + t + 1, ?_, ?_⟩
    · rw [size_encode_replicate_false_append, size_encode_replicate_true]
      have h2 : (j + 1 + 1) * (S + 15) = (j + 1) * (S + 15) + (S + 15) := Nat.succ_mul _ _
      omega
    · have hstep := Eval.append_of_wellScoped
        (decBody_false (List.replicate j false ++ true :: rest) (List.replicate i true))
        decBody_wellScoped env
      have hrun' : Eval (Data.cons (encode (List.replicate j false ++ true :: rest))
          (encode (true :: List.replicate i true)) :: env) (.loop decBody)
          (.cons (encode (false :: List.replicate (i + (j + 1)) true)) (encode rest)) t := by
        rw [show i + (j + 1) = i + 1 + j by omega]
        simpa [List.replicate_succ] using hrun
      have := Eval.loop_step hstep hrun'
      simpa [List.replicate_succ] using this

theorem decProg_runs (j : ℕ) (rest : BitStr) :
    ∃ t ≤ (j + 2) * (10 * (2 * j + (encode rest).size + 4) + 60),
      decProg.Runs (encode (List.replicate j false ++ true :: rest))
        (encode (List.replicate j true ++ false :: rest)) t := by
  have hl : (encode (List.replicate j false ++ true :: rest)).size =
      2 * j + (encode rest).size + 4 :=
    size_encode_replicate_false_append j rest
  have hp : (encode (false :: List.replicate j true)).size = 4 * j + 3 :=
    size_encode_false_cons_replicate_true j
  -- phase 1, from the empty accumulator
  obtain ⟨t₁, ht₁, h₁⟩ := decLoop_runs j rest 0 [encode (List.replicate j false ++ true :: rest)]
    (4 * j + (encode rest).size + 5) (by omega)
  -- phase 2: reverse `false :: true^j` onto `rest`
  obtain ⟨t₂, ht₂, h₂⟩ := revOntoProg_runs ((false :: List.replicate j true).map Data.ofBool)
    (rest.map Data.ofBool)
    [Data.cons (encode (List.replicate j false ++ true :: rest)) .nil,
      encode (List.replicate j false ++ true :: rest)]
    (4 * j + 3 + (encode rest).size)
    (le_of_eq (by rw [← encode_bitStr_eq_list, ← encode_bitStr_eq_list, hp]))
  refine ⟨(encode (List.replicate j false ++ true :: rest)).size + 1 + 1 + 1 +
    (t₁ + t₂ + 1) + 1, ?_, ?_⟩
  · have hA : t₁ ≤ (j + 2) * (4 * j + (encode rest).size + 20) :=
      ht₁.trans (Nat.mul_le_mul (by omega) (by omega))
    have hB : t₂ ≤ (j + 2) * (4 * j + (encode rest).size + 15) :=
      ht₂.trans (le_of_eq (by simp only [List.length_map, List.length_cons,
        List.length_replicate]; ring))
    have hC : (j + 2) * (4 * j + (encode rest).size + 20) +
        (j + 2) * (4 * j + (encode rest).size + 15) +
        (j + 2) * (2 * j + (encode rest).size + 9) =
        (j + 2) * (10 * j + 3 * (encode rest).size + 44) := by ring
    have hD : (j + 2) * (10 * j + 3 * (encode rest).size + 44) ≤
        (j + 2) * (10 * (2 * j + (encode rest).size + 4) + 60) :=
      Nat.mul_le_mul_left _ (by omega)
    have hE : 2 * j + (encode rest).size + 9 ≤ (j + 2) * (2 * j + (encode rest).size + 9) :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega
  · have hpre := Eval.cons
      (Eval.var_of_get (env := [encode (List.replicate j false ++ true :: rest)]) (i := 0)
        (v := encode (List.replicate j false ++ true :: rest)) (by simp))
      (Eval.nil [encode (List.replicate j false ++ true :: rest)])
    have h₁' : Eval (Data.cons (encode (List.replicate j false ++ true :: rest)) .nil ::
        [encode (List.replicate j false ++ true :: rest)]) (.loop decBody)
        (.cons (encode (false :: List.replicate j true)) (encode rest)) t₁ := by
      simpa using h₁
    have h₂' : Eval (Data.cons (encode (false :: List.replicate j true)) (encode rest) ::
        [Data.cons (encode (List.replicate j false ++ true :: rest)) .nil,
          encode (List.replicate j false ++ true :: rest)]) revOntoProg
        (encode (List.replicate j true ++ false :: rest)) t₂ := by
      simpa [encode_bitStr_eq_list, List.map_append, List.map_cons, List.map_replicate,
        List.reverse_cons, List.reverse_replicate] using h₂
    exact Eval.let_ hpre (Eval.let_ h₁' h₂')

end Prog

/-! ## The next level index -/

theorem encode_two_mul_add_one (n : ℕ) :
    encode (2 * n + 1) = Data.cons (.cons .nil .nil) (encode n) := by
  have h : (2 * n + 1).bits = true :: n.bits := by
    rw [← Nat.bit_true_apply]
    exact Nat.bits_append_bit n true (fun _ => rfl)
  show encode (2 * n + 1).bits = _
  rw [h]
  rfl

theorem size_two_mul_add_one (n : ℕ) : Nat.size (2 * n + 1) = Nat.size n + 1 := by
  rw [← Nat.bit_true_apply, Nat.size_bit (by rw [Nat.bit_true_apply]; omega)]

/-- `n ↦ 2 n + 1` on binary numerals: prepend a `true` bit. This is the "next level"
map of the recursive compression argument (the paper's `n + 1` would need a carry
propagation; `2 n + 1` is one node). -/
noncomputable def PolyTimeFun.next : PolyTimeFun ℕ ℕ where
  toFun n := 2 * n + 1
  code := .cons (.const (.cons .nil .nil)) (.var 0)
  closed := ⟨trivial, Nat.zero_lt_one⟩
  timeBound := Polynomial.X + Polynomial.C 5
  computes n := by
    refine ⟨3 + (esize n + 1) + 1, ?_, ?_⟩
    · simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]; omega
    · rw [encode_two_mul_add_one]
      exact Eval.cons (Eval.const _ _)
        (Eval.var_of_get (env := [encode n]) (i := 0) (v := encode n) (by simp))

@[simp] theorem PolyTimeFun.next_apply (n : ℕ) : PolyTimeFun.next n = 2 * n + 1 := rfl

end MIPRE.Cost

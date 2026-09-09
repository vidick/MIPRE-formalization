/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Cost.Numeric
import Mathlib.Tactic.Linarith

/-!
# The bit-query program

`bitAtProg` on `(y, m)` — a bit string and a binary index — returns the `m`-th bit of `y`,
or the out-of-range marker `ofNat 2`: this is the answer a succinct description must give
([MNY, Definition 2.4]; `bitQueryAnswer`). It walks `y` while decrementing `m` in binary,
testing for zero at each step, so its cost is `(|y| + 1) · bitAtIter (size y) |m|` with
`bitAtIter` quadratic in `|m|` (each zero test and decrement copies the index). This is
where the `(|m| + 1) ^ 2` factor of the succinctness budget of `IsSuccinctDesc` comes from.
-/

namespace MIPRE.Cost

/-- The answer a succinct description must give to the bit-query `m` about the string
`x`: the `m`-th bit for `m < |x|`, and the out-of-range marker (the unary numeral `2`)
otherwise. -/
def bitQueryAnswer (x : BitStr) (m : ℕ) : Data :=
  if h : m < x.length then encode (x.get ⟨m, h⟩) else Data.ofNat 2

@[simp] theorem bitQueryAnswer_nil (m : ℕ) : bitQueryAnswer [] m = Data.ofNat 2 := by
  simp [bitQueryAnswer]

@[simp] theorem bitQueryAnswer_cons_zero (b : Bool) (x : BitStr) :
    bitQueryAnswer (b :: x) 0 = encode b := by
  simp [bitQueryAnswer]

@[simp] theorem bitQueryAnswer_cons_succ (b : Bool) (x : BitStr) (m : ℕ) :
    bitQueryAnswer (b :: x) (m + 1) = bitQueryAnswer x m := by
  unfold bitQueryAnswer
  by_cases h : m < x.length
  · have h' : m + 1 < (b :: x).length := by simp [h]
    rw [dif_pos h', dif_pos h]
    rfl
  · have h' : ¬ m + 1 < (b :: x).length := by simp [h]
    rw [dif_neg h', dif_neg h]

namespace Prog

/-- Cost of one zero test on a bit string of length `L`. -/
def zeroBound (L : ℕ) : ℕ := (L + 1) * (4 * L + 1 + 8)

/-- Cost of one decrement on a bit string of length `L`. -/
def decBound (L : ℕ) : ℕ := (L + 2) * (10 * (6 * L + 4) + 60)

/-- Cost of one iteration of `bitAtProg` with a string of size at most `sy` and an index of
`L` bits. -/
def bitAtIter (sy L : ℕ) : ℕ := sy + 8 * L + zeroBound L + decBound L + 20

theorem isZeroProg_runs' (mb : BitStr) (env : Env) :
    ∃ t ≤ zeroBound mb.length, Eval (encode mb :: env) isZeroProg (encode (mb.any id)) t :=
  isZeroProg_runs mb env (4 * mb.length + 1) (esize_bitStr_le mb)

theorem decProg_runs' (mb : BitStr) (h : mb.any id = true) :
    ∃ mb' t, t ≤ decBound mb.length ∧ mb'.length = mb.length ∧ bitsVal mb' + 1 = bitsVal mb ∧
      decProg.Runs (encode mb) (encode mb') t := by
  obtain ⟨j, rest, rfl⟩ := exists_split_of_any mb h
  obtain ⟨t, ht, hrun⟩ := decProg_runs j rest
  refine ⟨List.replicate j true ++ false :: rest, t, ?_, by simp,
    bitsVal_replicate_true_append j rest, hrun⟩
  have hlen : (List.replicate j false ++ true :: rest).length = j + 1 + rest.length := by
    simp only [List.length_append, List.length_replicate, List.length_cons]
    omega
  have hsr : (encode rest).size ≤ 4 * rest.length + 1 := esize_bitStr_le rest
  rw [hlen]
  unfold decBound
  calc t ≤ (j + 2) * (10 * (2 * j + (encode rest).size + 4) + 60) := ht
    _ ≤ (j + 1 + rest.length + 2) * (10 * (6 * (j + 1 + rest.length) + 4) + 60) :=
        Nat.mul_le_mul (by omega) (by omega)

/-- Body of `bitAtProg`: on state `cons y m`, stop with `ofNat 2` if `y` is exhausted; else
test `m` for zero: if zero, stop with the head bit of `y`; otherwise continue with the tail
of `y` and `m - 1`. -/
def bitAtBody : Prog :=
  .elim 0 .nil (.elim 0 (.cons .nil (.const (.ofNat 2)))
    (.let_ (callVar 3 isZeroProg)
      (.elim 0 (.cons .nil (.var 1))
        (.cons (.cons .nil .nil) (.cons (.var 4) (callVar 6 decProg))))))

/-- `bitAtProg` on `cons (encode y) (encode m)` computes `bitQueryAnswer y m`. -/
def bitAtProg : Prog := .loop bitAtBody

theorem bitAtBody_wellScoped : bitAtBody.WellScoped 1 := by
  refine ⟨by decide, trivial, by decide, ⟨trivial, trivial⟩, ?_⟩
  refine ⟨callVar_wellScoped (by decide) isZeroProg_wellScoped, ?_⟩
  refine ⟨by decide, ⟨trivial, by simp [WellScoped]⟩, ⟨trivial, trivial⟩,
    ⟨by simp [WellScoped], ?_⟩⟩
  exact callVar_wellScoped (by decide) decProg_wellScoped

theorem bitAtProg_wellScoped : bitAtProg.WellScoped 1 :=
  ⟨Nat.zero_lt_one, bitAtBody_wellScoped⟩

/-- The body on an exhausted string: stop with the out-of-range marker. -/
theorem bitAtBody_nil (mb : BitStr) :
    Eval [.cons (encode ([] : BitStr)) (encode mb)] bitAtBody (.cons .nil (.ofNat 2)) 9 := by
  have e := Eval.elim_cons (env := [Data.cons (encode ([] : BitStr)) (encode mb)]) (i := 0)
    (n := .nil) (a := encode ([] : BitStr)) (b := encode mb) (by simp)
    (Eval.elim_nil (i := 0)
      (c := .let_ (callVar 3 isZeroProg)
        (.elim 0 (.cons .nil (.var 1))
          (.cons (.cons .nil .nil) (.cons (.var 4) (callVar 6 decProg))))) (by simp)
      (Eval.cons (Eval.nil _) (Eval.const _ (.ofNat 2))))
  exact e.cast_cost (by simp [Data.size_ofNat])

/-- The body when the index is zero: stop with the head bit. -/
theorem bitAtBody_zero (b : Bool) (ys mb : BitStr) (hz : mb.any id = false) (tz : ℕ)
    (hzr : Eval [encode mb] isZeroProg (encode (mb.any id)) tz) :
    Eval [.cons (encode (b :: ys)) (encode mb)] bitAtBody (.cons .nil (encode b))
      ((encode mb).size + tz + (encode b).size + 9) := by
  rw [hz] at hzr
  have e := Eval.elim_cons (env := [Data.cons (encode (b :: ys)) (encode mb)]) (i := 0)
    (n := .nil) (a := encode (b :: ys)) (b := encode mb) (by simp)
    (Eval.elim_cons (i := 0) (n := .cons .nil (.const (.ofNat 2))) (a := encode b)
      (b := encode ys) (by simp)
      (Eval.let_ (callVar_eval (i := 3) isZeroProg_wellScoped (v := encode mb) (by simp) hzr)
        (Eval.elim_nil (i := 0)
          (c := .cons (.cons .nil .nil) (.cons (.var 4) (callVar 6 decProg))) (by simp)
          (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 1) (v := encode b) (by simp))))))
  exact e.cast_cost (by omega)

/-- The body when the index is nonzero: continue with the tail and the decremented index. -/
theorem bitAtBody_succ (b : Bool) (ys mb mb' : BitStr) (hz : mb.any id = true) (tz td : ℕ)
    (hzr : Eval [encode mb] isZeroProg (encode (mb.any id)) tz)
    (hd : Eval [encode mb] decProg (encode mb') td) :
    Eval [.cons (encode (b :: ys)) (encode mb)] bitAtBody
      (.cons (.cons .nil .nil) (.cons (encode ys) (encode mb')))
      (2 * (encode mb).size + tz + td + (encode ys).size + 14) := by
  rw [hz] at hzr
  have e := Eval.elim_cons (env := [Data.cons (encode (b :: ys)) (encode mb)]) (i := 0)
    (n := .nil) (a := encode (b :: ys)) (b := encode mb) (by simp)
    (Eval.elim_cons (i := 0) (n := .cons .nil (.const (.ofNat 2))) (a := encode b)
      (b := encode ys) (by simp)
      (Eval.let_ (callVar_eval (i := 3) isZeroProg_wellScoped (v := encode mb) (by simp) hzr)
        (Eval.elim_cons (i := 0) (n := .cons .nil (.var 1)) (a := .nil) (b := .nil) (by simp)
          (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
            (Eval.cons (Eval.var_of_get (i := 4) (v := encode ys) (by simp))
              (callVar_eval (i := 6) decProg_wellScoped (v := encode mb) (by simp) hd))))))
  exact e.cast_cost (by omega)

/-- The loop of `bitAtProg`, by induction on the queried index. -/
theorem bitAtLoop_runs (m : ℕ) (y mb : BitStr) (hmb : bitsVal mb = m) (env : Env) (sy L : ℕ)
    (hsy : (encode y).size ≤ sy) (hL : mb.length = L) :
    ∃ t ≤ (y.length + 1) * bitAtIter sy L,
      Eval (.cons (encode y) (encode mb) :: env) bitAtProg (bitQueryAnswer y m) t := by
  have hI : bitAtIter sy L = sy + 8 * L + zeroBound L + decBound L + 20 := rfl
  have hmbsize : (encode mb).size ≤ 4 * L + 1 := by
    rw [← hL]; exact esize_bitStr_le mb
  induction m generalizing y mb with
  | zero =>
    have hz : mb.any id = false := (bitsVal_eq_zero_iff mb).1 hmb
    rcases y with _ | ⟨b, ys⟩
    · refine ⟨9 + 1, ?_, ?_⟩
      · simp only [List.length_nil, Nat.zero_add, Nat.one_mul]
        omega
      · have := Eval.loop_stop
          (Eval.append_of_wellScoped (bitAtBody_nil mb) bitAtBody_wellScoped env)
        simpa [bitAtProg] using this
    · obtain ⟨tz, htz, hzr⟩ := isZeroProg_runs' mb []
      have hb : (encode b).size ≤ 3 := Data.size_ofBool b
      refine ⟨(encode mb).size + tz + (encode b).size + 9 + 1, ?_, ?_⟩
      · simp only [List.length_cons]
        have h1 : bitAtIter sy L ≤ (ys.length + 1 + 1) * bitAtIter sy L :=
          Nat.le_mul_of_pos_left _ (by omega)
        rw [hL] at htz
        omega
      · have := Eval.loop_stop
          (Eval.append_of_wellScoped (bitAtBody_zero b ys mb hz tz hzr) bitAtBody_wellScoped env)
        simpa [bitAtProg] using this
  | succ m ih =>
    have hz : mb.any id = true := by
      cases h : mb.any id with
      | false =>
        have := (bitsVal_eq_zero_iff mb).2 h
        omega
      | true => rfl
    rcases y with _ | ⟨b, ys⟩
    · refine ⟨9 + 1, ?_, ?_⟩
      · simp only [List.length_nil, Nat.zero_add, Nat.one_mul]
        omega
      · have := Eval.loop_stop
          (Eval.append_of_wellScoped (bitAtBody_nil mb) bitAtBody_wellScoped env)
        simpa [bitAtProg] using this
    · obtain ⟨tz, htz, hzr⟩ := isZeroProg_runs' mb []
      obtain ⟨mb', td, htd, hlen', hval, hd⟩ := decProg_runs' mb hz
      have hmb' : bitsVal mb' = m := by omega
      have hsy' : (encode ys).size ≤ sy := by
        simp only [encode_bitStr_cons, Data.size_cons] at hsy
        omega
      have hL' : mb'.length = L := hlen'.trans hL
      have hmbsize' : (encode mb').size ≤ 4 * L + 1 := by
        rw [← hL']; exact esize_bitStr_le mb'
      obtain ⟨t', ht', hrun⟩ := ih ys mb' hmb' hsy' hL' hmbsize'
      have hstep := Eval.append_of_wellScoped (bitAtBody_succ b ys mb mb' hz tz td hzr hd)
        bitAtBody_wellScoped env
      refine ⟨2 * (encode mb).size + tz + td + (encode ys).size + 14 + t' + 1, ?_, ?_⟩
      · simp only [List.length_cons]
        have h2 : (ys.length + 1 + 1) * bitAtIter sy L =
            (ys.length + 1) * bitAtIter sy L + bitAtIter sy L := Nat.succ_mul _ _
        rw [hL] at htz htd
        omega
      · have := Eval.loop_step hstep hrun
        simpa [bitAtProg] using this

/-- `bitAtProg` answers bit queries: on `(encode y, encode m)` it computes
`bitQueryAnswer y m`, in time `(|y| + 1) · bitAtIter (size y) (Nat.size m)`. -/
theorem bitAtProg_runs (y : BitStr) (m : ℕ) :
    ∃ t ≤ (y.length + 1) * bitAtIter (encode y).size (Nat.size m),
      bitAtProg.Runs (.cons (encode y) (encode m)) (bitQueryAnswer y m) t :=
  bitAtLoop_runs m y m.bits (bitsVal_bits m) [] (encode y).size (Nat.size m) le_rfl
    (Nat.size_eq_bits_len m)

/-- `bitAtIter` is quadratic in the length of the index. -/
theorem bitAtIter_le (sy L : ℕ) : bitAtIter sy L ≤ (sy + 534) * (L + 1) ^ 2 := by
  unfold bitAtIter zeroBound decBound
  nlinarith [Nat.zero_le sy, Nat.zero_le L, Nat.zero_le (sy * L), Nat.zero_le (sy * (L * L)),
    Nat.zero_le (L * L)]

end Prog

end MIPRE.Cost

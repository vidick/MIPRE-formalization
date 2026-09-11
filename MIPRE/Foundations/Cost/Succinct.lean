/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Cost.BitQuery
import MIPRE.Foundations.Cost.Toolkit

/-!
# Succinct descriptions and the bit-query program

`IsSuccinctDesc c n x` is [MNY, Definition 2.4] (blueprint `def:succinct`), with the time
bound adapted to the ambient model (see the module docstring of
`MIPRE.Foundations.Compression`). The **bit-query program** `bitQueryProg univ` of the
recursive compression argument answers bit-queries about a string that is only given
*implicitly*, as the output of a program `c'` on an input `(e, n)`: on
`encode (((c', e), n), m)` it simulates `c'` on `encode (e, n)` through the universal machine
and indexes the result with `bitAtProg`. Its correctness is conditional on the run of `c'`
(`bitQueryProg_runs`), and hardcoding `((c', e), n)` into it gives a succinct description of
that output whenever the run is fast enough for the budget (`isSuccinctDesc_hardcode`).
-/

namespace MIPRE.Cost

open Polynomial

/-! ## Succinct descriptions ([MNY, Definition 2.4]; blueprint `def:succinct`) -/

/-- `(c, n)` **succinctly describes** the bit string `x`: `c` is a closed program, `x` has
length at most `2 ^ n`, and `c` answers every bit-query `m` (presented in binary; the
answer is `bitQueryAnswer x m`) within cost `(n + 1) * (|m| + 1) ^ 2`.

[MNY, Definition 2.4], with the time bound adapted as discussed in the module docstring of
`MIPRE.Foundations.Compression`. The pair `(c, n)` is exponentially smaller than `x` itself;
a compression procedure's guarantees are only required on genuine succinct descriptions,
but it must *run* (in polynomial time) on all inputs. -/
def IsSuccinctDesc (c : Prog) (n : ℕ) (x : BitStr) : Prop :=
  c.WellScoped 1 ∧ x.length ≤ 2 ^ n ∧
    ∀ m : ℕ, ∃ t ≤ (n + 1) * (Nat.size m + 1) ^ 2, c.Runs (encode m) (bitQueryAnswer x m) t

namespace Prog

/-- The bit-query program: on `encode (((c', e), n), m)`, run `univ` on
`cons (encode c') (encode (e, n))` to obtain the string `y`, then answer the bit-query `m`
about `y` with `bitAtProg`. -/
def bitQueryProg (univ : Prog) : Prog :=
  .elim 0 .nil (.elim 0 .nil (.elim 0 .nil
    (.let_ (.cons (.var 0) (.cons (.var 1) (.var 3)))
      (.let_ (callVar 0 univ)
        (.let_ (.cons (.var 0) (.var 7))
          (callVar 0 bitAtProg))))))

theorem bitQueryProg_wellScoped {univ : Prog} (hU : univ.WellScoped 1) :
    (bitQueryProg univ).WellScoped 1 :=
  ⟨by decide, trivial, by decide, trivial, by decide, trivial,
    ⟨by simp [WellScoped], by simp [WellScoped], by simp [WellScoped]⟩,
    callVar_wellScoped (by decide) hU,
    ⟨by simp [WellScoped], by simp [WellScoped]⟩,
    callVar_wellScoped (by decide) bitAtProg_wellScoped⟩

end Prog

/-- The cost of the bit-query program, as a polynomial in
`s = esize c' + esize e + esize n + t` (with `t` the cost of the run of `c'`), per
`(|m| + 1) ^ 2`. -/
noncomputable def bitQueryBound (U : UniversalMachine) : Polynomial ℕ :=
  U.bound.comp (X + C 1) + (X + C 1) * (X + C 534) + C 2 * X + C 29

theorem bitQueryBound_eval (U : UniversalMachine) (s : ℕ) :
    (bitQueryBound U).eval s = U.bound.eval (s + 1) + (s + 1) * (s + 534) + 2 * s + 29 := by
  simp [bitQueryBound, Polynomial.eval_comp]

/-- Conditional correctness of the bit-query program: if `c'` runs on `encode (e, n)` to
`encode y` at cost `t`, then `bitQueryProg U.univ` answers the bit-query `m` about `y`
within `bitQueryBound U (esize c' + esize e + esize n + t) · (|m| + 1) ^ 2`. -/
theorem Prog.bitQueryProg_runs (U : UniversalMachine) {α : Type*} [SizedEncoding α]
    (c' e : Prog) (n : α) (y : BitStr) (m : ℕ) {t : ℕ}
    (hrun : c'.Runs (encode (e, n)) (encode y) t) :
    ∃ T ≤ (bitQueryBound U).eval (esize c' + esize e + esize n + t) * (Nat.size m + 1) ^ 2,
      (bitQueryProg U.univ).Runs (encode (((c', e), n), m)) (bitQueryAnswer y m) T := by
  obtain ⟨t', ht', h'⟩ := U.time_le c' (encode (e, n)) (encode y) t hrun
  obtain ⟨tb, htb, hb⟩ := bitAtProg_runs y m
  -- the run
  have s1 : Eval [encode c', encode e, Data.cons (encode c') (encode e), encode n,
      Data.cons (Data.cons (encode c') (encode e)) (encode n), encode m,
      Data.cons (Data.cons (Data.cons (encode c') (encode e)) (encode n)) (encode m)]
      (.cons (.var 0) (.cons (.var 1) (.var 3)))
      (.cons (encode c') (.cons (encode e) (encode n))) _ :=
    Eval.cons (Eval.var_of_get (i := 0) (v := encode c') (by simp))
      (Eval.cons (Eval.var_of_get (i := 1) (v := encode e) (by simp))
        (Eval.var_of_get (i := 3) (v := encode n) (by simp)))
  have s2 := callVar_eval
    (env := Data.cons (encode c') (.cons (encode e) (encode n)) ::
      [encode c', encode e, Data.cons (encode c') (encode e), encode n,
        Data.cons (Data.cons (encode c') (encode e)) (encode n), encode m,
        Data.cons (Data.cons (Data.cons (encode c') (encode e)) (encode n)) (encode m)])
    (i := 0) U.closed (v := .cons (encode c') (.cons (encode e) (encode n))) (by simp) h'
  have s3 : Eval (encode y :: Data.cons (encode c') (.cons (encode e) (encode n)) ::
      [encode c', encode e, Data.cons (encode c') (encode e), encode n,
        Data.cons (Data.cons (encode c') (encode e)) (encode n), encode m,
        Data.cons (Data.cons (Data.cons (encode c') (encode e)) (encode n)) (encode m)])
      (.cons (.var 0) (.var 7)) (.cons (encode y) (encode m)) _ :=
    Eval.cons (Eval.var_of_get (i := 0) (v := encode y) (by simp))
      (Eval.var_of_get (i := 7) (v := encode m) (by simp))
  have s4 := callVar_eval
    (env := Data.cons (encode y) (encode m) :: encode y ::
      Data.cons (encode c') (.cons (encode e) (encode n)) ::
      [encode c', encode e, Data.cons (encode c') (encode e), encode n,
        Data.cons (Data.cons (encode c') (encode e)) (encode n), encode m,
        Data.cons (Data.cons (Data.cons (encode c') (encode e)) (encode n)) (encode m)])
    (i := 0) bitAtProg_wellScoped (v := .cons (encode y) (encode m)) (by simp) hb
  have run := Eval.elim_cons
    (env := [Data.cons (Data.cons (Data.cons (encode c') (encode e)) (encode n)) (encode m)])
    (i := 0) (n := .nil) (a := .cons (.cons (encode c') (encode e)) (encode n)) (b := encode m)
    (by simp)
    (Eval.elim_cons (i := 0) (n := .nil) (a := .cons (encode c') (encode e)) (b := encode n)
      (by simp)
      (Eval.elim_cons (i := 0) (n := .nil) (a := encode c') (b := encode e) (by simp)
        (Eval.let_ s1 (Eval.let_ s2 (Eval.let_ s3 s4)))))
  refine ⟨_, ?_, run⟩
  -- the bound
  rw [bitQueryBound_eval]
  have e1 : (encode (e, n)).size = esize e + esize n + 1 := rfl
  have e2 : (encode c').size = esize c' := rfl
  have e3 : (encode e).size = esize e := rfl
  have e4 : (encode n).size = esize n := rfl
  have hsy : (encode y).size ≤ t := hrun.size_le
  have hly : y.length ≤ (encode y).size := length_le_esize_bitStr y
  have hsm : (encode m).size ≤ 4 * Nat.size m + 1 := esize_nat_le m
  have hP1 : Nat.size m + 1 ≤ (Nat.size m + 1) ^ 2 := by
    rw [pow_two]; exact Nat.le_mul_self _
  have hB : t' ≤ U.bound.eval (esize c' + esize e + esize n + t + 1) :=
    ht'.trans (polynomial_eval_mono U.bound (by omega))
  have hb' : tb ≤ (esize c' + esize e + esize n + t + 1) *
      (esize c' + esize e + esize n + t + 534) * (Nat.size m + 1) ^ 2 := by
    calc tb ≤ (y.length + 1) * bitAtIter (encode y).size (Nat.size m) := htb
      _ ≤ (esize c' + esize e + esize n + t + 1) *
          ((esize c' + esize e + esize n + t + 534) * (Nat.size m + 1) ^ 2) :=
        Nat.mul_le_mul (by omega)
          ((bitAtIter_le _ _).trans (Nat.mul_le_mul_right _ (by omega)))
      _ = _ := by ring
  have hexp : (U.bound.eval (esize c' + esize e + esize n + t + 1) +
      (esize c' + esize e + esize n + t + 1) * (esize c' + esize e + esize n + t + 534) +
      2 * (esize c' + esize e + esize n + t) + 29) * (Nat.size m + 1) ^ 2 =
      U.bound.eval (esize c' + esize e + esize n + t + 1) * (Nat.size m + 1) ^ 2 +
      (esize c' + esize e + esize n + t + 1) * (esize c' + esize e + esize n + t + 534) *
        (Nat.size m + 1) ^ 2 +
      2 * ((esize c' + esize e + esize n + t) * (Nat.size m + 1) ^ 2) +
      29 * (Nat.size m + 1) ^ 2 := by ring
  have hBP : U.bound.eval (esize c' + esize e + esize n + t + 1) ≤
      U.bound.eval (esize c' + esize e + esize n + t + 1) * (Nat.size m + 1) ^ 2 :=
    Nat.le_mul_of_pos_right _ (pow_pos (Nat.succ_pos _) 2)
  have hsP : esize c' + esize e + esize n + t ≤
      (esize c' + esize e + esize n + t) * (Nat.size m + 1) ^ 2 :=
    Nat.le_mul_of_pos_right _ (pow_pos (Nat.succ_pos _) 2)
  simp only [Data.size_cons]
  omega

/-- Hardcoding `((c', e), n')` into the bit-query program gives a succinct description of
the output `y` of `c'` on `encode (e, n')`, with parameter `n`, as soon as the run of `c'`
fits the budget (`n'` may be any encodable value, e.g. a level or a pair of levels): its cost `t` is at most `2 ^ n`, and the bit-query overhead is at most
`n + 1`. -/
theorem isSuccinctDesc_hardcode (U : UniversalMachine) {α : Type*} [SizedEncoding α]
    (c' e : Prog) (n' : α) (n : ℕ) (y : BitStr)
    {t : ℕ} (hrun : c'.Runs (encode (e, n')) (encode y) t) (hlen : t ≤ 2 ^ n)
    (hbudget : (bitQueryBound U).eval (esize c' + esize e + esize n' + t) +
      (esize c' + esize e + 1 + esize n' + 1) + 4 ≤ n + 1) :
    IsSuccinctDesc (hardcode (Prog.bitQueryProg U.univ) (encode ((c', e), n'))) n y := by
  refine ⟨hardcode_wellScoped (Prog.bitQueryProg_wellScoped U.closed) _, ?_, fun m => ?_⟩
  · exact (length_le_esize_bitStr y).trans (hrun.size_le.trans hlen)
  · obtain ⟨T, hT, h⟩ := Prog.bitQueryProg_runs U c' e n' y m hrun
    refine ⟨T + (encode ((c', e), n')).size + (encode m).size + 3, ?_,
      hardcode_time (Prog.bitQueryProg_wellScoped U.closed) h⟩
    have hd : (encode ((c', e), n')).size = esize c' + esize e + 1 + esize n' + 1 := rfl
    have hsm : (encode m).size ≤ 4 * Nat.size m + 1 := esize_nat_le m
    have hP1 : Nat.size m + 1 ≤ (Nat.size m + 1) ^ 2 := by
      rw [pow_two]; exact Nat.le_mul_self _
    have hmul := Nat.mul_le_mul_right ((Nat.size m + 1) ^ 2) hbudget
    have hexp : ((bitQueryBound U).eval (esize c' + esize e + esize n' + t) +
        (esize c' + esize e + 1 + esize n' + 1) + 4) * (Nat.size m + 1) ^ 2 =
        (bitQueryBound U).eval (esize c' + esize e + esize n' + t) * (Nat.size m + 1) ^ 2 +
        (esize c' + esize e + 1 + esize n' + 1) * (Nat.size m + 1) ^ 2 +
        4 * (Nat.size m + 1) ^ 2 := by ring
    have hle : esize c' + esize e + 1 + esize n' + 1 ≤
        (esize c' + esize e + 1 + esize n' + 1) * (Nat.size m + 1) ^ 2 :=
      Nat.le_mul_of_pos_right _ (pow_pos (Nat.succ_pos _) 2)
    omega

end MIPRE.Cost

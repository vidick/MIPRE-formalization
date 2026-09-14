/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Halting.Lists
import MIPRE.Foundations.Cost.Unary
import MIPRE.Foundations.Cost.PolyTime
import MIPRE.Foundations.Cost.Growth
import Mathlib.Tactic.Linarith

/-!
# Arithmetic in the ambient model: increment, unary conversion, multiplication, polynomials

The arithmetic the wrapper decider (`Halting/Wrapper.lean`) and the compressor's decider
(`Halting/Compressor.lean`) need, each with its cost:

* `Prog.incProg`: the successor of a canonical binary numeral (`Data.inc`, with
  `Data.inc_bits : inc n.bits = (n + 1).bits`), used to enumerate the bit queries;
* `Prog.toUnaryProg`: a binary numeral to unary (`encode n ↦ ofNat n`), by the fold
  `k ↦ 2k + b` over the bits from the most significant one, doubling the unary accumulator with
  `revOntoProg`;
* `Prog.mulProg`: multiplication of unary numerals, by repeated `addProg`;
* `Prog.polyProg cs`: the Horner evaluation `c₀ + m (c₁ + m (…))` of a polynomial given by its
  coefficient list, on a unary input; `hornerCoeffs` and `Data.polyEval_hornerCoeffs` connect it
  to `Polynomial.eval`, so that the wrapper can compute the paper's `poly(n, λ)` bounds.

Costs are polynomial in the *values* (the unary numerals are as long as the values); the
polynomial evaluation is bounded by an explicit `Polynomial ℕ` in the argument
(`Prog.polyProg_runs`), which is what the time accounting downstream composes.
-/

namespace MIPRE.Cost

open Polynomial

namespace Data

/-! ## The successor of a binary numeral -/

/-- The successor of a binary numeral, least significant bit first. -/
def inc : BitStr → BitStr
  | [] => [true]
  | false :: l => true :: l
  | true :: l => false :: inc l

theorem bitsVal_inc (l : BitStr) : bitsVal (inc l) = bitsVal l + 1 := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    cases b
    · simp [inc, bitsVal_cons, Nat.bit]
    · simp only [inc, bitsVal_cons, ih, Nat.bit]
      simp only [Bool.cond_false, Bool.cond_true]
      omega

theorem inc_ne_nil (l : BitStr) : inc l ≠ [] := by
  cases l with
  | nil => simp [inc]
  | cons b l => cases b <;> simp [inc]

theorem inc_canon (l : BitStr) (hl : l = [] ∨ l.getLast? = some true) :
    (inc l).getLast? = some true := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    have hl' : l = [] ∨ l.getLast? = some true := by
      rcases hl with h | h
      · cases h
      · rcases l with _ | ⟨c, l⟩
        · exact Or.inl rfl
        · right; rw [List.getLast?_cons_cons] at h; exact h
    cases b
    · simp only [inc]
      rcases l with _ | ⟨c, l⟩
      · rfl
      · rw [List.getLast?_cons_cons]
        rcases hl' with h | h
        · cases h
        · exact h
    · simp only [inc]
      rcases hinc : inc l with _ | ⟨c, l'⟩
      · exact absurd hinc (inc_ne_nil l)
      · rw [List.getLast?_cons_cons, ← hinc]
        exact ih hl'

/-- The successor on canonical binary numerals is the successor. -/
theorem inc_bits (n : ℕ) : inc n.bits = (n + 1).bits := by
  have hcanon : inc n.bits = [] ∨ (inc n.bits).getLast? = some true :=
    Or.inr (inc_canon n.bits (bits_getLast n))
  have := bits_foldr_of_canon (inc n.bits) hcanon
  rw [← this]
  congr 1
  show bitsVal (inc n.bits) = n + 1
  rw [bitsVal_inc, bitsVal_bits]

/-- The first phase of the increment: `(rest, acc) ↦ (acc', rest')` with
`acc'.reverse ++ rest' = acc.reverse ++ inc rest`. -/
def incAcc : BitStr → BitStr → BitStr × BitStr
  | [], acc => (true :: acc, [])
  | false :: r, acc => (true :: acc, r)
  | true :: r, acc => incAcc r (false :: acc)

theorem incAcc_spec (l acc : BitStr) :
    (incAcc l acc).1.reverse ++ (incAcc l acc).2 = acc.reverse ++ inc l := by
  induction l generalizing acc with
  | nil => simp [incAcc, inc]
  | cons b l ih =>
    cases b
    · simp [incAcc, inc]
    · simp only [incAcc, inc, ih (false :: acc), List.reverse_cons, List.append_assoc,
        List.singleton_append]

theorem incAcc_length (l acc : BitStr) :
    (incAcc l acc).1.length + (incAcc l acc).2.length ≤ l.length + acc.length + 1 := by
  induction l generalizing acc with
  | nil => simp [incAcc]
  | cons b l ih =>
    cases b
    · simp only [incAcc, List.length_cons]; omega
    · have := ih (false :: acc)
      simp only [incAcc, List.length_cons] at this ⊢; omega

theorem size_encode_append (l₁ l₂ : BitStr) :
    (encode (l₁ ++ l₂) : Data).size + 1 = (encode l₁ : Data).size + (encode l₂ : Data).size := by
  induction l₁ with
  | nil => simp only [List.nil_append, encode_bitStr_nil, Data.size_nil]; omega
  | cons b l ih =>
    simp only [List.cons_append, encode_bitStr_cons, Data.size_cons] at ih ⊢
    omega

theorem size_encode_reverse (l : BitStr) : (encode l.reverse : Data).size = (encode l : Data).size := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    have := size_encode_append l.reverse [b]
    simp only [List.reverse_cons, encode_bitStr_cons, encode_bitStr_nil, Data.size_cons,
      Data.size_nil] at this ⊢
    omega

/-! ## Binary to unary -/

/-- The fold `k ↦ 2k + b` over bits, most significant first. -/
def msbFold : List Bool → ℕ → ℕ
  | [], k => k
  | b :: r, k => msbFold r (2 * k + b.toNat)

theorem msbFold_append_singleton (l : List Bool) (b : Bool) (k : ℕ) :
    msbFold (l ++ [b]) k = 2 * msbFold l k + b.toNat := by
  induction l generalizing k with
  | nil => rfl
  | cons c l ih => simp [msbFold, ih]

theorem msbFold_reverse (l : BitStr) (k : ℕ) :
    msbFold l.reverse k = k * 2 ^ l.length + bitsVal l := by
  induction l generalizing k with
  | nil => simp [msbFold]
  | cons b l ih =>
    rw [List.reverse_cons, msbFold_append_singleton, ih, bitsVal_cons, List.length_cons,
      pow_succ, Nat.bit]
    cases b <;> simp <;> ring

theorem msbFold_le (l : List Bool) (k : ℕ) : k ≤ msbFold l k := by
  induction l generalizing k with
  | nil => exact le_rfl
  | cons b l ih => exact le_trans (by omega) (ih (2 * k + b.toNat))

/-! ## Polynomials by their coefficients -/

/-- Horner evaluation of a coefficient list: `polyEval [c₀, c₁, …] m = c₀ + m (c₁ + m (…))`. -/
def polyEval : List ℕ → ℕ → ℕ
  | [], _ => 0
  | c :: cs, m => c + m * polyEval cs m

theorem polyEval_range_map (f : ℕ → ℕ) (k m : ℕ) :
    polyEval ((List.range k).map f) m = ∑ i ∈ Finset.range k, f i * m ^ i := by
  induction k generalizing f with
  | zero => simp [polyEval]
  | succ k ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, polyEval, ih, Finset.sum_range_succ',
      Finset.mul_sum]
    simp only [Function.comp_def, pow_zero, mul_one, pow_succ]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

end Data

/-- The coefficient list of a polynomial over `ℕ`, least significant first and padded to
`natDegree + 1` entries: the form Horner evaluation consumes (`Data.polyEval`). Mathlib's
`Polynomial.coeffList` is the big-endian list without the padding. -/
noncomputable def hornerCoeffs (p : Polynomial ℕ) : List ℕ :=
  (List.range (p.natDegree + 1)).map p.coeff

theorem Data.polyEval_hornerCoeffs (p : Polynomial ℕ) (m : ℕ) :
    Data.polyEval (hornerCoeffs p) m = p.eval m := by
  rw [hornerCoeffs, Data.polyEval_range_map, Polynomial.eval_eq_sum_range]

namespace Prog

open Data

/-- Close a cost bound after the run has been built: unfold the sizes of the small constants
and of unary numerals, and let `omega` finish. -/
macro "cost_omega'" : tactic =>
  `(tactic| (try simp only [Data.size_cons, Data.size_nil, Data.size_ofNat, encode_bool,
      Data.ofBool, encode_bitStr_nil, Bool.toNat_false, Bool.toNat_true]) <;> omega)

/-! ## The increment program -/

/-- Body of the first phase of `incProg`, on the state `cons rest acc`: at the end or at a
`false` bit, stop with `(true :: acc, rest)`; at a `true` bit, move a `false` onto `acc`. -/
def incBody : Prog :=
  .elim 0 .nil
    (.elim 0 (.cons .nil (.cons (.cons (.cons .nil .nil) (.var 1)) .nil))
      (.elim 0 (.cons .nil (.cons (.cons (.cons .nil .nil) (.var 3)) (.var 1)))
        (.cons (.cons .nil .nil) (.cons (.var 3) (.cons .nil (.var 5))))))

/-- `incProg` on the bits of `n` computes the bits of `n + 1`. -/
def incProg : Prog := .let_ (.cons (.var 0) .nil) (.let_ (.loop incBody) revOntoProg)

theorem incBody_wellScoped : incBody.WellScoped 1 := by simp [incBody, WellScoped]

theorem incProg_wellScoped : incProg.WellScoped 1 := by
  simp [incProg, WellScoped, incBody, revOntoProg, revOntoBody]

theorem incBody_nil (acc : BitStr) :
    ∃ t ≤ (encode acc : Data).size + 20,
      Eval [Data.cons (encode ([] : BitStr)) (encode acc)] incBody
        (Data.cons Data.nil (Data.cons (encode (true :: acc)) (encode ([] : BitStr)))) t := by
  refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := encode ([] : BitStr)) (b := encode acc) (by simp)
    (Eval.elim_nil (i := 0) (by simp [encode_bitStr_nil])
      (Eval.cons (Eval.nil _) (Eval.cons (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
        (Eval.var_of_get (i := 1) (v := encode acc) (by simp))) (Eval.nil _))))⟩
  cost_omega'

theorem incBody_false (r acc : BitStr) :
    ∃ t ≤ (encode r : Data).size + (encode acc : Data).size + 20,
      Eval [Data.cons (encode (false :: r)) (encode acc)] incBody
        (Data.cons Data.nil (Data.cons (encode (true :: acc)) (encode r))) t := by
  refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := encode (false :: r)) (b := encode acc) (by simp)
    (Eval.elim_cons (i := 0) (a := Data.nil) (b := encode r) (by simp [encode_bitStr_cons, ofBool])
      (Eval.elim_nil (i := 0) (by simp)
        (Eval.cons (Eval.nil _) (Eval.cons (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
          (Eval.var_of_get (i := 3) (v := encode acc) (by simp)))
          (Eval.var_of_get (i := 1) (v := encode r) (by simp))))))⟩
  omega

theorem incBody_true (r acc : BitStr) :
    ∃ t ≤ (encode r : Data).size + (encode acc : Data).size + 20,
      Eval [Data.cons (encode (true :: r)) (encode acc)] incBody
        (Data.cons (Data.cons Data.nil Data.nil) (Data.cons (encode r) (encode (false :: acc)))) t := by
  refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := encode (true :: r)) (b := encode acc) (by simp)
    (Eval.elim_cons (i := 0) (a := Data.cons Data.nil Data.nil) (b := encode r)
      (by simp [encode_bitStr_cons, ofBool])
      (Eval.elim_cons (i := 0) (a := Data.nil) (b := Data.nil) (by simp)
        (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
          (Eval.cons (Eval.var_of_get (i := 3) (v := encode r) (by simp))
            (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 5) (v := encode acc) (by simp)))))))⟩
  omega

/-- The first phase of the increment, on `(rest, acc)`. -/
theorem incLoop_runs (l acc : BitStr) (env : Env) (S : ℕ)
    (hS : (encode l : Data).size + (encode acc : Data).size + 3 * l.length ≤ S) :
    ∃ t ≤ (l.length + 1) * (S + 21),
      Eval (Data.cons (encode l) (encode acc) :: env) (.loop incBody)
        (Data.cons (encode (incAcc l acc).1) (encode (incAcc l acc).2)) t := by
  induction l generalizing acc with
  | nil =>
    obtain ⟨t, ht, hrun⟩ := incBody_nil acc
    have hstop := Eval.loop_stop (Eval.append_of_wellScoped hrun incBody_wellScoped env)
    refine ⟨t + 1, ?_, by simpa [incAcc] using hstop⟩
    simp only [List.length_nil, encode_bitStr_nil, Data.size_nil] at hS ⊢
    omega
  | cons b l ih =>
    cases b
    · obtain ⟨t, ht, hrun⟩ := incBody_false l acc
      have hstop := Eval.loop_stop (Eval.append_of_wellScoped hrun incBody_wellScoped env)
      refine ⟨t + 1, ?_, by simpa [incAcc] using hstop⟩
      have : S + 21 ≤ (l.length + 1 + 1) * (S + 21) := Nat.le_mul_of_pos_left _ (by omega)
      simp only [encode_bitStr_cons, Data.size_cons, List.length_cons] at hS ⊢
      omega
    · obtain ⟨t, ht, hrun⟩ := incBody_true l acc
      have hS' : (encode l : Data).size + (encode (false :: acc) : Data).size + 3 * l.length ≤ S := by
        simp only [encode_bitStr_cons, Data.size_cons, List.length_cons, ofBool, Data.size_nil]
          at hS ⊢
        omega
      obtain ⟨t', ht', hrun'⟩ := ih (false :: acc) hS'
      refine ⟨t + t' + 1, ?_, ?_⟩
      · have h2 : (l.length + 1 + 1) * (S + 21) = (l.length + 1) * (S + 21) + (S + 21) :=
          Nat.succ_mul _ _
        simp only [encode_bitStr_cons, Data.size_cons, List.length_cons] at hS ⊢
        omega
      · have := Eval.loop_step (Eval.append_of_wellScoped hrun incBody_wellScoped env) hrun'
        simpa [incAcc] using this

/-- `incProg` computes the successor of a binary numeral. -/
theorem incProg_runs (l : BitStr) :
    ∃ t ≤ (l.length + 2) * (8 * (encode l : Data).size + 8 * l.length + 60),
      incProg.Runs (encode l) (encode (inc l)) t := by
  have hsz : (encode l : Data).size ≤ 4 * l.length + 1 := esize_bitStr_le l
  obtain ⟨t₁, ht₁, h₁⟩ := incLoop_runs l [] [encode l] ((encode l : Data).size + 3 * l.length + 1)
    (by simp only [encode_bitStr_nil, Data.size_nil]; omega)
  -- phase 2
  set a := (incAcc l []).1 with ha
  set r := (incAcc l []).2 with hr
  have hlen : a.length + r.length ≤ l.length + 1 := by
    have := incAcc_length l []; simp only [List.length_nil] at this; omega
  have hspec : a.reverse ++ r = inc l := by
    have := incAcc_spec l []; simpa using this
  obtain ⟨t₂, ht₂, h₂⟩ := revOntoProg_runs (a.map Data.ofBool) (r.map Data.ofBool)
    [Data.cons (encode l) .nil, encode l] (4 * (l.length + 1) + 2)
    (by
      rw [← encode_bitStr_eq_list, ← encode_bitStr_eq_list]
      have := esize_bitStr_le a
      have := esize_bitStr_le r
      simp only [esize] at *
      omega)
  have hpre := Eval.cons (Eval.var_of_get (env := [encode l]) (i := 0) (v := encode l) (by simp))
    (Eval.nil [encode l])
  have h₁' : Eval [Data.cons (encode l) .nil, encode l] (.loop incBody)
      (Data.cons (encode a) (encode r)) t₁ := by
    have : Data.cons (encode l) (encode ([] : BitStr)) = Data.cons (encode l) .nil := by
      simp [encode_bitStr_nil]
    rw [this] at h₁
    exact h₁
  have h₂' : Eval [Data.cons (encode a) (encode r), Data.cons (encode l) .nil, encode l]
      revOntoProg (encode (inc l)) t₂ := by
    rw [← hspec]
    simp only [encode_bitStr_eq_list, List.map_append, List.map_reverse] at h₂ ⊢
    exact h₂
  refine ⟨_, ?_, Eval.let_ hpre (Eval.let_ h₁' h₂')⟩
  · have hA : t₁ ≤ (l.length + 1) * ((encode l : Data).size + 3 * l.length + 22) := ht₁
    have hB : t₂ ≤ (l.length + 2) * (4 * l.length + 18) := by
      refine ht₂.trans ?_
      simp only [List.length_map]
      exact Nat.mul_le_mul (by omega) (by omega)
    have h3 : (l.length + 1) * ((encode l : Data).size + 3 * l.length + 22) ≤
        (l.length + 2) * ((encode l : Data).size + 3 * l.length + 22) :=
      Nat.mul_le_mul_right _ (by omega)
    have h4 : (l.length + 2) * ((encode l : Data).size + 3 * l.length + 22) +
        (l.length + 2) * (4 * l.length + 18) + (encode l : Data).size + 5 ≤
        (l.length + 2) * (8 * (encode l : Data).size + 8 * l.length + 60) := by
      nlinarith
    cost_omega'

/-- The successor on canonical numerals, as a run on `encode n`. -/
theorem incProg_runs_nat (n : ℕ) :
    ∃ t ≤ (Nat.size n + 2) * (8 * esize n + 8 * Nat.size n + 60),
      incProg.Runs (encode n) (encode (n + 1)) t := by
  obtain ⟨t, ht, h⟩ := incProg_runs n.bits
  refine ⟨t, ?_, ?_⟩
  · rw [← Nat.size_eq_bits_len]; exact ht
  · show incProg.Runs (encode n.bits) (encode (n + 1).bits) t
    rw [← inc_bits]; exact h

/-! ## Binary to unary -/

/-- Body of `toUnaryProg`, on the state `cons rest acc` (`rest` the remaining bits, most
significant first; `acc` a unary numeral): double `acc` and add the next bit. -/
def toUnaryBody : Prog :=
  .elim 0 .nil
    (.elim 0 (.cons .nil (.var 1))
      (.let_ (.let_ (.cons (.var 3) (.var 3)) revOntoProg)
        (.elim 1 (.cons (.cons .nil .nil) (.cons (.var 2) (.var 0)))
          (.cons (.cons .nil .nil) (.cons (.var 4) (.cons .nil (.var 2)))))))

/-- `toUnaryProg` on `encode n` computes `ofNat n`. -/
def toUnaryProg : Prog :=
  .let_ (callVar 0 revProg) (.let_ (.cons (.var 0) .nil) (.loop toUnaryBody))

theorem toUnaryBody_wellScoped : toUnaryBody.WellScoped 1 := by
  simp [toUnaryBody, WellScoped, revOntoProg, revOntoBody]

theorem toUnaryProg_wellScoped : toUnaryProg.WellScoped 1 := by
  simp [toUnaryProg, WellScoped, callVar, revProg, revOntoProg, revOntoBody, toUnaryBody]

theorem toUnaryBody_nil (k : ℕ) :
    ∃ t ≤ 2 * k + 20, Eval [Data.cons (encode ([] : BitStr)) (ofNat k)] toUnaryBody
      (Data.cons Data.nil (ofNat k)) t := by
  refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := encode ([] : BitStr)) (b := ofNat k) (by simp)
    (Eval.elim_nil (i := 0) (by simp [encode_bitStr_nil])
      (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 1) (v := ofNat k) (by simp))))⟩
  cost_omega'

/-- The doubling of a unary numeral by `revOntoProg`. -/
theorem double_runs (k : ℕ) (env : Env) :
    ∃ t ≤ (k + 1) * (4 * k + 14),
      Eval (Data.cons (ofNat k) (ofNat k) :: env) revOntoProg (ofNat (2 * k)) t := by
  obtain ⟨t, ht, h⟩ := revOntoProg_runs (List.replicate k Data.nil) (List.replicate k Data.nil) env
    (4 * k + 2) (by simp only [← ofNat_eq_list_replicate, Data.size_ofNat]; omega)
  refine ⟨t, ?_, ?_⟩
  · simpa [List.length_replicate] using ht
  · simp only [← ofNat_eq_list_replicate] at h
    rw [List.reverse_replicate, List.replicate_append_replicate, ← ofNat_eq_list_replicate] at h
    rw [show 2 * k = k + k by ring]
    exact h

theorem toUnaryBody_step (b : Bool) (r : BitStr) (k : ℕ) :
    ∃ t ≤ (k + 1) * (4 * k + 14) + (encode r : Data).size + 8 * k + 64,
      Eval [Data.cons (encode (b :: r)) (ofNat k)] toUnaryBody
        (Data.cons (Data.cons Data.nil Data.nil) (Data.cons (encode r) (ofNat (2 * k + b.toNat)))) t := by
  obtain ⟨t₀, ht₀, hd⟩ := double_runs k
    [ofBool b, encode r, encode (b :: r), ofNat k, Data.cons (encode (b :: r)) (ofNat k)]
  have hpair : Eval [ofBool b, encode r, encode (b :: r), ofNat k, Data.cons (encode (b :: r)) (ofNat k)]
      (.cons (.var 3) (.var 3)) (Data.cons (ofNat k) (ofNat k)) ((ofNat k).size + 1 + ((ofNat k).size + 1) + 1) :=
    Eval.cons (Eval.var_of_get (i := 3) (v := ofNat k) (by simp))
      (Eval.var_of_get (i := 3) (v := ofNat k) (by simp))
  have hdbl := Eval.let_ hpair hd
  cases b
  · refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := encode (false :: r)) (b := ofNat k) (by simp)
      (Eval.elim_cons (i := 0) (a := ofBool false) (b := encode r) (by simp [encode_bitStr_cons])
        (Eval.let_ hdbl (Eval.elim_nil (i := 1) (by simp [ofBool])
          (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
            (Eval.cons (Eval.var_of_get (i := 2) (v := encode r) (by simp))
              (Eval.var_of_get (i := 0) (v := ofNat (2 * k)) (by simp)))))))⟩
    cost_omega'
  · refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := encode (true :: r)) (b := ofNat k) (by simp)
      (Eval.elim_cons (i := 0) (a := ofBool true) (b := encode r) (by simp [encode_bitStr_cons])
        (Eval.let_ hdbl (Eval.elim_cons (i := 1) (a := Data.nil) (b := Data.nil) (by simp [ofBool])
          (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
            (Eval.cons (Eval.var_of_get (i := 4) (v := encode r) (by simp))
              (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 2) (v := ofNat (2 * k)) (by simp))))))))⟩
    cost_omega'

/-- The unary fold over the bits, most significant first: from `(rest, ofNat k)` to
`ofNat (msbFold rest k)`, in time `(|rest| + 1) · B` for `B` a bound depending on the final
value `N = msbFold rest k`. -/
theorem toUnaryLoop_runs (l : List Bool) (k : ℕ) (env : Env) (N : ℕ) (hN : msbFold l k = N)
    (S : ℕ) (hS : (encode l : Data).size ≤ S) :
    ∃ t ≤ (l.length + 1) * ((N + 1) * (4 * N + 14) + S + 8 * N + 65),
      Eval (Data.cons (encode l) (ofNat k) :: env) (.loop toUnaryBody) (ofNat N) t := by
  induction l generalizing k with
  | nil =>
    simp only [msbFold] at hN; subst hN
    obtain ⟨t, ht, hrun⟩ := toUnaryBody_nil k
    have hstop := Eval.loop_stop (Eval.append_of_wellScoped hrun toUnaryBody_wellScoped env)
    refine ⟨t + 1, ?_, hstop⟩
    simp only [List.length_nil, Nat.zero_add, Nat.one_mul]
    nlinarith
  | cons b l ih =>
    simp only [msbFold] at hN
    have hk : k ≤ N := hN ▸ (msbFold_le l (2 * k + b.toNat)).trans' (by omega)
    obtain ⟨t, ht, hrun⟩ := toUnaryBody_step b l k
    have hS' : (encode l : Data).size ≤ S := by
      simp only [encode_bitStr_cons, Data.size_cons] at hS; omega
    obtain ⟨t', ht', hrun'⟩ := ih (2 * k + b.toNat) hN hS'
    refine ⟨t + t' + 1, ?_, ?_⟩
    · have hB : (k + 1) * (4 * k + 14) ≤ (N + 1) * (4 * N + 14) :=
        Nat.mul_le_mul (by omega) (by omega)
      have h2 : (l.length + 1 + 1) * ((N + 1) * (4 * N + 14) + S + 8 * N + 65) =
          (l.length + 1) * ((N + 1) * (4 * N + 14) + S + 8 * N + 65) +
            ((N + 1) * (4 * N + 14) + S + 8 * N + 65) := Nat.succ_mul _ _
      simp only [List.length_cons]
      omega
    · exact Eval.loop_step (Eval.append_of_wellScoped hrun toUnaryBody_wellScoped env) hrun'

/-- `toUnaryProg` converts a binary numeral to unary. -/
theorem toUnaryProg_runs (n : ℕ) :
    ∃ t ≤ (Nat.size n + 2) * ((n + 1) * (4 * n + 14) + 7 * esize n + 8 * n + 90),
      toUnaryProg.Runs (encode n) (ofNat n) t := by
  have hL : n.bits.length = Nat.size n := Nat.size_eq_bits_len n
  have hesz : (encode n.bits : Data).size = esize n := rfl
  have hrev : (encode n.bits.reverse : Data).size = esize n := by
    rw [size_encode_reverse]; exact hesz
  -- reversal
  obtain ⟨t₁, ht₁, h₁⟩ := revProg_runs (n.bits.map Data.ofBool)
  have h₁'' : revProg.Runs (encode n.bits) (encode n.bits.reverse) t₁ := by
    rw [encode_bitStr_eq_list, encode_bitStr_eq_list, List.map_reverse]
    exact h₁
  have h₁' : Eval [encode n] (callVar 0 revProg) (encode n.bits.reverse)
      ((encode n : Data).size + 1 + t₁ + 1) :=
    callVar_eval (env := [encode n]) (i := 0) revProg_wellScoped (v := encode n) (by simp) h₁''
  -- the fold
  obtain ⟨t₂, ht₂, h₂⟩ := toUnaryLoop_runs n.bits.reverse 0 [encode n.bits.reverse, encode n] n
    (by rw [msbFold_reverse, bitsVal_bits]; simp) (esize n) (le_of_eq hrev)
  have hpre := Eval.cons (Eval.var_of_get (env := [encode n.bits.reverse, encode n]) (i := 0)
    (v := encode n.bits.reverse) (by simp)) (Eval.nil [encode n.bits.reverse, encode n])
  have h₂' : Eval [Data.cons (encode n.bits.reverse) .nil, encode n.bits.reverse, encode n]
      (.loop toUnaryBody) (ofNat n) t₂ := by
    simpa [ofNat] using h₂
  refine ⟨_, ?_, Eval.let_ h₁' (Eval.let_ hpre h₂')⟩
  have hlen : n.bits.reverse.length = Nat.size n := by rw [List.length_reverse, hL]
  rw [hlen] at ht₂
  have hA : t₁ ≤ (Nat.size n + 2) * (esize n + 13) := by
    refine ht₁.trans ?_
    simp only [List.length_map, hL]
    rw [← encode_bitStr_eq_list, hesz]
  have key : (Nat.size n + 2) * (esize n + 13) +
      (Nat.size n + 1) * ((n + 1) * (4 * n + 14) + esize n + 8 * n + 65) + 2 * esize n + 10 ≤
      (Nat.size n + 2) * ((n + 1) * (4 * n + 14) + 7 * esize n + 8 * n + 90) := by
    nlinarith
  have hesz' : (encode n : Data).size = esize n := rfl
  rw [hrev, hesz']
  omega

/-! ## Multiplication of unary numerals -/

/-- Body of the multiplication loop, on the state `cons bRest acc`, with the first factor `a`
one variable further out: at the end stop with `acc`, otherwise add `a` to `acc`. -/
def mulBody : Prog :=
  .elim 0 .nil
    (.elim 0 (.cons .nil (.var 1))
      (.let_ (.let_ (.cons (.var 5) (.var 3)) addProg)
        (.cons (.cons .nil .nil) (.cons (.var 2) (.var 0)))))

/-- `mulProg` on `cons (ofNat a) (ofNat b)` computes `ofNat (a * b)`. -/
def mulProg : Prog := .elim 0 .nil (.let_ (.cons (.var 1) .nil) (.loop mulBody))

theorem mulBody_wellScoped : mulBody.WellScoped 4 := by
  simp [mulBody, WellScoped, addProg, lenBody]

theorem mulProg_wellScoped : mulProg.WellScoped 1 := by
  simp [mulProg, WellScoped, mulBody, addProg, lenBody]

theorem mulBody_nil (a acc : ℕ) (rest : Env) :
    ∃ t ≤ 2 * acc + 20,
      Eval (Data.cons (ofNat 0) (ofNat acc) :: ofNat a :: rest) mulBody
        (Data.cons Data.nil (ofNat acc)) t := by
  refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := ofNat 0) (b := ofNat acc) (by simp)
    (Eval.elim_nil (i := 0) (by simp [ofNat])
      (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 1) (v := ofNat acc) (by simp))))⟩
  cost_omega'

theorem mulBody_step (a b' acc : ℕ) (rest : Env) :
    ∃ t ≤ (a + 1) * (4 * a + 2 * acc + 15) + 4 * a + 4 * acc + 2 * b' + 40,
      Eval (Data.cons (ofNat (b' + 1)) (ofNat acc) :: ofNat a :: rest) mulBody
        (Data.cons (Data.cons Data.nil Data.nil) (Data.cons (ofNat b') (ofNat (a + acc)))) t := by
  obtain ⟨t₀, ht₀, hadd⟩ := addProg_runs a acc
    (Data.nil :: ofNat b' :: ofNat (b' + 1) :: ofNat acc ::
      Data.cons (ofNat (b' + 1)) (ofNat acc) :: ofNat a :: rest)
  have hpair := Eval.cons
    (Eval.var_of_get (env := Data.nil :: ofNat b' :: ofNat (b' + 1) :: ofNat acc ::
      Data.cons (ofNat (b' + 1)) (ofNat acc) :: ofNat a :: rest) (i := 5) (v := ofNat a) (by simp))
    (Eval.var_of_get (env := Data.nil :: ofNat b' :: ofNat (b' + 1) :: ofNat acc ::
      Data.cons (ofNat (b' + 1)) (ofNat acc) :: ofNat a :: rest) (i := 3) (v := ofNat acc) (by simp))
  have hsum := Eval.let_ hpair hadd
  refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := ofNat (b' + 1)) (b := ofNat acc) (by simp)
    (Eval.elim_cons (i := 0) (a := Data.nil) (b := ofNat b') (by simp [ofNat])
      (Eval.let_ (by simpa using hsum)
        (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
          (Eval.cons (Eval.var_of_get (i := 2) (v := ofNat b') (by simp))
            (Eval.var_of_get (i := 0) (v := ofNat (a + acc)) (by simp))))))⟩
  cost_omega'

/-- The multiplication loop: from `(ofNat b, ofNat acc)` with `a` one variable out, to
`ofNat (acc + a b)`. -/
theorem mulLoop_runs (a b acc : ℕ) (rest : Env) (P : ℕ) (hP : acc + a * b ≤ P) :
    ∃ t ≤ (b + 1) * ((a + 1) * (4 * a + 2 * P + 15) + 4 * a + 4 * P + 2 * b + 41),
      Eval (Data.cons (ofNat b) (ofNat acc) :: ofNat a :: rest) (.loop mulBody)
        (ofNat (acc + a * b)) t := by
  induction b generalizing acc with
  | zero =>
    obtain ⟨t, ht, hrun⟩ := mulBody_nil a acc rest
    refine ⟨t + 1, ?_, by simpa using Eval.loop_stop hrun⟩
    simp only [Nat.mul_zero, Nat.add_zero] at hP
    nlinarith
  | succ b ih =>
    obtain ⟨t, ht, hrun⟩ := mulBody_step a b acc rest
    have hP' : a + acc + a * b ≤ P := by rw [Nat.mul_succ] at hP; omega
    obtain ⟨t', ht', hrun'⟩ := ih (a + acc) hP'
    refine ⟨t + t' + 1, ?_, ?_⟩
    · have hacc : acc ≤ P := by nlinarith
      have h2 : (b + 1 + 1) * ((a + 1) * (4 * a + 2 * P + 15) + 4 * a + 4 * P + 2 * (b + 1) + 41) =
          (b + 1) * ((a + 1) * (4 * a + 2 * P + 15) + 4 * a + 4 * P + 2 * (b + 1) + 41) +
            ((a + 1) * (4 * a + 2 * P + 15) + 4 * a + 4 * P + 2 * (b + 1) + 41) := Nat.succ_mul _ _
      have h3 : (b + 1) * ((a + 1) * (4 * a + 2 * P + 15) + 4 * a + 4 * P + 2 * b + 41) ≤
          (b + 1) * ((a + 1) * (4 * a + 2 * P + 15) + 4 * a + 4 * P + 2 * (b + 1) + 41) :=
        Nat.mul_le_mul_left _ (by omega)
      have h4 : (a + 1) * (4 * a + 2 * acc + 15) ≤ (a + 1) * (4 * a + 2 * P + 15) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    · have := Eval.loop_step hrun hrun'
      rw [Nat.mul_succ]
      rw [show acc + (a * b + a) = a + acc + a * b by ring]
      exact this

/-- `mulProg` multiplies unary numerals. -/
theorem mulProg_runs (a b : ℕ) :
    ∃ t ≤ (b + 1) * ((a + 1) * (4 * a + 2 * (a * b) + 15) + 4 * a + 4 * (a * b) + 2 * b + 41) +
        2 * b + 10,
      mulProg.Runs (Data.cons (ofNat a) (ofNat b)) (ofNat (a * b)) t := by
  obtain ⟨t, ht, hrun⟩ := mulLoop_runs a b 0 [ofNat b, Data.cons (ofNat a) (ofNat b)] (a * b)
    (by omega)
  have hpre := Eval.cons (Eval.var_of_get (env := [ofNat a, ofNat b, Data.cons (ofNat a) (ofNat b)])
    (i := 1) (v := ofNat b) (by simp)) (Eval.nil [ofNat a, ofNat b, Data.cons (ofNat a) (ofNat b)])
  have hrun' : Eval (Data.cons (ofNat b) Data.nil :: [ofNat a, ofNat b, Data.cons (ofNat a) (ofNat b)])
      (.loop mulBody) (ofNat (a * b)) t := by simpa [ofNat] using hrun
  refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := ofNat a) (b := ofNat b) (by simp)
    (Eval.let_ hpre hrun')⟩
  cost_omega'

/-! ## Polynomials, by Horner's rule -/

/-- Horner evaluation of the coefficient list `cs` on a unary input `m`:
`polyProg (c :: cs)` computes `c + m · polyProg cs`. -/
def polyProg : List ℕ → Prog
  | [] => .nil
  | c :: cs =>
    .let_ (polyProg cs)
      (.let_ (.let_ (.cons (.var 1) (.var 0)) mulProg)
        (.let_ (.cons (.const (ofNat c)) (.var 0)) addProg))

theorem polyProg_wellScoped : ∀ cs : List ℕ, (polyProg cs).WellScoped 1
  | [] => trivial
  | c :: cs =>
    ⟨polyProg_wellScoped cs,
      ⟨⟨⟨by simp [WellScoped], by simp [WellScoped]⟩, mulProg_wellScoped.mono (by omega) _⟩,
        ⟨⟨trivial, by simp [WellScoped]⟩, addProg_wellScoped.mono (by omega) _⟩⟩⟩

/-- `polyProg cs` evaluates the polynomial, within a cost polynomial in the argument. -/
theorem polyProg_runs (cs : List ℕ) :
    ∃ Q : Polynomial ℕ, ∀ (m : ℕ) (env : Env),
      ∃ t ≤ Q.eval m, Eval (ofNat m :: env) (polyProg cs) (ofNat (polyEval cs m)) t := by
  induction cs with
  | nil => exact ⟨C 1, fun m env => ⟨1, by simp, Eval.nil _⟩⟩
  | cons c cs ih =>
    obtain ⟨Q, hQ⟩ := ih
    refine ⟨Q + (Q + 1) * ((X + 1) * (4 * X + 2 * X * Q + 15) + 4 * X + 4 * X * Q + 2 * Q + 41) +
      (C c + 1) * (4 * C c + 2 * X * Q + 15) + 4 * X * Q + 4 * X + 4 * Q + C (4 * c) + 40,
      fun m env => ?_⟩
    obtain ⟨t₁, ht₁, h₁⟩ := hQ m env
    set p := polyEval cs m with hp
    have hpQ : p ≤ Q.eval m := by
      have := h₁.size_le
      simp only [Data.size_ofNat] at this
      omega
    obtain ⟨t₂, ht₂, h₂⟩ := mulProg_runs m p
    obtain ⟨t₃, ht₃, h₃⟩ := addProg_runs c (m * p) [ofNat (m * p), ofNat p, ofNat m]
    -- the pair `(m, p)` and the product
    have hpair : Eval [ofNat p, ofNat m] (.cons (.var 1) (.var 0)) (Data.cons (ofNat m) (ofNat p))
        ((ofNat m).size + 1 + ((ofNat p).size + 1) + 1) :=
      Eval.cons (Eval.var_of_get (i := 1) (v := ofNat m) (by simp))
        (Eval.var_of_get (i := 0) (v := ofNat p) (by simp))
    have hmul := Eval.let_ hpair (Eval.append_of_wellScoped h₂ mulProg_wellScoped [ofNat p, ofNat m])
    -- the pair `(c, m p)` and the sum
    have hpair' : Eval [ofNat (m * p), ofNat p, ofNat m] (.cons (.const (ofNat c)) (.var 0))
        (Data.cons (ofNat c) (ofNat (m * p))) ((ofNat c).size + ((ofNat (m * p)).size + 1) + 1) :=
      Eval.cons (Eval.const _ _) (Eval.var_of_get (i := 0) (v := ofNat (m * p)) (by simp))
    have hadd := Eval.let_ hpair' h₃
    have hbody : Eval [ofNat p, ofNat m] (.let_ (.let_ (.cons (.var 1) (.var 0)) mulProg)
        (.let_ (.cons (.const (ofNat c)) (.var 0)) addProg)) (ofNat (c + m * p)) _ :=
      Eval.let_ hmul hadd
    have hbody' := Eval.append_of_wellScoped hbody
      (by simp [WellScoped, mulProg, mulBody, addProg, lenBody]) env
    refine ⟨_, ?_, Eval.let_ h₁ (by simpa [polyEval, hp] using hbody')⟩
    simp only [eval_add, eval_mul, eval_X, eval_C, eval_one, eval_ofNat]
    have hprod : m * p ≤ m * Q.eval m := Nat.mul_le_mul_left _ hpQ
    have hmulle : (p + 1) * ((m + 1) * (4 * m + 2 * (m * p) + 15) + 4 * m + 4 * (m * p) + 2 * p + 41) ≤
        (Q.eval m + 1) * ((m + 1) * (4 * m + 2 * (m * Q.eval m) + 15) + 4 * m + 4 * (m * Q.eval m) +
          2 * Q.eval m + 41) :=
      Nat.mul_le_mul (by omega) (by nlinarith)
    have haddle : (c + 1) * (4 * c + 2 * (m * p) + 15) ≤ (c + 1) * (4 * c + 2 * (m * Q.eval m) + 15) :=
      Nat.mul_le_mul_left _ (by omega)
    simp only [Data.size_ofNat] at *
    nlinarith

end Prog

end MIPRE.Cost

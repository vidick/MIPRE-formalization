/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Halting.Descriptions
import MIPRE.Foundations.Cost.Numeric

/-!
# Bounded walks over lists, in the ambient model

The programs with which the wrapper decider of `Halting/Wrapper.lean` performs the paper's
format checks: the questions must be bit strings of the sampler's length, the answers bit
strings within the answer-length budget, and equal questions must carry equal answers. All of
them walk their input under a *budget*, so that their cost is the budget times the size of the
input — the shape `T · (|input| + 1)` of `Decider.TimeBoundAt` — rather than a power of it.

* `Prog.bitWalkProg`: on `cons l u`, walk `l` against the budget `u` (a list, typically a unary
  numeral), checking that each element passed is a bit; the result is `nil` on a non-bit
  element, and otherwise the pair of what remains of `l` and of `u` (`Data.bitWalk`). Both
  format checks read off it: `|l| = |u|` is the result `cons nil nil`, `|l| ≤ |u|` a result
  `cons nil _`.
* `Prog.eqBitsProg`: equality of two bit lists (`Data.eqBits`).
* `Prog.normBinProg`: the normalization `Data.normBin` of a parameter, by a walk recording the
  last bit seen (`Data.canonWalk`).

Every walk copies the remainder of the lists at each step, which is what the ambient model
charges; the cost bounds are `(budget + 1) · (S + c)` for `S` the size of the input.
-/

namespace MIPRE.Cost

namespace Data

/-- The length of the right spine: the length of a list. -/
def spine : Data → ℕ
  | nil => 0
  | cons _ r => spine r + 1

@[simp] theorem spine_nil : spine nil = 0 := rfl
@[simp] theorem spine_cons (a r : Data) : spine (cons a r) = spine r + 1 := rfl

theorem spine_list (l : List Data) : spine (list l) = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem spine_ofNat (n : ℕ) : spine (ofNat n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ofNat, ih]

theorem spine_le_size (d : Data) : spine d ≤ d.size := by
  induction d with
  | nil => simp
  | cons a r _ ih => have := size_pos a; simp only [spine_cons, size_cons]; omega

/-- The bit an element denotes: `nil` is `false`, anything else `true`. -/
def bitOf : Data → Bool
  | nil => false
  | cons _ _ => true

@[simp] theorem bitOf_ofBool (b : Bool) : bitOf (ofBool b) = b := by cases b <;> rfl

/-- Walk `l` against the budget `u`, checking that every element passed is a bit: `nil` on a
non-bit, otherwise the pair of the remainders. -/
def bitWalk : Data → Data → Data
  | nil, u => cons nil u
  | cons h l', nil => cons (cons h l') nil
  | cons h l', cons _ u' => if isBit h then bitWalk l' u' else nil

/-- On a bit list and a list budget: the walk stops with the remainders. -/
theorem bitWalk_encode (x : BitStr) (u : List Data) :
    bitWalk (encode x) (list u) =
      cons (encode (x.drop u.length)) (list (u.drop x.length)) := by
  induction x generalizing u with
  | nil => simp [bitWalk, encode_bitStr_nil]
  | cons b x ih =>
    cases u with
    | nil => simp [bitWalk, encode_bitStr_cons]
    | cons c u => simp [bitWalk, encode_bitStr_cons, ih]

/-- Equality of two bit lists, element by element. -/
def eqBits : Data → Data → Bool
  | nil, nil => true
  | cons h₁ l₁, cons h₂ l₂ => (bitOf h₁ == bitOf h₂) && eqBits l₁ l₂
  | _, _ => false

/-- On unary numerals, `eqBits` is equality of the numbers: every element is `nil`, so the
walk compares only the lengths. -/
theorem eqBits_ofNat (a b : ℕ) : eqBits (ofNat a) (ofNat b) = decide (a = b) := by
  induction a generalizing b with
  | zero => cases b <;> simp [eqBits, ofNat]
  | succ a ih =>
    cases b with
    | zero => simp [eqBits, ofNat]
    | succ b => simp [eqBits, ofNat, ih, bitOf]

theorem eqBits_encode (x y : BitStr) : eqBits (encode x) (encode y) = (x == y) := by
  induction x generalizing y with
  | nil => cases y <;> simp [eqBits, encode_bitStr_nil, encode_bitStr_cons]
  | cons b x ih =>
    cases y with
    | nil => simp [eqBits, encode_bitStr_nil, encode_bitStr_cons]
    | cons c y => simp [eqBits, encode_bitStr_cons, ih]

/-- The walk of the normalization: `last` records whether the string so far is empty or ends
in `true`. -/
def canonWalk : Data → Bool → Bool
  | nil, last => last
  | cons nil r, _ => canonWalk r false
  | cons (cons nil nil) r, _ => canonWalk r true
  | cons _ _, _ => false

theorem canonWalk_iff (d : Data) (b : Bool) :
    canonWalk d b = true ↔
      ∃ l : BitStr, d = encode l ∧ (l = [] → b = true) ∧ (l ≠ [] → l.getLast? = some true) := by
  induction d generalizing b with
  | nil =>
    simp only [canonWalk]
    constructor
    · intro hb; exact ⟨[], rfl, fun _ => hb, fun h => absurd rfl h⟩
    · rintro ⟨l, hl, h1, -⟩
      cases l with
      | nil => exact h1 rfl
      | cons c l => simp [encode_bitStr_cons] at hl
  | cons h r _ ihr =>
    have key : ∀ (b' : Bool), canonWalk r b' = true ↔ ∃ l : BitStr, cons (ofBool b') r = encode (b' :: l) ∧
        ((b' :: l) = [] → b = true) ∧ ((b' :: l) ≠ [] → (b' :: l).getLast? = some true) := by
      intro b'
      rw [ihr]
      constructor
      · rintro ⟨l, rfl, h1, h2⟩
        refine ⟨l, rfl, fun h => absurd h (List.cons_ne_nil _ _), fun _ => ?_⟩
        cases l with
        | nil => simpa using h1 rfl
        | cons c l => rw [List.getLast?_cons_cons]; exact h2 (List.cons_ne_nil _ _)
      · rintro ⟨l, hl, -, h2⟩
        refine ⟨l, ?_, fun hnil => ?_, fun hne => ?_⟩
        · rw [encode_bitStr_cons] at hl; exact (cons.inj hl).2
        · subst hnil; simpa using h2 (List.cons_ne_nil _ _)
        · have := h2 (List.cons_ne_nil _ _)
          cases l with
          | nil => exact absurd rfl hne
          | cons c l => rw [List.getLast?_cons_cons] at this; exact this
    rcases h with _ | ⟨_ | ⟨a1, a2⟩, _ | ⟨b1, b2⟩⟩
    · -- `h = nil`
      simp only [canonWalk]
      rw [key false]
      constructor
      · rintro ⟨l, hl, h1, h2⟩; exact ⟨false :: l, hl, h1, h2⟩
      · rintro ⟨l, hl, h1, h2⟩
        cases l with
        | nil => simp [encode_bitStr_nil] at hl
        | cons c l =>
          rw [encode_bitStr_cons] at hl
          have hc : ofBool c = nil := ((cons.inj hl).1).symm
          cases c
          · exact ⟨l, by rw [encode_bitStr_cons]; exact hl, h1, h2⟩
          · simp [ofBool] at hc
    · -- `h = cons nil nil`
      simp only [canonWalk]
      rw [key true]
      constructor
      · rintro ⟨l, hl, h1, h2⟩; exact ⟨true :: l, hl, h1, h2⟩
      · rintro ⟨l, hl, h1, h2⟩
        cases l with
        | nil => simp [encode_bitStr_nil] at hl
        | cons c l =>
          rw [encode_bitStr_cons] at hl
          have hc : ofBool c = cons nil nil := ((cons.inj hl).1).symm
          cases c
          · simp [ofBool] at hc
          · exact ⟨l, by rw [encode_bitStr_cons]; exact hl, h1, h2⟩
    all_goals
      simp only [canonWalk, Bool.false_eq_true, false_iff, not_exists, not_and]
      rintro l hl
      cases l with
      | nil => simp [encode_bitStr_nil] at hl
      | cons c l =>
        rw [encode_bitStr_cons] at hl
        have hc := (cons.inj hl).1
        cases c <;> simp [ofBool] at hc

/-- The walk computes the normalization test. -/
theorem canonWalk_eq_isCanonBin (d : Data) : canonWalk d true = isCanonBin d := by
  rcases hc : isCanonBin d
  · rw [← Bool.not_eq_true, canonWalk_iff]
    rintro ⟨l, rfl, h1, h2⟩
    have : isCanonBin (encode l) = true := by
      simp only [isCanonBin]
      show (match (decode (encode l) : Option BitStr) with
        | some l => decide (l = [] ∨ l.getLast? = some true)
        | none => false) = true
      rw [SizedEncoding.decode_encode]
      by_cases hl : l = []
      · simp [hl]
      · simp [h2 hl]
    rw [hc] at this; exact absurd this Bool.false_ne_true
  · rw [canonWalk_iff]
    unfold isCanonBin at hc
    rcases hdec : (decode d : Option BitStr) with _ | l
    · rw [hdec] at hc; simp at hc
    · rw [hdec] at hc
      refine ⟨l, (encode_of_decode_bitStr hdec).symm, fun _ => rfl, fun hne => ?_⟩
      simp only [decide_eq_true_eq] at hc
      rcases hc with hc | hc
      · exact absurd hc hne
      · exact hc

end Data

namespace Prog

open Data

/-- Close a cost bound after the run has been built: unfold the sizes of the small constants
and let `omega` finish. -/
macro "cost_omega" : tactic =>
  `(tactic| (try simp only [Data.size_cons, Data.size_nil, encode_bool, Data.ofBool]) <;> omega)

/-! ## The bounded bit walk -/

/-- Body of `bitWalkProg`, on the state `cons l u`: stop with `cons nil u` if `l` is empty,
with `cons l nil` if the budget is exhausted, with `nil` if the head of `l` is not a bit, and
otherwise continue with the two tails. -/
def bitWalkBody : Prog :=
  .elim 0 .nil
    (.elim 0 (.cons .nil (.cons .nil (.var 1)))
      (.elim 3 (.cons .nil (.cons (.var 2) .nil))
        (.elim 2 (.cons (.cons .nil .nil) (.cons (.var 3) (.var 1)))
          (.elim 0 (.elim 1 (.cons (.cons .nil .nil) (.cons (.var 5) (.var 3)))
              (.cons .nil .nil))
            (.cons .nil .nil)))))

/-- The bounded bit walk: on `cons l u`, compute `bitWalk l u`. -/
def bitWalkProg : Prog := .loop bitWalkBody

theorem bitWalkBody_wellScoped : bitWalkBody.WellScoped 1 := by
  simp [bitWalkBody, WellScoped]

theorem bitWalkProg_wellScoped : bitWalkProg.WellScoped 1 :=
  ⟨Nat.zero_lt_one, bitWalkBody_wellScoped⟩

theorem bitWalkBody_lnil (u : Data) :
    ∃ t ≤ u.size + 20, Eval [Data.cons Data.nil u] bitWalkBody (Data.cons Data.nil (Data.cons Data.nil u)) t := by
  refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := Data.nil) (b := u) (by simp)
    (Eval.elim_nil (i := 0) (by simp)
    (Eval.cons (Eval.nil _) (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 1) (v := u) (by simp)))))⟩
  cost_omega

theorem bitWalkBody_unil (h l' : Data) :
    ∃ t ≤ (Data.cons h l').size + 20, Eval [Data.cons (Data.cons h l') Data.nil] bitWalkBody (Data.cons Data.nil (Data.cons (Data.cons h l') Data.nil)) t := by
  refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := Data.cons h l') (b := Data.nil) (by simp)
    (Eval.elim_cons (i := 0) (a := h) (b := l') (by simp)
    (Eval.elim_nil (i := 3) (by simp)
    (Eval.cons (Eval.nil _) (Eval.cons (Eval.var_of_get (i := 2) (v := Data.cons h l') (by simp)) (Eval.nil _)))))⟩
  cost_omega

theorem bitWalkBody_step (h l' c u' : Data) (hb : isBit h = true) :
    ∃ t ≤ l'.size + u'.size + 20,
      Eval [Data.cons (Data.cons h l') (Data.cons c u')] bitWalkBody
        (Data.cons (Data.cons Data.nil Data.nil) (Data.cons l' u')) t := by
  obtain ⟨b, rfl⟩ := (isBit_iff h).1 hb
  cases b
  · refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := Data.cons (ofBool false) l') (b := Data.cons c u') (by simp)
      (Eval.elim_cons (i := 0) (a := ofBool false) (b := l') (by simp)
      (Eval.elim_cons (i := 3) (a := c) (b := u') (by simp)
      (Eval.elim_nil (i := 2) (by simp [ofBool])
      (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _)) (Eval.cons (Eval.var_of_get (i := 3) (v := l') (by simp)) (Eval.var_of_get (i := 1) (v := u') (by simp)))))))⟩
    cost_omega
  · refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := Data.cons (ofBool true) l') (b := Data.cons c u') (by simp)
      (Eval.elim_cons (i := 0) (a := ofBool true) (b := l') (by simp)
      (Eval.elim_cons (i := 3) (a := c) (b := u') (by simp)
      (Eval.elim_cons (i := 2) (a := Data.nil) (b := Data.nil) (by simp [ofBool])
      (Eval.elim_nil (i := 0) (by simp)
      (Eval.elim_nil (i := 1) (by simp)
      (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _)) (Eval.cons (Eval.var_of_get (i := 5) (v := l') (by simp)) (Eval.var_of_get (i := 3) (v := u') (by simp)))))))))⟩
    cost_omega

theorem bitWalkBody_fail (h l' c u' : Data) (hb : isBit h = false) :
    ∃ t ≤ 20, Eval [Data.cons (Data.cons h l') (Data.cons c u')] bitWalkBody
      (Data.cons Data.nil Data.nil) t := by
  rcases h with _ | ⟨_ | ⟨a1, a2⟩, _ | ⟨b1, b2⟩⟩
  · simp [isBit] at hb
  · simp [isBit] at hb
  · refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := Data.cons (Data.cons Data.nil (Data.cons b1 b2)) l') (b := Data.cons c u') (by simp)
      (Eval.elim_cons (i := 0) (a := Data.cons Data.nil (Data.cons b1 b2)) (b := l') (by simp)
      (Eval.elim_cons (i := 3) (a := c) (b := u') (by simp)
      (Eval.elim_cons (i := 2) (a := Data.nil) (b := Data.cons b1 b2) (by simp)
      (Eval.elim_nil (i := 0) (by simp)
      (Eval.elim_cons (i := 1) (a := b1) (b := b2) (by simp)
      ((Eval.cons (Eval.nil _) (Eval.nil _))))))))⟩
    cost_omega
  · refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := Data.cons (Data.cons (Data.cons a1 a2) Data.nil) l') (b := Data.cons c u') (by simp)
      (Eval.elim_cons (i := 0) (a := Data.cons (Data.cons a1 a2) Data.nil) (b := l') (by simp)
      (Eval.elim_cons (i := 3) (a := c) (b := u') (by simp)
      (Eval.elim_cons (i := 2) (a := Data.cons a1 a2) (b := Data.nil) (by simp)
      (Eval.elim_cons (i := 0) (a := a1) (b := a2) (by simp)
      ((Eval.cons (Eval.nil _) (Eval.nil _)))))))⟩
    cost_omega
  · refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := Data.cons (Data.cons (Data.cons a1 a2) (Data.cons b1 b2)) l') (b := Data.cons c u') (by simp)
      (Eval.elim_cons (i := 0) (a := Data.cons (Data.cons a1 a2) (Data.cons b1 b2)) (b := l') (by simp)
      (Eval.elim_cons (i := 3) (a := c) (b := u') (by simp)
      (Eval.elim_cons (i := 2) (a := Data.cons a1 a2) (b := Data.cons b1 b2) (by simp)
      (Eval.elim_cons (i := 0) (a := a1) (b := a2) (by simp)
      ((Eval.cons (Eval.nil _) (Eval.nil _)))))))⟩
    cost_omega

/-- The bounded bit walk computes `bitWalk l u`, in time `(|u| + 1) · (S + 21)` for `S`
dominating the sizes of `l` and `u`: linear in the input, times the budget. -/
theorem bitWalkProg_runs (l u : Data) (env : Env) (S : ℕ) (hS : l.size + u.size ≤ S) :
    ∃ t ≤ (u.spine + 1) * (S + 21),
      Eval (Data.cons l u :: env) bitWalkProg (bitWalk l u) t := by
  induction l generalizing u with
  | nil =>
    obtain ⟨t, ht, hrun⟩ := bitWalkBody_lnil u
    have hstop := Eval.loop_stop (Eval.append_of_wellScoped hrun bitWalkBody_wellScoped env)
    refine ⟨t + 1, ?_, by simpa [bitWalk, bitWalkProg] using hstop⟩
    have : S + 21 ≤ (u.spine + 1) * (S + 21) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  | cons h l' _ ih =>
    cases u with
    | nil =>
      obtain ⟨t, ht, hrun⟩ := bitWalkBody_unil h l'
      have hstop := Eval.loop_stop (Eval.append_of_wellScoped hrun bitWalkBody_wellScoped env)
      refine ⟨t + 1, ?_, by simpa [bitWalk, bitWalkProg] using hstop⟩
      simp only [spine_nil, size_cons] at hS ht ⊢
      omega
    | cons c u' =>
      rcases hb : isBit h
      · obtain ⟨t, ht, hrun⟩ := bitWalkBody_fail h l' c u' hb
        have hstop := Eval.loop_stop (Eval.append_of_wellScoped hrun bitWalkBody_wellScoped env)
        refine ⟨t + 1, ?_, by simpa [bitWalk, hb, bitWalkProg] using hstop⟩
        have : S + 21 ≤ (spine (Data.cons c u') + 1) * (S + 21) :=
          Nat.le_mul_of_pos_left _ (by omega)
        omega
      · obtain ⟨t, ht, hrun⟩ := bitWalkBody_step h l' c u' hb
        have hS' : l'.size + u'.size ≤ S := by
          simp only [size_cons] at hS; have := size_pos h; have := size_pos c; omega
        obtain ⟨t', ht', hrun'⟩ := ih u' hS'
        refine ⟨t + t' + 1, ?_, ?_⟩
        · have h2 : (spine (Data.cons c u') + 1) * (S + 21) =
              (u'.spine + 1) * (S + 21) + (S + 21) := by
            simp only [spine_cons]; ring
          simp only [size_cons] at hS
          omega
        · have := Eval.loop_step (Eval.append_of_wellScoped hrun bitWalkBody_wellScoped env) hrun'
          simpa [bitWalk, hb, bitWalkProg] using this

/-! ## Equality of bit lists -/

/-- Body of `eqBitsProg`, on the state `cons l₁ l₂`. -/
def eqBitsBody : Prog :=
  .elim 0 .nil
    (.elim 0 (.elim 1 (.cons .nil (.cons .nil .nil)) (.cons .nil .nil))
      (.elim 3 (.cons .nil .nil)
        (.elim 2 (.elim 0 (.cons (.cons .nil .nil) (.cons (.var 3) (.var 1))) (.cons .nil .nil))
          (.elim 2 (.cons .nil .nil) (.cons (.cons .nil .nil) (.cons (.var 7) (.var 5)))))))

/-- Equality of two bit lists: on `cons l₁ l₂`, compute `encode (eqBits l₁ l₂)`. -/
def eqBitsProg : Prog := .loop eqBitsBody

theorem eqBitsBody_wellScoped : eqBitsBody.WellScoped 1 := by
  simp [eqBitsBody, WellScoped]

theorem eqBitsProg_wellScoped : eqBitsProg.WellScoped 1 :=
  ⟨Nat.zero_lt_one, eqBitsBody_wellScoped⟩

theorem eqBitsBody_nil_nil  :
    ∃ t ≤ 20, Eval [Data.cons Data.nil Data.nil] eqBitsBody (Data.cons Data.nil (encode true)) t := by
  refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := Data.nil) (b := Data.nil) (by simp)
    (Eval.elim_nil (i := 0) (by simp)
    (Eval.elim_nil (i := 1) (by simp)
    (Eval.cons (Eval.nil _) (Eval.cons (Eval.nil _) (Eval.nil _)))))⟩
  cost_omega

theorem eqBitsBody_nil_cons (h₂ l₂ : Data) :
    ∃ t ≤ 20, Eval [Data.cons Data.nil (Data.cons h₂ l₂)] eqBitsBody (Data.cons Data.nil (encode false)) t := by
  refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := Data.nil) (b := Data.cons h₂ l₂) (by simp)
    (Eval.elim_nil (i := 0) (by simp)
    (Eval.elim_cons (i := 1) (a := h₂) (b := l₂) (by simp)
    (Eval.cons (Eval.nil _) (Eval.nil _))))⟩
  cost_omega

theorem eqBitsBody_cons_nil (h₁ l₁ : Data) :
    ∃ t ≤ 20, Eval [Data.cons (Data.cons h₁ l₁) Data.nil] eqBitsBody (Data.cons Data.nil (encode false)) t := by
  refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := Data.cons h₁ l₁) (b := Data.nil) (by simp)
    (Eval.elim_cons (i := 0) (a := h₁) (b := l₁) (by simp)
    (Eval.elim_nil (i := 3) (by simp)
    (Eval.cons (Eval.nil _) (Eval.nil _))))⟩
  cost_omega

theorem eqBitsBody_cons_cons (h₁ l₁ h₂ l₂ : Data) :
    ∃ t ≤ l₁.size + l₂.size + 20,
      Eval [Data.cons (Data.cons h₁ l₁) (Data.cons h₂ l₂)] eqBitsBody
        (if bitOf h₁ = bitOf h₂ then Data.cons (Data.cons Data.nil Data.nil) (Data.cons l₁ l₂)
          else Data.cons Data.nil (encode false)) t := by
  rcases h₁ with _ | ⟨a1, a2⟩ <;> rcases h₂ with _ | ⟨b1, b2⟩
  · simp only [bitOf, if_true]
    refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := Data.cons Data.nil l₁) (b := Data.cons Data.nil l₂) (by simp)
      (Eval.elim_cons (i := 0) (a := Data.nil) (b := l₁) (by simp)
      (Eval.elim_cons (i := 3) (a := Data.nil) (b := l₂) (by simp)
      (Eval.elim_nil (i := 2) (by simp)
      (Eval.elim_nil (i := 0) (by simp)
      (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _)) (Eval.cons (Eval.var_of_get (i := 3) (v := l₁) (by simp)) (Eval.var_of_get (i := 1) (v := l₂) (by simp))))))))⟩
    cost_omega
  · simp only [bitOf, Bool.false_eq_true, if_false]
    refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := Data.cons Data.nil l₁) (b := Data.cons (Data.cons b1 b2) l₂) (by simp)
      (Eval.elim_cons (i := 0) (a := Data.nil) (b := l₁) (by simp)
      (Eval.elim_cons (i := 3) (a := Data.cons b1 b2) (b := l₂) (by simp)
      (Eval.elim_nil (i := 2) (by simp)
      (Eval.elim_cons (i := 0) (a := b1) (b := b2) (by simp)
      (Eval.cons (Eval.nil _) (Eval.nil _))))))⟩
    cost_omega
  · simp only [bitOf, Bool.true_eq_false, if_false]
    refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := Data.cons (Data.cons a1 a2) l₁) (b := Data.cons Data.nil l₂) (by simp)
      (Eval.elim_cons (i := 0) (a := Data.cons a1 a2) (b := l₁) (by simp)
      (Eval.elim_cons (i := 3) (a := Data.nil) (b := l₂) (by simp)
      (Eval.elim_cons (i := 2) (a := a1) (b := a2) (by simp)
      (Eval.elim_nil (i := 2) (by simp)
      (Eval.cons (Eval.nil _) (Eval.nil _))))))⟩
    cost_omega
  · simp only [bitOf, if_true]
    refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := Data.cons (Data.cons a1 a2) l₁) (b := Data.cons (Data.cons b1 b2) l₂) (by simp)
      (Eval.elim_cons (i := 0) (a := Data.cons a1 a2) (b := l₁) (by simp)
      (Eval.elim_cons (i := 3) (a := Data.cons b1 b2) (b := l₂) (by simp)
      (Eval.elim_cons (i := 2) (a := a1) (b := a2) (by simp)
      (Eval.elim_cons (i := 2) (a := b1) (b := b2) (by simp)
      (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _)) (Eval.cons (Eval.var_of_get (i := 7) (v := l₁) (by simp)) (Eval.var_of_get (i := 5) (v := l₂) (by simp))))))))⟩
    cost_omega

/-- `eqBitsProg` computes `eqBits l₁ l₂`, in time `(|l₁| + 1) · (S + 21)` for `S` dominating
the sizes. -/
theorem eqBitsProg_runs (l₁ l₂ : Data) (env : Env) (S : ℕ) (hS : l₁.size + l₂.size ≤ S) :
    ∃ t ≤ (l₁.spine + 1) * (S + 21),
      Eval (Data.cons l₁ l₂ :: env) eqBitsProg (encode (eqBits l₁ l₂)) t := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil =>
      obtain ⟨t, ht, hrun⟩ := eqBitsBody_nil_nil
      have := Eval.loop_stop (Eval.append_of_wellScoped hrun eqBitsBody_wellScoped env)
      exact ⟨t + 1, by simp only [spine_nil]; omega, by simpa [eqBits, eqBitsProg] using this⟩
    | cons h₂ l₂ =>
      obtain ⟨t, ht, hrun⟩ := eqBitsBody_nil_cons h₂ l₂
      have := Eval.loop_stop (Eval.append_of_wellScoped hrun eqBitsBody_wellScoped env)
      exact ⟨t + 1, by simp only [spine_nil]; omega, by simpa [eqBits, eqBitsProg] using this⟩
  | cons h₁ l₁ _ ih =>
    cases l₂ with
    | nil =>
      obtain ⟨t, ht, hrun⟩ := eqBitsBody_cons_nil h₁ l₁
      have hstop := Eval.loop_stop (Eval.append_of_wellScoped hrun eqBitsBody_wellScoped env)
      refine ⟨t + 1, ?_, by simpa [eqBits, eqBitsProg] using hstop⟩
      have : S + 21 ≤ (spine (Data.cons h₁ l₁) + 1) * (S + 21) := Nat.le_mul_of_pos_left _ (by omega)
      omega
    | cons h₂ l₂ =>
      obtain ⟨t, ht, hrun⟩ := eqBitsBody_cons_cons h₁ l₁ h₂ l₂
      by_cases hb : bitOf h₁ = bitOf h₂
      · rw [if_pos hb] at hrun
        have hS' : l₁.size + l₂.size ≤ S := by
          simp only [size_cons] at hS; have := size_pos h₁; have := size_pos h₂; omega
        obtain ⟨t', ht', hrun'⟩ := ih l₂ hS'
        refine ⟨t + t' + 1, ?_, ?_⟩
        · have h2 : (spine (Data.cons h₁ l₁) + 1) * (S + 21) =
              (l₁.spine + 1) * (S + 21) + (S + 21) := by
            simp only [spine_cons]; ring
          simp only [size_cons] at hS
          omega
        · have := Eval.loop_step (Eval.append_of_wellScoped hrun eqBitsBody_wellScoped env) hrun'
          simpa [eqBits, hb, eqBitsProg] using this
      · rw [if_neg hb] at hrun
        have hbeq : (bitOf h₁ == bitOf h₂) = false := beq_eq_false_iff_ne.2 hb
        have hstop := Eval.loop_stop (Eval.append_of_wellScoped hrun eqBitsBody_wellScoped env)
        refine ⟨t + 1, ?_, by simpa [eqBits, hbeq, eqBitsProg] using hstop⟩
        have : S + 21 ≤ (spine (Data.cons h₁ l₁) + 1) * (S + 21) :=
          Nat.le_mul_of_pos_left _ (by omega)
        simp only [size_cons] at hS
        omega

/-! ## Normalization of the parameter -/

/-- Body of the canonicity walk, on the state `cons rest last`. -/
def canonBody : Prog :=
  .elim 0 .nil
    (.elim 0 (.cons .nil (.var 1))
      (.elim 0 (.cons (.cons .nil .nil) (.cons (.var 1) .nil))
        (.elim 0 (.elim 1 (.cons (.cons .nil .nil) (.cons (.var 3) (.cons .nil .nil)))
            (.cons .nil .nil))
          (.cons .nil .nil))))

/-- `normBinProg` on `d` computes `normBin d`: the input itself if it is a canonical binary
numeral, `nil` otherwise. -/
def normBinProg : Prog :=
  .let_ (.let_ (.cons (.var 0) (.cons .nil .nil)) (.loop canonBody)) (.elim 0 .nil (.var 3))

theorem canonBody_wellScoped : canonBody.WellScoped 1 := by
  simp [canonBody, WellScoped]

theorem normBinProg_wellScoped : normBinProg.WellScoped 1 := by
  simp [normBinProg, WellScoped, canonBody]

theorem canonBody_nil (last : Data) :
    ∃ t ≤ last.size + 20, Eval [Data.cons Data.nil last] canonBody (Data.cons Data.nil last) t := by
  refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := Data.nil) (b := last) (by simp)
    (Eval.elim_nil (i := 0) (by simp)
    (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 1) (v := last) (by simp))))⟩
  cost_omega

theorem canonBody_step (h r last : Data) :
    ∃ t ≤ r.size + 20,
      Eval [Data.cons (Data.cons h r) last] canonBody
        (match h with
          | Data.nil => Data.cons (Data.cons Data.nil Data.nil) (Data.cons r Data.nil)
          | Data.cons Data.nil Data.nil =>
              Data.cons (Data.cons Data.nil Data.nil) (Data.cons r (Data.cons Data.nil Data.nil))
          | _ => Data.cons Data.nil Data.nil) t := by
  rcases h with _ | ⟨_ | ⟨a1, a2⟩, _ | ⟨b1, b2⟩⟩
  · refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := Data.cons Data.nil r) (b := last) (by simp)
      (Eval.elim_cons (i := 0) (a := Data.nil) (b := r) (by simp)
      (Eval.elim_nil (i := 0) (by simp)
      (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _)) (Eval.cons (Eval.var_of_get (i := 1) (v := r) (by simp)) (Eval.nil _)))))⟩
    cost_omega
  · refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := Data.cons (Data.cons Data.nil Data.nil) r) (b := last) (by simp)
      (Eval.elim_cons (i := 0) (a := Data.cons Data.nil Data.nil) (b := r) (by simp)
      (Eval.elim_cons (i := 0) (a := Data.nil) (b := Data.nil) (by simp)
      (Eval.elim_nil (i := 0) (by simp)
      (Eval.elim_nil (i := 1) (by simp)
      (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _)) (Eval.cons (Eval.var_of_get (i := 3) (v := r) (by simp)) (Eval.cons (Eval.nil _) (Eval.nil _))))))))⟩
    cost_omega
  · refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := Data.cons (Data.cons Data.nil (Data.cons b1 b2)) r) (b := last) (by simp)
      (Eval.elim_cons (i := 0) (a := Data.cons Data.nil (Data.cons b1 b2)) (b := r) (by simp)
      (Eval.elim_cons (i := 0) (a := Data.nil) (b := Data.cons b1 b2) (by simp)
      (Eval.elim_nil (i := 0) (by simp)
      (Eval.elim_cons (i := 1) (a := b1) (b := b2) (by simp)
      (Eval.cons (Eval.nil _) (Eval.nil _))))))⟩
    cost_omega
  · refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := Data.cons (Data.cons (Data.cons a1 a2) Data.nil) r) (b := last) (by simp)
      (Eval.elim_cons (i := 0) (a := Data.cons (Data.cons a1 a2) Data.nil) (b := r) (by simp)
      (Eval.elim_cons (i := 0) (a := Data.cons a1 a2) (b := Data.nil) (by simp)
      (Eval.elim_cons (i := 0) (a := a1) (b := a2) (by simp)
      (Eval.cons (Eval.nil _) (Eval.nil _)))))⟩
    cost_omega
  · refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := Data.cons (Data.cons (Data.cons a1 a2) (Data.cons b1 b2)) r) (b := last) (by simp)
      (Eval.elim_cons (i := 0) (a := Data.cons (Data.cons a1 a2) (Data.cons b1 b2)) (b := r) (by simp)
      (Eval.elim_cons (i := 0) (a := Data.cons a1 a2) (b := Data.cons b1 b2) (by simp)
      (Eval.elim_cons (i := 0) (a := a1) (b := a2) (by simp)
      (Eval.cons (Eval.nil _) (Eval.nil _)))))⟩
    cost_omega

/-- The canonicity loop computes `canonWalk d last`, in time `(|d| + 1) · (S + 21)`. -/
theorem canonLoop_runs (d : Data) (last : Bool) (env : Env) (S : ℕ) (hS : d.size + 3 ≤ S) :
    ∃ t ≤ (d.spine + 1) * (S + 21),
      Eval (Data.cons d (encode last) :: env) (.loop canonBody) (encode (canonWalk d last)) t := by
  induction d generalizing last with
  | nil =>
    obtain ⟨t, ht, hrun⟩ := canonBody_nil (encode last)
    have hstop := Eval.loop_stop (Eval.append_of_wellScoped hrun canonBody_wellScoped env)
    refine ⟨t + 1, ?_, by simpa [canonWalk] using hstop⟩
    have : (encode last : Data).size ≤ 3 := by cases last <;> simp [encode_bool, ofBool]
    simp only [spine_nil, size_nil] at hS ⊢
    omega
  | cons h r _ ih =>
    obtain ⟨t, ht, hrun⟩ := canonBody_step h r (encode last)
    have hS' : r.size + 3 ≤ S := by simp only [size_cons] at hS; have := size_pos h; omega
    have hle : S + 21 ≤ (spine (Data.cons h r) + 1) * (S + 21) :=
      Nat.le_mul_of_pos_left _ (by omega)
    have h2 : (spine (Data.cons h r) + 1) * (S + 21) = (r.spine + 1) * (S + 21) + (S + 21) := by
      simp only [spine_cons]; ring
    rcases h with _ | ⟨_ | ⟨a1, a2⟩, _ | ⟨b1, b2⟩⟩
    · obtain ⟨t', ht', hrun'⟩ := ih false hS'
      refine ⟨t + t' + 1, by simp only [size_cons] at hS; omega, ?_⟩
      have := Eval.loop_step (Eval.append_of_wellScoped hrun canonBody_wellScoped env)
        (by simpa [encode_bool] using hrun')
      simpa [canonWalk, encode_bool] using this
    · obtain ⟨t', ht', hrun'⟩ := ih true hS'
      refine ⟨t + t' + 1, by simp only [size_cons] at hS; omega, ?_⟩
      have := Eval.loop_step (Eval.append_of_wellScoped hrun canonBody_wellScoped env)
        (by simpa [encode_bool] using hrun')
      simpa [canonWalk, encode_bool] using this
    all_goals
      refine ⟨t + 1, by simp only [size_cons] at hS; omega, ?_⟩
      have := Eval.loop_stop (Eval.append_of_wellScoped hrun canonBody_wellScoped env)
      simpa [canonWalk, encode_bool, ofBool] using this

/-- `normBinProg` computes the normalization, in time `(|d| + 2) · (|d| + 25) + 3 |d| + 10`. -/
theorem normBinProg_runs (d : Data) :
    ∃ t ≤ (d.spine + 2) * (d.size + 25) + 3 * d.size + 10,
      normBinProg.Runs d (normBin d) t := by
  obtain ⟨t, ht, hrun⟩ := canonLoop_runs d true [d] (d.size + 3) le_rfl
  have hpre := Eval.cons (Eval.var_of_get (env := [d]) (i := 0) (v := d) (by simp))
    (Eval.cons (Eval.nil [d]) (Eval.nil [d]))
  have hloop := Eval.let_ hpre hrun
  rw [canonWalk_eq_isCanonBin] at hloop
  have hmul : (d.spine + 1) * (d.size + 3 + 21) ≤ (d.spine + 2) * (d.size + 25) :=
    Nat.mul_le_mul (by omega) (by omega)
  unfold normBin
  rcases hc : isCanonBin d
  · rw [hc] at hloop
    have hget : Env.get [encode false, d] 0 = Data.nil := by simp [encode_bool, ofBool]
    refine ⟨_, ?_, Eval.let_ hloop (Eval.elim_nil (i := 0) hget (Eval.nil _))⟩
    omega
  · rw [hc] at hloop
    have hget : Env.get [encode true, d] 0 = Data.cons Data.nil Data.nil := by
      simp [encode_bool, ofBool]
    refine ⟨_, ?_, Eval.let_ hloop (Eval.elim_cons (i := 0) (a := Data.nil) (b := Data.nil) hget
      (Eval.var_of_get (env := [Data.nil, Data.nil, encode true, d]) (i := 3) (v := d) (by simp)))⟩
    omega

end Prog

end MIPRE.Cost

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.SAT.GateProg
import MIPRE.Foundations.SAT.ArrayProg
import MIPRE.Foundations.SAT.InputRouting

/-!
# Effective lookup of the preceding input copy

The field evaluator scans the already supplied gate/value pairs. A read of
input `i` uses the last value attached to an earlier input gate for `i`, or
the external input value if there is no such gate. Binary indices are compared
directly; malformed large indices never cause unary expansion.
-/

namespace MIPRE.SAT.Circuit

open Cost Cost.PolyTimeFun Polynomial

/-- Test whether a gate reads the specified external input. -/
noncomputable def matchesInputProg : PolyTimeFun (ℕ × Gate) Bool :=
  congr (MIPRE.SAT.PolyTimeFun.casesGate ArrayProg.eqNat
    (const false) (const false) (const false) (const false))
    (fun p => decide (p.2 = .input p.1)) (by
      rintro ⟨i, g⟩
      cases g with
      | input j => change decide (i = j) = decide (Gate.input j = Gate.input i); simp [eq_comm]
      | const b => rfl
      | and u v => rfl
      | or u v => rfl
      | not u => rfl)

@[simp] theorem matchesInputProg_apply (p : ℕ × Gate) :
    matchesInputProg p = decide (p.2 = .input p.1) := rfl

variable {α : Type*} [SizedEncoding α]

/-- Last supplied value of an input gate for `i`, with a supplied initial value. -/
def lastInputValue (l : List (Gate × α)) (i : ℕ) (initial : α) : α :=
  l.foldl (fun acc p => if p.1 = .input i then p.2 else acc) initial

@[simp] theorem lastInputValue_append (l r : List (Gate × α)) (i : ℕ) (a : α) :
    lastInputValue (l ++ r) i a = lastInputValue r i (lastInputValue l i a) := by
  exact List.foldl_append

/-- The executable scan reads exactly the variable selected by input-copy routing. -/
theorem lastInputValue_range (C : Circuit) (k i : ℕ) (x w : ℕ → α) :
    lastInputValue ((List.range k).map (fun j => (C.gates.getD j (.const false), w j)))
      i (x i) = Sum.elim x w (C.inputRef k i) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.map_append, lastInputValue_append]
    change (if C.gates.getD k (.const false) = .input i then w k else
      lastInputValue ((List.range k).map (fun j => (C.gates.getD j (.const false), w j)))
        i (x i)) = _
    rw [ih]
    by_cases h : C.gates.getD k (.const false) = .input i
    · simp only [inputRef, inputOwner]; simp only [h, if_true]; simp
    · simp only [inputRef, inputOwner]; simp only [h, if_false]

private def inputStep (s : ℕ × α) (p : Gate × α) : ℕ × α :=
  (s.1, if p.1 = .input s.1 then p.2 else s.2)

private noncomputable def inputStepProg : PolyTimeFun ((ℕ × α) × (Gate × α)) (ℕ × α) :=
  congr ((fst.comp fst).pair
    (ite (ap₂ matchesInputProg (fst.comp fst) (fst.comp snd)) (snd.comp snd) (snd.comp fst)))
    (fun p => inputStep p.1 p.2) (by intro p; simp [inputStep])

private theorem fold_inputStep (l : List (Gate × α)) (i : ℕ) (initial : α) :
    l.foldl inputStep (i, initial) = (i, lastInputValue l i initial) := by
  induction l generalizing initial with
  | nil => rfl
  | cons p l ih =>
    simp only [List.foldl_cons, inputStep, ih, lastInputValue]

/-- The last-input-value scan, with an ambient polynomial running-time proof. -/
noncomputable def lastInputValueProg : PolyTimeFun ((ℕ × α) × List (Gate × α)) α :=
  let scan := foldlAdd inputStepProg X (by
    rintro ⟨i, a⟩ ⟨g, b⟩
    change esize (inputStep (i, a) (g, b)) ≤ _
    simp only [inputStep, esize_prod, Polynomial.eval_X]
    split_ifs <;> omega)
  congr (snd.comp (scan.comp (snd.pair fst)))
    (fun p => lastInputValue p.2 p.1.1 p.1.2) (by
      rintro ⟨⟨i, a⟩, l⟩
      change (l.foldl inputStep (i, a)).2 = _
      rw [fold_inputStep])

@[simp] theorem lastInputValueProg_apply (p : (ℕ × α) × List (Gate × α)) :
    lastInputValueProg p = lastInputValue p.2 p.1.1 p.1.2 := rfl

end MIPRE.SAT.Circuit

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fin.Basic

/-!
# Canonical observation indexing for coded machines

An *observation* of an `i`-input machine with `w` work tapes over the alphabet `Fin σ` is
a triple `(q, as, bs)` of a state `q : Fin Q`, the tuple `as` of symbols under the input
heads, and the tuple `bs` of symbols under the work heads (each an `Option (Fin σ)`,
`none` being the blank). This file fixes, once and for all, the bijection between
observations and positions in a dense transition table.

## Normative order

This order is normative: the serialization format (Milestone C) and the universal
machine's table lookup (Milestones E–G) cite it, and it must never change.

* `transitionIndex q as bs = q * (σ + 1) ^ (i + w) + obs`, where `obs` is the Horner
  evaluation (`Turing.encodeDigits`), in radix `σ + 1`, of the digit string consisting of
  the input-tape symbols in ascending tape order followed by the work-tape symbols in
  ascending tape order — input tape `0` is the *most* significant digit;
* the digit of the blank `none` is `0`, and the digit of the symbol `a : Fin σ` is
  `a + 1` (`Turing.encodeSymbol?`).

Nothing here depends on `Fintype.elems`, hash or enumeration order, a chosen basis, or
choice: the order is fixed by the explicit recursions below (decision D5 of
`planning/tm-infrastructure.md`; deliberately not `finFunctionFinEquiv`, whose digit
order is owned by Mathlib). Both inverse laws are proved for symbols, observations, and
transition indices; the decode direction is consumed by the Milestone C parser and by the
universal machine.
-/

namespace Turing

/-! ## Digit strings -/

/-- Horner evaluation of a digit string in radix `r + 1`; the *first* digit is the most
significant one. -/
def encodeDigits {r : ℕ} : List (Fin (r + 1)) → ℕ
  | [] => 0
  | a :: l => a.val * (r + 1) ^ l.length + encodeDigits l

@[simp]
theorem encodeDigits_nil {r : ℕ} : encodeDigits (r := r) [] = 0 := rfl

theorem encodeDigits_cons {r : ℕ} (a : Fin (r + 1)) (l : List (Fin (r + 1))) :
    encodeDigits (a :: l) = a.val * (r + 1) ^ l.length + encodeDigits l := rfl

/-- A digit string of length `len` encodes a number below `(r + 1) ^ len`. -/
theorem encodeDigits_lt {r : ℕ} :
    ∀ l : List (Fin (r + 1)), encodeDigits l < (r + 1) ^ l.length
  | [] => by simp
  | a :: l => by
    have ih := encodeDigits_lt l
    calc encodeDigits (a :: l)
        = a.val * (r + 1) ^ l.length + encodeDigits l := rfl
      _ < a.val * (r + 1) ^ l.length + (r + 1) ^ l.length := by omega
      _ = (a.val + 1) * (r + 1) ^ l.length := by rw [Nat.succ_mul]
      _ ≤ (r + 1) * (r + 1) ^ l.length := Nat.mul_le_mul a.isLt (Nat.le_refl _)
      _ = (r + 1) ^ (a :: l).length := by
          rw [List.length_cons, Nat.pow_succ, Nat.mul_comm]

/-- Decode `len` digits (most significant first) from a natural number. -/
def decodeDigits (r : ℕ) : ℕ → ℕ → List (Fin (r + 1))
  | 0, _ => []
  | len + 1, n =>
    ⟨n / (r + 1) ^ len % (r + 1), Nat.mod_lt _ (by omega)⟩ ::
      decodeDigits r len (n % (r + 1) ^ len)

@[simp]
theorem decodeDigits_length (r len n : ℕ) : (decodeDigits r len n).length = len := by
  induction len generalizing n with
  | zero => rfl
  | succ len ih => simp [decodeDigits, ih]

/-- Decoding inverts encoding on digit strings. -/
theorem decodeDigits_encodeDigits {r : ℕ} :
    ∀ l : List (Fin (r + 1)), decodeDigits r l.length (encodeDigits l) = l
  | [] => rfl
  | a :: l => by
    have hlt := encodeDigits_lt l
    have hB : 0 < (r + 1) ^ l.length := Nat.pow_pos (by omega)
    have hdiv : encodeDigits (a :: l) / (r + 1) ^ l.length = a.val := by
      rw [encodeDigits_cons, Nat.mul_comm, Nat.mul_add_div hB, Nat.div_eq_of_lt hlt,
        Nat.add_zero]
    have hmod : encodeDigits (a :: l) % (r + 1) ^ l.length = encodeDigits l := by
      rw [encodeDigits_cons, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
    show decodeDigits r (l.length + 1) (encodeDigits (a :: l)) = a :: l
    simp only [decodeDigits]
    congr 1
    · refine Fin.ext ?_
      show encodeDigits (a :: l) / (r + 1) ^ l.length % (r + 1) = a.val
      rw [hdiv, Nat.mod_eq_of_lt a.isLt]
    · rw [hmod]
      exact decodeDigits_encodeDigits l

/-- Encoding inverts decoding on numbers below `(r + 1) ^ len`. -/
theorem encodeDigits_decodeDigits (r : ℕ) :
    ∀ (len n : ℕ), n < (r + 1) ^ len → encodeDigits (decodeDigits r len n) = n
  | 0, n, h => by
    rw [Nat.pow_zero] at h
    simp only [decodeDigits, encodeDigits_nil]
    omega
  | len + 1, n, h => by
    have hB : 0 < (r + 1) ^ len := Nat.pow_pos (by omega)
    have hdivlt : n / (r + 1) ^ len < r + 1 := by
      rw [Nat.div_lt_iff_lt_mul hB, Nat.mul_comm]
      rw [Nat.pow_succ] at h
      exact h
    simp only [decodeDigits, encodeDigits_cons, decodeDigits_length]
    rw [encodeDigits_decodeDigits r len (n % (r + 1) ^ len) (Nat.mod_lt _ hB),
      Nat.mod_eq_of_lt hdivlt, Nat.mul_comm (n / (r + 1) ^ len) ((r + 1) ^ len)]
    exact Nat.div_add_mod n ((r + 1) ^ len)

/-! ## Symbol digits -/

variable {σ i w Q : ℕ}

/-- The digit of an optional symbol: blank `none` is `0`, symbol `a` is `a + 1`. -/
def encodeSymbol? : Option (Fin σ) → Fin (σ + 1)
  | none => 0
  | some a => a.succ

/-- Recover an optional symbol from its digit. -/
def decodeSymbol? (d : Fin (σ + 1)) : Option (Fin σ) :=
  if h : d.val = 0 then none else some ⟨d.val - 1, by have := d.isLt; omega⟩

@[simp]
theorem decodeSymbol?_encodeSymbol? (a : Option (Fin σ)) :
    decodeSymbol? (encodeSymbol? a) = a := by
  cases a with
  | none => simp [decodeSymbol?, encodeSymbol?]
  | some a => simp [decodeSymbol?, encodeSymbol?]

@[simp]
theorem encodeSymbol?_decodeSymbol? (d : Fin (σ + 1)) :
    encodeSymbol? (decodeSymbol? d) = d := by
  unfold decodeSymbol?
  split
  · next h => exact Fin.ext (by simp [encodeSymbol?, h])
  · next h =>
    simp only [encodeSymbol?]
    exact Fin.ext (by simp; omega)

/-! ## Observations -/

/-- The digit string of an observation: input symbols then work symbols, both in
ascending tape order, input tape `0` most significant. -/
def observationDigits (as : Fin i → Option (Fin σ)) (bs : Fin w → Option (Fin σ)) :
    List (Fin (σ + 1)) :=
  (List.ofFn fun j => encodeSymbol? (as j)) ++ (List.ofFn fun d => encodeSymbol? (bs d))

@[simp]
theorem observationDigits_length (as : Fin i → Option (Fin σ))
    (bs : Fin w → Option (Fin σ)) :
    (observationDigits as bs).length = i + w := by
  simp [observationDigits]

/-- The canonical position of an observation's symbol part, below `(σ + 1) ^ (i + w)`. -/
def encodeObservation (as : Fin i → Option (Fin σ)) (bs : Fin w → Option (Fin σ)) :
    Fin ((σ + 1) ^ (i + w)) :=
  ⟨encodeDigits (observationDigits as bs), by
    have h := encodeDigits_lt (observationDigits as bs)
    rwa [observationDigits_length] at h⟩

/-- Recover the symbol tuples from an observation position. -/
def decodeObservation (n : Fin ((σ + 1) ^ (i + w))) :
    (Fin i → Option (Fin σ)) × (Fin w → Option (Fin σ)) :=
  (fun j => decodeSymbol? ((decodeDigits σ (i + w) n.val)[j.val]'
      (by have := j.isLt; simp only [decodeDigits_length]; omega)),
   fun d => decodeSymbol? ((decodeDigits σ (i + w) n.val)[i + d.val]'
      (by have := d.isLt; simp only [decodeDigits_length]; omega)))

/-- Decoding inverts encoding on observations. -/
@[simp]
theorem decodeObservation_encodeObservation (as : Fin i → Option (Fin σ))
    (bs : Fin w → Option (Fin σ)) :
    decodeObservation (encodeObservation as bs) = (as, bs) := by
  have hdec : decodeDigits σ (i + w) (encodeObservation as bs).val =
      observationDigits as bs := by
    rw [show (encodeObservation as bs).val = encodeDigits (observationDigits as bs)
        from rfl, ← observationDigits_length as bs]
    exact decodeDigits_encodeDigits _
  unfold decodeObservation
  refine Prod.ext ?_ ?_
  · funext j
    simp only [hdec, observationDigits]
    rw [List.getElem_append_left (by simp)]
    simp
  · funext d
    simp only [hdec, observationDigits]
    rw [List.getElem_append_right (by simp)]
    simp

/-- Encoding inverts decoding on observation positions. -/
@[simp]
theorem encodeObservation_decodeObservation (n : Fin ((σ + 1) ^ (i + w))) :
    encodeObservation (decodeObservation n).1 (decodeObservation n).2 = n := by
  have hL : observationDigits (decodeObservation n).1 (decodeObservation n).2 =
      decodeDigits σ (i + w) n.val := by
    refine List.ext_getElem (by simp) ?_
    intro k hk hk'
    simp only [decodeDigits_length] at hk'
    by_cases hki : k < i
    · simp only [observationDigits]
      rw [List.getElem_append_left (by simpa using hki)]
      simp only [List.getElem_ofFn]
      unfold decodeObservation
      simp
    · simp only [observationDigits]
      rw [List.getElem_append_right (by simpa using hki)]
      simp only [List.getElem_ofFn]
      unfold decodeObservation
      simp only [encodeSymbol?_decodeSymbol?]
      congr 1
      simp
      omega
  refine Fin.ext ?_
  show encodeDigits (observationDigits _ _) = n.val
  rw [hL]
  exact encodeDigits_decodeDigits σ (i + w) n.val n.isLt

/-! ## Transition indices -/

/-- The canonical position of an observation in a dense transition table:
`q * (σ + 1) ^ (i + w) + obs`. This order is normative (see the module docstring). -/
def transitionIndex (q : Fin Q) (as : Fin i → Option (Fin σ))
    (bs : Fin w → Option (Fin σ)) :
    Fin (Q * (σ + 1) ^ (i + w)) :=
  ⟨q.val * (σ + 1) ^ (i + w) + (encodeObservation as bs).val, by
    have hobs := (encodeObservation as bs).isLt
    calc q.val * (σ + 1) ^ (i + w) + (encodeObservation as bs).val
        < q.val * (σ + 1) ^ (i + w) + (σ + 1) ^ (i + w) := by omega
      _ = (q.val + 1) * (σ + 1) ^ (i + w) := by rw [Nat.succ_mul]
      _ ≤ Q * (σ + 1) ^ (i + w) := Nat.mul_le_mul q.isLt (Nat.le_refl _)⟩

/-- Recover the observation from its position in a dense transition table. -/
def decodeTransitionIndex (n : Fin (Q * (σ + 1) ^ (i + w))) :
    Fin Q × (Fin i → Option (Fin σ)) × (Fin w → Option (Fin σ)) :=
  (⟨n.val / (σ + 1) ^ (i + w),
      (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by omega))).mpr n.isLt⟩,
   decodeObservation ⟨n.val % (σ + 1) ^ (i + w), Nat.mod_lt _ (Nat.pow_pos (by omega))⟩)

/-- Decoding inverts encoding on transition indices. -/
@[simp]
theorem decodeTransitionIndex_transitionIndex (q : Fin Q) (as : Fin i → Option (Fin σ))
    (bs : Fin w → Option (Fin σ)) :
    decodeTransitionIndex (transitionIndex q as bs) = (q, as, bs) := by
  have hB : 0 < (σ + 1) ^ (i + w) := Nat.pow_pos (by omega)
  have hobs := (encodeObservation as bs).isLt
  have hdiv : (transitionIndex q as bs).val / (σ + 1) ^ (i + w) = q.val := by
    show (q.val * (σ + 1) ^ (i + w) + (encodeObservation as bs).val) / _ = q.val
    rw [Nat.mul_comm, Nat.mul_add_div hB, Nat.div_eq_of_lt hobs, Nat.add_zero]
  have hmod : (transitionIndex q as bs).val % (σ + 1) ^ (i + w) =
      (encodeObservation as bs).val := by
    show (q.val * (σ + 1) ^ (i + w) + (encodeObservation as bs).val) % _ = _
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hobs]
  unfold decodeTransitionIndex
  refine Prod.ext (Fin.ext hdiv) ?_
  have hfin : (⟨(transitionIndex q as bs).val % (σ + 1) ^ (i + w),
      Nat.mod_lt _ (Nat.pow_pos (by omega))⟩ : Fin ((σ + 1) ^ (i + w))) =
      encodeObservation as bs := Fin.ext hmod
  rw [hfin, decodeObservation_encodeObservation]

/-- Encoding inverts decoding on transition-table positions. -/
@[simp]
theorem transitionIndex_decodeTransitionIndex (n : Fin (Q * (σ + 1) ^ (i + w))) :
    transitionIndex (decodeTransitionIndex n).1 (decodeTransitionIndex n).2.1
      (decodeTransitionIndex n).2.2 = n := by
  refine Fin.ext ?_
  show (decodeTransitionIndex n).1.val * (σ + 1) ^ (i + w) +
      (encodeObservation (decodeTransitionIndex n).2.1 (decodeTransitionIndex n).2.2).val
      = n.val
  have h2 : encodeObservation (decodeTransitionIndex n).2.1 (decodeTransitionIndex n).2.2
      = ⟨n.val % (σ + 1) ^ (i + w), Nat.mod_lt _ (Nat.pow_pos (by omega))⟩ := by
    show encodeObservation (decodeObservation _).1 (decodeObservation _).2 = _
    rw [encodeObservation_decodeObservation]
  rw [h2]
  show n.val / (σ + 1) ^ (i + w) * (σ + 1) ^ (i + w) + n.val % (σ + 1) ^ (i + w) = n.val
  rw [Nat.mul_comm]
  exact Nat.div_add_mod n.val ((σ + 1) ^ (i + w))

/-- The transition index determines the observation. -/
theorem transitionIndex_inj {q q' : Fin Q} {as as' : Fin i → Option (Fin σ)}
    {bs bs' : Fin w → Option (Fin σ)}
    (h : transitionIndex q as bs = transitionIndex q' as' bs') :
    q = q' ∧ as = as' ∧ bs = bs' := by
  have h' := congrArg decodeTransitionIndex h
  rw [decodeTransitionIndex_transitionIndex, decodeTransitionIndex_transitionIndex] at h'
  simpa [Prod.ext_iff] using h'

end Turing

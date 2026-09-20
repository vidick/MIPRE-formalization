/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Cost.Iterates
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Linarith

/-! # Polynomial-time unary arithmetic for degree decomposition -/

noncomputable section

namespace MIPRE.LowDegree.DegreeArithmetic

open Cost Cost.PolyTimeFun Polynomial

/-- A list emptiness test, uniform in its element encoding. -/
def isEmptyProg {α : Type*} [SizedEncoding α] : PolyTimeFun (List α) Bool :=
  congr ((casesList (const true) (const false)).comp ((const ()).pair (PolyTimeFun.id _)))
    List.isEmpty (by intro a; cases a <;> rfl)

@[simp] theorem isEmptyProg_apply {α : Type*} [SizedEncoding α] (a : List α) :
    isEmptyProg a = a.isEmpty := rfl

/-- Compare unary integers by removing the second length from the first. -/
def leUnaryProg : PolyTimeFun (Unary × Unary) Bool :=
  congr (isEmptyProg.comp drop) (fun q => decide (q.1.length ≤ q.2.length)) (by
    rintro ⟨u, v⟩
    change (u.drop v.length).isEmpty = decide (u.length ≤ v.length)
    apply Bool.eq_iff_iff.mpr
    simp)

@[simp] theorem leUnaryProg_apply (u v : Unary) :
    leUnaryProg (u, v) = decide (u.length ≤ v.length) := rfl

/-- Exact equality of unary values. -/
def eqUnaryProg : PolyTimeFun (Unary × Unary) Bool :=
  congr (ite leUnaryProg (leUnaryProg.comp (snd.pair fst)) (const false))
    (fun q => decide (q.1.length = q.2.length)) (by
      rintro ⟨u, v⟩
      change (if decide (u.length ≤ v.length) then decide (v.length ≤ u.length) else false) = _
      by_cases h : u.length ≤ v.length <;> simp [Nat.le_antisymm_iff, h])

@[simp] theorem eqUnaryProg_apply (u v : Unary) :
    eqUnaryProg (u, v) = decide (u.length = v.length) := rfl

private abbrev ModState := Unary × Unary

/-- Increment the remainder and reset it when the modulus is reached. -/
def modStep (s : ModState) : ModState :=
  (s.1, if s.2.length + 1 = s.1.length then [] else () :: s.2)

private def modStepProg : PolyTimeFun (ModState × Unit) ModState :=
  let d := fst.comp fst
  let r := snd.comp fst
  d.pair (ite (eqUnaryProg.comp ((cons (const ()) r).pair d)) (const []) (cons (const ()) r))

private theorem modStepProg_apply (s : ModState) (x : Unit) : modStepProg (s, x) = modStep s := by
  rcases s with ⟨d, r⟩
  change (d, if decide ((() :: r).length = d.length) then [] else () :: r) = _
  simp only [List.length_cons, decide_eq_true_eq, modStep]

private theorem modStep_growth (s : ModState) (x : Unit) :
    esize (modStepProg (s, x)) ≤ esize s + (2 : Polynomial ℕ).eval (esize x) := by
  rw [modStepProg_apply]
  rcases s with ⟨d, r⟩
  simp only [modStep]
  split <;> simp only [esize_prod, esize_list_cons, esize_list_nil, eval_ofNat, show esize () = 1 from rfl] <;> omega

/-- One counter step advances a canonical remainder by one modulo the divisor. -/
theorem modStep_mod (d : Unary) (n : ℕ) :
    modStep (d, unary (n % d.length)) = (d, unary ((n + 1) % d.length)) := by
  have hm : (n % d.length + 1) % d.length = (n + 1) % d.length := by
    simp [Nat.add_mod]
  by_cases hd : d.length = 0
  · simp [modStep, hd, unary, List.replicate_succ]
  · have hlt := Nat.mod_lt n (Nat.pos_of_ne_zero hd)
    by_cases he : n % d.length + 1 = d.length
    · have hz : (n + 1) % d.length = 0 := by rw [← hm, he, Nat.mod_self]
      simp [modStep, he, hz, unary]
    · have hsmall : n % d.length + 1 < d.length := by omega
      have hh : (n + 1) % d.length = n % d.length + 1 := by rw [← hm, Nat.mod_eq_of_lt hsmall]
      simp [modStep, he, hh, unary, List.replicate_succ]

private theorem iterate_modStep (d : Unary) (n : ℕ) :
    modStep^[n] (d, []) = (d, unary (n % d.length)) := by
  induction n with
  | zero => simp [unary]
  | succ n ih => rw [Function.iterate_succ_apply', ih, modStep_mod]

private theorem fold_modStep (u : Unary) (s : ModState) :
    u.foldl (fun s _ => modStep s) s = modStep^[u.length] s := by
  induction u generalizing s with
  | nil => rfl
  | cons x u ih => rw [List.foldl_cons, ih, List.length_cons, Function.iterate_succ_apply]

/-- A globally polynomial-time unary remainder program, including divisor zero. -/
def modUnaryProg : PolyTimeFun (Unary × Unary) Unary :=
  let scan := foldlAdd modStepProg 2 modStep_growth
  congr (snd.comp (scan.comp (fst.pair (snd.pair (const [])))))
    (fun q => unary (q.1.length % q.2.length)) (by
      rintro ⟨u, d⟩
      have hs : modStepProg.step = fun s _ => modStep s := by
        funext s x
        exact modStepProg_apply s x
      change (u.foldl modStepProg.step (d, [])).2 = _
      rw [hs, fold_modStep, iterate_modStep])

@[simp] theorem modUnaryProg_apply (u d : Unary) :
    modUnaryProg (u, d) = unary (u.length % d.length) := rfl

/-- A divisibility test on two unary values. -/
def dvdUnaryProg : PolyTimeFun (Unary × Unary) Bool :=
  congr (isEmptyProg.comp (modUnaryProg.comp (snd.pair fst)))
    (fun q => decide (q.1.length ∣ q.2.length)) (by
      rintro ⟨d, u⟩
      change (unary (u.length % d.length)).isEmpty = decide (d.length ∣ u.length)
      apply Bool.eq_iff_iff.mpr
      simp [unary, Nat.dvd_iff_mod_eq_zero])

@[simp] theorem dvdUnaryProg_apply (d u : Unary) :
    dvdUnaryProg (d, u) = decide (d.length ∣ u.length) := rfl

private theorem iterate_tail_size (n : ℕ) (u : Unary) :
    esize (((tail : PolyTimeFun Unary Unary) : Unary → Unary)^[n] u) ≤ X.eval (esize u) := by
  rw [eval_X]
  change esize (List.tail^[n] u) ≤ esize u
  induction n generalizing u with
  | zero => exact le_rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact (ih u.tail).trans (esize_tail_le u)

/-- Enumerate unary values from the input down through zero, without duplicates. -/
def descendingUnary (u : Unary) : List Unary := recordIterates List.tail (() :: u) u

/-- Every bounded candidate degree can be printed in polynomial time. -/
def descendingUnaryProg : PolyTimeFun Unary (List Unary) :=
  (recordIteratesProg tail X iterate_tail_size).comp ((cons (const ()) (PolyTimeFun.id _)).pair (PolyTimeFun.id _))

@[simp] theorem descendingUnaryProg_apply (u : Unary) : descendingUnaryProg u = descendingUnary u := rfl

/-- The enumeration consists exactly of the successive suffixes. -/
theorem descendingUnary_eq (u : Unary) :
    descendingUnary u = List.ofFn (fun i : Fin (u.length + 1) => u.drop i) := by
  simp [descendingUnary, recordIterates, List.tail_iterate]

/-- Enumerated values lie between zero and the supplied bound, each exactly once. -/
theorem descendingUnary_length (u : Unary) : (descendingUnary u).length = u.length + 1 := by
  simp [descendingUnary_eq]


/-- A unary value occurs in the descending enumeration exactly when it is bounded by the input. -/
theorem mem_descendingUnary_iff (u d : Unary) : d ∈ descendingUnary u ↔ d.length ≤ u.length := by
  rw [descendingUnary_eq, List.mem_ofFn]
  constructor
  · rintro ⟨i, rfl⟩
    simp
  · intro h
    refine ⟨⟨u.length - d.length, by omega⟩, ?_⟩
    apply List.ext_getElem
    · simp only [List.length_drop]
      omega
    · intro i hi hj
      exact Subsingleton.elim _ _

/-- Every unary encoding has exact size linear in its value. -/
theorem esize_unary_list (u : Unary) : esize u = 2 * u.length + 1 := by
  rw [← unary_length u, esize_unary, length_unary]

private abbrev MultiplyState := Unary × Unary

private def multiplyStep (s : MultiplyState) (_ : Unit) : MultiplyState := (s.1, s.1 ++ s.2)

private theorem fold_multiplyStep (pre v acc : Unary) :
    (pre.foldl multiplyStep (v, acc)).1 = v ∧
      (pre.foldl multiplyStep (v, acc)).2.length = acc.length + pre.length * v.length := by
  induction pre generalizing acc with
  | nil => exact ⟨rfl, by simp⟩
  | cons x pre ih =>
    have h := ih (v ++ acc)
    refine ⟨h.1, ?_⟩
    simpa only [List.foldl_cons, multiplyStep, List.length_append, List.length_cons,
      Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h.2

private def multiplyStepProg : PolyTimeFun (MultiplyState × Unit) MultiplyState :=
  (fst.comp fst).pair (append.comp ((fst.comp fst).pair (snd.comp fst)))

private theorem multiplyStep_bounded : FoldBounded multiplyStepProg (10 * X ^ 2 + 10 * X + 10) := by
  intro u s pre post heq
  rcases s with ⟨v, acc⟩
  let N := esize (u, v, acc)
  have hs : N = esize u + esize v + esize acc + 2 := by simp [N, esize_prod]; omega
  have hv : v.length ≤ N := by have := length_le_esize_list v; omega
  have ha : acc.length ≤ N := by have := length_le_esize_list acc; omega
  have hp : pre.length ≤ N := by
    have := length_le_esize_list u
    have h := congrArg List.length heq
    simp only [List.length_append] at h
    omega
  have h := fold_multiplyStep pre v acc
  have hm := Nat.mul_le_mul hp hv
  change esize (pre.foldl multiplyStep (v, acc)) ≤ _
  rw [esize_prod, h.1, esize_unary_list (pre.foldl multiplyStep (v, acc)).2, h.2]
  simp only [eval_add, eval_mul, eval_pow, eval_X, eval_ofNat]
  change esize v + (2 * (acc.length + pre.length * v.length) + 1) + 1 ≤
    10 * N ^ 2 + 10 * N + 10
  nlinarith

/-- Unary multiplication has a global quadratic-size fold implementation. -/
def mulUnaryProg : PolyTimeFun (Unary × Unary) Unary :=
  let scan := foldl multiplyStepProg (10 * X ^ 2 + 10 * X + 10) multiplyStep_bounded
  congr (snd.comp (scan.comp (fst.pair (snd.pair (const [])))))
    (fun q => unary (q.1.length * q.2.length)) (by
      rintro ⟨u, v⟩
      change (u.foldl multiplyStep (v, [])).2 = _
      rw [← unary_length (u.foldl multiplyStep (v, [])).2, (fold_multiplyStep u v []).2]
      simp)

@[simp] theorem mulUnaryProg_apply (u v : Unary) :
    mulUnaryProg (u, v) = unary (u.length * v.length) := rfl

end MIPRE.LowDegree.DegreeArithmetic

end

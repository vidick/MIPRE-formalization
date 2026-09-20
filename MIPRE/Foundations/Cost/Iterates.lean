/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Cost.Reader

/-! # Recording a polynomially bounded sequence of iterates -/

namespace MIPRE.Cost

open PolyTimeFun Polynomial

variable {α : Type*} [SizedEncoding α]

/-- Print the initial point and each subsequent iterate, up to the unary budget. -/
def recordIterates (f : α → α) (u : Unary) (a : α) : List α :=
  List.ofFn (fun i : Fin u.length => f^[i] a)

@[simp] theorem recordIterates_nil (f : α → α) (a : α) : recordIterates f [] a = [] := rfl

theorem recordIterates_cons (f : α → α) (u : Unary) (a : α) :
    recordIterates f (() :: u) a = a :: recordIterates f u (f a) := by
  rw [recordIterates, List.ofFn_succ]
  congr 1

def recordStep (f : α → α) (s : α × List α) (_ : Unit) : α × List α :=
  (f s.1, s.1 :: s.2)

theorem fold_recordStep (f : α → α) (u : Unary) (a : α) (acc : List α) :
    u.foldl (recordStep f) (a, acc) =
      (f^[u.length] a, (recordIterates f u a).reverse ++ acc) := by
  induction u generalizing a acc with
  | nil => simp
  | cons x u ih =>
    cases x
    rw [List.foldl_cons]
    change u.foldl (recordStep f) (f a, a :: acc) = _
    rw [ih, recordIterates_cons]
    simp only [List.length_cons, Function.iterate_succ_apply, List.reverse_cons,
      List.append_assoc, List.singleton_append]

theorem esize_recordIterates (f : α → α) (B : Polynomial ℕ)
    (hB : ∀ n a, esize (f^[n] a) ≤ B.eval (esize a)) (u : Unary) (a : α) :
    esize (recordIterates f u a) ≤ u.length * (B.eval (esize a) + 1) + 1 := by
  have bound (l : List α) (hl : ∀ x ∈ l, esize x ≤ B.eval (esize a)) :
      esize l ≤ l.length * (B.eval (esize a) + 1) + 1 := by
    induction l with
    | nil => simp
    | cons x l ih =>
      have hx := hl x (by simp)
      have ht := ih (fun y hy => hl y (by simp [hy]))
      rw [esize_list_cons, List.length_cons]
      rw [Nat.add_mul, Nat.one_mul]
      omega
  apply (bound _ ?_).trans_eq (by simp [recordIterates])
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  exact hB i a

private noncomputable def recordStepProg (f : PolyTimeFun α α) :
    PolyTimeFun ((α × List α) × Unit) (α × List α) :=
  (f.comp (fst.comp fst)).pair (cons (fst.comp fst) (snd.comp fst))

/-- Any uniformly polynomially size-bounded orbit can be printed in polynomial time.
The iteration count is unary, and the bound must hold on every raw input. -/
noncomputable def recordIteratesProg (f : PolyTimeFun α α) (B : Polynomial ℕ)
    (hB : ∀ n a, esize ((f : α → α)^[n] a) ≤ B.eval (esize a)) :
    PolyTimeFun (Unary × α) (List α) :=
  let scan := foldl (recordStepProg f) (B + X * (B + 1) + X + 2) (by
    intro l s pre post hl
    rcases s with ⟨a, acc⟩
    change esize (pre.foldl (recordStep f) (a, acc)) ≤ _
    rw [fold_recordStep, esize_prod]
    have ha := hB pre.length a
    have hr := esize_recordIterates f B hB pre a
    have he := esize_list_append (recordIterates f pre a).reverse acc
    rw [esize_list_reverse] at he
    have hpre : pre.length ≤ esize (l, a, acc) := by
      have hp := congrArg List.length hl
      have hh := length_le_esize_list l
      simp only [esize_prod, List.length_append] at *
      omega
    have haa : esize a ≤ esize (l, a, acc) := by simp only [esize_prod]; omega
    have hacc : esize acc ≤ esize (l, a, acc) := by simp only [esize_prod]; omega
    have hb := polynomial_eval_mono B haa
    have hm := Nat.mul_le_mul hpre (Nat.add_le_add_right hb 1)
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_one, Polynomial.eval_ofNat]
    omega)
  congr (reverse.comp (snd.comp (scan.comp (fst.pair (snd.pair (const []))))))
    (fun p => recordIterates f p.1 p.2) (by
      rintro ⟨u, a⟩
      change (u.foldl (recordStep f) (a, [])).2.reverse = _
      rw [fold_recordStep]
      simp)

@[simp] theorem recordIteratesProg_apply (f : PolyTimeFun α α) (B : Polynomial ℕ)
    (hB : ∀ n a, esize ((f : α → α)^[n] a) ≤ B.eval (esize a)) (u : Unary) (a : α) :
    recordIteratesProg f B hB (u, a) = recordIterates f u a := rfl

end MIPRE.Cost

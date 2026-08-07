/-
Copyright (c) 2026 Sean Perazzolo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Perazzolo
-/
import MIPRE.LCS.Basic

/-!
# Common Utilities for LCS Games

This module provides technical lemmas and definitions for signs, indicator functions,
and basic properties of the outcome space $\mathbb{F}_2$.

## Key Definitions
- `observableSign`: Returns $1$ if $a=0$ or $-1$ if $a=1$.

## Key Lemmas
- `sign_mul`: The product of signs corresponds to the sum in $\mathbb{F}_2$.
- `sign_indicator`: Relates the sign-based expression $(1/2)(1 + (-1)^{b+s})$
  to the Kronecker delta.
-/

namespace MIPRE.LCS
open scoped BigOperators

set_option linter.unusedSectionVars false



lemma fin2_eq_zero_or_one (a : Fin 2) : a = 0 ∨ a = 1 := by
  match a with | 0 => left; rfl | 1 => right; rfl



lemma sign_mul (a b : Fin 2) :
    (-1 : ℂ) ^ a.val * (-1 : ℂ) ^ b.val = (-1 : ℂ) ^ (a + b).val := by
  fin_cases a <;> fin_cases b <;> simp


/-- Arithmetic helper: the sign factor `$(1/2)(1 + (-1)^b * (-1)^s)$` equals the
indicator `s = b`. -/
lemma sign_indicator (b s : Fin 2) :
    (1 / 2 : ℂ) + (1 / 2 : ℂ) * (-1 : ℂ) ^ b.val * (-1 : ℂ) ^ s.val = if s = b then 1 else 0 := by
  match b, s with
  | 0, 0 => norm_num
  | 0, 1 => norm_num
  | 1, 0 => norm_num
  | 1, 1 => norm_num


def observableSign (a : Fin 2) : ℂ :=
  if a = 0 then 1 else -1

lemma sign_fin2_sq (x : Fin 2) : (-1 : ℂ) ^ x.val * (-1 : ℂ) ^ x.val = 1 := by
  rcases fin2_eq_zero_or_one x with rfl | rfl <;> norm_num

lemma prod_sign_eq_sum_sign_aux {G : LCSLayout} {i : Fin G.r}
  (x : Assignment G i) (s : Finset (G.V i)) :
  (s.prod fun j => (-1 : ℂ) ^ (x j).val) =
    (-1 : ℂ) ^ ((s.sum fun j => (x j : Fin 2)).val) := by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s ha ih => rw [Finset.prod_cons, Finset.sum_cons, ih, sign_mul]

lemma prod_sign_eq_sum_sign {G : LCSLayout} (i : Fin G.r) (x : Assignment G i) :
  ((G.V i).attach.prod fun j => (-1 : ℂ) ^ (x j).val) =
    (-1 : ℂ) ^ ((∑ j : G.V i, (x j : Fin 2)).val) :=
  prod_sign_eq_sum_sign_aux x _

lemma finset_filter_eq_inter_univ_filter {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (p : α → Prop) [DecidablePred p] :
    S.filter p = S ∩ Finset.univ.filter p := by
  ext x; simp

end MIPRE.LCS

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




/-- Case analysis for `ZMod 2`. -/
lemma zmod_two_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

@[simp] lemma zmod_two_val_one : (1 : ZMod 2).val = 1 := rfl

/-- The `ZMod 2` counterpart of `Fin.sum_univ_two`. -/
lemma sum_univ_zmod_two {M : Type*} [AddCommMonoid M] (f : ZMod 2 → M) :
    ∑ x, f x = f 0 + f 1 := by
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from by decide,
    Finset.sum_insert (by decide), Finset.sum_singleton]

lemma sign_mul (a b : ZMod 2) :
    (-1 : ℂ) ^ a.val * (-1 : ℂ) ^ b.val = (-1 : ℂ) ^ (a + b).val := by
  rcases zmod_two_eq_zero_or_one a with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one b with rfl | rfl <;>
      simp [ZMod.val_add]


/-- Arithmetic helper: the sign factor `$(1/2)(1 + (-1)^b * (-1)^s)$` equals the
indicator `s = b`. -/
lemma sign_indicator (b s : ZMod 2) :
    (1 / 2 : ℂ) + (1 / 2 : ℂ) * (-1 : ℂ) ^ b.val * (-1 : ℂ) ^ s.val = if s = b then 1 else 0 := by
  rcases zmod_two_eq_zero_or_one b with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one s with rfl | rfl <;>
      norm_num [ZMod.val_zero, zmod_two_val_one]


def observableSign (a : ZMod 2) : ℂ :=
  if a = 0 then 1 else -1

lemma sign_sq (x : ZMod 2) : (-1 : ℂ) ^ x.val * (-1 : ℂ) ^ x.val = 1 := by
  rcases zmod_two_eq_zero_or_one x with rfl | rfl <;> norm_num [ZMod.val_zero, zmod_two_val_one]

lemma prod_sign_eq_sum_sign_aux {G : Layout} {i : Fin G.r}
  (x : Layout.Assignment G i) (s : Finset (G.V i)) :
  (s.prod fun j => (-1 : ℂ) ^ (x j).val) =
    (-1 : ℂ) ^ ((s.sum fun j => (x j : ZMod 2)).val) := by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s ha ih => rw [Finset.prod_cons, Finset.sum_cons, ih, sign_mul]

lemma prod_sign_eq_sum_sign {G : Layout} (i : Fin G.r) (x : Layout.Assignment G i) :
  ((G.V i).attach.prod fun j => (-1 : ℂ) ^ (x j).val) =
    (-1 : ℂ) ^ ((∑ j : G.V i, (x j : ZMod 2)).val) :=
  prod_sign_eq_sum_sign_aux x _

lemma finset_filter_eq_inter_univ_filter {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (p : α → Prop) [DecidablePred p] :
    S.filter p = S ∩ Finset.univ.filter p := by
  ext x; simp

end MIPRE.LCS

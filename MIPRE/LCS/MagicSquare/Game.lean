/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.LCS.NonlocalGame
import MIPRE.LCS.MagicSquare.Strategy

/-!
# The Magic Square as a nonlocal game

`MIPRE.LCS.MagicSquare.game` is the Mermin--Peres magic square as an LCS instance;
`nonlocalGame` is the two-player game it induces through `MIPRE.LCS.Game.toNonlocalGame`, which
is what blueprint `lem:ms-direct-anticomm` and the Pauli basis test's Magic Square subtest are
about.

The point of this file is the **non-vacuity witnesses**. A decider that accepts everything, or
rejects everything, makes every soundness statement about the game either false or empty, and
that is not a hypothetical: `reports/clgame-format-check-missing.md` records the seeded CL
game's missing format check doing exactly that. So each of the four possibilities is pinned
here by `decide` on explicit answers:

* an oriented pair that is **accepted** (`accepts_zero`), in both orientations;
* one that is **rejected because the bits disagree** (`rejects_disagree`);
* one that is **rejected because the assignment violates its equation**
  (`rejects_unsatisfied`) --- note this one has the bits *agreeing*, so it isolates the
  parity check;
* one that is **rejected because an answer has the wrong shape** (`rejects_shape`).

`layout.V 5 = {2, 5, 8}` carries the odd right-hand side, so `rejects_odd_column` also checks
that the parity actually reads `game.b` rather than always testing against zero.
-/

namespace MIPRE.LCS.MagicSquare

open MIPRE.LCS

/-- The magic square has six equations. -/
theorem r_pos : 0 < layout.r := by decide

/-- Every equation of the magic square has a nonempty support. -/
theorem V_nonempty : ∀ i, (layout.V i).Nonempty := by decide

/-- **The Magic Square as a nonlocal game.** -/
noncomputable def nonlocalGame : MIPRE.Game layout.Question layout.Question
    layout.Answer layout.Answer :=
  game.toNonlocalGame r_pos V_nonempty

/-! ## Non-vacuity

The all-zero assignment satisfies equation `0` (whose right-hand side is `0`), so with the
matching bit it is accepted; changing the bit, or the assignment's parity, is rejected. -/

/-- A variable index, written as a numeral. `layout.s` is not a literal, so the `OfNat`
instance does not fire. -/
def v (k : ℕ) (h : k < layout.s := by decide) : Fin layout.s := ⟨k, h⟩

/-- An equation index, written as a numeral. -/
def e (k : ℕ) (h : k < layout.r := by decide) : Fin layout.r := ⟨k, h⟩

/-- The all-zero assignment. -/
def zeroAssign : Fin layout.s → ZMod 2 := fun _ => 0

/-- The assignment that is `1` at variable `k` and `0` elsewhere. -/
def oneAt (k : Fin layout.s) : Fin layout.s → ZMod 2 := fun l => if l = k then 1 else 0

theorem accepts_zero :
    game.accepts (.inl (e 0)) (.inr (v 0)) (.inl zeroAssign) (.inr 0) = true := by decide

theorem accepts_zero_swapped :
    game.accepts (.inr (v 0)) (.inl (e 0)) (.inr 0) (.inl zeroAssign) = true := by decide

theorem rejects_disagree :
    game.accepts (.inl (e 0)) (.inr (v 0)) (.inl zeroAssign) (.inr 1) = false := by decide

theorem rejects_unsatisfied :
    game.accepts (.inl (e 0)) (.inr (v 0)) (.inl (oneAt (v 0))) (.inr 1) = false := by decide

theorem rejects_shape :
    game.accepts (.inl (e 0)) (.inr (v 0)) (.inr 0) (.inl zeroAssign) = false := by decide

/-- The last column has right-hand side `1`, so the all-zero assignment fails it: the parity
check reads `game.b` and does not always test against zero. -/
theorem rejects_odd_column :
    game.accepts (.inl (e 5)) (.inr (v 2)) (.inl zeroAssign) (.inr 0) = false := by decide

/-- ... and the assignment that is `1` at variable `2` alone does satisfy it. -/
theorem accepts_odd_column :
    game.accepts (.inl (e 5)) (.inr (v 2)) (.inl (oneAt (v 2))) (.inr 1) = true := by decide

/-- An off-support incidence is rejected: variable `3` does not occur in equation `0`. -/
theorem rejects_off_support :
    game.accepts (.inl (e 0)) (.inr (v 3)) (.inl zeroAssign) (.inr 0) = false := by decide

/-! ## The cells of a constraint

The magic square's six equations are the three rows and the three columns, in that order, so
the `j`-th cell of equation `c` is `3c + j` for a row and `3j + (c - 3)` for a column. -/

/-- The index of the `j`-th cell of the `c`-th equation. -/
def cellNat (c j : ℕ) : ℕ := if c < 3 then 3 * c + j else 3 * j + (c - 3)

/-- The `j`-th cell of constraint `c`. -/
def cell (c : Fin layout.r) (j : Fin 3) : Fin layout.s :=
  ⟨cellNat c.val j.val, by
    have hc := c.isLt
    have hj := j.isLt
    simp only [layout] at hc ⊢
    simp only [cellNat]
    split_ifs <;> omega⟩

theorem V_eq_cells (c : Fin layout.r) : layout.V c = {cell c 0, cell c 1, cell c 2} := by
  fin_cases c <;> decide

theorem cell_ne_01 (c : Fin layout.r) : cell c 0 ≠ cell c 1 := by fin_cases c <;> decide

theorem cell_ne_02 (c : Fin layout.r) : cell c 0 ≠ cell c 2 := by fin_cases c <;> decide

theorem cell_ne_12 (c : Fin layout.r) : cell c 1 ≠ cell c 2 := by fin_cases c <;> decide

theorem cell_mem (c : Fin layout.r) (j : Fin 3) : cell c j ∈ layout.V c := by
  rw [V_eq_cells]
  fin_cases j <;> simp

/-- A sum over a constraint's support is the sum over its three cells. -/
theorem sum_cells (c : Fin layout.r) (a : Fin layout.s → ZMod 2) :
    ∑ k ∈ layout.V c, a k = a (cell c 0) + a (cell c 1) + a (cell c 2) := by
  classical
  rw [V_eq_cells, Finset.sum_insert (by simp [cell_ne_01 c, cell_ne_02 c]),
    Finset.sum_insert (by simp [cell_ne_12 c]), Finset.sum_singleton, add_assoc]

/-- The position of the variable `j` within the support of constraint `c`, the inverse of
`cell c`; junk (`2`) for a variable outside the support. -/
def cellIdx (c : Fin layout.r) (j : Fin layout.s) : Fin 3 :=
  if cell c 0 = j then 0 else if cell c 1 = j then 1 else 2

theorem cell_cellIdx {c : Fin layout.r} {j : Fin layout.s} (h : j ∈ layout.V c) :
    cell c (cellIdx c j) = j := by
  revert h; revert j; revert c; decide

@[simp] theorem cellIdx_cell (c : Fin layout.r) (k : Fin 3) : cellIdx c (cell c k) = k := by
  revert k; revert c; decide

end MIPRE.LCS.MagicSquare

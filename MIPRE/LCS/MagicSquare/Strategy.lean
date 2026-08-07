/-
Copyright (c) 2026 Sean Perazzolo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Perazzolo
-/
import MIPRE.LCS.Basic
import MIPRE.LCS.Observable
import MIPRE.LCS.Strategy.ObservableStrategy
import MIPRE.LCS.Pauli

/-!
# Mermin-Peres Magic Square Game Strategy

This module defines the layout for the Mermin-Peres magic square Linear Constraint System (LCS) game
and provides a valid quantum strategy for it using observables.

It verifies the commutativity requirements
(both local within equations and global bipartite commutativity)
necessary to define a valid `ObservableStrategy`.
-/

namespace MIPRE.LCS.MagicSquare

section Layout
/-! ## Layout
This section defines the layout/geometry of the Mermin-Peres magic square game.
  -/
/-- The layout of the Mermin-Peres magic square game.
It consists of 6 equations (3 rows and 3 columns) over 9 variables (the cells of the 3x3 grid). -/
def layout : Layout  := {
  r := 6
  s := 9
  V := fun i =>
  match i with
  | 0 => {0, 1, 2}
  | 1 => {3, 4, 5}
  | 2 => {6, 7, 8}
  | 3 => {0, 3, 6}
  | 4 => {1, 4, 7}
  | 5 => {2, 5, 8}
  }

end Layout

/-- The support-style magic square game, with the final column equation having odd parity. -/
def game : Game layout := {
  b := fun i => if i = ⟨5, by decide⟩ then 1 else 0
}

open Matrix
open Kronecker
open Pauli
open scoped BigOperators

section Grid
/-! ## Grid
This section defines a strategy for the game from the previous section,
given as a grid of observables.
-/

/-- The 9 observables for the Mermin-Peres magic square, defined as Kronecker products of
Pauli matrices (X, Y, Z) and the identity (I). -/
def grid : Fin 9 → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ
  | 0 => X  ⊗ₖ I
  | 1 => I ⊗ₖ X
  | 2 => X  ⊗ₖ X
  | 3 => I ⊗ₖ Y
  | 4 => Y  ⊗ₖ I
  | 5 => Y  ⊗ₖ Y
  | 6 => X  ⊗ₖ Y
  | 7 => Y  ⊗ₖ X
  | 8 => Z  ⊗ₖ Z

/-- Each observable in the Mermin-Peres grid is a self-adjoint involution. -/
lemma isObservable_grid (j : Fin 9) : IsObservable (grid j) := by
  fin_cases j <;>
    dsimp [grid] <;>
    repeat
      first
      | apply IsObservable.kronecker
      | exact isObservable_I
      | exact isObservable_X
      | exact isObservable_Y
      | exact isObservable_Z

end Grid

section Commutativity
/-!
## Commutativity
This section proves the commutativity properties of the magic square grid.

These properties are required for the strategy to be valid.
-/

/-- A tactic for proving pairwise commutativity within one row or column of the square. -/
macro "solve_line_comm" : tactic => `(tactic| {
  intro j k hjk
  rcases j with ⟨j, hj⟩
  rcases k with ⟨k, hk⟩
  fin_cases j <;> fin_cases k <;> simp +decide [layout] at hj hk hjk ⊢
  <;> dsimp [grid]
  <;> first
    | (apply commute_kronecker_of_commute; all_goals {
        first
        | exact Commute.refl _
        | { rw [I_eq_one]; exact Commute.one_left _ }
        | { rw [I_eq_one]; exact Commute.one_right _ }
      })
    | (apply commute_kronecker_of_anticomm; all_goals {
        first
        | exact X_anticomm_Y
        | exact X_anticomm_Z
        | exact Y_anticomm_Z
        | { rw [X_anticomm_Y]; simp }
        | { rw [Z_mul_X, X_mul_Z]; simp }
        | { rw [Z_mul_Y, Y_mul_Z]; simp }
      })
})

/-- Helper lemmas establishing pairwise commutativity for each row and column. -/
private lemma row1_comm :
    Pairwise
      (fun j k : layout.V (0 : Fin 6) =>
        Commute (grid j.1) (grid k.1)) := by
  solve_line_comm

private lemma row2_comm :
    Pairwise
      (fun j k : layout.V (1 : Fin 6) =>
        Commute (grid j.1) (grid k.1)) := by
  solve_line_comm

private lemma row3_comm :
    Pairwise
      (fun j k : layout.V (2 : Fin 6) =>
        Commute (grid j.1) (grid k.1)) := by
  solve_line_comm

private lemma col1_comm :
    Pairwise
      (fun j k : layout.V (3 : Fin 6) =>
        Commute (grid j.1) (grid k.1)) := by
  solve_line_comm

private lemma col2_comm :
    Pairwise
      (fun j k : layout.V (4 : Fin 6) =>
        Commute (grid j.1) (grid k.1)) := by
  solve_line_comm

private lemma col3_comm :
    Pairwise
      (fun j k : layout.V (5 : Fin 6) =>
        Commute (grid j.1) (grid k.1)) := by
  solve_line_comm

/-- For every equation of the layout, the associated grid observables commute pairwise. -/
lemma grid_sameEquation_comm (i : Fin 6) :
    Pairwise
      (fun j k : layout.V i =>
        Commute (grid j.1) (grid k.1)) := by
  fin_cases i
  · exact row1_comm
  · exact row2_comm
  · exact row3_comm
  · exact col1_comm
  · exact col2_comm
  · exact col3_comm

end Commutativity

section Strategy
/-!
## Strategy
This section shows that the grid strategy is a valid strategy for the magic square game.
-/


/-- The Mermin-Peres strategy for the magic square game.
This strategy uses `BipartiteObservableStrategy` to lift the 9 `grid` observables to a
valid bipartite observable strategy on a 16x16 space. It relies on
`grid_sameEquation_comm` to satisfy the commutativity constraints for each equation. -/
noncomputable def merminPeresStrategy :
    BipartiteObservableStrategy (Fin 2 × Fin 2) layout where
  obs := grid
  isObservable := isObservable_grid
  sameEquation_comm := grid_sameEquation_comm

end Strategy

end MIPRE.LCS.MagicSquare

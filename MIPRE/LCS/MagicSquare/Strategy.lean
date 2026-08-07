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

namespace MIPRE.LCS

section Types
/-! ## Types  -/

/-- The 4×4 matrix type used for two-qubit observables in the magic square construction. -/
abbrev mat4 := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ
/-- The 16×16 matrix type used for the bipartite lift of the two-qubit strategy. -/
abbrev mat16 := Matrix ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ℂ

end Types

section Layout
/-! ## Layout
This section defines the layout/geometry of the Mermin-Peres magic square game.
  -/
/-- The layout of the Mermin-Peres magic square game.
It consists of 6 equations (3 rows and 3 columns) over 9 variables (the cells of the 3x3 grid). -/
def magic_square_layout : LCSLayout  := {
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
def magic_square_game : LCSGame magic_square_layout := {
  b := fun i => if i = ⟨5, by decide⟩ then 1 else 0
}

open Matrix
open Kronecker
open scoped BigOperators

section Grid
/-! ## Grid
This section defines a strategy for the game from the previous section,
given as a grid of observables.
-/

/-- The 9 observables for the Mermin-Peres magic square, defined as Kronecker products of
Pauli matrices (X, Y, Z) and the identity (I2). -/
def magic_square_grid : Fin 9 → mat4
  | 0 => X  ⊗ₖ I2
  | 1 => I2 ⊗ₖ X
  | 2 => X  ⊗ₖ X
  | 3 => I2 ⊗ₖ Y
  | 4 => Y  ⊗ₖ I2
  | 5 => Y  ⊗ₖ Y
  | 6 => X  ⊗ₖ Y
  | 7 => Y  ⊗ₖ X
  | 8 => Z  ⊗ₖ Z

/-- Each observable in the Mermin-Peres grid is a self-adjoint involution. -/
lemma magic_square_is_observable (j : Fin 9) : IsObservable (magic_square_grid j) := by
  fin_cases j <;>
    dsimp [magic_square_grid] <;>
    repeat
      first
      | apply kronecker_observable
      | exact I2_observable
      | exact X_observable
      | exact Y_observable
      | exact Z_observable

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
  fin_cases j <;> fin_cases k <;> simp +decide [magic_square_layout] at hj hk hjk ⊢
  <;> dsimp [magic_square_grid]
  <;> first
    | (apply kronecker_comm_of_comm; all_goals {
        first
        | exact Commute.refl _
        | { rw [I2_eq_one]; exact Commute.one_left _ }
        | { rw [I2_eq_one]; exact Commute.one_right _ }
      })
    | (apply kronecker_comm_of_anticomm; all_goals {
        first
        | exact XY_anticomm
        | exact XZ_anticomm
        | exact YZ_anticomm
        | { rw [XY_anticomm]; simp }
        | { rw [ZX_mul, XZ_mul]; simp }
        | { rw [ZY_mul, YZ_mul]; simp }
      })
})

/-- Helper lemmas establishing pairwise commutativity for each row and column. -/
private lemma row1_comm :
    Pairwise
      (fun j k : magic_square_layout.V (0 : Fin 6) =>
        Commute (magic_square_grid j.1) (magic_square_grid k.1)) := by
  solve_line_comm

private lemma row2_comm :
    Pairwise
      (fun j k : magic_square_layout.V (1 : Fin 6) =>
        Commute (magic_square_grid j.1) (magic_square_grid k.1)) := by
  solve_line_comm

private lemma row3_comm :
    Pairwise
      (fun j k : magic_square_layout.V (2 : Fin 6) =>
        Commute (magic_square_grid j.1) (magic_square_grid k.1)) := by
  solve_line_comm

private lemma col1_comm :
    Pairwise
      (fun j k : magic_square_layout.V (3 : Fin 6) =>
        Commute (magic_square_grid j.1) (magic_square_grid k.1)) := by
  solve_line_comm

private lemma col2_comm :
    Pairwise
      (fun j k : magic_square_layout.V (4 : Fin 6) =>
        Commute (magic_square_grid j.1) (magic_square_grid k.1)) := by
  solve_line_comm

private lemma col3_comm :
    Pairwise
      (fun j k : magic_square_layout.V (5 : Fin 6) =>
        Commute (magic_square_grid j.1) (magic_square_grid k.1)) := by
  solve_line_comm

/-- For every equation of the layout, the associated grid observables commute pairwise. -/
lemma MP_sameEquation_comm (i : Fin 6) :
    Pairwise
      (fun j k : magic_square_layout.V i =>
        Commute (magic_square_grid j.1) (magic_square_grid k.1)) := by
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
This strategy uses `BipartiteObservableStrategy` to lift the 9 `MP_observables` to a
valid bipartite observable strategy on a 16x16 space. It relies on
`MP_sameEquation_comm` to satisfy the commutativity constraints for each equation. -/
noncomputable def Strat_merminPeres :
    BipartiteObservableStrategy (Fin 2 × Fin 2) magic_square_layout where
  obs := magic_square_grid
  is_observable := magic_square_is_observable
  sameEquation_comm := MP_sameEquation_comm

end Strategy

end MIPRE.LCS

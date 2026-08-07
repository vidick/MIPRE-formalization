/-
Copyright (c) 2026 Sean Perazzolo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Perazzolo
-/
import MIPRE.LCS.MagicSquare.Strategy
import MIPRE.LCS.SolutionGroup

/-!
# Magic Square Solution Group

This module builds the binary linear system of the Mermin-Peres magic square game
from its layout/game data and attaches the generic `SolutionGroup` construction,
together with helpers rendering the presentation data (coefficient matrix,
right-hand side, and equation supports) as plain lists.
-/

namespace MIPRE.LCS.MagicSquare

/-- The explicit binary linear system underlying the Mermin-Peres magic square game. -/
def linearSystem : LinearSystem :=
  game.toLinearSystem

/-- The solution group of the magic square linear system. -/
abbrev solutionGroup : Type :=
  SolutionGroup linearSystem

/-- The coefficient row of equation `i`, rendered as a list of `0`/`1` naturals. -/
def coefficientRow (i : Fin linearSystem.layout.r) : List Nat :=
  (List.finRange linearSystem.layout.s).map fun j => (linearSystem.A i j).val

/-- The full coefficient matrix, rendered as rows of `0`/`1` naturals. -/
def coefficientMatrix : List (List Nat) :=
  (List.finRange linearSystem.layout.r).map coefficientRow

/-- The right-hand side vector, rendered as a list of `0`/`1` naturals. -/
def rhsVector : List Nat :=
  (List.finRange linearSystem.layout.r).map fun i => (linearSystem.b i).val

/-- The variables occurring in equation `i`, rendered as zero-based indices. -/
def equationSupportIndices (i : Fin linearSystem.layout.r) : List Nat :=
  ((eqSupport linearSystem i).sort (· ≤ ·)).map Fin.val

/-- All equation supports, rendered as zero-based variable indices. -/
def equationSupports : List (List Nat) :=
  (List.finRange linearSystem.layout.r).map equationSupportIndices

/-- The equation relators in presentation form:
`([variables in the equation], parity)`, where parity `1` means the product is `J`.
-/
def equationPresentation : List (List Nat × Nat) :=
  (List.finRange linearSystem.layout.r).map fun i =>
    (equationSupportIndices i, (linearSystem.b i).val)

end MIPRE.LCS.MagicSquare

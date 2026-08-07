/-
Copyright (c) 2026 Sean Perazzolo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Perazzolo
-/
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Algebra.Star.Module
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Linear Constraint System (LCS) Game Layout

This module defines the basic geometric structure of a Linear Constraint System (LCS) game.
An LCS game is defined by a set of binary variables and a set of linear equations
over $\mathbb{F}_2$.

## Key Definitions
- `Layout`: The structure describing the relationship between equations and variables.
- `Layout.Assignment`: A local mapping of values to variables in a specific equation.
- `Game`: The specification of the right-hand sides of the linear equations.
-/

namespace MIPRE.LCS

open scoped BigOperators

structure Layout where
  r : ℕ
  s : ℕ
  V : Fin r → Finset (Fin s)

abbrev Layout.Assignment (G : Layout) (i : Fin G.r) : Type :=
  (G.V i) → ZMod 2


structure Game (G : Layout) where
  b : Fin G.r → ZMod 2

/-- A full binary linear system with explicit coefficient matrix and right-hand side. -/
structure LinearSystem where
  layout : Layout
  A : Fin layout.r → Fin layout.s → ZMod 2
  b : Fin layout.r → ZMod 2

namespace Game

/-- Recover the explicit binary linear system encoded by a support-only LCS game. -/
def toLinearSystem {G : Layout} (game : Game G) : LinearSystem where
  layout := G
  A i j := if j ∈ G.V i then 1 else 0
  b := game.b

end Game

end MIPRE.LCS

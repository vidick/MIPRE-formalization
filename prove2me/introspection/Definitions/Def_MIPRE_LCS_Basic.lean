/-
Copyright (c) 2026 Sean Perazzolo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Perazzolo
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/LCS/Basic.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation

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

/-- The layout of a binary linear constraint system: `r` equations over `s` variables,
with `V i` the set of variables occurring in equation `i`. -/
structure Layout where
  /-- The number of equations. -/
  r : ℕ
  /-- The number of variables. -/
  s : ℕ
  /-- The support of each equation: `V i` is the set of variables occurring in equation `i`. -/
  V : Fin r → Finset (Fin s)

/-- An LCS game over the layout `G`, given by the right-hand sides of the equations. -/
structure Game (G : Layout) where
  /-- The right-hand side of each equation. -/
  b : Fin G.r → ZMod 2

namespace Game

end Game

end MIPRE.LCS

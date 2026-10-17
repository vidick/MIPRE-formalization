/-
Copyright (c) 2026 Sean Perazzolo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Perazzolo
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/LCS/Observable.lean (definition bundle: declarations the uploaded statements rest on);
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
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_LCS_Basic
import Definitions.Def_MIPRE_LCS_Common
import Definitions.Def_MIPRE_LCS_Measurement

/-!
# Observables in LCS Games

This module defines the algebraic properties of quantum observables
in the context of Linear Constraint System (LCS) games. An observable
is represented as a self-adjoint, involutive operator.

## Key Definitions
- `IsObservable`: A property of an element $O$ in a star-ring if $O^2=1$ and $O^\dagger=O$.
- `observableOfMeasurementSystem`: Constructs an observable from a binary projector measurement $P$
  as $O = P_0 - P_1$.

## Key Lemmas
- `isObservable_observableOfMeasurementSystem`: Verifies that the difference of projectors
  in a binary measurement forms a valid observable.
-/

namespace MIPRE.LCS

variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]

/-- A binary observable in a star-ring: a self-adjoint involution. -/
structure IsObservable (O : R) : Prop where
  /-- The observable squares to one. -/
  involutive   : O * O = 1
  /-- The observable is self-adjoint. -/
  self_adjoint : star O = O

/-- The `±1`-observable `P₀ - P₁` associated with a binary measurement. -/
def observableOfMeasurementSystem (f : ZMod 2 → R) : R :=
  f 0 - f 1

end MIPRE.LCS

/-
Copyright (c) 2026 Sean Perazzolo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Perazzolo
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/LCS/Measurement.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_LCS_Basic

/-!
# Projector Measurement Systems

This module defines the concept of a projector-valued measurement (PVM) in a general star-ring.
A measurement system is a family of self-adjoint, idempotent, and mutually orthogonal elements
that sum to the identity.

## Key Definitions
- `IsMeasurementSystem`: A property of a family of elements $\{E_i\}_{i \in I}$ indicating
  they form a valid measurement system.
- `inducedMeasurementSystem`: A construction to build a measurement over a smaller outcome space
  given a function $g : I \to J$.

## Key Lemmas
- `IsMeasurementSystem.commute`: Projectors in a measurement system always commute with each other.
- `IsMeasurementSystem.sum_mul_sum`: The product of two sums of projectors corresponds to the sum
  over the intersection of the outcome sets.
-/

namespace MIPRE.LCS

variable {R : Type*} [Ring R] [StarRing R]

/-- A projector-valued measurement in a star-ring: a family of self-adjoint, idempotent,
mutually orthogonal elements that sum to the identity. -/
structure IsMeasurementSystem
  {I : Type*} [Fintype I]
  (f : I → R) : Prop where
  /-- The measurement operators sum to one. -/
  sum_one      : ∑ x, f x = 1
  /-- Each measurement operator is idempotent. -/
  idempotent   : ∀ x, f x * f x = f x
  /-- Distinct measurement operators are orthogonal. -/
  orthogonal   : ∀ x y, x ≠ y → f x * f y = 0
  /-- Each measurement operator is self-adjoint. -/
  self_adjoint : ∀ x, star (f x) = f x

end MIPRE.LCS

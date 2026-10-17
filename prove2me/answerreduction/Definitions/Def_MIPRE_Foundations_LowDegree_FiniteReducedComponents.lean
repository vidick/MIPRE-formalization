/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/FiniteReducedComponents.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Ring

/-!
# Primitive components of a finite ring with bijective squaring

This supplies the algebraic justification for splitting the binary cyclic group
algebra by its fixed vectors. The computations need only multiplication and
linear algebra; the finite permutation argument below is a correctness proof,
not an enumeration performed by the algorithm.
-/

namespace MIPRE.LowDegree

variable {R : Type*} [CommRing R] [Finite R]

/-- A primitive nonzero idempotent sees every idempotent as either zero or itself. -/
def PrimitiveBinaryComponent (e : R) : Prop :=
  e ≠ 0 ∧ e * e = e ∧ ∀ u : R, u * u = u → e * u = 0 ∨ e * u = e

end MIPRE.LowDegree

/-
Copyright (c) 2026 Sean Perazzolo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Perazzolo
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/LCS/Common.lean (definition bundle: declarations the uploaded statements rest on);
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

@[simp] lemma zmod_two_val_one : (1 : ZMod 2).val = 1 := rfl

/-- The sign `(-1)^a` of an `𝔽₂`-value: `1` for `a = 0` and `-1` for `a = 1`. -/
def observableSign (a : ZMod 2) : ℂ :=
  if a = 0 then 1 else -1

end MIPRE.LCS

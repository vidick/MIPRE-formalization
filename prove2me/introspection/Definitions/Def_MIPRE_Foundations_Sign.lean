/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Sign.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.IntervalCases

/-!
# The sign of a bit

`sgn x = (-1)^x` for `x : ZMod 2`, as a complex number. It is the character group of `𝔽₂` written
multiplicatively, and it is what every `±1`-observable in this development is built from: the
observable of a two-outcome measurement, the phase of a Weyl operator in characteristic two, and
the sign a Magic Square constraint carries.

Characteristic two is why this is a *sign* and not a root of unity. Over `𝔽_p` the generalized
Pauli operators carry phases `e^{2πi/p}`; this project's fields are always of admissible size
`q = 2^k`, so `p = 2` and every phase is real. That collapse is worth having in one place.
-/

noncomputable section

namespace MIPRE

/-- `(-1)^x` for a bit `x`. -/
def sgn (x : ZMod 2) : ℂ := if x.val = 1 then -1 else 1

@[simp] theorem sgn_zero : sgn 0 = 1 := by rw [sgn]; norm_num

@[simp] theorem sgn_one : sgn 1 = -1 := by
  rw [sgn, show ZMod.val (1 : ZMod 2) = 1 from rfl, if_pos rfl]

end MIPRE

end

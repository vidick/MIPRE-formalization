/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
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

theorem sgn_add (x y : ZMod 2) : sgn (x + y) = sgn x * sgn y := by
  have hx : x.val < 2 := ZMod.val_lt x
  have hy : y.val < 2 := ZMod.val_lt y
  rw [sgn, sgn, sgn, ZMod.val_add]
  interval_cases h : x.val <;> interval_cases h2 : y.val <;> norm_num

theorem sgn_mul_self (x : ZMod 2) : sgn x * sgn x = 1 := by
  rw [sgn]; split_ifs <;> norm_num

theorem star_sgn (x : ZMod 2) : star (sgn x) = sgn x := by
  rw [sgn]; split_ifs <;> norm_num

@[simp] theorem sgn_zero : sgn 0 = 1 := by rw [sgn]; norm_num

@[simp] theorem sgn_one : sgn 1 = -1 := by
  rw [sgn, show ZMod.val (1 : ZMod 2) = 1 from rfl, if_pos rfl]

theorem sgn_mul_self_eq_one (x : ZMod 2) : sgn x * sgn x = 1 := sgn_mul_self x

/-- `sgn` takes values `±1`, hence modulus one. -/
theorem norm_sgn (x : ZMod 2) : ‖sgn x‖ = 1 := by
  rw [sgn]; split_ifs <;> norm_num

theorem sgn_ne_zero (x : ZMod 2) : sgn x ≠ 0 := by
  rw [sgn]; split_ifs <;> norm_num

/-- `sgn` is its own inverse, so dividing by it is multiplying by it. -/
theorem inv_sgn (x : ZMod 2) : (sgn x)⁻¹ = sgn x :=
  inv_eq_of_mul_eq_one_left (sgn_mul_self x)

/-- Summing `sgn` over both bits gives zero: the character is nontrivial. -/
theorem sum_sgn : ∑ x : ZMod 2, sgn x = 0 := by
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from by decide,
    Finset.sum_insert (by decide), Finset.sum_singleton, sgn_zero, sgn_one]
  ring

end MIPRE

end

/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/Positivity.lean
-/
/-
# Operator-order toolbox

Generic order-theoretic facts about the C⋆-algebra `H →L[ℂ] H` of bounded
operators on a complex Hilbert space, used throughout the formalization of
M. de la Salle, *Orthogonalization of Positive Operator Valued Measures*
(arXiv:2103.14126v2).

Nothing in this file refers to POVMs, von Neumann algebras or the paper's
statements: it collects the elementary Loewner-order manipulations that the
assembly step (`PLAN.md` §1, step **F3**) and the reduction steps use over and
over:

* products of commuting positive operators (`mul_nonneg_of_commute`);
* the two operator inequalities the paper uses for `0 ≤ y ≤ 1`, namely
  `y² ≤ y` (`sq_le_self_of_le_one`) and `(1 - y)² ≤ 1 - y²`
  (`one_sub_sq_le_one_sub_sq'`);
* compressions by a projection commuting with a positive operator
  (`IsStarProjection.mul_le_of_commute`, `IsStarProjection.mul_nonneg_of_commute`);
* the continuous-functional-calculus square root: positivity, the bound
  `√y ≤ 1` for `y ≤ 1`, and the fact that it inherits every commutant
  (`Commute.sqrt`);
* positive linear functionals `φ` on `H →L[ℂ] H`, i.e. `ℂ`-linear maps with
  `0 ≤ φ (x* x)` for the `ComplexOrder` order on `ℂ`: they are monotone
  (`re_le_re_of_le`), real on positives (`im_eq_zero_of_nonneg`), and
  positive on positives (`nonneg_of_nonneg`).

The order on `H →L[ℂ] H` is the Loewner order
(`ContinuousLinearMap.le_def : f ≤ g ↔ (g - f).IsPositive`), for which Mathlib
provides a `StarOrderedRing` structure and the continuous functional calculus.
-/
import Mathlib

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace Orthogonalization

open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Products of commuting positive operators -/

section Order

variable {x y : H →L[ℂ] H}

/-- The product of two **commuting** positive operators is positive.
(Without the commutation hypothesis this is false.) This is Mathlib's
`Commute.mul_nonneg`, restated with the hypotheses in the order in which the
proof uses them. -/
theorem mul_nonneg_of_commute (hx : 0 ≤ x) (hy : 0 ≤ y) (h : Commute x y) : 0 ≤ x * y :=
  h.mul_nonneg hx hy

/-- If `0 ≤ x ≤ 1` then `x² ≤ x`: indeed `x - x² = x (1 - x)` is a product of
commuting positive operators. -/
theorem sq_le_self_of_le_one (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : x * x ≤ x := by
  have hc : Commute x (1 - x) := (Commute.one_right x).sub_right (Commute.refl x)
  have h : 0 ≤ x * (1 - x) := mul_nonneg_of_commute hx0 (sub_nonneg.mpr hx1) hc
  have he : x * (1 - x) = x - x * x := by noncomm_ring
  rw [he] at h
  exact sub_nonneg.mp h

/-- If `0 ≤ s ≤ 1` then `(1 - s)² ≤ 1 - s²`, because
`(1 - s²) - (1 - s)² = 2 (s - s²) = 2 s (1 - s) ≥ 0`.
This is the operator inequality used in the assembly step of the paper. -/
theorem one_sub_sq_le_one_sub_sq' {s : H →L[ℂ] H} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (1 - s) * (1 - s) ≤ 1 - s * s := by
  have h : 0 ≤ s - s * s := sub_nonneg.mpr (sq_le_self_of_le_one hs0 hs1)
  have key : (1 - s * s) - (1 - s) * (1 - s) = (s - s * s) + (s - s * s) := by noncomm_ring
  refine sub_nonneg.mp ?_
  rw [key]
  exact add_nonneg h h

/-- A convenience restatement of `sub_nonneg`: an operator inequality is the
positivity of the difference. -/
theorem le_of_nonneg_sub (h : 0 ≤ y - x) : x ≤ y := sub_nonneg.mp h

/-- A convenience restatement of `sub_nonneg` in the other direction. -/
theorem nonneg_sub_of_le (h : x ≤ y) : 0 ≤ y - x := sub_nonneg.mpr h

/-- Conjugation by a fixed operator is monotone for the Loewner order. -/
theorem conj_le_conj (h : x ≤ y) (c : H →L[ℂ] H) : star c * x * c ≤ star c * y * c :=
  star_left_conjugate_le_conjugate h c

/-- Conjugation by a fixed operator preserves positivity. -/
theorem conj_nonneg (hx : 0 ≤ x) (c : H →L[ℂ] H) : 0 ≤ star c * x * c :=
  star_left_conjugate_nonneg hx c

end Order

/-! ### Compression by a commuting projection -/

namespace IsStarProjection

variable {q b : H →L[ℂ] H}

/-- If `q` is a projection commuting with a positive `b`, then `q b` is positive. -/
theorem mul_nonneg_of_commute (hq : IsStarProjection q) (hb : 0 ≤ b) (h : Commute q b) :
    0 ≤ q * b :=
  Orthogonalization.mul_nonneg_of_commute hq.nonneg hb h

/-- If `q` is a projection commuting with a positive `b`, then `q b ≤ b`,
because `b - q b = (1 - q) b` is a product of commuting positive operators. -/
theorem mul_le_of_commute (hq : IsStarProjection q) (hb : 0 ≤ b) (h : Commute q b) :
    q * b ≤ b := by
  have hc : Commute (1 - q) b := (Commute.one_left b).sub_left h
  have h1 : 0 ≤ (1 - q) * b :=
    Orthogonalization.mul_nonneg_of_commute hq.one_sub_nonneg hb hc
  have he : (1 - q) * b = b - q * b := by noncomm_ring
  rw [he] at h1
  exact sub_nonneg.mp h1

end IsStarProjection

/-! ### The continuous functional calculus square root -/

section Sqrt

variable {x y : H →L[ℂ] H}

/-- The square root of an operator is positive (junk value `0` if the argument
is not positive). Re-export of `CFC.sqrt_nonneg`. -/
theorem sqrt_nonneg (y : H →L[ℂ] H) : 0 ≤ CFC.sqrt y := CFC.sqrt_nonneg y

/-- `√y √y = y` for `0 ≤ y`. Re-export of `CFC.sqrt_mul_sqrt_self`. -/
theorem sqrt_mul_sqrt_self (hy : 0 ≤ y) : CFC.sqrt y * CFC.sqrt y = y :=
  CFC.sqrt_mul_sqrt_self y hy

/-- If `y ≤ 1` then `√y ≤ 1`, by operator monotonicity of the square root and
`√1 = 1`. (Positivity of `y` is not needed: if `y` is not positive then
`√y = 0 ≤ 1`.) -/
theorem sqrt_le_one_of_le_one (hy1 : y ≤ 1) : CFC.sqrt y ≤ 1 := by
  simpa using CFC.sqrt_le_sqrt y 1 hy1

/-- Anything commuting with `y` commutes with `√y`: the square root is a
continuous functional calculus of `y`. (Positivity of `y` is not needed
because of the junk value.) -/
theorem Commute.sqrt (h : Commute x y) : Commute x (CFC.sqrt y) :=
  (Commute.cfcₙ_nnreal h.symm NNReal.sqrt).symm

/-- `Commute.sqrt` with the arguments in the other order. -/
theorem Commute.sqrt_left (h : Commute x y) : Commute (CFC.sqrt x) y :=
  (Commute.sqrt h.symm).symm

end Sqrt

/-! ### Positive linear functionals

A *positive linear functional* on `H →L[ℂ] H` is a `ℂ`-linear map
`φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ` with `0 ≤ φ (star x * x)` for every `x`, the order on
`ℂ` being the `ComplexOrder` one (`0 ≤ z ↔ 0 ≤ z.re ∧ z.im = 0`). We do not
bundle the hypothesis, so that the lemmas apply verbatim to the functional
underlying a normal state. -/

section Functional

variable {φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ}

/-- A positive functional takes nonnegative real values on `star x * x`. -/
theorem re_star_mul_self_nonneg (hφ : ∀ z : H →L[ℂ] H, 0 ≤ φ (star z * z)) (x : H →L[ℂ] H) :
    0 ≤ (φ (star x * x)).re :=
  (Complex.nonneg_iff.mp (hφ x)).1

/-- A positive functional is nonnegative on positive operators: every positive
operator is of the form `star c * c` (`CStarAlgebra.nonneg_iff_eq_star_mul_self`). -/
theorem nonneg_of_nonneg (hφ : ∀ z : H →L[ℂ] H, 0 ≤ φ (star z * z)) {x : H →L[ℂ] H}
    (hx : 0 ≤ x) : 0 ≤ φ x := by
  obtain ⟨c, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hx
  exact hφ c

/-- A positive functional is real on positive operators. -/
theorem im_eq_zero_of_nonneg (hφ : ∀ z : H →L[ℂ] H, 0 ≤ φ (star z * z)) {x : H →L[ℂ] H}
    (hx : 0 ≤ x) : (φ x).im = 0 :=
  (Complex.nonneg_iff.mp (nonneg_of_nonneg hφ hx)).2.symm

/-- A positive functional is monotone (hence so is its real part). -/
theorem le_of_le (hφ : ∀ z : H →L[ℂ] H, 0 ≤ φ (star z * z)) {x y : H →L[ℂ] H}
    (hxy : x ≤ y) : φ x ≤ φ y := by
  have h := nonneg_of_nonneg hφ (sub_nonneg.mpr hxy)
  rw [map_sub] at h
  exact sub_nonneg.mp h

/-- The real part of a positive functional is monotone for the Loewner order. -/
theorem re_le_re_of_le (hφ : ∀ z : H →L[ℂ] H, 0 ≤ φ (star z * z)) {x y : H →L[ℂ] H}
    (hxy : x ≤ y) : (φ x).re ≤ (φ y).re := by
  have h := nonneg_of_nonneg hφ (sub_nonneg.mpr hxy)
  rw [map_sub] at h
  have := (Complex.nonneg_iff.mp h).1
  simpa using this

/-- A positive functional as a bundled `PositiveLinearMap`; this is the input of
Mathlib's GNS construction, which is how the Cauchy–Schwarz inequality of
`Orthogonalization/PhiNorm.lean` is obtained. -/
def toPositiveLinearMap (φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ)
    (hφ : ∀ z : H →L[ℂ] H, 0 ≤ φ (star z * z)) : (H →L[ℂ] H) →ₚ[ℂ] ℂ where
  toLinearMap := φ
  monotone' _ _ hab := le_of_le hφ hab

@[simp]
theorem toPositiveLinearMap_apply (hφ : ∀ z : H →L[ℂ] H, 0 ≤ φ (star z * z)) (x : H →L[ℂ] H) :
    toPositiveLinearMap φ hφ x = φ x := rfl

end Functional

end Orthogonalization

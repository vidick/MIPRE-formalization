/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/PhiNorm.lean
-/
/-
# The seminorm `‖·‖_φ` of a positive functional, and its triangle inequality

For a positive linear functional `φ` on `H →L[ℂ] H` the paper
(M. de la Salle, *Orthogonalization of Positive Operator Valued Measures*,
arXiv:2103.14126v2, Section 1) writes `‖b‖_φ = √(φ (b* b))`, and the assembly
step (`PLAN.md` §1, step **F3**) applies its triangle inequality to *tuples*
`(b_i)_{i ∈ ι}`, i.e. to the norm of `PiLp 2` over the GNS space:

`‖(b_i)‖_φ = √(∑ i, φ (b_i* b_i))`.

This file defines the square of that quantity, `phiNormSq φ b`, as a real
number, and proves what the three-term estimate of step **F3** needs:

* `norm_map_star_mul_le` / `sq_norm_map_star_mul_le`: the Cauchy–Schwarz
  inequality for a positive functional, obtained from Mathlib's GNS
  construction (`PositiveLinearMap.PreGNS`), which turns `x, y ↦ φ (x* y)`
  into an honest (semi-definite) inner product;
* `phiNormSq_nonneg`, `phiNormSq_add_le`: the triangle inequality
  `√(phiNormSq φ (b + c)) ≤ √(phiNormSq φ b) + √(phiNormSq φ c)`;
* `phiNormSq_add_add_lt`: the three-term corollary
  `phiNormSq φ b ≤ ε`, `phiNormSq φ c ≤ ε`, `phiNormSq φ d < ε`
  imply `phiNormSq φ (b + c + d) < 9 ε`, which is exactly the shape in which
  the constant `9` of Theorem 1.2 is produced.

Positivity of `φ` is kept as a bare hypothesis
`hφ : ∀ z, 0 ≤ φ (star z * z)` (with the `ComplexOrder` order on `ℂ`) rather
than bundled, so that the lemmas apply verbatim to the functional underlying a
normal state.
-/
import Mathlib
import MIPRE.Background.Orthonormalization.Orthogonalization.Positivity

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace Orthogonalization

open scoped ComplexOrder BigOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Cauchy–Schwarz for a positive functional -/

section CauchySchwarz

variable {φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ}

/-- **Cauchy–Schwarz inequality** for a positive linear functional, in the form
`|φ (x* y)| ≤ ‖x‖_φ ‖y‖_φ`.

The proof is Mathlib's GNS construction: `φ` becomes a `PositiveLinearMap` and
`x, y ↦ φ (star x * y)` is then the (semi-definite) inner product of
`PositiveLinearMap.PreGNS`, whose Cauchy–Schwarz inequality is
`norm_inner_le_norm`. -/
theorem norm_map_star_mul_le (hφ : ∀ z : H →L[ℂ] H, 0 ≤ φ (star z * z)) (x y : H →L[ℂ] H) :
    ‖φ (star x * y)‖ ≤ Real.sqrt ((φ (star x * x)).re) * Real.sqrt ((φ (star y * y)).re) := by
  set f := toPositiveLinearMap φ hφ with hf
  have h := norm_inner_le_norm (𝕜 := ℂ) (f.toPreGNS x) (f.toPreGNS y)
  rw [PositiveLinearMap.preGNS_inner_def, PositiveLinearMap.preGNS_norm_def,
    PositiveLinearMap.preGNS_norm_def] at h
  simpa only [PositiveLinearMap.ofPreGNS_toPreGNS, hf, toPositiveLinearMap_apply] using h

/-- **Cauchy–Schwarz inequality** for a positive linear functional, squared form:
`|φ (x* y)|² ≤ φ (x* x) φ (y* y)` (real parts; the values on `x* x` are real by
positivity, see `Orthogonalization.im_eq_zero_of_nonneg`). -/
theorem sq_norm_map_star_mul_le (hφ : ∀ z : H →L[ℂ] H, 0 ≤ φ (star z * z)) (x y : H →L[ℂ] H) :
    ‖φ (star x * y)‖ ^ 2 ≤ (φ (star x * x)).re * (φ (star y * y)).re := by
  have hx : 0 ≤ (φ (star x * x)).re := re_star_mul_self_nonneg hφ x
  have hy : 0 ≤ (φ (star y * y)).re := re_star_mul_self_nonneg hφ y
  have h := norm_map_star_mul_le hφ x y
  have hsq := mul_self_le_mul_self (norm_nonneg _) h
  calc ‖φ (star x * y)‖ ^ 2 = ‖φ (star x * y)‖ * ‖φ (star x * y)‖ := sq _
    _ ≤ (Real.sqrt ((φ (star x * x)).re) * Real.sqrt ((φ (star y * y)).re)) *
          (Real.sqrt ((φ (star x * x)).re) * Real.sqrt ((φ (star y * y)).re)) := hsq
    _ = (φ (star x * x)).re * (φ (star y * y)).re := by
        rw [show Real.sqrt ((φ (star x * x)).re) * Real.sqrt ((φ (star y * y)).re) *
              (Real.sqrt ((φ (star x * x)).re) * Real.sqrt ((φ (star y * y)).re)) =
            (Real.sqrt ((φ (star x * x)).re) * Real.sqrt ((φ (star x * x)).re)) *
              (Real.sqrt ((φ (star y * y)).re) * Real.sqrt ((φ (star y * y)).re)) by ring,
          Real.mul_self_sqrt hx, Real.mul_self_sqrt hy]

/-- The real part of `φ (x* y)` is bounded by `‖x‖_φ ‖y‖_φ`. -/
theorem re_map_star_mul_le (hφ : ∀ z : H →L[ℂ] H, 0 ≤ φ (star z * z)) (x y : H →L[ℂ] H) :
    (φ (star x * y)).re ≤
      Real.sqrt ((φ (star x * x)).re) * Real.sqrt ((φ (star y * y)).re) :=
  le_trans (Complex.re_le_norm _) (norm_map_star_mul_le hφ x y)

end CauchySchwarz

/-! ### The squared seminorm of a tuple -/

/-- The square of the seminorm `‖(b_i)‖_φ = √(∑ i, φ (b_i* b_i))` of a tuple of
operators, as a *real* number (the values `φ (b_i* b_i)` are real by
positivity of `φ`; no positivity hypothesis is needed for the definition since
we take real parts). -/
noncomputable def phiNormSq (φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ) {ι : Type*} [Fintype ι]
    (b : ι → H →L[ℂ] H) : ℝ :=
  ∑ i, (φ (star (b i) * b i)).re

variable {φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ} {ι : Type*} [Fintype ι]

/-- Unfolding lemma for `phiNormSq`. -/
theorem phiNormSq_def (b : ι → H →L[ℂ] H) :
    phiNormSq φ b = ∑ i, (φ (star (b i) * b i)).re := rfl

/-- `phiNormSq` is the real part of `φ` applied to the single operator
`∑ i, b_i* b_i`; this is the form in which the conclusion of Theorem 1.2 is
stated. -/
theorem phiNormSq_eq_re_map_sum (b : ι → H →L[ℂ] H) :
    phiNormSq φ b = (φ (∑ i, star (b i) * b i)).re := by
  rw [phiNormSq_def, map_sum, Complex.re_sum]

@[simp]
theorem phiNormSq_zero : phiNormSq φ (0 : ι → H →L[ℂ] H) = 0 := by
  simp [phiNormSq_def]

/-- The squared seminorm of a tuple is nonnegative. -/
theorem phiNormSq_nonneg (hφ : ∀ z : H →L[ℂ] H, 0 ≤ φ (star z * z)) (b : ι → H →L[ℂ] H) :
    0 ≤ phiNormSq φ b :=
  Finset.sum_nonneg fun i _ => re_star_mul_self_nonneg hφ (b i)

omit [Fintype ι] in
/-- Expansion of the squared seminorm of a sum, coordinatewise. -/
theorem re_map_star_add_mul_add (b c : ι → H →L[ℂ] H) (i : ι) :
    (φ (star ((b + c) i) * (b + c) i)).re
      = (φ (star (b i) * b i)).re + (φ (star (b i) * c i)).re
        + (φ (star (c i) * b i)).re + (φ (star (c i) * c i)).re := by
  have hstar : star ((b + c) i) * (b + c) i
      = star (b i) * b i + star (b i) * c i + star (c i) * b i + star (c i) * c i := by
    simp only [Pi.add_apply, star_add]
    noncomm_ring
  rw [hstar, map_add, map_add, map_add]
  simp

/-- **Triangle inequality** for the seminorm `‖·‖_φ` of tuples:
`‖b + c‖_φ ≤ ‖b‖_φ + ‖c‖_φ`.

The proof expands `‖b + c‖_φ²`, bounds each cross term by Cauchy–Schwarz for
`φ` and then sums with the discrete Cauchy–Schwarz inequality
`Real.sum_sqrt_mul_sqrt_le`. -/
theorem phiNormSq_add_le (hφ : ∀ z : H →L[ℂ] H, 0 ≤ φ (star z * z)) (b c : ι → H →L[ℂ] H) :
    Real.sqrt (phiNormSq φ (b + c))
      ≤ Real.sqrt (phiNormSq φ b) + Real.sqrt (phiNormSq φ c) := by
  have hFnn : ∀ i, 0 ≤ (φ (star (b i) * b i)).re := fun i => re_star_mul_self_nonneg hφ (b i)
  have hGnn : ∀ i, 0 ≤ (φ (star (c i) * c i)).re := fun i => re_star_mul_self_nonneg hφ (c i)
  have hBn : 0 ≤ phiNormSq φ b := phiNormSq_nonneg hφ b
  have hCn : 0 ≤ phiNormSq φ c := phiNormSq_nonneg hφ c
  -- Step 1: coordinatewise bound.
  have step1 : ∀ i ∈ (Finset.univ : Finset ι),
      (φ (star ((b + c) i) * (b + c) i)).re
        ≤ (φ (star (b i) * b i)).re
          + 2 * (Real.sqrt ((φ (star (b i) * b i)).re) * Real.sqrt ((φ (star (c i) * c i)).re))
          + (φ (star (c i) * c i)).re := by
    intro i _
    have h1 : (φ (star (b i) * c i)).re
        ≤ Real.sqrt ((φ (star (b i) * b i)).re) * Real.sqrt ((φ (star (c i) * c i)).re) :=
      re_map_star_mul_le hφ (b i) (c i)
    have h2 : (φ (star (c i) * b i)).re
        ≤ Real.sqrt ((φ (star (c i) * c i)).re) * Real.sqrt ((φ (star (b i) * b i)).re) :=
      re_map_star_mul_le hφ (c i) (b i)
    rw [re_map_star_add_mul_add b c i]
    have h2' : (φ (star (c i) * b i)).re
        ≤ Real.sqrt ((φ (star (b i) * b i)).re) * Real.sqrt ((φ (star (c i) * c i)).re) := by
      rw [mul_comm]; exact h2
    linarith
  -- Step 2: sum the coordinatewise bounds.
  have step2 : phiNormSq φ (b + c)
      ≤ phiNormSq φ b
        + 2 * (∑ i, Real.sqrt ((φ (star (b i) * b i)).re)
                      * Real.sqrt ((φ (star (c i) * c i)).re))
        + phiNormSq φ c := by
    calc phiNormSq φ (b + c) = ∑ i, (φ (star ((b + c) i) * (b + c) i)).re := rfl
      _ ≤ ∑ i, ((φ (star (b i) * b i)).re
            + 2 * (Real.sqrt ((φ (star (b i) * b i)).re)
                    * Real.sqrt ((φ (star (c i) * c i)).re))
            + (φ (star (c i) * c i)).re) := Finset.sum_le_sum step1
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
          rfl
  -- Step 3: discrete Cauchy–Schwarz on the cross term.
  have step3 : (∑ i, Real.sqrt ((φ (star (b i) * b i)).re)
                        * Real.sqrt ((φ (star (c i) * c i)).re))
      ≤ Real.sqrt (phiNormSq φ b) * Real.sqrt (phiNormSq φ c) :=
    Real.sum_sqrt_mul_sqrt_le Finset.univ hFnn hGnn
  -- Step 4: recognize a perfect square and take square roots.
  have hsq : phiNormSq φ (b + c)
      ≤ (Real.sqrt (phiNormSq φ b) + Real.sqrt (phiNormSq φ c)) ^ 2 := by
    have e1 : Real.sqrt (phiNormSq φ b) ^ 2 = phiNormSq φ b := Real.sq_sqrt hBn
    have e2 : Real.sqrt (phiNormSq φ c) ^ 2 = phiNormSq φ c := Real.sq_sqrt hCn
    nlinarith [step2, step3, e1, e2]
  calc Real.sqrt (phiNormSq φ (b + c))
      ≤ Real.sqrt ((Real.sqrt (phiNormSq φ b) + Real.sqrt (phiNormSq φ c)) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (phiNormSq φ b) + Real.sqrt (phiNormSq φ c) :=
        Real.sqrt_sq (by positivity)

/-- The triangle inequality in the form used downstream: if each of `b` and `c`
has squared seminorm at most `ε`, then `b + c` has squared seminorm at most
`4 ε`. -/
theorem phiNormSq_add_le_of_le (hφ : ∀ z : H →L[ℂ] H, 0 ≤ φ (star z * z))
    {b c : ι → H →L[ℂ] H} {ε : ℝ} (hb : phiNormSq φ b ≤ ε) (hc : phiNormSq φ c ≤ ε) :
    phiNormSq φ (b + c) ≤ 4 * ε := by
  have hBn : 0 ≤ phiNormSq φ b := phiNormSq_nonneg hφ b
  have hε : 0 ≤ ε := le_trans hBn hb
  have h := phiNormSq_add_le hφ b c
  have hb' : Real.sqrt (phiNormSq φ b) ≤ Real.sqrt ε := Real.sqrt_le_sqrt hb
  have hc' : Real.sqrt (phiNormSq φ c) ≤ Real.sqrt ε := Real.sqrt_le_sqrt hc
  have hsum : Real.sqrt (phiNormSq φ (b + c)) ≤ 2 * Real.sqrt ε := by linarith
  have hSn : 0 ≤ phiNormSq φ (b + c) := phiNormSq_nonneg hφ (b + c)
  nlinarith [Real.sq_sqrt hSn, Real.sq_sqrt hε, Real.sqrt_nonneg (phiNormSq φ (b + c)),
    Real.sqrt_nonneg ε]

/-- **The three-term estimate.** If `b` and `c` have squared seminorm at most
`ε` and `d` has squared seminorm strictly less than `ε`, then `b + c + d` has
squared seminorm strictly less than `9 ε`. This is exactly how the constant `9`
of Theorem 1.2 arises from three applications of the triangle inequality. -/
theorem phiNormSq_add_add_lt (hφ : ∀ z : H →L[ℂ] H, 0 ≤ φ (star z * z))
    {b c d : ι → H →L[ℂ] H} {ε : ℝ} (hε : 0 < ε)
    (hb : phiNormSq φ b ≤ ε) (hc : phiNormSq φ c ≤ ε) (hd : phiNormSq φ d < ε) :
    phiNormSq φ (b + c + d) < 9 * ε := by
  have hBn : 0 ≤ phiNormSq φ b := phiNormSq_nonneg hφ b
  have hCn : 0 ≤ phiNormSq φ c := phiNormSq_nonneg hφ c
  have hDn : 0 ≤ phiNormSq φ d := phiNormSq_nonneg hφ d
  have hSn : 0 ≤ phiNormSq φ (b + c + d) := phiNormSq_nonneg hφ (b + c + d)
  have h1 : Real.sqrt (phiNormSq φ (b + c + d))
      ≤ Real.sqrt (phiNormSq φ (b + c)) + Real.sqrt (phiNormSq φ d) :=
    phiNormSq_add_le hφ (b + c) d
  have h2 : Real.sqrt (phiNormSq φ (b + c))
      ≤ Real.sqrt (phiNormSq φ b) + Real.sqrt (phiNormSq φ c) :=
    phiNormSq_add_le hφ b c
  have hb' : Real.sqrt (phiNormSq φ b) ≤ Real.sqrt ε := Real.sqrt_le_sqrt hb
  have hc' : Real.sqrt (phiNormSq φ c) ≤ Real.sqrt ε := Real.sqrt_le_sqrt hc
  have hd' : Real.sqrt (phiNormSq φ d) < Real.sqrt ε := Real.sqrt_lt_sqrt hDn hd
  have hsum : Real.sqrt (phiNormSq φ (b + c + d)) < 3 * Real.sqrt ε := by linarith
  nlinarith [Real.sq_sqrt hSn, Real.sq_sqrt hε.le, Real.sqrt_nonneg (phiNormSq φ (b + c + d)),
    Real.sqrt_nonneg ε]

end Orthogonalization

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Games

/-!
# Approximating the quantum value from below

Groundwork for `lem:value-lower-approx`, the `MIP* ⊆ RE` direction: a machine that,
given a game `G` and a rational `t`, halts if and only if `val*(G) > t`. It enumerates
candidate strategies with Gaussian-rational entries, computes their values exactly, and
halts on a certificate; `val*` is by definition a supremum over finite-dimensional
tensor-product strategies (`MIPRE.quantumValue`), so no infinite-dimensional truncation
and no semidefinite programming enter.

The decomposition followed here is the one validated in the adversarial campaign
recorded in `vidick/mipre-proof` (ledger nodes `1.1.7.2.1` to `1.1.7.2.6`); see
`planning/ledger-informed-plan.md`. This file carries the part of node `1.1.7.2.1`
that makes the candidate set decidable: an operator-norm constraint on a Hermitian
matrix is equivalent to two positive-semidefiniteness tests, and positive
semidefiniteness of a Gaussian-rational Hermitian matrix is decidable.

Everything is stated through the quadratic form `⟨x| M |x⟩` rather than a matrix norm.
That is faithful — for Hermitian `M` the operator norm *is* the supremum of
`|⟨x| M |x⟩|` over unit `x` — and it keeps the statements independent of which of
Mathlib's several matrix-norm instances is in scope.
-/

namespace MIPRE.ValueApprox

open Matrix
open scoped ComplexOrder

variable {d : Type} [Fintype d] [DecidableEq d]

omit [Fintype d] in
/-- Shifting by a real multiple of the identity keeps a matrix Hermitian. -/
theorem isHermitian_realSmul_one_add {M : Matrix d d ℂ} (hM : M.IsHermitian) (c : ℝ) :
    ((c : ℂ) • (1 : Matrix d d ℂ) + M).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hM]
  simp

omit [Fintype d] in
/-- Likewise for the reflected shift. -/
theorem isHermitian_realSmul_one_sub {M : Matrix d d ℂ} (hM : M.IsHermitian) (c : ℝ) :
    ((c : ℂ) • (1 : Matrix d d ℂ) - M).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hM]
  simp

/-- The quadratic form of a shifted matrix splits. -/
theorem dotProduct_realSmul_one_add (c : ℂ) (M : Matrix d d ℂ) (x : d → ℂ) :
    star x ⬝ᵥ ((c • (1 : Matrix d d ℂ) + M) *ᵥ x)
      = c * (star x ⬝ᵥ x) + star x ⬝ᵥ (M *ᵥ x) := by
  rw [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_smul, smul_eq_mul]

/-- The quadratic form of the reflected shift splits. -/
theorem dotProduct_realSmul_one_sub (c : ℂ) (M : Matrix d d ℂ) (x : d → ℂ) :
    star x ⬝ᵥ ((c • (1 : Matrix d d ℂ) - M) *ᵥ x)
      = c * (star x ⬝ᵥ x) - star x ⬝ᵥ (M *ᵥ x) := by
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_smul, smul_eq_mul]

/-- **Ledger node `1.1.7.2.1`, the norm constraint.** For a Hermitian `M` and a real
`c`, the two positive-semidefiniteness tests on `c·1 + M` and `c·1 - M` hold exactly
when the quadratic form of `M` is sandwiched by `±c⟨x|x⟩` — which for a Hermitian
matrix says `‖M‖ ≤ c`. This is what the enumeration of node `1.1.7.2.2` needs: its
constraint `‖∑ a A^x_a - 1‖ ≤ |A|η` is two psd tests, and psd of a Gaussian-rational
Hermitian matrix is decidable, so membership in the candidate set is decidable. -/
theorem posSemidef_realSmul_one_add_and_sub_iff {M : Matrix d d ℂ} (hM : M.IsHermitian)
    (c : ℝ) :
    (((c : ℂ) • (1 : Matrix d d ℂ) + M).PosSemidef ∧
        ((c : ℂ) • (1 : Matrix d d ℂ) - M).PosSemidef)
      ↔ ∀ x : d → ℂ, -((c : ℂ) * (star x ⬝ᵥ x)) ≤ star x ⬝ᵥ (M *ᵥ x) ∧
          star x ⬝ᵥ (M *ᵥ x) ≤ (c : ℂ) * (star x ⬝ᵥ x) := by
  constructor
  · intro ⟨hadd, hsub⟩ x
    have h1 := hadd.dotProduct_mulVec_nonneg x
    have h2 := hsub.dotProduct_mulVec_nonneg x
    rw [dotProduct_realSmul_one_add] at h1
    rw [dotProduct_realSmul_one_sub] at h2
    refine ⟨sub_nonneg.mp ?_, sub_nonneg.mp h2⟩
    rw [sub_neg_eq_add, add_comm]
    exact h1
  · intro h
    refine ⟨Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
        (isHermitian_realSmul_one_add hM c) fun x => ?_,
      Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
        (isHermitian_realSmul_one_sub hM c) fun x => ?_⟩
    · rw [dotProduct_realSmul_one_add, add_comm, ← sub_neg_eq_add]
      exact sub_nonneg.mpr (h x).1
    · rw [dotProduct_realSmul_one_sub]
      exact sub_nonneg.mpr (h x).2

end MIPRE.ValueApprox

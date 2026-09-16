/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Star.BigOperators

/-!
# The Kronecker product of a family of matrices

The `k`-fold tensor product `M₁ ⊗ ⋯ ⊗ M_k` of matrices on `ℂ^ι`, as a matrix on
`ℂ^{Fin k → ι}`: `(⊗ᵢ Mᵢ) v w = ∏ᵢ Mᵢ (v i) (w i)`. This is what the `k`-fold tensor power of a
strategy measures with (`MIPRE.SyncStrategy.tensorPow`, `Background/Repetition/TensorPower.lean`),
and the four facts about it that the value and PCC computations use: it is multiplicative
(`tensorFamily_mul`), compatible with the adjoint (`tensorFamily_conjTranspose`), sends the
constant family `1` to `1` (`tensorFamily_one`), sums coordinatewise (`sum_tensorFamily`) and
has trace the product of the traces (`trace_tensorFamily`). All are `Fintype.prod_sum`, the
distributivity of a product of sums over `Fin k` into a sum over `Fin k → ι`.

Mathlib's `Matrix.kronecker` is the binary case with the product index `ι × ι`; the family
form is more convenient than iterating it, because `Fin k → ι` needs no reassociation.
-/

namespace MIPRE

open Matrix

variable {k : ℕ} {ι : Type*}

/-- The tensor product `⊗ᵢ Mᵢ` of a family of matrices, as a matrix indexed by `Fin k → ι`. -/
def tensorFamily (M : Fin k → Matrix ι ι ℂ) : Matrix (Fin k → ι) (Fin k → ι) ℂ :=
  Matrix.of fun v w => ∏ i, M i (v i) (w i)

@[simp] theorem tensorFamily_apply (M : Fin k → Matrix ι ι ℂ) (v w : Fin k → ι) :
    tensorFamily M v w = ∏ i, M i (v i) (w i) := rfl

theorem tensorFamily_mul [Fintype ι] (M N : Fin k → Matrix ι ι ℂ) :
    tensorFamily M * tensorFamily N = tensorFamily fun i => M i * N i := by
  ext v w
  simp only [Matrix.mul_apply, tensorFamily_apply]
  rw [Fintype.prod_sum]
  exact Finset.sum_congr rfl fun x _ => (Finset.prod_mul_distrib).symm

theorem tensorFamily_conjTranspose (M : Fin k → Matrix ι ι ℂ) :
    (tensorFamily M)ᴴ = tensorFamily fun i => (M i)ᴴ := by
  ext v w
  simp only [Matrix.conjTranspose_apply, tensorFamily_apply, star_prod]

theorem tensorFamily_one [DecidableEq ι] : tensorFamily (fun _ : Fin k => (1 : Matrix ι ι ℂ)) = 1 := by
  ext v w
  simp only [tensorFamily_apply, Matrix.one_apply, Finset.prod_boole, Finset.mem_univ, true_imp_iff]
  by_cases h : v = w
  · subst h; simp
  · have h' : ¬ ∀ i, v i = w i := fun h' => h (funext h')
    simp [h, h']

theorem trace_tensorFamily [Fintype ι] (M : Fin k → Matrix ι ι ℂ) :
    (tensorFamily M).trace = ∏ i, (M i).trace := by
  simp only [Matrix.trace, Matrix.diag, tensorFamily_apply]
  rw [Fintype.prod_sum]

theorem sum_tensorFamily {A : Type*} [Fintype A] (M : Fin k → A → Matrix ι ι ℂ) :
    ∑ a : Fin k → A, tensorFamily (fun i => M i (a i)) = tensorFamily fun i => ∑ a, M i a := by
  ext v w
  simp only [Matrix.sum_apply, tensorFamily_apply]
  rw [Fintype.prod_sum]

/-- The tensor product of a family of idempotents is idempotent. -/
theorem tensorFamily_mul_self [Fintype ι] {M : Fin k → Matrix ι ι ℂ} (h : ∀ i, M i * M i = M i) :
    tensorFamily M * tensorFamily M = tensorFamily M := by
  rw [tensorFamily_mul]; congr 1; funext i; exact h i

/-- The tensor product of a family of self-adjoint matrices is self-adjoint. -/
theorem tensorFamily_star {M : Fin k → Matrix ι ι ℂ} (h : ∀ i, star (M i) = M i) :
    star (tensorFamily M) = tensorFamily M := by
  rw [Matrix.star_eq_conjTranspose, tensorFamily_conjTranspose]; congr 1; funext i
  rw [← Matrix.star_eq_conjTranspose]; exact h i

end MIPRE

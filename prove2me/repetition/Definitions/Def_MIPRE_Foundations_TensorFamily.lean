/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/TensorFamily.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace

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

end MIPRE

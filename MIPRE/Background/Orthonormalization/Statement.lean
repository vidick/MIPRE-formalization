/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.Orthonormalization.Orthogonalization.Blocks.Main

/-!
# The orthonormalization theorem, in this repository's vocabulary

The bridge to the vendored formalization of de la Salle's POVM orthogonalization
(`Orthogonalization/`, `MIPRE/Background/Orthonormalization/README.md`): blueprint
`thm:orthonormalization` names the declaration here, not the vendored one, as the
repetition chapter names `MIPRE.Repetition.*` rather than the trees behind it.

This is the finite-dimensional case, which is the one the main theorem needs. What the
vendored development proves beyond it, and what it leaves conditional on an undischarged
structure-theory interface, is recorded in `Axioms.lean` and in the blueprint's
`rem:orthonormalization-scope`.

The statement is still phrased with the vendored `IsPOVM`, `IsPVM` and `NormalState`,
which are Mathlib's `VonNeumannAlgebra` vocabulary rather than this repository's
`MIPRE.ProjectiveMeasurement` on `Matrix (Fin d) (Fin d) ℂ`. Restating it there is the
transport along `Matrix.toEuclideanCLM` — positivity, star-projections and the normalized
trace as a state — and is separate work, wanted when a projectivization site actually
consumes this.
-/

namespace MIPRE.Orthonormalization

open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

/-- **Orthonormalization** (blueprint `thm:orthonormalization`): a POVM in a von Neumann
algebra on a finite-dimensional space that is `ε`-nearly projective against a normal state
`φ` — meaning `φ (∑ i, aᵢ²) > 1 - ε` — is `9ε`-close to a projective measurement in the
same algebra. Neither faithfulness nor traciality of `φ` is needed, which is what makes
the lemma usable at the bipartite vector states of the projectivization sites. -/
theorem povm_orthogonalization_finDim (M : VonNeumannAlgebra H)
    (φ : Orthogonalization.NormalState M) {ι : Type*} [Fintype ι] (a : ι → H →L[ℂ] H)
    (ha : Orthogonalization.IsPOVM M a) (ε : ℝ)
    (hε : 1 - ε < (φ (∑ i, a i * a i)).re) :
    ∃ p : ι → H →L[ℂ] H, Orthogonalization.IsPVM M p ∧
      (φ (∑ i, star (a i - p i) * (a i - p i))).re < 9 * ε :=
  Orthogonalization.povm_orthogonalization_finDim_vn M φ a ha ε hε

end MIPRE.Orthonormalization

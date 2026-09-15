/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/Blocks/Main.lean
-/
/-
# Tier T1b: Theorem 1.2 for every von Neumann algebra on a finite-dimensional space

Assembly of the block decomposition (`PLAN.md` §8, T1b): the central
decomposition `1 = ∑ z_j` into minimal central projections
(`Blocks/Minimal.lean`), Theorem 1.2 at each block (`Blocks/Factor.lean`,
through the transport theorem `Blocks/Transport.lean` and the finite-dimensional
bicommutant theorem `Blocks/Bicommutant.lean`), and the gluing
(`Blocks/Glue.lean`).

`orthAt_one` is the engine (any functional positive on `M` and normalized);
`povm_orthogonalization_finDim_vn` is the literal instance of the signed statement
`povm_orthogonalization` (Theorem 1.2) with `[FiniteDimensional ℂ H]` added
(FIDELITY.md, "Instances").
-/
import Mathlib
import MIPRE.Background.Orthonormalization.Orthogonalization.Basic
import MIPRE.Background.Orthonormalization.Orthogonalization.Blocks.Minimal
import MIPRE.Background.Orthonormalization.Orthogonalization.Blocks.Glue
import MIPRE.Background.Orthonormalization.Orthogonalization.Blocks.Factor

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace Orthogonalization

open scoped BigOperators ComplexOrder
open Blocks

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

/-- **Theorem 1.2 for every von Neumann algebra on a finite-dimensional space**, for
functionals positive on `M` and normalized (the engine of tier T1b). -/
theorem orthAt_one (M : VonNeumannAlgebra H) (ι : Type*) [Fintype ι] : OrthAt M 1 ι := by
  obtain ⟨κ, _, z, hz, hzo, hzs⟩ := exists_minimal_central_decomposition M
  exact orthAt_one_of_blocks M z (fun j => (hz j).isCentralProj) hzo hzs ι
    fun j => orthAt_of_isMinimalCentral M (hz j) ι

/-- **Theorem 1.2** (`povm_orthogonalization`) for every von Neumann algebra `M` on a
finite-dimensional space `H`: the instance of the signed statement delivered by tier
T1b. -/
theorem povm_orthogonalization_finDim_vn (M : VonNeumannAlgebra H) (φ : NormalState M)
    {ι : Type*} [Fintype ι] (a : ι → H →L[ℂ] H) (ha : IsPOVM M a) (ε : ℝ)
    (hε : 1 - ε < (φ (∑ i, a i * a i)).re) :
    ∃ p : ι → H →L[ℂ] H, IsPVM M p ∧
      (φ (∑ i, star (a i - p i) * (a i - p i))).re < 9 * ε := by
  obtain ⟨p, hpM, hp, -, hsum, hlt⟩ := orthAt_one M ι φ.toLinearMap φ.nonneg' φ.map_one' a ha.1
    (fun i => (ContinuousLinearMap.nonneg_iff_isPositive _).mpr (ha.2.1 i)) ha.2.2 ε hε
  exact ⟨p, ⟨hpM, hp, hsum⟩, hlt⟩

end Orthogonalization

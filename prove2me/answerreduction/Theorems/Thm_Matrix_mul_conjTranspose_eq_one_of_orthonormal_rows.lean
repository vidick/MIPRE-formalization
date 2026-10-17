/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/Quantum/FiniteHilbert.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/Quantum/FiniteHilbert.lean (statement stub of Matrix.mul_conjTranspose_eq_one_of_orthonormal_rows);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2

open Matrix
open Module
set_option backward.isDefEq.respectTransparency false

theorem Matrix.mul_conjTranspose_eq_one_of_orthonormal_rows
    {𝕜 : Type*} [RCLike 𝕜]
    {m n : Type*} [DecidableEq m] [Fintype n]
    (row : m → EuclideanSpace 𝕜 n)
    (hrow : Orthonormal 𝕜 row) :
    (Matrix.of fun i j => row i j) * (Matrix.of fun i j => row i j)ᴴ =
      (1 : Matrix m m 𝕜) := by sorry

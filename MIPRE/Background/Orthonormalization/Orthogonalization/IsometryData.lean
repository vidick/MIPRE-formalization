/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/IsometryData.lean
-/
/-
# The isometry data of Step F3 (proof-side interface)

In the paper's finite case (Section 3), after Lemma 3.1 produced projections
`q_i` commuting with the `a_i` and with `∑ E(q_i) = 1`, Lemma 3.2 supplies a
partial isometry `u ∈ M_n(M)` with `u u* = ∑ e_{ii} ⊗ q_i`, `u* u = e_{11} ⊗ 1`
and `u |x| = x` for `x = ∑ e_{i1} ⊗ q_i a_i^{1/2}`. Reading `u` block by block,
`w_i := (e_{1i} ⊗ 1) u` is a family of operators on `H` with

* (W1) `∑ w_i* w_i = 1`,
* (W2) `w_i w_j* = δ_{ij} q_i`,
* (W3) `w_i √y = q_i √a_i` where `y = ∑ q_i a_i`.

Everything the assembly (`Assembly.lean`) needs is (W1)–(W3); the PVM is
`p_i = w_i* w_i`. This file only defines the interface; it is produced in
finite dimension by `FinDim/Isometry.lean` and in general from the comparison
theory of the structure-theory interface (PLAN.md T3). Nothing here is a
statement of the paper.
-/
import Mathlib

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace Orthogonalization

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The block-wise partial isometry of Lemma 3.2 / the proof of Theorem 1.2 in
the finite case: (W1) `∑ wᵢ* wᵢ = 1`, (W2) `wᵢ wⱼ* = δᵢⱼ qᵢ`,
(W3) `wᵢ √(∑ qⱼ aⱼ) = qᵢ √aᵢ`. -/
structure IsometryData {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a q w : ι → H →L[ℂ] H) : Prop where
  sum_star_mul : ∑ i, star (w i) * w i = 1
  mul_star : ∀ i j, w i * star (w j) = if i = j then q i else 0
  mul_sqrt : ∀ i, w i * CFC.sqrt (∑ j, q j * a j) = q i * CFC.sqrt (a i)

end Orthogonalization

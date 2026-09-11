/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Resolver/ArenaDef.lean
-/
/-
# The common finite-trace resolver arena: the consumed-form structure (node 1.2.5)

Consumed form of Theorem 4.1 (04_resolver_corner.tex, thm
common-resolver-arena): given finite families of `[0,1]`-effects with
positive refinements in a tracial standard-form algebra `M`, there is a
single finite tracial standard-form algebra `N` carrying POVMs and, for
every density and every index pair, a branch vector whose norm and
answer weights reproduce the exact pairings
`τ(σ* F_i σ G_j)` and `τ(σ* F_i^a σ G_j^b)` (eqs joint-branch-norm,
joint-branch-answer-weight). On `L²(N)` Alice uses `L(𝖠_i^a)` and Bob
uses `R(𝖡_j^b)`, so all measurement operators commute — the shape the
correlated-sampling section consumes.

Encoding decisions (for the fidelity review):
- Totals are derived: the families enter through their refinements
  (`F i = ∑ a, F i a`, eq effect-refinements), so the theorem's
  `F_i = ∑_a F_i^a` compatibility is definitional.
- `0 ≤ F_i ≤ 1` (eq resolver-families) is encoded in the D13 cone:
  `IsPosElem (F i a)` per refinement piece (which also gives the
  positivity of the refinements) and `IsPosElem (1 - ∑ a, F i a)` for
  the upper bound.
- The corner internals of the construction — the source projection
  `p₀`, the canonical copy of `M`, the columns `c_i` and rows `d_j` with
  their square and refinement identities (eqs resolver-square-identities,
  resolver-refinement-identities), the unnormalized trace `Tr_N` and the
  normalization unitary `U_Q` — are the *proof* of this statement and
  the vocabulary of nodes 1.2.5.1–1.2.5.6 and 1.2.6; they will be
  packaged as an extension of this structure when the resolver entropy
  lemma (node 1.2.6) is stated. This statement packages only what
  sections 5–6 consume from the theorem's conclusion: the algebra, the
  POVMs, and the branch vectors with their two exact numerical
  identities (DIFFERENCES.md D14).
- The identities are stated as ℂ-equalities of inner products with
  traces; both sides are real (commuting positive pairings against
  hermitian traces), so this is the strong form of the manuscript's
  numerical displays.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Tracial.Interface

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

open scoped BigOperators InnerProductSpace

/-- **The resolver arena, consumed form** (node 1.2.5;
04_resolver_corner.tex, thm common-resolver-arena): a finite tracial
standard-form algebra `N`, POVMs `𝖠_i` (Alice) and `𝖡_j` (Bob) in `N`,
and for every density `σ ∈ M` and index pair `(i, j)` a branch vector
`Φ_{ij} ∈ L²(N)` reproducing the exact pairings of the input effect
families: `‖Φ_{ij}‖² = τ(σ* F_i σ G_j)` (eq joint-branch-norm) and
`⟪Φ_{ij}, L(𝖠_i^a) R(𝖡_j^b) Φ_{ij}⟫ = τ(σ* F_i^a σ G_j^b)` (eq
joint-branch-answer-weight), with the totals `F_i = ∑_a F_i^a`,
`G_j = ∑_b G_j^b` (eq effect-refinements). -/
structure ResolverArena (M : StdTracialAlgebra.{0})
    {I J A B : Type} [Fintype I] [Fintype J] [Fintype A] [Fintype B]
    (F : I → A → M.A) (G : J → B → M.A) : Type 1 where
  N : StdTracialAlgebra.{0}
  Ameas : I → A → N.A
  Bmeas : J → B → N.A
  Ameas_pos : ∀ i a, IsPosElem (Ameas i a)
  Bmeas_pos : ∀ j b, IsPosElem (Bmeas j b)
  Ameas_sum : ∀ i, (∑ a : A, Ameas i a) = 1
  Bmeas_sum : ∀ j, (∑ b : B, Bmeas j b) = 1
  branch : M.A → I → J → N.H
  branch_norm : ∀ (σ : M.A) (i : I) (j : J),
    ⟪branch σ i j, branch σ i j⟫_ℂ
      = M.τ (star σ * ((∑ a : A, F i a) * σ * (∑ b : B, G j b)))
  branch_answer : ∀ (σ : M.A) (i : I) (j : J) (a : A) (b : B),
    ⟪branch σ i j,
        N.L (Ameas i a) (N.Rop (Bmeas j b) (branch σ i j))⟫_ℂ
      = M.τ (star σ * (F i a * σ * G j b))


end CommutingRepetition

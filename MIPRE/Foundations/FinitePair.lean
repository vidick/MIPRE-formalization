/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.ModelStrategy

@[expose] public section

/-!
# Finite pairs: bipartite models whose two algebras carry faithful tracial states

Phase 6 of `planning/mipco-track.md` (`reports/lidt-co-audit.md`, §3.4) replaces the hypothesis
`LIDT.Simul.SoundCo` — soundness of the low-individual-degree test in the model of every
commuting-operator strategy, with an arbitrary vector state — by soundness in a smaller class of
models, the **finite pairs**: the two players' algebras are each other's commutants on the model's
space, and both carry a faithful normal tracial state. The state of the model stays arbitrary.
What the smaller class buys is a trace on both algebras, which the finite-dimensional proof's
two non-dimension-free steps (its semidefinite program and its orthonormalization) can be
replaced with; what makes it enough is that `ω_co` is approached by projective strategies in
finite pairs, and that the class is closed under the ancilla extensions the Pauli basis analysis
uses (`IsFinitePair.expand`, `MIPRE/Foundations/FinitePairExpand.lean`). The hypothesis
`LIDT.Simul.SoundFin` asks for soundness only in the narrower class of **dyadic pairs**, the finite
pairs whose two algebras have unital dyadic matrix units (`BipartiteModel.IsDyadicPair` and
`CommutingFinitePairApprox`, `MIPRE/Foundations/DyadicPair.lean`), in which neither algebra has an
abelian projection.

* **`VecTrace s`**: a faithful tracial state on a set `s` of operators, given by finitely many
  vectors, `τ(x) = ∑ₖ ⟪gₖ, x gₖ⟫` with `∑ₖ ‖gₖ‖² = 1`. A finite sum of vector functionals is
  normal (even weak-operator continuous), and the form survives amplification by matrices, which
  a single vector state does not. Faithfulness is stated as separation: an operator of `s`
  vanishing at every `gₖ` vanishes, which is `τ(x⋆ x) = ∑ₖ ‖x gₖ‖² = 0 → x = 0`.
* **`BipartiteModel.IsFinitePair M`** (`def:finite-pair`): the players' represented operators,
  `π (πA a)` and `π (πB b)`, act injectively, each player's operators are exactly the operators
  commuting with the other player's, and each player's operators carry a `VecTrace`. The order
  of each player's algebra is its own. It agrees with the operator order, since a positive
  operator of a commutant has its square root there, but no lemma here states this yet; the
  soundness interface `LIDT.Simul.SoundIn` reads only projections, which are positive in both.

Two features of the class bear on the port of the soundness proof to it (C6b of the plan).
* **Finite coupling.** A `VecTrace` has finitely many vectors, so the class is narrower than that of
  all pairs with faithful normal traces: `ℓ^∞(ℕ)` acting blockwise on `⊕ₙ ℂⁿ`, with commutant
  `⊕ₙ Mₙ`, is excluded. This is deliberate. The standard form needs one vector, and the extensions,
  the doubling `H ⊕ H` and amplification by a tracial algebra in standard form
  (`MIPRE/Background/Repetition/Amplify.lean`) all stay inside the class, while corner
  reductions `p 𝒜 p` do not. The vendored II₁ orthonormalization tier takes families indexed by
  `ℕ` with summable squared norms, of which a `VecTrace` padded with zeros is one.
* **Type I pairs.** The class contains type I pairs with diffuse centre, such as `L^∞[0, 1]` acting
  on `L²[0, 1]`, its own commutant, with the trace vector `1`. Their projections are abelian, and
  the orthonormalization step of the port needs none, so `LIDT.Simul.SoundFin` asks for soundness
  only in dyadic pairs, which exclude them; the value lemma reaches dyadic pairs by amplifying by
  an algebra with unital dyadic matrix units, the twisted Pauli algebra
  (`reports/c6b-paper-proofs.md`, §3).
-/

namespace MIPRE

open scoped InnerProductSpace

/-- **A faithful tracial state given by finitely many vectors** on a set `s` of operators on a
Hilbert space: `τ(x) = ∑ₖ ⟪gₖ, x gₖ⟫`, normalized, tracial on `s`, and faithful on `s` in the form
that the vectors `gₖ` together separate `s`. -/
structure VecTrace {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (s : Set (H →L[ℂ] H)) where
  /-- The number of vectors. -/
  n : ℕ
  /-- The vectors. -/
  g : Fin n → H
  /-- The state is normalized: `τ(1) = ∑ₖ ‖gₖ‖² = 1`. -/
  norm_sq_sum : ∑ k, ‖g k‖ ^ 2 = 1
  /-- The state is tracial on the set. -/
  trace_mul_comm : ∀ x ∈ s, ∀ y ∈ s,
    ∑ k, ⟪g k, (x * y) (g k)⟫_ℂ = ∑ k, ⟪g k, (y * x) (g k)⟫_ℂ
  /-- The vectors separate the set: the state is faithful on it. -/
  separating : ∀ x ∈ s, (∀ k, x (g k) = 0) → x = 0

namespace BipartiteModel

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]

/-- The first player's operators on the model's space. -/
def opsA (M : BipartiteModel 𝒞 𝒜 ℬ) : Set (M.H →L[ℂ] M.H) :=
  Set.range fun a : 𝒜 => M.π (M.πA a)

/-- The second player's operators on the model's space. -/
def opsB (M : BipartiteModel 𝒞 𝒜 ℬ) : Set (M.H →L[ℂ] M.H) :=
  Set.range fun b : ℬ => M.π (M.πB b)

/-- **A finite pair** (`def:finite-pair`): the two players' algebras act injectively on the
model's space, each player's operators are exactly the operators commuting with the other
player's (so both are von Neumann algebras, each other's commutants), and both carry a faithful
tracial state given by finitely many vectors. The model's state is arbitrary. -/
structure IsFinitePair (M : BipartiteModel 𝒞 𝒜 ℬ) : Prop where
  /-- The first player's algebra acts injectively. -/
  injA : Function.Injective fun a : 𝒜 => M.π (M.πA a)
  /-- The second player's algebra acts injectively. -/
  injB : Function.Injective fun b : ℬ => M.π (M.πB b)
  /-- Every operator commuting with the second player's is the first player's. -/
  commutantA : ∀ T : M.H →L[ℂ] M.H, (∀ b : ℬ, Commute T (M.π (M.πB b))) → T ∈ M.opsA
  /-- Every operator commuting with the first player's is the second player's. -/
  commutantB : ∀ T : M.H →L[ℂ] M.H, (∀ a : 𝒜, Commute T (M.π (M.πA a))) → T ∈ M.opsB
  /-- The first player's operators carry a faithful tracial state. -/
  traceA : Nonempty (VecTrace M.opsA)
  /-- The second player's operators carry a faithful tracial state. -/
  traceB : Nonempty (VecTrace M.opsB)

end BipartiteModel

end MIPRE

end

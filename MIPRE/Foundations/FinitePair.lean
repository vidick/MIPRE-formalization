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
finite pairs (`CommutingFinitePairApprox`, proved on the `Background` side from Lin's tracial
density), and that the class is closed under the ancilla extensions the Pauli basis analysis
uses (`IsFinitePair.expand`, `MIPRE/Foundations/FinitePairExpand.lean`).

* **`VecTrace s`**: a faithful tracial state on a set `s` of operators, given by finitely many
  vectors, `τ(x) = ∑ₖ ⟪gₖ, x gₖ⟫` with `∑ₖ ‖gₖ‖² = 1`. A finite sum of vector functionals is
  normal (even weak-operator continuous), and the form survives amplification by matrices, which
  a single vector state does not. Faithfulness is stated as separation: an operator of `s`
  vanishing at every `gₖ` vanishes, which is `τ(x⋆ x) = ∑ₖ ‖x gₖ‖² = 0 → x = 0`.
* **`BipartiteModel.IsFinitePair M`** (`def:finite-pair`): the players' represented operators,
  `π (πA a)` and `π (πB b)`, act injectively, each player's operators are exactly the operators
  commuting with the other player's, and each player's operators carry a `VecTrace`. The order
  of each player's algebra is its own; since the algebras are star-ordered rings and each image
  is a commutant, closed under square roots, it is the operator order.
* **`CommutingFinitePairApprox`**: below `ω_co(G)`, and above `0`, lies the value of a projective
  strategy for `G` in a finite pair on a Hilbert space of `Type`.
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

/-- **`ω_co` is approached by projective strategies in finite pairs**: below `ω_co(G)`, and
above `0`, lies the value of a projective strategy for `G` in a finite pair on a Hilbert space of
`Type`. Proved from Lin's tracial density (`MIPRE.Repetition.commutingFinitePairApprox`). -/
def CommutingFinitePairApprox : Prop :=
  ∀ {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B] (G : Game X Y A B) {t : ℝ},
    0 ≤ t → t < commutingOperatorValue G →
      ∃ (𝒞 𝒜 ℬ : Type) (_ : Ring 𝒞) (_ : StarRing 𝒞) (_ : Algebra ℂ 𝒞) (_ : Ring 𝒜)
        (_ : StarRing 𝒜) (_ : Algebra ℂ 𝒜) (_ : Ring ℬ) (_ : StarRing ℬ) (_ : Algebra ℂ ℬ)
        (_ : PartialOrder 𝒜) (_ : StarOrderedRing 𝒜) (_ : PartialOrder ℬ)
        (_ : StarOrderedRing ℬ) (_ : StarModule ℂ 𝒜) (_ : StarProper 𝒜) (_ : StarModule ℂ ℬ)
        (_ : StarProper ℬ) (M : BipartiteModel.{0} 𝒞 𝒜 ℬ),
        M.IsFinitePair ∧ ∃ S : M.ProjStrat G, t < S.value

end MIPRE

end

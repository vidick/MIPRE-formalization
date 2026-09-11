/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Statement.lean
-/
/-
# The main theorem, with complete definitions, in one standalone file

This file depends on Mathlib only. It contains every definition needed to
state the uniform direct parallel repetition theorem for commuting-operator
strategies (07_main_theorem.tex, Theorem 7.1), and the statement itself,
`UniformParallelRepetition`, as a proposition — the convention Mathlib uses
for `FermatLastTheorem : Prop`. Apart from the proof obligations inside the
definition of the repeated game, it contains no proofs.

* Part 1 — games, direct repetition, commuting-operator strategies and the
  commuting value `ω^co` (02_preliminaries.tex).
* Part 2 — the tracial standard form and Lin's density theorem (Lin,
  arXiv:2304.01940, Theorem 3.2). Once the one external input of the
  manuscript; the development now *proves* it, as
  `MainStatement.tracialDensity`, so these definitions are the vocabulary
  of a theorem rather than of a hypothesis.
* Part 3 — the statement, unconditional.

The proposition is proved by the development:
`MainStatement.uniform_parallel_repetition : UniformParallelRepetition` in
`CommutingRepetition/StatementBridge.lean`, from the root theorem
`CommutingRepetition.uniform_parallel_repetition` (MainTheorem/Main.lean),
with no hypotheses and no axioms beyond `propext`, `Classical.choice`,
`Quot.sound` (checked by `scripts/AxiomGate.lean`).

Every definition below is copied character-for-character from its home
file in the development (Game/Basic, Game/Strategy, Game/Value,
Tracial/Interface, Tracial/Density), whose statements are adversarially
reviewed and hash-signed in FIDELITY.md, and the body of
`UniformParallelRepetition` is the conclusion of the root theorem
verbatim; CI enforces both (`scripts/statement_copy_check.py`).

To check this file on its own: `lake env lean CommutingRepetition/Statement.lean`
from `lean/`, or from any project that has Mathlib.
-/
import Mathlib

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace MainStatement

open scoped BigOperators InnerProductSpace

universe u

/-! ## Part 1 — Games, direct repetition, commuting-operator strategies, ω^co -/

/-- A finite two-player one-round game `G = (X, Y, A, B, μ, V)`:
finite nonempty question sets `X, Y` and answer sets `A, B` (nonemptiness is
assumed at the theorems that need it), a probability distribution `μ` on
`X × Y` given by `questionWeight`, and an acceptance function
`payoff = V(a, b | x, y) ∈ [0,1]`.
[02_preliminaries.tex, "Games and direct repetition"; audit def `game`] -/
structure Game (X Y A B : Type*)
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B] where
  questionWeight : X → Y → ℝ
  weight_nonneg : ∀ x y, 0 ≤ questionWeight x y
  weight_normalized : (∑ x : X, ∑ y : Y, questionWeight x y) = 1
  payoff : X → Y → A → B → ℝ
  payoff_nonneg : ∀ x y a b, 0 ≤ payoff x y a b
  payoff_le_one : ∀ x y a b, payoff x y a b ≤ 1

namespace Game

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- Direct `n`-fold repetition `G^{⊗n}`: product question law on
`(Fin n → X) × (Fin n → Y)` and product acceptance
`V^{⊗n}(a^n, b^n | x^n, y^n) = ∏ᵢ V(aᵢ, bᵢ | xᵢ, yᵢ)`.
`n = 0` is a total-function extension outside the paper's `n ≥ 1` scope
(empty products; the main theorem hypothesizes `1 ≤ n`).
[02_preliminaries.tex, eq for V^{⊗n}; audit def `direct_repetition`] -/
def «repeat» (G : Game X Y A B) (n : ℕ) :
    Game (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B) where
  questionWeight xs ys := ∏ i : Fin n, G.questionWeight (xs i) (ys i)
  weight_nonneg xs ys :=
    Finset.prod_nonneg fun i _ => G.weight_nonneg (xs i) (ys i)
  weight_normalized := by
    classical
    calc
      (∑ xs : Fin n → X, ∑ ys : Fin n → Y,
        ∏ i : Fin n, G.questionWeight (xs i) (ys i)) =
          ∑ xs : Fin n → X, ∏ i : Fin n, ∑ y : Y,
            G.questionWeight (xs i) y := by
              apply Finset.sum_congr rfl
              intro xs _
              exact (Fintype.prod_sum
                (fun i : Fin n => fun y : Y => G.questionWeight (xs i) y)).symm
      _ = ∏ _i : Fin n, ∑ x : X, ∑ y : Y,
            G.questionWeight x y := by
              exact (Fintype.prod_sum
                (fun _i : Fin n => fun x : X => ∑ y : Y,
                  G.questionWeight x y)).symm
      _ = 1 := by simp [G.weight_normalized]
  payoff xs ys as bs := ∏ i : Fin n, G.payoff (xs i) (ys i) (as i) (bs i)
  payoff_nonneg xs ys as bs :=
    Finset.prod_nonneg fun i _ => G.payoff_nonneg (xs i) (ys i) (as i) (bs i)
  payoff_le_one xs ys as bs :=
    Finset.prod_le_one
      (fun i _ => G.payoff_nonneg (xs i) (ys i) (as i) (bs i))
      (fun i _ => G.payoff_le_one (xs i) (ys i) (as i) (bs i))

end Game

/-- A commuting-operator strategy over question alphabets `X, Y` and answer
alphabets `A, B`: a complex Hilbert space `H`, a unit vector `ψ`, and
POVM families `E x` (Alice) and `F y` (Bob) of positive continuous linear
maps summing to `1`, with every Alice effect commuting with every Bob
effect. [02_preliminaries.tex; audit def `commuting_strategy`] -/
structure CommutingStrategy (X Y A B : Type)
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B] where
  H : Type u
  [normedAddCommGroup : NormedAddCommGroup H]
  [innerProductSpace : InnerProductSpace ℂ H]
  [completeSpace : CompleteSpace H]
  ψ : H
  ψ_norm : ‖ψ‖ = 1
  E : X → A → H →L[ℂ] H
  F : Y → B → H →L[ℂ] H
  E_pos : ∀ x a, (E x a).IsPositive
  F_pos : ∀ y b, (F y b).IsPositive
  E_sum : ∀ x, (∑ a : A, E x a) = 1
  F_sum : ∀ y, (∑ b : B, F y b) = 1
  commutes : ∀ x y a b, Commute (E x a) (F y b)

attribute [instance] CommutingStrategy.normedAddCommGroup
  CommutingStrategy.innerProductSpace CommutingStrategy.completeSpace

namespace CommutingStrategy

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The correlation table of a strategy:
`p(a, b | x, y) = ⟪ψ, E_x^a F_y^b ψ⟫` (a real number; the inner product is
real because the commuting product of self-adjoint effects is
self-adjoint). [02_preliminaries.tex, success-probability display] -/
noncomputable def correlation (S : CommutingStrategy.{u} X Y A B)
    (x : X) (y : Y) (a : A) (b : B) : ℝ :=
  (⟪S.ψ, S.E x a (S.F y b S.ψ)⟫_ℂ).re

end CommutingStrategy

section Value

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- A correlation table on alphabets `X, Y, A, B`. -/
abbrev Correlation (X Y A B : Type*) := X → Y → A → B → ℝ

/-- Realizability by a commuting-operator strategy at universe 0 (the
Hilbert space is a `Type`; the restriction is disclosed in DIFFERENCES.md,
D1, and is content-free for the finite alphabets in scope). -/
def IsCommutingCorrelation (p : Correlation X Y A B) : Prop :=
  ∃ S : CommutingStrategy.{0} X Y A B, S.correlation = p

namespace Game

/-- Expected payoff of a correlation in the game `G`:
`win_G(p) = ∑ μ(x,y) V(a,b|x,y) p(a,b|x,y)` — a linear functional of the
correlation table. -/
def win (G : Game X Y A B) (p : Correlation X Y A B) : ℝ :=
  ∑ x : X, ∑ y : Y, ∑ a : A, ∑ b : B,
    G.questionWeight x y * G.payoff x y a b * p x y a b

/-- The commuting-operator value `ω^co(G)`: the supremum of winning
probabilities over commuting-operator strategies.
[02_preliminaries.tex, "The supremum of this expression is the commuting
value"; non-attainment is never assumed anywhere downstream.] -/
noncomputable def omegaCO (G : Game X Y A B) : ℝ :=
  sSup (Set.range fun S : CommutingStrategy.{0} X Y A B =>
    G.win S.correlation)

end Game

end Value

/-! ## Part 2 — The tracial standard form and Lin's density theorem -/

/-- Algebraic positivity: `a` is a finite sum of hermitian squares
`∑ᵢ cᵢ* cᵢ` — the algebraic positive cone of a ∗-ring. In a C*-algebra
this coincides with the usual positive cone. [DIFFERENCES.md D13] -/
def IsPosElem {A : Type*} [AddCommMonoid A] [Mul A] [Star A] (a : A) : Prop :=
  ∃ (k : ℕ) (c : Fin k → A), a = ∑ i, star (c i) * c i

/-- Standard form of a tracial ∗-algebra: carrier `A` with a normalized
trace `τ`, the GNS Hilbert space `H = L²(A, τ)` with dense embedding `ι`,
commuting left and right actions `L`, `R`, and the evaluation identities.
[02_preliminaries.tex, "Finite tracial standard form"] -/
structure StdTracialAlgebra : Type (u + 1) where
  A : Type u
  [ringA : Ring A]
  [starRingA : StarRing A]
  [algebraA : Algebra ℂ A]
  [starModuleA : StarModule ℂ A]
  τ : A →ₗ[ℂ] ℂ
  τ_one : τ 1 = 1
  τ_mul_comm : ∀ a b : A, τ (a * b) = τ (b * a)
  τ_star : ∀ a : A, τ (star a) = star (τ a)
  H : Type u
  [nacgH : NormedAddCommGroup H]
  [ipsH : InnerProductSpace ℂ H]
  [completeH : CompleteSpace H]
  ι : A →ₗ[ℂ] H
  ι_dense : DenseRange ι
  ι_inner : ∀ a b : A, ⟪ι a, ι b⟫_ℂ = τ (star a * b)
  L : A →⋆ₐ[ℂ] (H →L[ℂ] H)
  R : Aᵐᵒᵖ →⋆ₐ[ℂ] (H →L[ℂ] H)
  L_apply : ∀ a b : A, L a (ι b) = ι (a * b)
  R_apply : ∀ a b : A, R (MulOpposite.op a) (ι b) = ι (b * a)
  LR_commute : ∀ a b : A, Commute (L a) (R (MulOpposite.op b))

attribute [instance] StdTracialAlgebra.ringA StdTracialAlgebra.starRingA
  StdTracialAlgebra.algebraA StdTracialAlgebra.starModuleA
  StdTracialAlgebra.nacgH StdTracialAlgebra.ipsH StdTracialAlgebra.completeH

/-- ℓ¹ distance between two correlation tables on common finite alphabets. -/
def l1Dist {X Y A B : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (p q : Correlation X Y A B) : ℝ :=
  ∑ x : X, ∑ y : Y, ∑ a : A, ∑ b : B, |p x y a b - q x y a b|

/-- A tracially embeddable correlation on common alphabets, in the exact
shape of Lin's Definition 3.1: standard form of a tracial algebra, density
`σ ∈ M₊` with `τ(σ²) = 1`, Alice POVMs in `M` acting on the left, Bob
POVMs given by positive operators in the COMMUTANT of the left action. -/
structure TraciallyEmbeddableCorrelation (Xc Ac : Type)
    [Fintype Xc] [Fintype Ac] : Type 1 where
  M : StdTracialAlgebra.{0}
  σ : M.A
  σ_pos : IsPosElem σ
  σ_normalized : M.τ (star σ * σ) = 1
  E : Xc → Ac → M.A
  E_pos : ∀ x a, IsPosElem (E x a)
  E_sum : ∀ x, (∑ a : Ac, E x a) = 1
  G : Xc → Ac → M.H →L[ℂ] M.H
  G_pos : ∀ y b, (G y b).IsPositive
  G_sum : ∀ y, (∑ b : Ac, G y b) = 1
  G_commutant : ∀ y b (m : M.A), Commute (G y b) (M.L m)

namespace TraciallyEmbeddableCorrelation

variable {Xc Ac : Type} [Fintype Xc] [Fintype Ac]

/-- The correlation table realized by a tracially embeddable strategy in
commutant form: `p(a, b | x, y) = ⟪ι σ, L(E_x^a) G_y^b (ι σ)⟫`. -/
noncomputable def toCorrelation (q : TraciallyEmbeddableCorrelation Xc Ac) :
    Correlation Xc Xc Ac Ac := fun x y a b =>
  (⟪q.M.ι q.σ, q.M.L (q.E x a) (q.G y b (q.M.ι q.σ))⟫_ℂ).re

end TraciallyEmbeddableCorrelation

/-- **Lin's tracial density theorem** (arXiv:2304.01940, Thm 3.2): for all
finite common alphabets, every commuting-operator correlation is an ℓ¹-limit
of tracially embeddable correlations. The name says "hypothesis" for
historical reasons — it was the manuscript's one external input, and the
name is load-bearing for `scripts/statement_copy_check.py` and the fidelity
ledger — but the development *proves* it: `MainStatement.tracialDensity` in
`StatementBridge.lean`, transferred from
`CommutingRepetition.Density.tracialDensity`. The main theorem therefore
takes no hypothesis. -/
def TracialDensityHypothesis : Prop :=
  ∀ (Xc Ac : Type) [Fintype Xc] [Fintype Ac] [Nonempty Xc] [Nonempty Ac],
    ∀ p : Correlation Xc Xc Ac Ac, IsCommutingCorrelation p →
      ∀ δ : ℝ, 0 < δ →
        ∃ q : TraciallyEmbeddableCorrelation Xc Ac,
          l1Dist p q.toCorrelation < δ

/-! ## Part 3 — The statement -/

/-- **Uniform direct parallel repetition for commuting-operator
strategies** (07_main_theorem.tex, Theorem 7.1), as a proposition: there is
a universal `c > 0` such that for every finite game `G` with payoffs in
`[0,1]` and every `n ≥ 1`,
`ω^co(G^{⊗n}) ≤ exp(−c·n·ε⁷/(ε + log(|A||B|)))` where `ε = 1 − ω^co(G)`
(when `ε = log(|A||B|) = 0` the quotient is `0/0 = 0` in Lean, the
manuscript's convention). Unconditional: Lin's density theorem
(`TracialDensityHypothesis` above) is itself proved by the development, as
`MainStatement.tracialDensity`. Proved in `StatementBridge.lean`. -/
def UniformParallelRepetition : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ (X Y A B : Type) [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
      [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
      (G : Game X Y A B) (n : ℕ), 1 ≤ n →
      (G.«repeat» n).omegaCO ≤
        Real.exp
          (-(c * ((1 - G.omegaCO) ^ 7 /
            ((1 - G.omegaCO) +
              Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)))))
            * (n : ℝ))

end MainStatement

/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Tracial/Density.lean
-/
/-
# The tracial density hypothesis (Lin's theorem, hypothesis-parameterized)

Encoding decision D5. This file contains NO axiom: Lin's density theorem
(arXiv:2304.01940, Definition 3.1 and Theorem 3.2, verified against the
author's self-citation in arXiv:2510.07162 — see AUDIT.md §1) enters the
development exclusively as the named Prop `TracialDensityHypothesis`,
taken as an explicit hypothesis by the main theorem.

Faithfulness notes (fidelity review #2 checklist):
- common alphabets for both players (`Xc` questions, `Ac` answers), per
  Lin's statement; the asymmetric case is recovered by the manuscript's
  tagging construction (03_tracial_reduction.tex, nodes 1.1.2-1.1.3);
- Bob's effects lie in the COMMUTANT of the left action, exactly as in
  Lin's Definition 3.1; the pullback to right multiplication is node
  1.1.4's theorem, proved in Stage B — never folded into the hypothesis;
- σ is a positive element OF THE ALGEBRA (bounded), with τ(σ²) = 1;
- closeness is in the ℓ¹ norm of the finite correlation table
  ([0,1]^{|Xc|²·|Ac|²}). Lin's Theorem 3.2 states the closure EQUALS
  C_qc(Xc, Ac); the Prop below assumes only the C_qc ⊆ closure inclusion
  — the direction the manuscript uses — while the converse inclusion is
  proved, not assumed (`toCorrelation_isCommuting`).

**Update (stage E7, 2026-09-10): this Prop is now a theorem.**
`Density.tracialDensity` in `Tracial/Density/Main.lean` proves it, so the
`hLin : TracialDensityHypothesis` binders have been removed throughout —
`uniform_parallel_repetition`, `uniform_parallel_repetition_pow13` and the
four intermediates (`strict_tracial_reduction`, `counterexample_extraction`,
`predicate_case`, `rational_case`) are unconditional. The statement below is
unchanged — hash-signed in FIDELITY.md (at `9dd73c68b643c27c` since the
`def`-span widening of review #23) and copied into `Statement.lean` — so the
D5 encoding decision, that the density theorem appears as a named Prop and
never as an axiom, still holds; the axiom gate now
certifies `tracialDensity` itself.

Audit anchor: node 1.1.1 (admitted in the natural-language audit, proved in
Lean); AUDIT.md §1.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Tracial.Interface
import MIPRE.Background.Repetition.CommutingRepetition.Game.Value

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

open scoped BigOperators InnerProductSpace

universe u

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

/-- Every tracially embeddable correlation is a commuting-operator
correlation — the easy inclusion C_qc^Tr ⊆ C_qc, realized on the
standard-form Hilbert space with state `ι σ`, Alice through the left
representation and Bob's commutant effects as given. -/
theorem toCorrelation_isCommuting (q : TraciallyEmbeddableCorrelation Xc Ac) :
    IsCommutingCorrelation q.toCorrelation := by
  refine ⟨{ H := q.M.H
            ψ := q.M.ι q.σ
            ψ_norm := ?_
            E := fun x a => q.M.L (q.E x a)
            F := fun y b => q.G y b
            E_pos := fun x a => q.M.L_isPositive (q.E_pos x a)
            F_pos := q.G_pos
            E_sum := ?_
            F_sum := q.G_sum
            commutes := fun x y a b => (q.G_commutant y b (q.E x a)).symm },
    rfl⟩
  · have h : (⟪q.M.ι q.σ, q.M.ι q.σ⟫_ℂ) = 1 := by
      rw [q.M.ι_inner, q.σ_normalized]
    have h3 : ‖q.M.ι q.σ‖ ^ 2 = 1 := by
      have h4 := inner_self_eq_norm_sq (𝕜 := ℂ) (q.M.ι q.σ)
      rw [h] at h4
      simpa using h4.symm
    nlinarith [norm_nonneg (q.M.ι q.σ)]
  · intro x
    rw [← map_sum, q.E_sum x, map_one]

end TraciallyEmbeddableCorrelation

/-- **The tracial density hypothesis** (Lin, arXiv:2304.01940, Thm 3.2):
for all finite common alphabets, every commuting-operator correlation is an
ℓ¹-limit of tracially embeddable correlations. It is never an axiom, and since
stage E7 it is *proved* — `Density.tracialDensity` in
`Tracial/Density/Main.lean` — so the root theorems no longer take it as a
hypothesis. `MainStatement.tracialDensity` is the same theorem in the
vocabulary of the standalone `Statement.lean`. -/
def TracialDensityHypothesis : Prop :=
  ∀ (Xc Ac : Type) [Fintype Xc] [Fintype Ac] [Nonempty Xc] [Nonempty Ac],
    ∀ p : Correlation Xc Xc Ac Ac, IsCommutingCorrelation p →
      ∀ δ : ℝ, 0 < δ →
        ∃ q : TraciallyEmbeddableCorrelation Xc Ac,
          l1Dist p q.toCorrelation < δ

end CommutingRepetition

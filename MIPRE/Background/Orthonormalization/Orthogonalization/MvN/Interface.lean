/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/MvN/Interface.lean
-/
/-
# The structure-theory interface and the conditional form of Theorem 1.2

`MvNStructureTheory` packages the classical results of the Murray–von Neumann
structure theory of von Neumann algebras that the paper's proof of Theorem 1.2
consumes and that Mathlib does not have (PLAN.md §9.2, encoding decision E7):
the trace-class form of normal states (H0), the type decomposition (H1, H1'),
the finite net of a semifinite algebra (H2), the center-valued trace of a
finite algebra with the comparison theorem (H3), halving in type III (H4),
the paper's own Lemma 3.1 for finite type I algebras — its measurable-selection
step (H5) — and the polar decomposition inside `M` (H6). Every field is a
theorem (cited in PLAN.md §9.2); the interface is consumed only as a binder of
`povm_orthogonalization_of_structure` (`Orthogonalization/MvN/Main.lean`), never
as an axiom, and each field is a candidate for later discharge (tier T4).
Reviewed adversarially (review #3, R1 applied) for faithfulness *and
satisfiability*: no field may be stronger than its source.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.Normal
import MIPRE.Background.Orthonormalization.Orthogonalization.Basic
import MIPRE.Background.Orthonormalization.Orthogonalization.Blocks.Local
import MIPRE.Background.Orthonormalization.Orthogonalization.MvN.Defs

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace Orthogonalization

open scoped BigOperators ComplexOrder InnerProductSpace
open Filter Topology CommutingRepetition.VN MvN Blocks

universe u

/-- **The structure-theory interface** (PLAN.md §9.2). All fields quantify over every
complex Hilbert space `H : Type u` and every von Neumann algebra on it. -/
structure MvNStructureTheory : Prop where
  /-- **H0** (Kadison–Ringrose 7.1.12, Takesaki III.2.14): a positive functional
  normal on `M` is, on `M`, of the trace-class form `∑ₖ ⟪gₖ, · gₖ⟫` with
  `∑ ‖gₖ‖² < ∞`. -/
  normal_traceClass : ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (M : VonNeumannAlgebra H) (φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ),
    (∀ x ∈ M, 0 ≤ φ (star x * x)) → IsNormalOn M φ →
    ∃ g : ℕ → H, Summable (fun k => ‖g k‖ ^ 2) ∧ ∀ x ∈ M, φ x = ∑' k, ⟪g k, x (g k)⟫_ℂ
  /-- **H1** (Takesaki V.1.19): `M = z M ⊕ (1 − z) M` with `z M` semifinite and
  `(1 − z) M` of type III. -/
  type_decomposition : ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (M : VonNeumannAlgebra H),
    ∃ z, IsCentralProj M z ∧ IsSemifiniteAt M z ∧ IsTypeIIIAt M (1 - z)
  /-- **H1'** (Takesaki V.1.19, V.1.27): a finite algebra `p M p` splits along a
  projection `c` of its center `Z(p M p)` into a type I part `c M c` and a type II₁
  part `(p − c) M (p − c)`. -/
  finite_decomposition : ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (M : VonNeumannAlgebra H) (p : H →L[ℂ] H), IsFiniteProj M p →
    ∃ c, IsStarProjection c ∧ IsCentralIn M p c ∧ IsTypeIAt M c ∧ IsTypeII₁At M (p - c)
  /-- **H2** (Takesaki V.1.37): a semifinite `z M z` has an increasing net of finite
  projections converging strongly to `z`. -/
  semifinite_net : ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (M : VonNeumannAlgebra H) (z : H →L[ℂ] H),
    IsCentralProj M z → IsSemifiniteAt M z →
    ∃ (κ : Type u) (_ : Preorder κ) (_ : IsDirected κ (· ≤ ·)) (_ : Nonempty κ)
      (p : κ → H →L[ℂ] H), Monotone p ∧ (∀ α, IsFiniteProj M (p α) ∧ p α * z = p α) ∧
        TendstoStrongBdd atTop p z
  /-- **H3** (Takesaki V.2.6; Anantharaman–Popa 9.1.8): every finite algebra `p M p`
  carries a center-valued trace detecting equivalence of projections. -/
  center_valued_trace : ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (M : VonNeumannAlgebra H) (p : H →L[ℂ] H), IsFiniteProj M p →
    ∃ E : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H), IsCenterValuedTrace M p E
  /-- **H4** (Takesaki V.1.36): in a type III algebra every nonzero projection `q`
  splits as `e + (q − e)` with `e ∼ q − e ∼ q`. -/
  halving : ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (M : VonNeumannAlgebra H) (z : H →L[ℂ] H),
    IsCentralProj M z → IsTypeIIIAt M z →
    ∀ q, IsStarProjection q → q ∈ M → q * z = q → q ≠ 0 →
      ∃ e, IsStarProjection e ∧ e ∈ M ∧ e * q = e ∧ MvNEquiv M e (q - e) ∧ MvNEquiv M e q
  /-- **H5** (the paper's Lemma 3.1 for finite type I algebras — the direct sum over
  `d` of the algebras `M_d(ℂ) ⊗ L∞(Ω_d)`, proved there by measurable selection): for
  the type I part `c M c` (`c` a central
  projection of `p M p`) of a finite algebra `p M p` with center-valued trace `E`, a
  POVM `(aᵢ)` of `c M c` and a functional `φ` positive and normal on `M`, there are
  projections `qᵢ ≤ c` of `M` commuting with `aᵢ`, with `∑ E(qᵢ) = c` and
  `φ(∑ qᵢ aᵢ) ≥ φ(∑ aᵢ²)` (the intermediate inequality of the paper's proof,
  DIFFERENCES.md D6 addendum). -/
  selection_typeI : ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (M : VonNeumannAlgebra H) (p c : H →L[ℂ] H), IsFiniteProj M p →
    IsStarProjection c → IsCentralIn M p c → IsTypeIAt M c →
    ∀ E : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H), IsCenterValuedTrace M p E →
    ∀ (n : ℕ) (a : Fin n → H →L[ℂ] H), (∀ i, a i ∈ M) → (∀ i, 0 ≤ a i) → ∑ i, a i = c →
    ∀ φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ, (∀ x ∈ M, 0 ≤ φ (star x * x)) → IsNormalOn M φ →
    ∃ q : Fin n → H →L[ℂ] H,
      (∀ i, IsStarProjection (q i) ∧ q i ∈ M ∧ q i * c = q i ∧ Commute (q i) (a i)) ∧
      ∑ i, E (q i) = c ∧ (φ (∑ i, a i * a i)).re ≤ (φ (∑ i, q i * a i)).re
  /-- **H6** (Anantharaman–Popa 2.2.4): polar decomposition inside `M`, with the
  partial isometry between the right and left supports. -/
  polar : ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (M : VonNeumannAlgebra H) (x : H →L[ℂ] H), x ∈ M →
    ∃ u ∈ M, star u * u = rightSupport x ∧ u * star u = leftSupport x ∧
      x = u * CFC.sqrt (star x * x)

end Orthogonalization

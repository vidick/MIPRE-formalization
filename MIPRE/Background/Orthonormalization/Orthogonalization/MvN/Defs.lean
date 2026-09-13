/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/MvN/Defs.lean
-/
/-
# Murray–von Neumann vocabulary (definitions only)

The notions of Section 2 of the paper ("Facts on von Neumann algebras"), stated
over Mathlib's `VonNeumannAlgebra` on the ambient space `H` and relative to a
central projection where the paper speaks of a direct summand (PLAN.md §9.1):
equivalence of projections, finite projections, abelian projections, and the
types (semifinite, III, I, II₁) of the corner `z M z` for a central projection
`z`. These are the words in which the structure-theory interface
(`Orthogonalization/MvN/Interface.lean`) is written; they encode the paper's
definitions verbatim (Takesaki, Chapter V) and are reviewed with it.

Conventions: "projection" means `IsStarProjection` (self-adjoint idempotent);
`q ≤ p` for projections is written `q * p = q`; `p M p` is described through
its elements `x ∈ M` with `p * x * p = x`.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.Normal
import MIPRE.Background.Orthonormalization.Orthogonalization.Blocks.Local
import MIPRE.Background.Orthonormalization.Orthogonalization.FinDim.Blocks

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace Orthogonalization.MvN

open scoped BigOperators ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Murray–von Neumann equivalence** `p ∼ q` of two projections of `M`: a partial
isometry `v ∈ M` with `v* v = p` and `v v* = q` (Section 2, "we say that two
projections `p, q ∈ M` are equivalent … if there is `u ∈ M` such that `u* u = p`,
`u u* = q`"). -/
def MvNEquiv (M : VonNeumannAlgebra H) (p q : H →L[ℂ] H) : Prop :=
  ∃ v ∈ M, star v * v = p ∧ v * star v = q

/-- A **finite projection** of `M`: a projection of `M` with no proper equivalent
subprojection (`q ≤ p`, `q ∼ p` ⇒ `q = p`; Takesaki V.1.16, equivalent to the
paper's "`p M p` is finite", Section 2). -/
def IsFiniteProj (M : VonNeumannAlgebra H) (p : H →L[ℂ] H) : Prop :=
  IsStarProjection p ∧ p ∈ M ∧
    ∀ q, IsStarProjection q → q ∈ M → q * p = q → MvNEquiv M q p → q = p

/-- An **abelian projection** of `M`: a projection `p ∈ M` such that `p M p` is
commutative (Section 2, in the definition of type `II₁`). -/
def IsAbelianProj (M : VonNeumannAlgebra H) (p : H →L[ℂ] H) : Prop :=
  IsStarProjection p ∧ p ∈ M ∧
    ∀ x ∈ M, ∀ y ∈ M, (p * x * p) * (p * y * p) = (p * y * p) * (p * x * p)

/-- `z M z` is **semifinite**: every nonzero projection of `M` below `z` majorizes a
nonzero finite projection (Section 2; projection-wise form, DIFFERENCES.md D7). The
notion is intrinsic to the corner `z M z` (finiteness of `q ≤ z` in `M` and in `z M z`
agree), so it applies to `z` central in `M` or in a corner `p M p`. -/
def IsSemifiniteAt (M : VonNeumannAlgebra H) (z : H →L[ℂ] H) : Prop :=
  ∀ p, IsStarProjection p → p ∈ M → p * z = p → p ≠ 0 →
    ∃ q, IsFiniteProj M q ∧ q ≠ 0 ∧ q * p = q

/-- `z M z` is of **type III**: it contains no nonzero finite projection (Section 2;
intrinsic to the corner `z M z`). -/
def IsTypeIIIAt (M : VonNeumannAlgebra H) (z : H →L[ℂ] H) : Prop :=
  ∀ p, IsFiniteProj M p → p * z = p → p = 0

/-- `z M z` is of **type I**: every nonzero projection of `M` below `z` majorizes a
nonzero abelian projection (Takesaki V.1.17, "discrete", in the equivalent
projection-wise form, DIFFERENCES.md D7; intrinsic to the corner `z M z`). -/
def IsTypeIAt (M : VonNeumannAlgebra H) (z : H →L[ℂ] H) : Prop :=
  ∀ p, IsStarProjection p → p ∈ M → p * z = p → p ≠ 0 →
    ∃ q, IsAbelianProj M q ∧ q ≠ 0 ∧ q * p = q

/-- `z M z` is of **type II₁**: `z` is finite and `z M z` contains no nonzero abelian
projection (Section 2: "finite and `0` is the only projection `p` such that `p M p`
is commutative"; intrinsic to the corner `z M z`). -/
def IsTypeII₁At (M : VonNeumannAlgebra H) (z : H →L[ℂ] H) : Prop :=
  IsFiniteProj M z ∧ ∀ p, IsAbelianProj M p → p * z = p → p = 0

/-! ### The matrix algebra `M_n(M)` on `H^n`

The paper's Lemma 3.2 and the type III case work in `M_n(M)`; we realize it as
the von Neumann algebra of operators on `H^n = BlockSpace H (Fin n)` commuting
with the amplification `y ⊕ ⋯ ⊕ y` of every `y ∈ M'` (its elements are exactly
the block matrices with entries in `M'' = M`). -/

/-- The amplification `x ↦ x ⊕ ⋯ ⊕ x` (`n` copies) on `H^n`. -/
noncomputable def amplify (n : ℕ) (x : H →L[ℂ] H) :
    FinDim.BlockSpace H (Fin n) →L[ℂ] FinDim.BlockSpace H (Fin n) :=
  FinDim.blockProj (fun _ : Fin n => x)

/-- The `(i, j)` block entry of an operator on `H^n`. -/
noncomputable def entry {n : ℕ} (X : FinDim.BlockSpace H (Fin n) →L[ℂ] FinDim.BlockSpace H (Fin n))
    (i j : Fin n) : H →L[ℂ] H :=
  FinDim.proj i ∘L X ∘L FinDim.embed j

/-- The matrix algebra `M_n(M)`: the commutant, on `H^n`, of the amplified commutant
`{y ⊕ ⋯ ⊕ y | y ∈ M'}` (Mathlib's `StarSubalgebra.centralizer` closes the set under
`star` first; a no-op here since `M'` is self-adjoint). -/
noncomputable def matrixAlgebra (M : VonNeumannAlgebra H) (n : ℕ) :
    VonNeumannAlgebra (FinDim.BlockSpace H (Fin n)) where
  toStarSubalgebra :=
    StarSubalgebra.centralizer ℂ (Set.range fun y : M.commutant => amplify n (y : H →L[ℂ] H))
  centralizer_centralizer' := by
    show Set.centralizer (Set.centralizer (SetLike.coe (StarSubalgebra.centralizer ℂ
      (Set.range fun y : M.commutant => amplify n (y : H →L[ℂ] H))))) =
      SetLike.coe (StarSubalgebra.centralizer ℂ
        (Set.range fun y : M.commutant => amplify n (y : H →L[ℂ] H)))
    rw [StarSubalgebra.coe_centralizer, Set.centralizer_centralizer_centralizer]

/-- The **right support** of `x`: the projection onto `(ker x)ᗮ` (the smallest
projection `p` with `x p = x`; `u* u` in the polar decomposition, Anantharaman–Popa
2.2.4 — the paper's Lemma 3.2 calls this projection `p₀`, "the left support":
DIFFERENCES.md D6 addendum). -/
noncomputable def rightSupport (x : H →L[ℂ] H) : H →L[ℂ] H :=
  (LinearMap.ker (x : H →ₗ[ℂ] H))ᗮ.starProjection

/-- The **left support** of `x`: the projection onto the closure of the range of `x`
(the smallest projection `q` with `q x = x`; `u u*` in the polar decomposition). -/
noncomputable def leftSupport (x : H →L[ℂ] H) : H →L[ℂ] H :=
  (LinearMap.range (x : H →ₗ[ℂ] H)).topologicalClosure.starProjection

end Orthogonalization.MvN

namespace Orthogonalization.MvN

open scoped BigOperators ComplexOrder InnerProductSpace
open Filter CommutingRepetition.VN

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A functional is **normal on `M`** when it is continuous along bounded strongly
convergent nets of elements of `M` with limit in `M` — the `normal'` field of
`NormalState`, for unbundled functionals (DIFFERENCES.md D3). -/
def IsNormalOn (M : VonNeumannAlgebra H) (φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ) : Prop :=
  ∀ {κ : Type u} (l : Filter κ) (T : κ → H →L[ℂ] H) (L : H →L[ℂ] H),
    (∀ k, T k ∈ M) → L ∈ M → TendstoStrongBdd l T L →
      Tendsto (fun k => φ (T k)) l (nhds (φ L))

/-- **Bounded weak-operator convergence** of a net of operators: the norms are bounded
and `⟪ξ, T k η⟫ → ⟪ξ, L η⟫` for all `ξ, η` (the weak operator topology on bounded
sets, which coincides there with the σ-weak topology; Takesaki II.2.6). The
weak counterpart of `TendstoStrongBdd`. -/
def TendstoWeakBdd {κ : Type*} (l : Filter κ) (T : κ → H →L[ℂ] H) (L : H →L[ℂ] H) : Prop :=
  (∃ C, ∀ k, ‖T k‖ ≤ C) ∧ ∀ ξ η : H, Tendsto (fun k => ⟪ξ, T k η⟫_ℂ) l (nhds ⟪ξ, L η⟫_ℂ)

/-- `c` is a **central element of the corner `p M p`**: `c ∈ p M p` and `c` commutes with
every element of `p M p` (so `c ∈ Z(p M p)`; for `p = 1` this is `c ∈ Z(M)`). -/
def IsCentralIn (M : VonNeumannAlgebra H) (p c : H →L[ℂ] H) : Prop :=
  c ∈ M ∧ p * c * p = c ∧ ∀ y ∈ M, p * y * p = y → Commute c y

/-- A **center-valued trace** on the finite algebra `p M p` (`p` a finite projection
of `M`): a linear map `E` on `B(H)` which, on `p M p`, takes values in the center
`Z(p M p)`, is positive, tracial, the identity on `Z(p M p)`, `Z(p M p)`-linear,
faithful, normal (weak-operator continuous on bounded sets), detects equivalence
of projections (Takesaki V.2.6; Anantharaman–Popa 9.1.8), and admits the division
`E b = z E r` (`0 ≤ z ≤ p` central) for `0 ≤ b ≤ r` (the functional calculus of the
abelian algebra `Z(p M p)`). Only the values of `E` on `p M p` are constrained. -/
structure IsCenterValuedTrace (M : VonNeumannAlgebra H) (p : H →L[ℂ] H)
    (E : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H)) : Prop where
  /-- Values in `Z(p M p)`. -/
  mem_center : ∀ x ∈ M, p * x * p = x → IsCentralIn M p (E x)
  /-- Positivity. -/
  nonneg : ∀ x ∈ M, p * x * p = x → 0 ≤ x → 0 ≤ E x
  /-- The trace property. -/
  trace : ∀ x ∈ M, p * x * p = x → ∀ y ∈ M, p * y * p = y → E (x * y) = E (y * x)
  /-- The identity on the center `Z(p M p)`. -/
  center_fixed : ∀ c, IsCentralIn M p c → E c = c
  /-- `Z(p M p)`-linearity (the conditional-expectation property). -/
  center_mul : ∀ c, IsCentralIn M p c → ∀ x ∈ M, p * x * p = x → E (c * x) = c * E x
  /-- Faithfulness. -/
  faithful : ∀ x ∈ M, p * x * p = x → E (star x * x) = 0 → x = 0
  /-- Normality: continuity along bounded weak-operator convergent nets of `p M p`. -/
  normal : ∀ {κ : Type u} (l : Filter κ) (T : κ → H →L[ℂ] H) (L : H →L[ℂ] H),
    (∀ k, T k ∈ M ∧ p * T k * p = T k) → L ∈ M → p * L * p = L →
      TendstoWeakBdd l T L → TendstoWeakBdd l (fun k => E (T k)) (E L)
  /-- Comparison: projections of `p M p` with the same trace are equivalent. -/
  equiv_of_eq : ∀ q q', IsStarProjection q → q ∈ M → q * p = q →
    IsStarProjection q' → q' ∈ M → q' * p = q' → E q = E q' → MvNEquiv M q q'
  /-- Division in the abelian algebra `Z(p M p)`: for `0 ≤ b ≤ r` with `r` a projection of
  `p M p`, `E b = z * E r` for some central `0 ≤ z ≤ p`. -/
  div : ∀ r, IsStarProjection r → r ∈ M → r * p = r → ∀ b ∈ M, 0 ≤ b → b ≤ r →
    ∃ z, IsCentralIn M p z ∧ 0 ≤ z ∧ z ≤ p ∧ E b = z * E r
  /-- Comparison in `M_n(p M p)` (Takesaki V.2.6, V.2.8 for the finite algebra
  `M_n(p M p)`, whose center-valued trace is `X ↦ (1/n) ∑ᵢ E(Xᵢᵢ)`): projections of
  `M_n(M)` below `1_n ⊗ p` with the same diagonal trace `∑ᵢ E(Xᵢᵢ)` are equivalent. -/
  equiv_of_eq_matrix : ∀ (n : ℕ)
    (P Q : FinDim.BlockSpace H (Fin n) →L[ℂ] FinDim.BlockSpace H (Fin n)),
    P ∈ matrixAlgebra M n → IsStarProjection P → P * amplify n p = P →
    Q ∈ matrixAlgebra M n → IsStarProjection Q → Q * amplify n p = Q →
    ∑ i, E (entry P i i) = ∑ i, E (entry Q i i) → MvNEquiv (matrixAlgebra M n) P Q

end Orthogonalization.MvN

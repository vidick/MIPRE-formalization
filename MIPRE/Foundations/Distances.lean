/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Games

/-!
# Distance measures

This file contains the definitions of the blueprint subsection "Distance measures"
(Section 2, "Foundations"): the dimension-normalized Hilbert--Schmidt inner product and
squared norm on complex matrices, and the distance between two families of POVMs
relative to a question distribution.

## Main definitions

- `MIPRE.hsInner`: the dimension-normalized Hilbert--Schmidt inner product
  `⟨A, B⟩_hs = τ(Aᴴ B)`, where `τ = Tr/d` is the dimension-normalized trace
  (blueprint `def:hs-norm`).
- `MIPRE.hsNormSq`: the squared dimension-normalized Hilbert--Schmidt norm
  `‖A‖²_hs = τ(Aᴴ A)` (blueprint `def:hs-norm`).
- `MIPRE.povmDistance`: the squared distance `𝔼_{x ∼ μ} ∑ₐ ‖M^x_a - N^x_a‖²_hs`
  between two families of POVMs (blueprint `def:distance`).
- `MIPRE.IsPOVMClose`: the δ-closeness relation `M ≈_δ N` of the blueprint.

## Implementation notes

- As elsewhere in the foundations, question distributions are bare real-valued
  functions: `povmDistance` and `IsPOVMClose` take any `μ : X → ℝ`, and results about
  them will assume nonnegativity and normalization as needed.
- `⟨A, A⟩_hs` is a nonnegative real for every `A`, but proving so requires a positivity
  argument; `hsNormSq` takes the real part `.re` so that the definition carries no
  proof obligations. Nonnegativity is recorded separately in `hsNormSq_nonneg`.
- The blueprint writes the POVM distance as `𝔼_{x ∼ μ} ∑ₐ τ((M^x_a - N^x_a)²)`; since
  differences of POVM elements are Hermitian, this agrees with the definition here (see
  `hsNormSq_of_isHermitian`).
-/

namespace MIPRE

open ComplexOrder Matrix

/-! ## The normalized Hilbert--Schmidt inner product -/

variable {n : Type*} [Fintype n]

/-- The dimension-normalized Hilbert--Schmidt inner product on square complex matrices
(blueprint `def:hs-norm`): `⟨A, B⟩_hs = τ(Aᴴ B)`, where `τ = Tr/d` is the
dimension-normalized trace. -/
noncomputable def hsInner (A B : Matrix n n ℂ) : ℂ :=
  (Aᴴ * B).trace / (Fintype.card n : ℂ)

/-- The squared dimension-normalized Hilbert--Schmidt norm on square complex matrices
(blueprint `def:hs-norm`): `‖A‖²_hs = τ(Aᴴ A)`, a nonnegative real
(`hsNormSq_nonneg`). -/
noncomputable def hsNormSq (A : Matrix n n ℂ) : ℝ :=
  (hsInner A A).re

theorem hsNormSq_nonneg (A : Matrix n n ℂ) : 0 ≤ hsNormSq A := by
  have h : (0 : ℂ) ≤ (Aᴴ * A).trace :=
    (Matrix.posSemidef_conjTranspose_mul_self A).trace_nonneg
  have hre : 0 ≤ (Aᴴ * A).trace.re := by
    simpa using (RCLike.nonneg_iff.mp h).1
  unfold hsNormSq hsInner
  rw [← Complex.ofReal_natCast, Complex.div_ofReal_re]
  exact div_nonneg hre (Nat.cast_nonneg _)

/-- For a Hermitian matrix, the squared normalized Hilbert--Schmidt norm is the
normalized trace of the square, which is the form used in blueprint `def:distance`. -/
theorem hsNormSq_of_isHermitian {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    hsNormSq A = ((A * A).trace / (Fintype.card n : ℂ)).re := by
  unfold hsNormSq hsInner
  rw [hA.eq]

/-! ## POVM distance -/

variable {X A d : Type*} [Fintype X] [Fintype A] [Fintype d] [DecidableEq d]

/-- The squared distance between two families of POVMs relative to a question
distribution `μ` (blueprint `def:distance`):
`𝔼_{x ∼ μ} ∑ₐ ‖M^x_a - N^x_a‖²_hs`. -/
noncomputable def povmDistance (μ : X → ℝ) (M N : X → POVM A d) : ℝ :=
  ∑ x, μ x * ∑ a, hsNormSq (((M x).mats a).val - ((N x).mats a).val)

/-- Two families of POVMs are `δ`-close relative to the question distribution `μ`,
written `M^x_a ≈_δ N^x_a` in the blueprint (blueprint `def:distance`). -/
def IsPOVMClose (μ : X → ℝ) (δ : ℝ) (M N : X → POVM A d) : Prop :=
  povmDistance μ M N ≤ δ

end MIPRE

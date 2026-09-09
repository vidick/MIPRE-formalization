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

/-! ## Constructions on POVMs -/

open scoped MatrixOrder in
/-- Relabel the outcomes of a POVM along `f : A → B` (data processing): the operator of
the outcome `b` is the sum of the operators of the outcomes `a` with `f a = b`. -/
noncomputable def POVM.map {B : Type*} [Fintype B] [DecidableEq B] (f : A → B)
    (M : POVM A d) : POVM B d where
  mats b := ∑ a ∈ Finset.univ.filter (fun a => f a = b), M.mats a
  nonneg b := by
    have h : (0 : Matrix d d ℂ) ≤ ∑ a ∈ Finset.univ.filter (fun a => f a = b), (M.mats a).val :=
      Finset.sum_nonneg fun a _ => Subtype.coe_le_coe.mpr (M.nonneg a)
    rw [← AddSubmonoidClass.coe_finsetSum] at h
    exact Subtype.coe_le_coe.mp h
  normalized := (Finset.sum_fiberwise Finset.univ f M.mats).trans M.normalized

open scoped MatrixOrder in
/-- The measurement for the question `x` of a projective measurement family on the matrix
algebra `ℂ^{d×d}`, as a POVM (positivity follows from projectivity). -/
def ProjectiveMeasurement.toPOVM (P : ProjectiveMeasurement X A (Matrix d d ℂ)) (x : X) :
    POVM A d where
  mats a := ⟨P.M x a, selfAdjoint.mem_iff.mpr (P.selfAdjoint x a)⟩
  nonneg a := by
    have h := Matrix.posSemidef_conjTranspose_mul_self (P.M x a)
    rw [← Matrix.star_eq_conjTranspose, P.selfAdjoint x a, P.projective x a] at h
    exact Subtype.coe_le_coe.mp h.nonneg
  normalized := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    exact P.normalized x

/-- The uniform distribution on a finite type, as a real-valued weight function. -/
noncomputable def uniform (X : Type*) [Fintype X] : X → ℝ := fun _ => (Fintype.card X : ℝ)⁻¹

/-! ## Inconsistency of two measurement families on a bipartite state -/

open Kronecker in
/-- The inconsistency of two families of POVMs `M` (acting on `ℂ^dA`) and `N` (acting on
`ℂ^dB`) with the same question and outcome alphabets, relative to a question distribution
`μ` and a bipartite state `ψ ∈ ℂ^dA ⊗ ℂ^dB = ℂ^(dA × dB)`: the probability that measuring
`M^x` on the first factor and `N^x` on the second factor yields different outcomes,
`𝔼_{x ∼ μ} ∑_{a ≠ b} ⟨ψ| M^x_a ⊗ N^x_b |ψ⟩`
(the consistency relation of JNVWY21qld, Definition 4.8, in its two-space form). The
tensor product is realized by the Kronecker product, as in `TensorProductStrategy.value`;
the probability is a nonnegative real, and we take the real part so that the definition
carries no proof obligation. -/
noncomputable def inconsistency {dA dB : Type*} [Fintype dA] [DecidableEq dA]
    [Fintype dB] [DecidableEq dB] [DecidableEq A]
    (μ : X → ℝ) (ψ : dA × dB → ℂ) (M : X → POVM A dA) (N : X → POVM A dB) : ℝ :=
  ∑ x, μ x * ∑ a, ∑ b, if a = b then 0 else
    (star ψ ⬝ᵥ ((((M x).mats a).val ⊗ₖ ((N x).mats b).val) *ᵥ ψ)).re

end MIPRE

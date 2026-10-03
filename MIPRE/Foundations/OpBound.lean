/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import MIPRE.Foundations.StateModel
public import MIPRE.Tactics

@[expose] public section

/-!
# Operator bounds on matrices, by hand

The rigidity arguments of the Pauli basis test's appendix are chains of estimates
`‖M |ψ⟩‖ ≤ …`, and the only thing they need about the operators in front is a bound
`‖M v‖ ≤ K ‖v‖`. `Bnd M K` is that bound, with the four closure properties the chains use ---
sums, products, scalars, and the two sources: a self-adjoint contraction has `Bnd M 1`, and an
isometry has `‖M v‖ = ‖v‖` on the nose.

This is the `ℓ²` operator norm, spelled as a relation instead of a number. That is deliberate.
Mathlib has the norm, through `Matrix.toEuclideanCLM` and the C*-algebra structure on
continuous linear maps, but the Loewner order on `EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n`
costs enough instance search to time out the elaborator on a statement as small as
`T * T ≤ 1 → ‖T‖ ≤ 1`. The order the arguments actually need is the one on *matrices*
(`Matrix.nonneg_iff_posSemidef`, which is cheap), so the bridge here goes from a matrix
inequality straight to a vector-norm inequality and never mentions an operator norm.

**The instance of the Hilbert-space calculus.** The bound, the state norm and the quadratic
form of this file are those of the matrix state model `StateModel.mat v`
(`MIPRE/Foundations/StateModel.lean`), where matrices act on `EuclideanSpace ℂ N` through
`Matrix.toEuclideanCLM` (`bnd_iff`, `snorm_eq_mat`, `qform_eq_mat`), and their rules are proved
there once, for every represented algebra (Phase 1(b) of `planning/mipco-track.md`). The state
norm is the model's by definition, so its rules are the model's rules verbatim. What this file
adds is about matrices: the matrix order, and the Kronecker embeddings of the two factors.
-/

noncomputable section

namespace MIPRE

open Finset Matrix
open scoped ComplexOrder MatrixOrder

variable {N : Type*} [Fintype N]

/-- A vector of `N → ℂ`, as a vector of `EuclideanSpace ℂ N`. -/
def evec (v : N → ℂ) : EuclideanSpace ℂ N := WithLp.toLp 2 v

omit [Fintype N] in
@[simp] theorem evec_add (v w : N → ℂ) : evec (v + w) = evec v + evec w := rfl

omit [Fintype N] in
@[simp] theorem evec_smul (c : ℂ) (v : N → ℂ) : evec (c • v) = c • evec v := rfl

omit [Fintype N] in
@[simp] theorem evec_zero : evec (0 : N → ℂ) = 0 := rfl

omit [Fintype N] in
theorem evec_sub (v w : N → ℂ) : evec (v - w) = evec v - evec w := rfl

/-- The sesquilinear form of two matrices applied to the same vector, moved onto one side:
`⟨A v, B v⟩ = ⟨v, A† B v⟩`. -/
theorem star_mulVec_dotProduct {M : Type*} [Fintype M] (A B : Matrix M N ℂ) (v : N → ℂ) :
    star (A *ᵥ v) ⬝ᵥ (B *ᵥ v) = star v ⬝ᵥ ((Aᴴ * B) *ᵥ v) := by
  rw [Matrix.star_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec]

theorem norm_evec_sq (v : N → ℂ) : ‖evec v‖ ^ 2 = (star v ⬝ᵥ v).re := by
  classical
  rw [evec, EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : star v i * v i = ((‖v i‖ ^ 2 : ℝ) : ℂ) := by
    rw [Pi.star_apply, RCLike.star_def, RCLike.conj_mul]
    norm_cast
  rw [h, Complex.ofReal_re]

theorem norm_evec_mulVec_sq {M : Type*} [Fintype M] (A : Matrix M N ℂ) (v : N → ℂ) :
    ‖evec (A *ᵥ v)‖ ^ 2 = (star v ⬝ᵥ ((Aᴴ * A) *ᵥ v)).re := by
  rw [norm_evec_sq, star_mulVec_dotProduct]

/-- **A rectangular isometry preserves the norm.** -/
theorem norm_evec_mulVec_eq {M : Type*} [Fintype M] {A : Matrix M N ℂ} [DecidableEq N]
    (h : Aᴴ * A = 1) (v : N → ℂ) : ‖evec (A *ᵥ v)‖ = ‖evec v‖ := by
  have hsq : ‖evec (A *ᵥ v)‖ ^ 2 = ‖evec v‖ ^ 2 := by
    rw [norm_evec_mulVec_sq, h, Matrix.one_mulVec, norm_evec_sq]
  nlinarith [norm_nonneg (evec (A *ᵥ v)), norm_nonneg (evec v), hsq]

/-! ## The bound -/

/-- `‖M v‖ ≤ K ‖v‖` for every `v`: the `ℓ²` operator norm of `M` is at most `K`. -/
def Bnd (M : Matrix N N ℂ) (K : ℝ) : Prop := ∀ v : N → ℂ, ‖evec (M *ᵥ v)‖ ≤ K * ‖evec v‖

/-- **The bound is that of the matrix model**, whatever its state. -/
theorem bnd_iff [DecidableEq N] {M : Matrix N N ℂ} {K : ℝ} (w : N → ℂ) :
    Bnd M K ↔ (StateModel.mat w).Bnd M K :=
  ⟨fun h v => h (WithLp.ofLp v), fun h v => h (evec v)⟩

/-! ## The norm on a fixed state

`snorm v M = ‖M v‖`. Every estimate in a rigidity argument is a statement about this, and the
four rules below --- the triangle inequality, scalars, a bound in front, an isometry in front ---
are all of them. -/

section SNorm

variable (v : N → ℂ)

/-- `‖M v‖`, for a fixed state `v`. -/
def snorm (M : Matrix N N ℂ) : ℝ := ‖evec (M *ᵥ v)‖

/-- **The state norm is that of the matrix model**, by definition. -/
theorem snorm_eq_mat [DecidableEq N] (M : Matrix N N ℂ) :
    snorm v M = (StateModel.mat v).snorm M :=
  rfl

theorem snorm_nonneg (M : Matrix N N ℂ) : 0 ≤ snorm v M := by
  classical
  exact (StateModel.mat v).snorm_nonneg M

theorem snorm_add_le (M M' : Matrix N N ℂ) : snorm v (M + M') ≤ snorm v M + snorm v M' := by
  classical
  exact (StateModel.mat v).snorm_add_le M M'

theorem snorm_sub_le (M M' : Matrix N N ℂ) : snorm v (M - M') ≤ snorm v M + snorm v M' := by
  classical
  exact (StateModel.mat v).snorm_sub_le M M'

theorem snorm_sub_comm (M M' : Matrix N N ℂ) : snorm v (M - M') = snorm v (M' - M) := by
  classical
  exact (StateModel.mat v).snorm_sub_comm M M'

theorem snorm_smul (c : ℂ) (M : Matrix N N ℂ) : snorm v (c • M) = ‖c‖ * snorm v M := by
  classical
  exact (StateModel.mat v).snorm_smul c M

/-- A bound in front of anything. -/
theorem snorm_mul_le {M : Matrix N N ℂ} {K : ℝ} (h : Bnd M K) (M' : Matrix N N ℂ) :
    snorm v (M * M') ≤ K * snorm v M' := by
  classical
  exact (StateModel.mat v).snorm_mul_le ((bnd_iff v).1 h) M'

end SNorm

/-! ## The quadratic form -/

section QForm

variable (v : N → ℂ)

/-- `⟨v| M |v⟩`, as a real. -/
def qform (M : Matrix N N ℂ) : ℝ := (star v ⬝ᵥ (M *ᵥ v)).re

/-- **The quadratic form is that of the matrix model.** -/
theorem qform_eq_mat [DecidableEq N] (M : Matrix N N ℂ) :
    qform v M = (StateModel.mat v).qform M := by
  show (star v ⬝ᵥ (M *ᵥ v)).re = ((M *ᵥ v) ⬝ᵥ star v).re
  rw [dotProduct_comm]

theorem qform_add (M M' : Matrix N N ℂ) : qform v (M + M') = qform v M + qform v M' := by
  classical
  simp only [qform_eq_mat]
  exact (StateModel.mat v).qform_add M M'

theorem qform_sub (M M' : Matrix N N ℂ) : qform v (M - M') = qform v M - qform v M' := by
  classical
  simp only [qform_eq_mat]
  exact (StateModel.mat v).qform_sub M M'

theorem qform_smul_real (r : ℝ) (M : Matrix N N ℂ) :
    qform v ((r : ℂ) • M) = r * qform v M := by
  classical
  simp only [qform_eq_mat]
  exact (StateModel.mat v).qform_smul_real r M

theorem qform_sum {ι : Type*} (s : Finset ι) (f : ι → Matrix N N ℂ) :
    qform v (∑ i ∈ s, f i) = ∑ i ∈ s, qform v (f i) := by
  classical
  simp only [qform_eq_mat]
  exact (StateModel.mat v).qform_sum s f

theorem qform_one [DecidableEq N] (hv : ‖evec v‖ = 1) : qform v (1 : Matrix N N ℂ) = 1 := by
  rw [qform_eq_mat]
  exact (StateModel.mat v).qform_one hv

/-- **The squared state norm is the quadratic form of `M† M`.** -/
theorem snorm_sq_eq_qform (M : Matrix N N ℂ) : snorm v M ^ 2 = qform v (Mᴴ * M) := by
  classical
  rw [qform_eq_mat]
  exact (StateModel.mat v).snorm_sq_eq_qform M

end QForm

variable [DecidableEq N]

/-- **A self-adjoint contraction is bounded by one.** The hypothesis is the *matrix*
inequality `M† M ≤ 1`, which is `Matrix.PosSemidef` of the difference. -/
theorem bnd_one_of_conjTranspose_mul_self_le {M : Matrix N N ℂ}
    (h : (Mᴴ * M) ≤ (1 : Matrix N N ℂ)) : Bnd M 1 := by
  intro v
  have hsq : ‖evec (M *ᵥ v)‖ ^ 2 ≤ ‖evec v‖ ^ 2 := by
    rw [norm_evec_mulVec_sq, norm_evec_sq]
    have hpsd : (0 : Matrix N N ℂ) ≤ 1 - Mᴴ * M := sub_nonneg.mpr h
    have hnn : (0 : ℂ) ≤ star v ⬝ᵥ (((1 : Matrix N N ℂ) - Mᴴ * M) *ᵥ v) :=
      (Matrix.nonneg_iff_posSemidef.mp hpsd).dotProduct_mulVec_nonneg v
    have hsplit : star v ⬝ᵥ (((1 : Matrix N N ℂ) - Mᴴ * M) *ᵥ v)
        = (star v ⬝ᵥ v) - star v ⬝ᵥ ((Mᴴ * M) *ᵥ v) := by
      rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec]
    rw [hsplit] at hnn
    have := (Complex.nonneg_iff.mp hnn).1
    simp only [Complex.sub_re] at this
    linarith
  rw [one_mul]
  nlinarith [norm_nonneg (evec (M *ᵥ v)), norm_nonneg (evec v), hsq]

/-- **`X² ≤ X` for `0 ≤ X ≤ 1`**: `X - X² = X (1 - X)` is a product of commuting positive
matrices. -/
theorem mul_self_le_of_le_one {X : Matrix N N ℂ} (h0 : (0 : Matrix N N ℂ) ≤ X)
    (h1 : X ≤ (1 : Matrix N N ℂ)) : X * X ≤ X := by
  have hc : Commute X ((1 : Matrix N N ℂ) - X) := by
    show X * (1 - X) = (1 - X) * X
    noncomm_ring
  have hprod : (0 : Matrix N N ℂ) ≤ X * (1 - X) := hc.mul_nonneg h0 (sub_nonneg.mpr h1)
  have heq : X * ((1 : Matrix N N ℂ) - X) = X - X * X := by noncomm_ring
  rw [heq] at hprod
  exact sub_nonneg.mp hprod

/-- An isometry preserves the norm exactly. -/
theorem norm_evec_mulVec_of_isometry {M : Matrix N N ℂ} (h : Mᴴ * M = 1) (v : N → ℂ) :
    ‖evec (M *ᵥ v)‖ = ‖evec v‖ := by
  have hsq : ‖evec (M *ᵥ v)‖ ^ 2 = ‖evec v‖ ^ 2 := by
    rw [norm_evec_mulVec_sq, h, Matrix.one_mulVec, norm_evec_sq]
  have h1 : (0 : ℝ) ≤ ‖evec (M *ᵥ v)‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ ‖evec v‖ := norm_nonneg _
  nlinarith [hsq]

/-! ## The bipartite structure

A soundness argument on a bipartite state works with two commuting copies of a matrix algebra
inside the one on the product space: `aOp X = X ⊗ Id` for the first factor and `bOp Y = Id ⊗ Y`
for the second. Both are ring homomorphisms, they commute with each other, and both carry a
matrix contraction to a `Bnd _ 1`, which is all the estimates need. -/

section Bipartite

-- Every lemma below mentions both factors, and matrix multiplication on the product space
-- needs all four instances; the linter's suggestion would be twenty `omit` lines that no
-- consumer benefits from, since a consumer of this section has all four.
set_option linter.unusedSectionVars false

variable {HA HB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]

open Kronecker

/-- A matrix on the first factor, acting on the product space. -/
def aOp (X : Matrix HA HA ℂ) : Matrix (HA × HB) (HA × HB) ℂ := X ⊗ₖ (1 : Matrix HB HB ℂ)

/-- A matrix on the second factor, acting on the product space. -/
def bOp (Y : Matrix HB HB ℂ) : Matrix (HA × HB) (HA × HB) ℂ := (1 : Matrix HA HA ℂ) ⊗ₖ Y

@[simp] theorem aOp_one : aOp (1 : Matrix HA HA ℂ) = (1 : Matrix (HA × HB) (HA × HB) ℂ) :=
  Matrix.one_kronecker_one

@[simp] theorem bOp_one : bOp (1 : Matrix HB HB ℂ) = (1 : Matrix (HA × HB) (HA × HB) ℂ) :=
  Matrix.one_kronecker_one

theorem aOp_mul (X Y : Matrix HA HA ℂ) :
    aOp (X * Y) = (aOp X : Matrix (HA × HB) _ ℂ) * aOp Y := by
  rw [aOp, aOp, aOp, ← Matrix.mul_kronecker_mul, Matrix.one_mul]

theorem bOp_mul (X Y : Matrix HB HB ℂ) :
    bOp (X * Y) = (bOp X : Matrix (HA × HB) _ ℂ) * bOp Y := by
  rw [bOp, bOp, bOp, ← Matrix.mul_kronecker_mul, Matrix.one_mul]

theorem aOp_add (X Y : Matrix HA HA ℂ) :
    aOp (X + Y) = (aOp X : Matrix (HA × HB) _ ℂ) + aOp Y := Matrix.add_kronecker _ _ _

theorem bOp_add (X Y : Matrix HB HB ℂ) :
    bOp (X + Y) = (bOp X : Matrix (HA × HB) _ ℂ) + bOp Y := Matrix.kronecker_add _ _ _

theorem aOp_smul (c : ℂ) (X : Matrix HA HA ℂ) :
    aOp (c • X) = c • (aOp X : Matrix (HA × HB) _ ℂ) := Matrix.smul_kronecker _ _ _

theorem bOp_smul (c : ℂ) (X : Matrix HB HB ℂ) :
    bOp (c • X) = c • (bOp X : Matrix (HA × HB) _ ℂ) := Matrix.kronecker_smul _ _ _

theorem aOp_sub (X Y : Matrix HA HA ℂ) :
    aOp (X - Y) = (aOp X : Matrix (HA × HB) _ ℂ) - aOp Y := by
  have h : X - Y = X + (-1 : ℂ) • Y := by module
  rw [h, aOp_add, aOp_smul]
  module

theorem bOp_sub (X Y : Matrix HB HB ℂ) :
    bOp (X - Y) = (bOp X : Matrix (HA × HB) _ ℂ) - bOp Y := by
  have h : X - Y = X + (-1 : ℂ) • Y := by module
  rw [h, bOp_add, bOp_smul]
  module

theorem aOp_conjTranspose (X : Matrix HA HA ℂ) :
    (aOp X : Matrix (HA × HB) _ ℂ)ᴴ = aOp (Xᴴ) := by
  rw [aOp, aOp, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]

theorem bOp_conjTranspose (X : Matrix HB HB ℂ) :
    (bOp X : Matrix (HA × HB) _ ℂ)ᴴ = bOp (Xᴴ) := by
  rw [bOp, bOp, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]

theorem aOp_sum {ι : Type*} (s : Finset ι) (f : ι → Matrix HA HA ℂ) :
    aOp (∑ i ∈ s, f i) = ∑ i ∈ s, (aOp (f i) : Matrix (HA × HB) _ ℂ) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, aOp, Matrix.zero_kronecker]
  | insert i s hi ih => rw [Finset.sum_insert hi, aOp_add, ih, Finset.sum_insert hi]

/-- **The two factors commute.** -/
theorem aOp_mul_bOp (X : Matrix HA HA ℂ) (Y : Matrix HB HB ℂ) :
    (aOp X : Matrix (HA × HB) _ ℂ) * bOp Y = bOp Y * aOp X := by
  rw [aOp, bOp, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    Matrix.mul_one, Matrix.one_mul, Matrix.mul_one]

theorem aOp_nonneg {X : Matrix HA HA ℂ} (hX : (0 : Matrix HA HA ℂ) ≤ X) :
    (0 : Matrix (HA × HB) (HA × HB) ℂ) ≤ aOp X :=
  Matrix.nonneg_iff_posSemidef.mpr
    ((Matrix.nonneg_iff_posSemidef.mp hX).kronecker (Matrix.PosSemidef.one))

theorem bOp_nonneg {Y : Matrix HB HB ℂ} (hY : (0 : Matrix HB HB ℂ) ≤ Y) :
    (0 : Matrix (HA × HB) (HA × HB) ℂ) ≤ bOp Y :=
  Matrix.nonneg_iff_posSemidef.mpr
    (Matrix.PosSemidef.one.kronecker (Matrix.nonneg_iff_posSemidef.mp hY))

/-- A contraction on the first factor is a contraction on the product space. -/
theorem bnd_aOp {X : Matrix HA HA ℂ} (h : (Xᴴ * X) ≤ (1 : Matrix HA HA ℂ)) :
    Bnd (aOp X : Matrix (HA × HB) _ ℂ) 1 := by
  refine bnd_one_of_conjTranspose_mul_self_le ?_
  rw [aOp_conjTranspose, ← aOp_mul, ← aOp_one (HA := HA) (HB := HB)]
  refine sub_nonneg.mp ?_
  rw [← aOp_sub]
  exact aOp_nonneg (sub_nonneg.mpr h)

/-- A contraction on the second factor is a contraction on the product space. -/
theorem bnd_bOp {Y : Matrix HB HB ℂ} (h : (Yᴴ * Y) ≤ (1 : Matrix HB HB ℂ)) :
    Bnd (bOp Y : Matrix (HA × HB) _ ℂ) 1 := by
  refine bnd_one_of_conjTranspose_mul_self_le ?_
  rw [bOp_conjTranspose, ← bOp_mul, ← bOp_one (HA := HA) (HB := HB)]
  refine sub_nonneg.mp ?_
  rw [← bOp_sub]
  exact bOp_nonneg (sub_nonneg.mpr h)

end Bipartite

end MIPRE

end

end

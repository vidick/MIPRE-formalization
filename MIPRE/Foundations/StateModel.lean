/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import MIPRE.Foundations.OpCalculus
public import MIPRE.Tactics

@[expose] public section

/-!
# A state on a represented `⋆`-algebra

The state calculus of `MIPRE/Foundations/OpCalculus.lean` is about operators on a Hilbert space.
The analyses write their operators in an algebra: matrices on `ℂ^N`, or elements of the players'
algebras. A **state model** (`StateModel 𝒞`) is the bridge: a complex Hilbert space `H` with a
state `ψ`, and a `⋆`-algebra `𝒞` represented on `H` by a `⋆`-homomorphism `π`. Its state norm,
bound and quadratic form are those of `π T`:

* `M.snorm T = ‖π T ψ‖`,
* `M.Bnd T K`, the bound `‖π T v‖ ≤ K ‖v‖` for every `v`,
* `M.qform T = Re ⟨ψ, π T ψ⟩`,

with the rules of the calculus restated in `𝒞`, so that a chain of estimates about products and
sums in `𝒞` never has to push `π` through them by hand.

The matrix calculus of `MIPRE/Foundations/OpBound.lean` is this calculus in the model
`StateModel.mat v`: `𝒞 = M_N(ℂ)` acting on `EuclideanSpace ℂ N` through `Matrix.toEuclideanCLM`,
with the state `v`. Its state norm is literally the matrix one (`snorm_mat`), and so are its
products and sums: a matrix statement is the generic statement in that model, with no operator
pushed through anything. This is why the algebra is a parameter rather than always `H →L[ℂ] H`:
the elaborator never has to move `Matrix.toEuclideanCLM` across a product.
-/

namespace MIPRE

open scoped InnerProductSpace

universe u v

/-- **A state model**: a complex Hilbert space with a state, and a `⋆`-algebra represented on it
by a `⋆`-homomorphism. -/
structure StateModel (𝒞 : Type v) [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] where
  /-- The Hilbert space. -/
  H : Type u
  [normedAddCommGroup : NormedAddCommGroup H]
  [innerProductSpace : InnerProductSpace ℂ H]
  [completeSpace : CompleteSpace H]
  /-- The state. -/
  ψ : H
  /-- The representation of the algebra. -/
  π : 𝒞 →⋆ₐ[ℂ] (H →L[ℂ] H)

attribute [instance] StateModel.normedAddCommGroup StateModel.innerProductSpace
  StateModel.completeSpace

namespace StateModel

variable {𝒞 : Type v} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] (M : StateModel.{u} 𝒞)

/-! ## The calculus -/

/-- `‖π T ψ‖`. -/
def snorm (T : 𝒞) : ℝ := Op.snorm M.ψ (M.π T)

/-- `Re ⟨ψ, π T ψ⟩`. -/
def qform (T : 𝒞) : ℝ := Op.qform M.ψ (M.π T)

/-- `‖π T v‖ ≤ K ‖v‖` for every `v`. -/
def Bnd (T : 𝒞) (K : ℝ) : Prop := Op.Bnd (M.π T) K

theorem snorm_nonneg (T : 𝒞) : 0 ≤ M.snorm T := Op.snorm_nonneg _ _

theorem snorm_add_le (T T' : 𝒞) : M.snorm (T + T') ≤ M.snorm T + M.snorm T' := by
  unfold snorm
  rw [map_add]
  exact Op.snorm_add_le _ _ _

theorem snorm_sub_le (T T' : 𝒞) : M.snorm (T - T') ≤ M.snorm T + M.snorm T' := by
  unfold snorm
  rw [map_sub]
  exact Op.snorm_sub_le _ _ _

theorem snorm_sub_comm (T T' : 𝒞) : M.snorm (T - T') = M.snorm (T' - T) := by
  unfold snorm
  rw [map_sub, map_sub]
  exact Op.snorm_sub_comm _ _ _

theorem snorm_smul (c : ℂ) (T : 𝒞) : M.snorm (c • T) = ‖c‖ * M.snorm T := by
  unfold snorm
  rw [map_smul]
  exact Op.snorm_smul _ _ _

theorem snorm_neg (T : 𝒞) : M.snorm (-T) = M.snorm T := by
  unfold snorm
  rw [map_neg]
  exact norm_neg _

theorem snorm_zero : M.snorm 0 = 0 := by
  unfold snorm
  rw [map_zero]
  exact norm_zero

theorem snorm_one (hψ : ‖M.ψ‖ = 1) : M.snorm 1 = 1 := by
  unfold snorm
  rw [map_one]
  exact Op.snorm_one _ hψ

/-- A bound in front of anything. -/
theorem snorm_mul_le {T : 𝒞} {K : ℝ} (h : M.Bnd T K) (T' : 𝒞) :
    M.snorm (T * T') ≤ K * M.snorm T' := by
  unfold snorm
  rw [map_mul]
  exact Op.snorm_mul_le _ h _

/-- An isometry of `𝒞` is represented by an isometry. -/
theorem star_π_mul_self {T : 𝒞} (h : star T * T = 1) : star (M.π T) * M.π T = 1 := by
  rw [← map_star, ← map_mul, h, map_one]

/-- An isometry in front changes nothing. -/
theorem snorm_mul_of_isometry {T : 𝒞} (h : star T * T = 1) (T' : 𝒞) :
    M.snorm (T * T') = M.snorm T' := by
  unfold snorm
  rw [map_mul]
  exact Op.snorm_mul_of_isometry _ (M.star_π_mul_self h) _

/-- **Replacing an operator by an isometry it is close to, in front of anything.** -/
theorem snorm_mul_swap {W WD Z : 𝒞} {δ K : ℝ} (hWD : star WD * WD = 1)
    (hcomm : WD * Z = Z * WD) (hZ : M.Bnd Z K) (hK : 0 ≤ K) (hd : M.snorm (W - WD) ≤ δ) :
    M.snorm (Z * W) ≤ M.snorm Z + K * δ := by
  unfold snorm at hd ⊢
  rw [map_mul]
  refine Op.snorm_mul_swap _ (M.star_π_mul_self hWD) ?_ hZ hK ?_
  · rw [← map_mul, hcomm, map_mul]
  · rwa [← map_sub]

theorem qform_add (T T' : 𝒞) : M.qform (T + T') = M.qform T + M.qform T' := by
  unfold qform
  rw [map_add]
  exact Op.qform_add _ _ _

theorem qform_sub (T T' : 𝒞) : M.qform (T - T') = M.qform T - M.qform T' := by
  unfold qform
  rw [map_sub]
  exact Op.qform_sub _ _ _

theorem qform_smul_real (r : ℝ) (T : 𝒞) : M.qform ((r : ℂ) • T) = r * M.qform T := by
  unfold qform
  rw [map_smul]
  exact Op.qform_smul_real _ _ _

theorem qform_zero : M.qform 0 = 0 := by
  unfold qform
  rw [map_zero]
  exact Op.qform_zero _

theorem qform_sum {ι : Type*} (s : Finset ι) (f : ι → 𝒞) :
    M.qform (∑ i ∈ s, f i) = ∑ i ∈ s, M.qform (f i) := by
  unfold qform
  rw [map_sum]
  exact Op.qform_sum _ _ _

theorem qform_one (hψ : ‖M.ψ‖ = 1) : M.qform 1 = 1 := by
  unfold qform
  rw [map_one]
  exact Op.qform_one _ hψ

/-- **The squared state norm is the quadratic form of `T* T`.** -/
theorem snorm_sq_eq_qform (T : 𝒞) : M.snorm T ^ 2 = M.qform (star T * T) := by
  unfold snorm qform
  rw [map_mul, map_star]
  exact Op.snorm_sq_eq_qform _ _

theorem Bnd.mono {T : 𝒞} {K L : ℝ} (h : M.Bnd T K) (hKL : K ≤ L) : M.Bnd T L :=
  Op.Bnd.mono h hKL

theorem Bnd.add {T T' : 𝒞} {K L : ℝ} (h : M.Bnd T K) (h' : M.Bnd T' L) :
    M.Bnd (T + T') (K + L) := by
  unfold Bnd at *
  rw [map_add]
  exact h.add h'

theorem Bnd.sub {T T' : 𝒞} {K L : ℝ} (h : M.Bnd T K) (h' : M.Bnd T' L) :
    M.Bnd (T - T') (K + L) := by
  unfold Bnd at *
  rw [map_sub]
  exact h.sub h'

theorem Bnd.mul {T T' : 𝒞} {K L : ℝ} (hK : 0 ≤ K) (h : M.Bnd T K) (h' : M.Bnd T' L) :
    M.Bnd (T * T') (K * L) := by
  unfold Bnd at *
  rw [map_mul]
  exact h.mul hK h'

theorem Bnd.smul {T : 𝒞} {K : ℝ} (c : ℂ) (h : M.Bnd T K) : M.Bnd (c • T) (‖c‖ * K) := by
  unfold Bnd at *
  rw [map_smul]
  exact h.smul c

theorem bnd_zero (K : ℝ) (hK : 0 ≤ K) : M.Bnd 0 K := by
  unfold Bnd
  rw [map_zero]
  exact Op.bnd_zero K hK

theorem bnd_one : M.Bnd 1 1 := by
  unfold Bnd
  rw [map_one]
  exact Op.bnd_one

theorem bnd_one_of_isometry {T : 𝒞} (h : star T * T = 1) : M.Bnd T 1 :=
  Op.bnd_one_of_isometry (M.star_π_mul_self h)

/-- **An orthogonal projection of `𝒞` is bounded by one.** -/
theorem bnd_one_of_isStarProjection {P : 𝒞} (hP : IsStarProjection P) : M.Bnd P 1 :=
  Op.bnd_one_of_isStarProjection (hP.map M.π)

/-! ## The matrix model -/

section Matrix

open Matrix

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- **The matrix model** of a vector `v` of `ℂ^N`: matrices acting on `EuclideanSpace ℂ N`. -/
noncomputable def mat (v : N → ℂ) : StateModel (Matrix N N ℂ) where
  H := EuclideanSpace ℂ N
  ψ := WithLp.toLp 2 v
  π := (Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ)).toStarAlgHom

theorem mat_ψ (v : N → ℂ) : (mat v).ψ = WithLp.toLp 2 v := rfl

theorem mat_π_apply (v : N → ℂ) (T : Matrix N N ℂ) (w : N → ℂ) :
    (mat v).π T (WithLp.toLp 2 w) = WithLp.toLp 2 (T *ᵥ w) := rfl

end Matrix

end StateModel

end MIPRE

end

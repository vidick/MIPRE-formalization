/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import MIPRE.Tactics

@[expose] public section

/-!
# The state calculus on a Hilbert space

The estimates of the rigidity arguments are chains of bounds `‖T ψ‖ ≤ …` for operators `T` in
front of a fixed state `ψ`. This file is that calculus for bounded operators on any complex
inner product space:

* `Op.snorm ψ T = ‖T ψ‖`, with the triangle inequality, scalars, a bound in front and an
  isometry in front;
* `Op.Bnd T K`, the bound `‖T v‖ ≤ K ‖v‖` for every `v`, closed under sums, products and
  scalars;
* `Op.qform ψ T = Re ⟨ψ, T ψ⟩`, additive in `T`, with `‖T ψ‖² = qform ψ (T* T)`.

It is the first piece of the operator calculus of Phase 1(b) of `planning/mipco-track.md`,
which restates the matrix calculus over `H →L[ℂ] H` so that the stage analyses can be read in
any model with two commuting families of measurements. The matrix calculus of
`MIPRE/Foundations/OpBound.lean` is its instance on `EuclideanSpace ℂ N` through
`Matrix.toEuclideanCLM`, and its lemmas are proved from these.

As in the matrix calculus, the bound is a relation rather than the operator norm, and nothing
here uses the Loewner order on operators: the estimates need neither.
-/

namespace MIPRE

namespace Op

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ## The bound -/

/-- `‖T v‖ ≤ K ‖v‖` for every `v`: the operator norm of `T` is at most `K`, as a relation. -/
def Bnd (T : H →L[ℂ] H) (K : ℝ) : Prop := ∀ v, ‖T v‖ ≤ K * ‖v‖

theorem Bnd.mono {T : H →L[ℂ] H} {K L : ℝ} (h : Bnd T K) (hKL : K ≤ L) : Bnd T L := fun v =>
  le_trans (h v) (mul_le_mul_of_nonneg_right hKL (norm_nonneg _))

theorem Bnd.add {T T' : H →L[ℂ] H} {K L : ℝ} (h : Bnd T K) (h' : Bnd T' L) :
    Bnd (T + T') (K + L) := fun v => by
  show ‖T v + T' v‖ ≤ (K + L) * ‖v‖
  rw [add_mul]
  exact le_trans (norm_add_le _ _) (add_le_add (h v) (h' v))

theorem Bnd.sub {T T' : H →L[ℂ] H} {K L : ℝ} (h : Bnd T K) (h' : Bnd T' L) :
    Bnd (T - T') (K + L) := fun v => by
  show ‖T v - T' v‖ ≤ (K + L) * ‖v‖
  rw [add_mul]
  exact le_trans (norm_sub_le _ _) (add_le_add (h v) (h' v))

theorem Bnd.mul {T T' : H →L[ℂ] H} {K L : ℝ} (hK : 0 ≤ K) (h : Bnd T K) (h' : Bnd T' L) :
    Bnd (T * T') (K * L) := fun v => by
  show ‖T (T' v)‖ ≤ K * L * ‖v‖
  rw [mul_assoc]
  exact le_trans (h (T' v)) (mul_le_mul_of_nonneg_left (h' v) hK)

theorem Bnd.smul {T : H →L[ℂ] H} {K : ℝ} (c : ℂ) (h : Bnd T K) : Bnd (c • T) (‖c‖ * K) :=
  fun v => by
  show ‖c • T v‖ ≤ ‖c‖ * K * ‖v‖
  rw [norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h v) (norm_nonneg c)

theorem bnd_zero (K : ℝ) (hK : 0 ≤ K) : Bnd (0 : H →L[ℂ] H) K := fun v => by
  show ‖(0 : H)‖ ≤ K * ‖v‖
  rw [norm_zero]
  positivity

theorem bnd_one : Bnd (1 : H →L[ℂ] H) 1 := fun v => by
  show ‖v‖ ≤ 1 * ‖v‖
  rw [one_mul]

/-- An operator of norm at most `K` is bounded by `K`. -/
theorem bnd_of_norm_le {T : H →L[ℂ] H} {K : ℝ} (h : ‖T‖ ≤ K) : Bnd T K := fun v =>
  le_trans (T.le_opNorm v) (mul_le_mul_of_nonneg_right h (norm_nonneg v))

/-! ## The norm on a fixed state -/

section SNorm

variable (ψ : H)

/-- `‖T ψ‖`, for a fixed state `ψ`. -/
def snorm (T : H →L[ℂ] H) : ℝ := ‖T ψ‖

theorem snorm_nonneg (T : H →L[ℂ] H) : 0 ≤ snorm ψ T := norm_nonneg _

theorem snorm_add_le (T T' : H →L[ℂ] H) : snorm ψ (T + T') ≤ snorm ψ T + snorm ψ T' :=
  norm_add_le (T ψ) (T' ψ)

theorem snorm_sub_le (T T' : H →L[ℂ] H) : snorm ψ (T - T') ≤ snorm ψ T + snorm ψ T' :=
  norm_sub_le (T ψ) (T' ψ)

theorem snorm_sub_comm (T T' : H →L[ℂ] H) : snorm ψ (T - T') = snorm ψ (T' - T) :=
  norm_sub_rev (T ψ) (T' ψ)

theorem snorm_smul (c : ℂ) (T : H →L[ℂ] H) : snorm ψ (c • T) = ‖c‖ * snorm ψ T :=
  norm_smul c (T ψ)

theorem snorm_one (hψ : ‖ψ‖ = 1) : snorm ψ (1 : H →L[ℂ] H) = 1 := hψ

/-- A bound in front of anything. -/
theorem snorm_mul_le {T : H →L[ℂ] H} {K : ℝ} (h : Bnd T K) (T' : H →L[ℂ] H) :
    snorm ψ (T * T') ≤ K * snorm ψ T' :=
  h (T' ψ)

end SNorm

/-! ## The quadratic form -/

section QForm

variable (ψ : H)

/-- `Re ⟨ψ, T ψ⟩`. -/
def qform (T : H →L[ℂ] H) : ℝ := (⟪ψ, T ψ⟫_ℂ).re

theorem qform_add (T T' : H →L[ℂ] H) : qform ψ (T + T') = qform ψ T + qform ψ T' := by
  show (⟪ψ, T ψ + T' ψ⟫_ℂ).re = _
  rw [inner_add_right, Complex.add_re]
  rfl

theorem qform_sub (T T' : H →L[ℂ] H) : qform ψ (T - T') = qform ψ T - qform ψ T' := by
  show (⟪ψ, T ψ - T' ψ⟫_ℂ).re = _
  rw [inner_sub_right, Complex.sub_re]
  rfl

theorem qform_smul_real (r : ℝ) (T : H →L[ℂ] H) : qform ψ ((r : ℂ) • T) = r * qform ψ T := by
  show (⟪ψ, (r : ℂ) • T ψ⟫_ℂ).re = _
  rw [inner_smul_right, Complex.re_ofReal_mul]
  rfl

theorem qform_zero : qform ψ (0 : H →L[ℂ] H) = 0 := by
  show (⟪ψ, (0 : H)⟫_ℂ).re = 0
  rw [inner_zero_right, Complex.zero_re]

theorem qform_sum {ι : Type*} (s : Finset ι) (f : ι → H →L[ℂ] H) :
    qform ψ (∑ i ∈ s, f i) = ∑ i ∈ s, qform ψ (f i) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, qform_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, qform_add, ih, Finset.sum_insert hi]

theorem qform_one (hψ : ‖ψ‖ = 1) : qform ψ (1 : H →L[ℂ] H) = 1 := by
  show (⟪ψ, ψ⟫_ℂ).re = 1
  rw [← RCLike.re_to_complex, inner_self_eq_norm_sq, hψ, one_pow]

end QForm

/-! ## Isometries and adjoints -/

section Adjoint

variable [CompleteSpace H] (ψ : H)

/-- **An isometry preserves the norm.** -/
theorem norm_apply_of_isometry {T : H →L[ℂ] H} (h : star T * T = 1) (v : H) : ‖T v‖ = ‖v‖ :=
  (ContinuousLinearMap.norm_map_iff_adjoint_comp_self T).2
    (by rw [← ContinuousLinearMap.star_eq_adjoint]; exact h) v

theorem bnd_one_of_isometry {T : H →L[ℂ] H} (h : star T * T = 1) : Bnd T 1 := fun v => by
  rw [norm_apply_of_isometry h, one_mul]

/-- **An orthogonal projection is bounded by one.** -/
theorem bnd_one_of_isStarProjection {P : H →L[ℂ] H} (hP : IsStarProjection P) : Bnd P 1 :=
  bnd_of_norm_le hP.norm_le

/-- An isometry in front changes nothing. -/
theorem snorm_mul_of_isometry {T : H →L[ℂ] H} (h : star T * T = 1) (T' : H →L[ℂ] H) :
    snorm ψ (T * T') = snorm ψ T' :=
  norm_apply_of_isometry h (T' ψ)

/-- **Replacing an operator by an isometry it is close to, in front of anything.** If `W` and
the isometry `WD` agree on the state to within `δ`, and `WD` commutes with `Z`, then `Z W` is
within `K δ` of `Z`, where `K` bounds `Z`. -/
theorem snorm_mul_swap {W WD Z : H →L[ℂ] H} {δ K : ℝ} (hWD : star WD * WD = 1)
    (hcomm : WD * Z = Z * WD) (hZ : Bnd Z K) (hK : 0 ≤ K) (hd : snorm ψ (W - WD) ≤ δ) :
    snorm ψ (Z * W) ≤ snorm ψ Z + K * δ := by
  have hsplit : Z * W = Z * (W - WD) + WD * Z := by
    rw [hcomm]
    noncomm_ring
  calc snorm ψ (Z * W) ≤ snorm ψ (Z * (W - WD)) + snorm ψ (WD * Z) := by
        rw [hsplit]; exact snorm_add_le ψ _ _
    _ ≤ K * δ + snorm ψ Z := by
        refine add_le_add ?_ (le_of_eq (snorm_mul_of_isometry ψ hWD Z))
        exact le_trans (snorm_mul_le ψ hZ _) (mul_le_mul_of_nonneg_left hd hK)
    _ = snorm ψ Z + K * δ := by ring

/-- **The squared state norm is the quadratic form of `T* T`.** -/
theorem snorm_sq_eq_qform (T : H →L[ℂ] H) : snorm ψ T ^ 2 = qform ψ (star T * T) := by
  show ‖T ψ‖ ^ 2 = (⟪ψ, (star T) (T ψ)⟫_ℂ).re
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    ← RCLike.re_to_complex, inner_self_eq_norm_sq]

end Adjoint

end Op

end MIPRE

end

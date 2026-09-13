/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/Blocks/StateOnM.lean
-/
/-
# Functionals positive on a von Neumann algebra `M`

The functional of a `NormalState M` is positive on `M` only
(`∀ x ∈ M, 0 ≤ φ (star x * x)`, DIFFERENCES.md D1). This file collects the
consequences used by the block decomposition of tier T1b: `φ` is nonnegative and
real on positive elements of `M`, monotone on `M`, and vanishes on `star b * b`
for `b ∈ M` supported in a projection `z ∈ M` of `φ`-mass zero (the "zero-mass"
lemma, needed for the blocks the state does not see). Proof-side only.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.Generated
import MIPRE.Background.Orthonormalization.Orthogonalization.Positivity

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace Orthogonalization.Blocks

open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ}

/-- Scalar multiples of elements of `M` lie in `M`. -/
theorem smul_mem_vn (M : VonNeumannAlgebra H) (c : ℂ) {z : H →L[ℂ] H} (hz : z ∈ M) : c • z ∈ M := by
  rw [Algebra.smul_def]
  exact mul_mem (VonNeumannAlgebra.mem_carrier.mp (M.toStarSubalgebra.algebraMap_mem c)) hz

/-- The square root of a positive element of `M` lies in `M` (functional calculus). -/
theorem sqrt_mem (M : VonNeumannAlgebra H) {y : H →L[ℂ] H} (hy : y ∈ M) (hy0 : 0 ≤ y) :
    CFC.sqrt y ∈ M := by
  rw [CFC.sqrt_eq_cfc, cfc_nnreal_eq_real _ y hy0]
  exact CommutingRepetition.VN.cfc_real_mem M hy _

/-- A functional positive on `M` is nonnegative on the positive elements of `M`. -/
theorem map_nonneg_of_mem (hφ : ∀ x ∈ M, 0 ≤ φ (star x * x)) {y : H →L[ℂ] H} (hy : y ∈ M)
    (hy0 : 0 ≤ y) : 0 ≤ φ y := by
  have h := hφ (CFC.sqrt y) (sqrt_mem M hy hy0)
  rwa [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg y)).star_eq, CFC.sqrt_mul_sqrt_self y hy0] at h

theorem re_map_nonneg_of_mem (hφ : ∀ x ∈ M, 0 ≤ φ (star x * x)) {y : H →L[ℂ] H} (hy : y ∈ M)
    (hy0 : 0 ≤ y) : 0 ≤ (φ y).re :=
  (Complex.nonneg_iff.mp (map_nonneg_of_mem hφ hy hy0)).1

theorem im_map_eq_zero_of_mem (hφ : ∀ x ∈ M, 0 ≤ φ (star x * x)) {y : H →L[ℂ] H} (hy : y ∈ M)
    (hy0 : 0 ≤ y) : (φ y).im = 0 :=
  (Complex.nonneg_iff.mp (map_nonneg_of_mem hφ hy hy0)).2.symm

/-- On positive elements of `M`, `φ` is its real part. -/
theorem map_eq_ofReal_re_of_mem (hφ : ∀ x ∈ M, 0 ≤ φ (star x * x)) {y : H →L[ℂ] H} (hy : y ∈ M)
    (hy0 : 0 ≤ y) : φ y = ((φ y).re : ℂ) :=
  Complex.ext (by simp) (by simp [im_map_eq_zero_of_mem hφ hy hy0])

/-- A functional positive on `M` is monotone on `M` (real parts). -/
theorem re_map_le_of_mem (hφ : ∀ x ∈ M, 0 ≤ φ (star x * x)) {x y : H →L[ℂ] H} (hx : x ∈ M)
    (hy : y ∈ M) (hxy : x ≤ y) : (φ x).re ≤ (φ y).re := by
  have h := re_map_nonneg_of_mem hφ (sub_mem hy hx) (sub_nonneg.mpr hxy)
  rw [map_sub, Complex.sub_re] at h
  linarith

/-- **Zero-mass lemma.** If `b ∈ M` is supported in a projection `z ∈ M` (`b z = b`) and
`φ z` has real part `0`, then `φ (b* b) = 0` (real part). -/
theorem re_map_star_mul_self_eq_zero (hφ : ∀ x ∈ M, 0 ≤ φ (star x * x)) {z b : H →L[ℂ] H}
    (hz : IsStarProjection z) (hzM : z ∈ M) (hb : b ∈ M) (hbz : b * z = b)
    (h0 : (φ z).re = 0) : (φ (star b * b)).re = 0 := by
  have hsa : IsSelfAdjoint (star b * b) := IsSelfAdjoint.star_mul_self b
  set c : ℝ := ‖star b * b‖ with hc
  have h1 : star b * b ≤ algebraMap ℝ (H →L[ℂ] H) c := hsa.le_algebraMap_norm_self
  have h2 := conj_le_conj h1 z
  have hl : star z * (star b * b) * z = star b * b := by
    rw [hz.isSelfAdjoint.star_eq]
    calc z * (star b * b) * z = star (b * z) * (b * z) := by
          rw [star_mul, hz.isSelfAdjoint.star_eq]; noncomm_ring
      _ = star b * b := by rw [hbz]
  have hr : star z * algebraMap ℝ (H →L[ℂ] H) c * z = c • z := by
    rw [hz.isSelfAdjoint.star_eq, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one,
      smul_mul_assoc, hz.isIdempotentElem.eq]
  rw [hl, hr] at h2
  have hbb : star b * b ∈ M := mul_mem (star_mem hb) hb
  have hcz : c • z ∈ M := by
    have : c • z = (c : ℂ) • z := (Complex.coe_smul c z).symm
    rw [this]
    exact smul_mem_vn M _ hzM
  have hle := re_map_le_of_mem hφ hbb hcz h2
  have hge := re_map_nonneg_of_mem hφ hbb (star_mul_self_nonneg b)
  have hcz' : (φ (c • z)).re = 0 := by
    rw [LinearMap.map_smul_of_tower, Complex.smul_re, h0, smul_zero]
  linarith

end Orthogonalization.Blocks

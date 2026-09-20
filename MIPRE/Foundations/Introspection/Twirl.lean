/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.LinearMeasurement

/-! # Exact Pauli twirling on a field-linear subspace -/

noncomputable section

namespace MIPRE.Introspection

open Finset Weyl Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ}

def twirlX (K : Submodule F (Fin n → F)) (M : Matrix (Fin n → F) (Fin n → F) ℂ) :
    Matrix (Fin n → F) (Fin n → F) ℂ :=
  (Fintype.card K : ℂ)⁻¹ • ∑ v : K, wX v.1 * M * wX v.1

def twirlZ (K : Submodule F (Fin n → F)) (M : Matrix (Fin n → F) (Fin n → F) ℂ) :
    Matrix (Fin n → F) (Fin n → F) ℂ :=
  (Fintype.card K : ℂ)⁻¹ • ∑ v : K, wZ v.1 * M * wZ v.1

theorem conjugate_wZ_by_wX (v u : Fin n → F) :
    wX v * wZ u * wX v = sgn (trDot v u) • wZ u := by
  rw [wX_mul_wZ, Matrix.smul_mul, mul_assoc, wX_mul_self, mul_one]

theorem conjugate_wX_by_wZ (v u : Fin n → F) :
    wZ v * wX u * wZ v = sgn (trDot v u) • wX u := by
  rw [mul_assoc, wX_mul_wZ, Matrix.mul_smul, ← mul_assoc, wZ_mul_self, one_mul,
    trDot_comm u v]

/-- The `X(K)` twirl retains exactly those `Z` operators in the dot-product annihilator. -/
theorem twirlX_wZ (K : Submodule F (Fin n → F)) (u : Fin n → F) :
    twirlX K (wZ u) = if u ∈ CL.perp K then wZ u else 0 := by
  have hcard : (Fintype.card K : ℂ) ≠ 0 := by exact_mod_cast (Fintype.card_pos (α := K)).ne'
  unfold twirlX
  simp_rw [conjugate_wZ_by_wX]
  rw [← Finset.sum_smul, sum_subspace_sign]
  by_cases hu : u ∈ CL.perp K
  · rw [if_pos hu, smul_smul, inv_mul_cancel₀ hcard, one_smul, if_pos hu]
  · rw [if_neg hu, zero_smul, smul_zero, if_neg hu]

/-- The dual `Z(K)` twirl has the same annihilator criterion. -/
theorem twirlZ_wX (K : Submodule F (Fin n → F)) (u : Fin n → F) :
    twirlZ K (wX u) = if u ∈ CL.perp K then wX u else 0 := by
  have hcard : (Fintype.card K : ℂ) ≠ 0 := by exact_mod_cast (Fintype.card_pos (α := K)).ne'
  unfold twirlZ
  simp_rw [conjugate_wX_by_wZ]
  rw [← Finset.sum_smul, sum_subspace_sign]
  by_cases hu : u ∈ CL.perp K
  · rw [if_pos hu, smul_smul, inv_mul_cancel₀ hcard, one_smul, if_pos hu]
  · rw [if_neg hu, zero_smul, smul_zero, if_neg hu]

end MIPRE.Introspection

end

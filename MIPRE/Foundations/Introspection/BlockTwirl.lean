/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.Twirl
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import MIPRE.Tactics
public import MIPRE.Foundations.AncillaModel

@[expose] public section

/-! # Entry formulas for Pauli twirls with an ancillary space

Stated for block matrices over an arbitrary algebra `𝒜` (Phase 4 of `planning/mipco-track.md`):
the register is `Fin n → F`, the ancilla is abstract, an operator of register and ancilla is a
matrix `Matrix (Fin n → F) (Fin n → F) 𝒜`, and a register operator `A` is `smulKron 1 A`. The
matrix statements, on `(Fin n → F) × H`, are the case `𝒜 = Matrix H H ℂ`.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Weyl Classical Matrix Kronecker

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ} {𝒜 : Type*} [Ring 𝒜] [Algebra ℂ 𝒜]

theorem smulKron_wZ_mul_entry (v x y : Fin n → F) (M : Matrix (Fin n → F) (Fin n → F) 𝒜) :
    (smulKron (1 : 𝒜) (wZ v) * M) x y = sgn (trDot v x) • M x y := by
  simp [Matrix.mul_apply, smulKron_apply, wZ_apply, ite_smul, ite_mul]

theorem mul_smulKron_wZ_entry (v x y : Fin n → F) (M : Matrix (Fin n → F) (Fin n → F) 𝒜) :
    (M * smulKron (1 : 𝒜) (wZ v)) x y = sgn (trDot v y) • M x y := by
  simp [Matrix.mul_apply, smulKron_apply, wZ_apply, ite_smul, mul_ite]

theorem smulKron_wZ_conjugate_entry (v x y : Fin n → F)
    (M : Matrix (Fin n → F) (Fin n → F) 𝒜) :
    (smulKron (1 : 𝒜) (wZ v) * M * smulKron (1 : 𝒜) (wZ v)) x y =
      sgn (trDot v (x + y)) • M x y := by
  rw [mul_smulKron_wZ_entry, smulKron_wZ_mul_entry, trDot_add_right, sgn_add, smul_smul,
    mul_comm]

/-- Average over the full `Z` Pauli family on the register. -/
def dephaseZ (M : Matrix (Fin n → F) (Fin n → F) 𝒜) : Matrix (Fin n → F) (Fin n → F) 𝒜 :=
  (Fintype.card (Fin n → F) : ℂ)⁻¹ •
    ∑ v : Fin n → F, smulKron (1 : 𝒜) (wZ v) * M * smulKron (1 : 𝒜) (wZ v)

/-- The full `Z` twirl removes precisely the off-diagonal blocks in the sampled register. -/
theorem dephaseZ_entry (x y : Fin n → F) (M : Matrix (Fin n → F) (Fin n → F) 𝒜) :
    dephaseZ M x y = if x = y then M x y else 0 := by
  rw [dephaseZ, Matrix.smul_apply, Matrix.sum_apply]
  simp only [smulKron_wZ_conjugate_entry]
  rw [← Finset.sum_smul, smul_smul]
  by_cases hxy : x = y
  · subst y
    rw [Weyl.add_self_vec, sum_sgn_trDot_zero, ite_eq_left rfl,
      inv_mul_cancel₀ (Weyl.card_ne_zero (F := F) (n := Fin n)), one_smul]
  · have hne : x + y ≠ 0 := fun h => hxy ((Weyl.add_eq_zero_iff_vec x y).mp h)
    rw [sum_sgn_trDot hne, mul_zero, zero_smul, ite_eq_right hxy]

theorem smulKron_wX_mul_entry (v x y : Fin n → F) (M : Matrix (Fin n → F) (Fin n → F) 𝒜) :
    (smulKron (1 : 𝒜) (wX v) * M) x y = M (x + v) y := by
  have hx (z : Fin n → F) : x = z + v ↔ z = x + v := by
    constructor
    · intro h
      rw [h, Weyl.add_add_cancel_vec]
    · intro h
      rw [h, Weyl.add_add_cancel_vec]
  simp [Matrix.mul_apply, smulKron_apply, wX_apply, ite_smul, ite_mul, hx]

theorem mul_smulKron_wX_entry (v x y : Fin n → F) (M : Matrix (Fin n → F) (Fin n → F) 𝒜) :
    (M * smulKron (1 : 𝒜) (wX v)) x y = M x (y + v) := by
  simp [Matrix.mul_apply, smulKron_apply, wX_apply, ite_smul, mul_ite]

theorem smulKron_wX_conjugate_entry (v x y : Fin n → F)
    (M : Matrix (Fin n → F) (Fin n → F) 𝒜) :
    (smulKron (1 : 𝒜) (wX v) * M * smulKron (1 : 𝒜) (wX v)) x y = M (x + v) (y + v) := by
  rw [mul_smulKron_wX_entry, smulKron_wX_mul_entry]

/-- Average the `X` Pauli conjugations belonging to a subspace. -/
def averageX (K : Submodule F (Fin n → F)) (M : Matrix (Fin n → F) (Fin n → F) 𝒜) :
    Matrix (Fin n → F) (Fin n → F) 𝒜 :=
  (Fintype.card K : ℂ)⁻¹ •
    ∑ v : K, smulKron (1 : 𝒜) (wX v.1) * M * smulKron (1 : 𝒜) (wX v.1)

/-- The diagonal ancillary block obtained by averaging the fiber through `x`. -/
def averagedBlock (K : Submodule F (Fin n → F)) (M : Matrix (Fin n → F) (Fin n → F) 𝒜)
    (x : Fin n → F) : 𝒜 :=
  (Fintype.card K : ℂ)⁻¹ • ∑ v : K, M (x + v.1) (x + v.1)

/-- First dephasing, then averaging `X(K)`, leaves only the averaged diagonal blocks. -/
theorem averageX_dephaseZ_entry (K : Submodule F (Fin n → F))
    (M : Matrix (Fin n → F) (Fin n → F) 𝒜) (x y : Fin n → F) :
    averageX K (dephaseZ M) x y = if x = y then averagedBlock K M x else 0 := by
  rw [averageX, Matrix.smul_apply, Matrix.sum_apply]
  simp only [smulKron_wX_conjugate_entry, dephaseZ_entry, add_left_inj]
  by_cases hxy : x = y
  · subst y
    simp only [↓reduceIte]
    rfl
  · simp [hxy]

/-- The averaged ancillary block is constant on each coset of the twirled subspace. -/
theorem averagedBlock_eq_of_sub_mem (K : Submodule F (Fin n → F))
    (M : Matrix (Fin n → F) (Fin n → F) 𝒜)
    (x y : Fin n → F) (hxy : x - y ∈ K) : averagedBlock K M x = averagedBlock K M y := by
  let t : K := ⟨x - y, hxy⟩
  have hv (v : K) : y + (v + t).1 = x + v.1 := by
    change y + (v.1 + (x - y)) = x + v.1
    abel
  unfold averagedBlock
  congr 1
  apply Fintype.sum_equiv (Equiv.addRight t)
  intro v
  simp only [Equiv.coe_addRight, hv]

theorem synOf_wZ_entry (L : (Fin n → F) →ₗ[F] (Fin n → F))
    (a x y : Fin n → F) :
    synOf wZ L a x y = if x = y then (if L x = a then 1 else 0) else 0 := by
  rw [synOf, Matrix.sum_apply]
  simp only [proj_wZ, zProj_apply]
  by_cases hxy : x = y
  · subst y
    simp only [ite_true]
    by_cases ha : L x = a
    · rw [ite_eq_left ha]
      rw [Finset.sum_eq_single_of_mem x (by simp [ha])]
      · simp
      · intro z hz hzx
        exact ite_eq_right (Ne.symm hzx)
    · rw [ite_eq_right ha]
      apply Finset.sum_eq_zero
      intro z hz
      apply ite_eq_right
      intro hxz
      subst z
      exact ha (Finset.mem_filter.mp hz).2
  · simp [hxy]

/-- The exact block decomposition used by the hiding argument, including an arbitrary ancilla. -/
theorem linear_twirl_blocks (L : (Fin n → F) →ₗ[F] (Fin n → F))
    (M : Matrix (Fin n → F) (Fin n → F) 𝒜) :
    averageX L.ker (dephaseZ M) =
      ∑ a : Fin n → F, smulKron (averagedBlock L.ker M (linearPreimage L a)) (synOf wZ L a) := by
  ext x y
  rw [averageX_dephaseZ_entry, Matrix.sum_apply]
  simp only [smulKron_apply, synOf_wZ_entry]
  by_cases hxy : x = y
  · subst y
    simp only [↓reduceIte, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte]
    have hker : x - linearPreimage L (L x) ∈ L.ker := by
      rw [LinearMap.mem_ker, map_sub, linearPreimage_image, sub_self]
    rw [averagedBlock_eq_of_sub_mem L.ker M _ _ hker]
  · simp [hxy]

end MIPRE.Introspection

end

end

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.Twirl
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! # Entry formulas for Pauli twirls with an ancillary space -/

noncomputable section

namespace MIPRE.Introspection

open Finset Weyl Classical Matrix Kronecker

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ} {H : Type*} [Fintype H] [DecidableEq H]

def amplify (A : Matrix (Fin n → F) (Fin n → F) ℂ) :
    Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ := A ⊗ₖ (1 : Matrix H H ℂ)

theorem amplify_wZ_mul_entry (v x y : Fin n → F) (a b : H)
    (M : Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) :
    (amplify (H := H) (wZ v) * M) (x, a) (y, b) = sgn (trDot v x) * M (x, a) (y, b) := by
  simp [amplify, Matrix.mul_apply, Matrix.kroneckerMap_apply, wZ_apply,
    Fintype.sum_prod_type, Matrix.one_apply, mul_ite, ite_mul]

theorem mul_amplify_wZ_entry (v x y : Fin n → F) (a b : H)
    (M : Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) :
    (M * amplify (H := H) (wZ v)) (x, a) (y, b) = M (x, a) (y, b) * sgn (trDot v y) := by
  simp [amplify, Matrix.mul_apply, Matrix.kroneckerMap_apply, wZ_apply,
    Fintype.sum_prod_type, Matrix.one_apply, mul_ite, ite_mul]

theorem amplify_wZ_conjugate_entry (v x y : Fin n → F) (a b : H)
    (M : Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) :
    (amplify (H := H) (wZ v) * M * amplify (H := H) (wZ v)) (x, a) (y, b) =
      sgn (trDot v (x + y)) * M (x, a) (y, b) := by
  rw [mul_amplify_wZ_entry, amplify_wZ_mul_entry, trDot_add_right, sgn_add]
  ring

/-- Average over the full `Z` Pauli family on the first tensor factor. -/
def dephaseZ (M : Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) :
    Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ :=
  (Fintype.card (Fin n → F) : ℂ)⁻¹ •
    ∑ v : Fin n → F, amplify (H := H) (wZ v) * M * amplify (H := H) (wZ v)

/-- The full `Z` twirl removes precisely the off-diagonal blocks in the sampled register. -/
theorem dephaseZ_entry (x y : Fin n → F) (a b : H)
    (M : Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) :
    dephaseZ M (x, a) (y, b) = if x = y then M (x, a) (y, b) else 0 := by
  rw [dephaseZ, Matrix.smul_apply, Matrix.sum_apply]
  simp only [amplify_wZ_conjugate_entry, smul_eq_mul]
  rw [← Finset.sum_mul]
  by_cases hxy : x = y
  · subst y
    rw [Weyl.add_self_vec, sum_sgn_trDot_zero, if_pos rfl, ← mul_assoc,
      inv_mul_cancel₀ (Weyl.card_ne_zero (F := F) (n := Fin n)), one_mul]
  · have hne : x + y ≠ 0 := fun h => hxy ((Weyl.add_eq_zero_iff_vec x y).mp h)
    rw [sum_sgn_trDot hne, zero_mul, mul_zero, if_neg hxy]

theorem amplify_wX_mul_entry (v x y : Fin n → F) (a b : H)
    (M : Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) :
    (amplify (H := H) (wX v) * M) (x, a) (y, b) = M (x + v, a) (y, b) := by
  have hx (z : Fin n → F) : x = z + v ↔ z = x + v := by
    constructor
    · intro h
      rw [h, Weyl.add_add_cancel_vec]
    · intro h
      rw [h, Weyl.add_add_cancel_vec]
  simp [amplify, Matrix.mul_apply, Matrix.kroneckerMap_apply, wX_apply,
    Fintype.sum_prod_type, Matrix.one_apply, mul_ite, ite_mul, hx]

theorem mul_amplify_wX_entry (v x y : Fin n → F) (a b : H)
    (M : Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) :
    (M * amplify (H := H) (wX v)) (x, a) (y, b) = M (x, a) (y + v, b) := by
  simp [amplify, Matrix.mul_apply, Matrix.kroneckerMap_apply, wX_apply,
    Fintype.sum_prod_type, Matrix.one_apply, mul_ite, ite_mul]

theorem amplify_wX_conjugate_entry (v x y : Fin n → F) (a b : H)
    (M : Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) :
    (amplify (H := H) (wX v) * M * amplify (H := H) (wX v)) (x, a) (y, b) =
      M (x + v, a) (y + v, b) := by
  rw [mul_amplify_wX_entry, amplify_wX_mul_entry]

/-- Average the `X` Pauli conjugations belonging to a subspace. -/
def averageX (K : Submodule F (Fin n → F))
    (M : Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) :
    Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ :=
  (Fintype.card K : ℂ)⁻¹ • ∑ v : K, amplify (H := H) (wX v.1) * M * amplify (H := H) (wX v.1)

/-- The diagonal ancillary block obtained by averaging the fiber through `x`. -/
def averagedBlock (K : Submodule F (Fin n → F))
    (M : Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) (x : Fin n → F) : Matrix H H ℂ :=
  (Fintype.card K : ℂ)⁻¹ • ∑ v : K, M.submatrix (fun a => (x + v.1, a)) (fun a => (x + v.1, a))

/-- First dephasing, then averaging `X(K)`, leaves only the averaged diagonal blocks. -/
theorem averageX_dephaseZ_entry (K : Submodule F (Fin n → F))
    (M : Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ)
    (x y : Fin n → F) (a b : H) :
    averageX K (dephaseZ M) (x, a) (y, b) =
      if x = y then averagedBlock K M x a b else 0 := by
  rw [averageX, Matrix.smul_apply, Matrix.sum_apply]
  simp only [amplify_wX_conjugate_entry, dephaseZ_entry, add_left_inj, add_right_inj]
  by_cases hxy : x = y
  · subst y
    simp only [if_pos rfl]
    rw [averagedBlock, Matrix.smul_apply, Matrix.sum_apply]
    rfl
  · simp [hxy]

/-- The averaged ancillary block is constant on each coset of the twirled subspace. -/
theorem averagedBlock_eq_of_sub_mem (K : Submodule F (Fin n → F))
    (M : Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ)
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
    · rw [if_pos ha]
      rw [Finset.sum_eq_single_of_mem x (by simp [ha])]
      · simp
      · intro z hz hzx
        exact if_neg (Ne.symm hzx)
    · rw [if_neg ha]
      apply Finset.sum_eq_zero
      intro z hz
      apply if_neg
      intro hxz
      subst z
      exact ha (Finset.mem_filter.mp hz).2
  · simp [hxy]

/-- The exact block decomposition used by the hiding argument, including an arbitrary ancilla. -/
theorem linear_twirl_blocks (L : (Fin n → F) →ₗ[F] (Fin n → F))
    (M : Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) :
    averageX L.ker (dephaseZ M) =
      ∑ a : Fin n → F, synOf wZ L a ⊗ₖ averagedBlock L.ker M (linearPreimage L a) := by
  ext ⟨x, i⟩ ⟨y, j⟩
  rw [averageX_dephaseZ_entry, Matrix.sum_apply]
  simp only [Matrix.kroneckerMap_apply, synOf_wZ_entry]
  by_cases hxy : x = y
  · subst y
    simp only [if_pos rfl, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    have hker : x - linearPreimage L (L x) ∈ L.ker := by
      rw [LinearMap.mem_ker, map_sub, linearPreimage_image, sub_self]
    rw [averagedBlock_eq_of_sub_mem L.ker M _ _ hker]
  · simp [hxy]

end MIPRE.Introspection

end

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.VaryingPauliMixing
import MIPRE.Foundations.Introspection.Conditioning

/-! # Transporting finite register operators and their state distances

All transports below are explicit permutations of computational basis labels.
In particular they preserve positivity, projectivity and squared state norms.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder

set_option linter.unusedSectionVars false

variable {I J K L A : Type*}
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K] [Fintype L] [DecidableEq L]
  [Fintype A] [DecidableEq A]

/-- Pull an operator back along a bijective labelling of the basis. -/
def registerOp (e : I ≃ J) (M : Matrix J J ℂ) : Matrix I I ℂ :=
  M.submatrix e e

@[simp] theorem registerOp_apply (e : I ≃ J) (M : Matrix J J ℂ) (i j : I) :
    registerOp e M i j = M (e i) (e j) := rfl

@[simp] theorem registerOp_one (e : I ≃ J) : registerOp e (1 : Matrix J J ℂ) = 1 :=
  Matrix.submatrix_one_equiv e

@[simp] theorem registerOp_sub (e : I ≃ J) (M N : Matrix J J ℂ) :
    registerOp e (M - N) = registerOp e M - registerOp e N := rfl

@[simp] theorem registerOp_mul (e : I ≃ J) (M N : Matrix J J ℂ) :
    registerOp e (M * N) = registerOp e M * registerOp e N := by
  exact (Matrix.submatrix_mul_equiv M N e e e).symm

@[simp] theorem registerOp_sum (e : I ≃ J) (M : A → Matrix J J ℂ) :
    registerOp e (∑ a, M a) = ∑ a, registerOp e (M a) := by
  ext i j
  simp only [registerOp_apply, Matrix.sum_apply]

@[simp] theorem registerOp_conjTranspose (e : I ≃ J) (M : Matrix J J ℂ) :
    registerOp e Mᴴ = (registerOp e M)ᴴ := rfl

@[simp] theorem registerOp_symm (e : I ≃ J) (M : Matrix I I ℂ) :
    registerOp e (registerOp e.symm M) = M := by
  ext i j
  simp only [registerOp_apply, Equiv.symm_apply_apply]

@[simp] theorem registerOp_inv (e : I ≃ J) (M : Matrix J J ℂ) :
    registerOp e.symm (registerOp e M) = M := registerOp_symm e.symm M

/-- Positivity is preserved without changing any eigenvalues. -/
theorem registerOp_posSemidef (e : I ≃ J) {M : Matrix J J ℂ} (hM : M.PosSemidef) :
    (registerOp e M).PosSemidef := hM.submatrix e

/-- A projective measurement remains projective after permuting its basis. -/
theorem registerOp_isPVM (e : I ≃ J) {M : A → Matrix J J ℂ} (hM : IsPVM M) :
    IsPVM (fun a => registerOp e (M a)) where
  isSelfAdjoint a := by rw [← registerOp_conjTranspose, hM.isSelfAdjoint]
  idem a := by rw [← registerOp_mul, hM.idem]
  sum_eq_one := by rw [← registerOp_sum, hM.sum_eq_one, registerOp_one]

/-- Transport the actual normalized positive measurement, rather than only its matrices. -/
def registerPOVM (e : I ≃ J) (M : POVM A J) : POVM A I where
  mats a := ⟨registerOp e (M.mats a).val, by
    rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose]
    exact (registerOp_posSemidef e
      (Matrix.nonneg_iff_posSemidef.mp (Subtype.coe_le_coe.mpr (M.nonneg a)))).isHermitian⟩
  nonneg a := by
    change (0 : Matrix I I ℂ) ≤ registerOp e (M.mats a).val
    exact Matrix.nonneg_iff_posSemidef.mpr (registerOp_posSemidef e
      (Matrix.nonneg_iff_posSemidef.mp (Subtype.coe_le_coe.mpr (M.nonneg a))))
  normalized := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    change (∑ a, registerOp e (M.mats a).val) = 1
    rw [← registerOp_sum]
    have hM : (∑ a, (M.mats a).val) = (1 : Matrix J J ℂ) := by
      simpa only [AddSubmonoidClass.coe_finsetSum, selfAdjoint.val_one] using
        congrArg Subtype.val M.normalized
    rw [hM, registerOp_one]

@[simp] theorem registerPOVM_mats (e : I ≃ J) (M : POVM A J) (a : A) :
    ((registerPOVM e M).mats a).val = registerOp e (M.mats a).val := rfl

/-- A computational-basis permutation preserves the Euclidean norm. -/
theorem norm_evec_comp_equiv (e : I ≃ J) (v : J → ℂ) :
    ‖evec (v ∘ e)‖ = ‖evec v‖ := by
  simp only [evec, EuclideanSpace.norm_eq]
  congr 1
  exact Equiv.sum_comp e (fun j => ‖v j‖ ^ 2)

/-- Simultaneous matrix and vector reindexing commutes with matrix application. -/
theorem registerOp_mulVec (e : I ≃ J) (M : Matrix J J ℂ) (v : J → ℂ) :
    registerOp e M *ᵥ (v ∘ e) = (M *ᵥ v) ∘ e := by
  funext i
  exact Equiv.sum_comp e (fun j => M (e i) j * v j)

theorem registerOp_kronecker (e : I ≃ J) (f : K ≃ L)
    (M : Matrix J J ℂ) (N : Matrix L L ℂ) :
    registerOp (e.prodCongr f) (M ⊗ₖ N) = registerOp e M ⊗ₖ registerOp f N := rfl

/-- State distances are unchanged by independent permutations of the two parties. -/
theorem stateSqNorm_registerOp (e : I ≃ J) (f : K ≃ L)
    (ψ : J × L → ℂ) (M : Matrix J J ℂ) :
    stateSqNorm (ψ ∘ e.prodCongr f) (registerOp e M) = stateSqNorm ψ M := by
  unfold stateSqNorm stateNorm stateVec
  change ‖evec _‖ ^ 2 = ‖evec _‖ ^ 2
  rw [← registerOp_one f, ← registerOp_kronecker, registerOp_mulVec, norm_evec_comp_equiv]

end MIPRE.Introspection

end

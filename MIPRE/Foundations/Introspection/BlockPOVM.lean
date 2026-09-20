/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.BlockTwirl
import MIPRE.Foundations.Games

/-! # The ancillary blocks of a twirled POVM are POVMs -/

noncomputable section

namespace MIPRE.Introspection

open Finset Weyl Classical Matrix
open scoped ComplexOrder MatrixOrder

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ} {H : Type*} [Fintype H] [DecidableEq H]

/-- Averaging diagonal compressions preserves positivity. -/
theorem averagedBlock_posSemidef (K : Submodule F (Fin n → F))
    (M : Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ)
    (hM : M.PosSemidef) (x : Fin n → F) : (averagedBlock K M x).PosSemidef := by
  apply Matrix.PosSemidef.smul
  · exact Matrix.posSemidef_sum _ (fun v _ => hM.submatrix (fun a => (x + v.1, a)))
  · positivity

theorem averagedBlock_sum {A : Type*} [Fintype A] (K : Submodule F (Fin n → F))
    (M : A → Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) (x : Fin n → F) :
    averagedBlock K (∑ a, M a) x = ∑ a, averagedBlock K (M a) x := by
  ext i j
  simp only [averagedBlock, Matrix.smul_apply, Matrix.sum_apply, Matrix.submatrix_apply,
    smul_eq_mul]
  rw [Finset.sum_comm, Finset.mul_sum]

theorem averagedBlock_one (K : Submodule F (Fin n → F)) (x : Fin n → F) :
    averagedBlock K (1 : Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) x = 1 := by
  have hc : (Fintype.card K : ℂ) ≠ 0 := by exact_mod_cast (Fintype.card_pos (α := K)).ne'
  ext i j
  simp only [averagedBlock, Matrix.smul_apply, Matrix.sum_apply, Matrix.submatrix_apply,
    Matrix.one_apply, Prod.mk.injEq, true_and, smul_eq_mul]
  by_cases hij : i = j
  · simp [hij, hc]
  · simp [hij]

/-- Each averaged diagonal block of a normalized positive family is itself normalized. -/
theorem sum_averagedBlock_eq_one {A : Type*} [Fintype A]
    (K : Submodule F (Fin n → F))
    (M : A → Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) (hM : ∑ a, M a = 1)
    (x : Fin n → F) : (∑ a, averagedBlock K (M a) x) = 1 := by
  rw [← averagedBlock_sum, hM, averagedBlock_one]

set_option maxHeartbeats 800000 in
/-- The actual ancillary POVM at a selected fiber, obtained by compressing and averaging. -/
def blockPOVM {A : Type*} [Fintype A] (K : Submodule F (Fin n → F))
    (P : POVM A ((Fin n → F) × H)) (x : Fin n → F) : POVM A H where
  mats a := ⟨averagedBlock (H := H) K (P.mats a) x, by
    rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose]
    exact (averagedBlock_posSemidef K _
      (Matrix.nonneg_iff_posSemidef.mp (Subtype.coe_le_coe.mpr (P.nonneg a))) x).isHermitian⟩
  nonneg a := by
    change (0 : Matrix H H ℂ) ≤ averagedBlock (H := H) K (P.mats a) x
    exact Matrix.nonneg_iff_posSemidef.mpr (averagedBlock_posSemidef K _
      (Matrix.nonneg_iff_posSemidef.mp (Subtype.coe_le_coe.mpr (P.nonneg a))) x)
  normalized := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    change (∑ a, averagedBlock (H := H) K (P.mats a) x) = 1
    apply sum_averagedBlock_eq_one
    simpa only [AddSubmonoidClass.coe_finsetSum, selfAdjoint.val_one] using
      congrArg (fun M : selfAdjoint (Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) =>
      (M : Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ)) P.normalized

@[simp] theorem blockPOVM_mats {A : Type*} [Fintype A] (K : Submodule F (Fin n → F))
    (P : POVM A ((Fin n → F) × H)) (x : Fin n → F) (a : A) :
    ((blockPOVM K P x).mats a : Matrix H H ℂ) = averagedBlock (H := H) K (P.mats a) x := rfl

set_option maxHeartbeats 800000 in
open Kronecker in
/-- A Pauli-twirled POVM is a linear-map readout followed by an actual ancillary POVM. -/
theorem linear_twirl_povm {A : Type*} [Fintype A]
    (L : (Fin n → F) →ₗ[F] (Fin n → F)) (P : POVM A ((Fin n → F) × H)) :
    ∃ Q : (Fin n → F) → POVM A H, ∀ a,
      averageX L.ker (dephaseZ (H := H) (P.mats a)) =
        ∑ y : Fin n → F, synOf wZ L y ⊗ₖ ((Q y).mats a : Matrix H H ℂ) := by
  refine ⟨fun y => blockPOVM L.ker P (linearPreimage L y), fun a => ?_⟩
  simp only [blockPOVM_mats]
  exact linear_twirl_blocks (H := H) L (P.mats a)

end MIPRE.Introspection

end

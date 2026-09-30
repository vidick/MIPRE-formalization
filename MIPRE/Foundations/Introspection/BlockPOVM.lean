/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.BlockTwirl
public import MIPRE.Foundations.Games
public import MIPRE.Foundations.BlockOrder

@[expose] public section

/-! # The ancillary blocks of a twirled POVM are POVMs

For block matrices over an ordered `⋆`-algebra `𝒜` (Phase 4 of `planning/mipco-track.md`), ordered
as sums of elements `Z⋆ Z` (`MIPRE.MatrixStar.instPartialOrderStar`): a POVM of the register and
the ancilla, twirled, is a linear-map readout on the register followed by a POVM in `𝒜`.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Weyl Classical Matrix

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ} {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] [StarModule ℂ 𝒜]

theorem averagedBlock_sum {A : Type*} [Fintype A] (K : Submodule F (Fin n → F))
    (M : A → Matrix (Fin n → F) (Fin n → F) 𝒜) (x : Fin n → F) :
    averagedBlock K (∑ a, M a) x = ∑ a, averagedBlock K (M a) x := by
  simp only [averagedBlock, Matrix.sum_apply]
  rw [Finset.sum_comm, Finset.smul_sum]

theorem averagedBlock_one (K : Submodule F (Fin n → F)) (x : Fin n → F) :
    averagedBlock K (1 : Matrix (Fin n → F) (Fin n → F) 𝒜) x = 1 := by
  have hc : (Fintype.card K : ℂ) ≠ 0 := by exact_mod_cast (Fintype.card_pos (α := K)).ne'
  simp only [averagedBlock, Matrix.one_apply_eq, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- Each averaged diagonal block of a normalized family is itself normalized. -/
theorem sum_averagedBlock_eq_one {A : Type*} [Fintype A]
    (K : Submodule F (Fin n → F))
    (M : A → Matrix (Fin n → F) (Fin n → F) 𝒜) (hM : ∑ a, M a = 1)
    (x : Fin n → F) : (∑ a, averagedBlock K (M a) x) = 1 := by
  rw [← averagedBlock_sum, hM, averagedBlock_one]

/-- An averaged block of a self-adjoint matrix is self-adjoint. -/
theorem star_averagedBlock (K : Submodule F (Fin n → F)) (M : Matrix (Fin n → F) (Fin n → F) 𝒜)
    (hM : star M = M) (x : Fin n → F) : star (averagedBlock K M x) = averagedBlock K M x := by
  have hdiag : ∀ y, star (M y y) = M y y := fun y => by
    conv_rhs => rw [← hM]
    rw [Matrix.star_apply]
  have hc : star ((Fintype.card K : ℂ)⁻¹) = (Fintype.card K : ℂ)⁻¹ := by
    rw [star_inv₀, star_natCast]
  simp only [averagedBlock, star_smul, star_sum, hdiag, hc]

variable [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarProper 𝒜]

/-- Averaging diagonal compressions preserves positivity. -/
theorem averagedBlock_nonneg (K : Submodule F (Fin n → F))
    (M : Matrix (Fin n → F) (Fin n → F) 𝒜) (hM : 0 ≤ M) (x : Fin n → F) :
    0 ≤ averagedBlock K M x := by
  have hsum : 0 ≤ ∑ v : K, M (x + v.1) (x + v.1) :=
    Finset.sum_nonneg fun v _ => MatrixStar.diag_nonneg hM _
  have hr : (Fintype.card K : ℂ)⁻¹ = (((Fintype.card K : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [averagedBlock, hr]
  exact real_smul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) hsum

/-- The actual ancillary POVM at a selected fiber, obtained by compressing and averaging. -/
def blockPOVM {A : Type*} [Fintype A] (K : Submodule F (Fin n → F))
    (P : POVMIn A (Matrix (Fin n → F) (Fin n → F) 𝒜)) (x : Fin n → F) : POVMIn A 𝒜 where
  mats a := ⟨averagedBlock K (P.op a) x, star_averagedBlock K _ (P.star_op a) x⟩
  nonneg a := Subtype.coe_le_coe.mp (averagedBlock_nonneg K _ (P.op_nonneg a) x)
  normalized := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    exact sum_averagedBlock_eq_one K P.op P.sum_op x

@[simp] theorem blockPOVM_mats {A : Type*} [Fintype A] (K : Submodule F (Fin n → F))
    (P : POVMIn A (Matrix (Fin n → F) (Fin n → F) 𝒜)) (x : Fin n → F) (a : A) :
    (blockPOVM K P x).op a = averagedBlock K (P.op a) x := rfl

/-- A Pauli-twirled POVM is a linear-map readout followed by an actual ancillary POVM. -/
theorem linear_twirl_povm {A : Type*} [Fintype A]
    (L : (Fin n → F) →ₗ[F] (Fin n → F)) (P : POVMIn A (Matrix (Fin n → F) (Fin n → F) 𝒜)) :
    ∃ Q : (Fin n → F) → POVMIn A 𝒜, ∀ a,
      averageX L.ker (dephaseZ (P.op a)) = ∑ y : Fin n → F, smulKron ((Q y).op a) (synOf wZ L y) := by
  refine ⟨fun y => blockPOVM L.ker P (linearPreimage L y), fun a => ?_⟩
  simp only [blockPOVM_mats]
  exact linear_twirl_blocks L (P.op a)

end MIPRE.Introspection

end

end

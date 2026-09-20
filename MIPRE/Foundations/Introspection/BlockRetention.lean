/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.RetainedFibre
import MIPRE.Foundations.Introspection.BlockPOVM
import MIPRE.Foundations.Introspection.Measurements

/-! # Completing the matching blocks of a twirled measurement -/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder

variable {V H Y A : Type*} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]
  [Fintype Y] [DecidableEq Y] [Fintype A] [DecidableEq A]

/-- Read a projective register, then use the POVM selected by its outcome on the ancilla. -/
def controlledPOVM (P : Y → Matrix V V ℂ) (hP : IsPVM P) (Q : Y → POVM A H) :
    POVM (Y × A) (V × H) where
  mats p := ⟨P p.1 ⊗ₖ ((Q p.1).mats p.2).val, by
    rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose]
    exact ((hP.posSemidef p.1).kronecker (Matrix.nonneg_iff_posSemidef.mp
      (Subtype.coe_le_coe.mpr ((Q p.1).nonneg p.2)))).isHermitian⟩
  nonneg p := by
    apply Subtype.coe_le_coe.mp
    exact ((hP.posSemidef p.1).kronecker (Matrix.nonneg_iff_posSemidef.mp
      (Subtype.coe_le_coe.mpr ((Q p.1).nonneg p.2)))).nonneg
  normalized := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    change (∑ p : Y × A, P p.1 ⊗ₖ ((Q p.1).mats p.2).val) = 1
    rw [Fintype.sum_prod_type]
    simp_rw [← kronecker_sum_right, POVM.sum_val]
    rw [← sum_kronecker_left, hP.sum_eq_one, Matrix.one_kronecker_one]

/-- Multiplication by a readout projector retains exactly its own block. -/
theorem sum_blocks_mul_readout (P : Y → Matrix V V ℂ) (hP : IsPVM P)
    (Q : Y → Matrix H H ℂ) (y : Y) :
    (∑ z, P z ⊗ₖ Q z) * aOp (P y) = P y ⊗ₖ Q y := by
  rw [Finset.sum_mul]
  have hterm z : (P z ⊗ₖ Q z) * aOp (P y) = (P z * P y) ⊗ₖ Q z := by
    rw [aOp, ← Matrix.mul_kronecker_mul, Matrix.mul_one]
  simp_rw [hterm, hP.mul_eq_ite]
  rw [Finset.sum_eq_single y]
  · simp
  · intro z _ hzy
    simp [hzy]
  · simp

/-- Every individual joint element is below the marginal that forgets its first outcome. -/
theorem joint_le_second_marginal (Q : POVM (Y × A) H) (y : Y) (a : A) :
    (Q.mats (y, a)).val ≤ ((Q.map Prod.snd).mats a).val := by
  rw [show ((Q.map Prod.snd).mats a).val =
    ∑ p ∈ univ.filter (fun p : Y × A => p.2 = a), (Q.mats p).val from
    AddSubmonoidClass.coe_finsetSum _ _]
  exact Finset.single_le_sum
    (fun p _ => Subtype.coe_le_coe.mpr (Q.nonneg p)) (by simp)

/-- The matching block is positive and dominated by the controlled marginal POVM. -/
theorem retained_block_le_completion (P : Y → Matrix V V ℂ) (hP : IsPVM P)
    (Q : Y → POVM (Y × A) H) (p : Y × A) :
    P p.1 ⊗ₖ ((Q p.1).mats p).val ≤
      ((controlledPOVM P hP (fun y => (Q y).map Prod.snd)).mats p).val := by
  change P p.1 ⊗ₖ ((Q p.1).mats p).val ≤
    P p.1 ⊗ₖ (((Q p.1).map Prod.snd).mats p.2).val
  apply sub_nonneg.mp
  rw [show P p.1 ⊗ₖ (((Q p.1).map Prod.snd).mats p.2).val -
      P p.1 ⊗ₖ ((Q p.1).mats p).val =
      P p.1 ⊗ₖ ((((Q p.1).map Prod.snd).mats p.2).val - ((Q p.1).mats p).val) from by
    ext i j
    simp only [Matrix.sub_apply, Matrix.kroneckerMap_apply]
    ring]
  exact ((hP.posSemidef p.1).kronecker (Matrix.nonneg_iff_posSemidef.mp
    (sub_nonneg.mpr (joint_le_second_marginal (Q p.1) p.1 p.2)))).nonneg

variable {B : Type*} [Fintype B] [DecidableEq B]

/-- Retain the matching ancillary block, using the exactly consistent mirror readout. -/
theorem block_retention_precompletion (ψ : (V × H) × B → ℂ)
    (M : Y × A → Matrix (V × H) (V × H) ℂ) (hM : IsPVM M)
    (P : Y → Matrix V V ℂ) (hP : IsPVM P) (Q : Y → POVM (Y × A) H)
    (R : Y → Matrix B B ℂ) (hR : IsPVM R)
    (hPR : ∀ y, aOp (aOp (P y) : Matrix (V × H) _ ℂ) *ᵥ ψ = bOp (R y) *ᵥ ψ) :
    (∑ p : Y × A, stateSqNorm ψ (M p - P p.1 ⊗ₖ ((Q p.1).mats p).val)) ≤
      2 * (∑ y, stateSqNorm ψ ((∑ a, M (y, a)) - aOp (P y))) +
      2 * (∑ p : Y × A, stateSqNorm ψ (M p - ∑ z, P z ⊗ₖ ((Q z).mats p).val)) := by
  have h := retained_fibre_dist ψ (fun p => aOp (M p))
    (fun p => aOp (∑ z, P z ⊗ₖ ((Q z).mats p).val)) (fun y => aOp (aOp (P y)))
    (fun y => bOp (R y)) hM.aOp hR.bOp hPR
    (fun y a => aOp_mul_bOp _ _) (fun y a => aOp_mul_bOp _ _)
  simp only [← aOp_mul, sum_blocks_mul_readout P hP, ← aOp_sub, ← aOp_sum] at h
  simpa only [stateSqNorm, stateNorm, norm_stateVec_eq_snorm] using h

/-- Complete the retained blocks after averaging questions; the result is an actual family of POVMs. -/
theorem block_retention_dist_avg {X : Type*} [Fintype X]
    (D : X → ℝ) (hD0 : ∀ x, 0 ≤ D x) (hD1 : ∑ x, D x = 1)
    (ψ : (V × H) × B → ℂ) (hψ : ‖evec ψ‖ = 1)
    (M : X → Y × A → Matrix (V × H) (V × H) ℂ) (hM : ∀ x, IsPVM (M x))
    (P : X → Y → Matrix V V ℂ) (hP : ∀ x, IsPVM (P x))
    (Q : X → Y → POVM (Y × A) H) (R : X → Y → Matrix B B ℂ) (hR : ∀ x, IsPVM (R x))
    (hPR : ∀ x y, aOp (aOp (P x y) : Matrix (V × H) _ ℂ) *ᵥ ψ = bOp (R x y) *ᵥ ψ)
    {δ : ℝ} (hclose : ∑ x, D x *
      (2 * (∑ y, stateSqNorm ψ ((∑ a, M x (y, a)) - aOp (P x y))) +
       2 * (∑ p : Y × A, stateSqNorm ψ (M x p - ∑ z, P x z ⊗ₖ ((Q x z).mats p).val))) ≤ δ) :
    (∑ x, D x * ∑ p : Y × A, stateSqNorm ψ
      (M x p - P x p.1 ⊗ₖ (((Q x p.1).map Prod.snd).mats p.2).val)) ≤
      2 * δ + 4 * Real.sqrt δ := by
  let Bb x (p : Y × A) := P x p.1 ⊗ₖ ((Q x p.1).mats p).val
  let Cc x := controlledPOVM (P x) (hP x) (fun y => (Q x y).map Prod.snd)
  have hret := Finset.sum_le_sum fun x (_ : x ∈ univ) =>
    mul_le_mul_of_nonneg_left
      (block_retention_precompletion ψ (M x) (hM x) (P x) (hP x) (Q x) (R x) (hR x)
        (hPR x)) (hD0 x)
  have hret' : ∑ x, D x * ∑ p : Y × A, snorm ψ (aOp (M x p) - aOp (Bb x p)) ^ 2 ≤ δ := by
    simpa only [← aOp_sub, Bb, stateSqNorm, stateNorm, norm_stateVec_eq_snorm] using
      hret.trans hclose
  have h := submeasurement_completion_dist_avg D hD0 hD1 ψ hψ
    (fun x p => aOp (M x p)) (fun x p => aOp (Bb x p))
    (fun x p => aOp (((Cc x).mats p).val)) (fun x => (hM x).aOp)
    (fun x p => aOp_nonneg (((hP x).posSemidef p.1).kronecker
      (Matrix.nonneg_iff_posSemidef.mp (Subtype.coe_le_coe.mpr ((Q x p.1).nonneg p)))).nonneg)
    (fun x p => aOp_nonneg (Subtype.coe_le_coe.mpr ((Cc x).nonneg p)))
    (fun x => by rw [← aOp_sum, POVM.sum_val, aOp_one])
    (fun x p => aOp_mono (retained_block_le_completion (P x) (hP x) (Q x) p)) hret'
  simpa only [← aOp_sub, stateSqNorm, stateNorm, norm_stateVec_eq_snorm,
    Cc, controlledPOVM] using h

end MIPRE.Introspection

end

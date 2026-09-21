/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.ConditionalConsistency
import MIPRE.Foundations.Introspection.Measurements

/-! # Replacing a conditional hiding normalizer by its ideal prefix

The coarse outcome map may depend on the retained conditioning label. Positivity
of the ideal commuting prefix/fine-projector products lets us retain the fine
agreement without a factor depending on either outcome alphabet. The resulting
replacement costs three times each of the conditional, prefix, and fine errors.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder

set_option linter.unusedSectionVars false

variable {H K I Y Z : Type*}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype Y] [DecidableEq Y]
  [Fintype Z] [DecidableEq Z]

/-- The ideal joint outcome: its prefix times the fine family coarsened with
the map selected by that prefix. -/
def conditionalIdeal (P : I → Matrix K K ℂ) (Q : Y → Matrix K K ℂ)
    (f : Y → I → Z) (p : Y × Z) : Matrix K K ℂ :=
  Q p.1 * fibSum P (f p.1) p.2

theorem commute_fibSum_right (P : I → Matrix K K ℂ) (Q : Y → Matrix K K ℂ)
    (hc : ∀ y i, Commute (Q y) (P i)) (f : I → Z) (y : Y) (z : Z) :
    Commute (Q y) (fibSum P f z) := by
  apply Commute.sum_right
  intro i _
  exact hc y i

/-- Conditional ideal outcomes form a complete PVM although their coarse maps vary. -/
theorem conditionalIdeal_isPVM (P : I → Matrix K K ℂ) (Q : Y → Matrix K K ℂ)
    (f : Y → I → Z) (hP : IsPVM P) (hQ : IsPVM Q)
    (hc : ∀ y i, Commute (Q y) (P i)) : IsPVM (conditionalIdeal P Q f) where
  isSelfAdjoint p :=
    (joint_measurement_isPVM Q (fibSum P (f p.1)) hQ (isPVM_fibSum hP _)
      (commute_fibSum_right P Q hc _)).isSelfAdjoint p
  idem p :=
    (joint_measurement_isPVM Q (fibSum P (f p.1)) hQ (isPVM_fibSum hP _)
      (commute_fibSum_right P Q hc _)).idem p
  sum_eq_one := by
    simp only [conditionalIdeal, Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, (isPVM_fibSum hP _).sum_eq_one, mul_one]
    exact hQ.sum_eq_one

theorem conditionalIdeal_mul_normalizer (P : I → Matrix K K ℂ) (Q : Y → Matrix K K ℂ)
    (f : Y → I → Z) (hQ : IsPVM Q) (hc : ∀ y i, Commute (Q y) (P i)) (p : Y × Z) :
    conditionalIdeal P Q f p * Q p.1 = conditionalIdeal P Q f p := by
  unfold conditionalIdeal
  rw [mul_assoc, ← (commute_fibSum_right P Q hc (f p.1) p.1 p.2).eq,
    ← mul_assoc, hQ.idem]

/-- Keyed coarse agreement dominates fine agreement when the ideal normalizers
commute with the fine ideal PVM. All extra cross terms are positive. -/
theorem conditional_coarse_overlap (ψ : H × K → ℂ)
    (M : I → Matrix H H ℂ) (P : I → Matrix K K ℂ) (Q : Y → Matrix K K ℂ)
    (f : Y → I → Z) (hM : IsPVM M) (hP : IsPVM P) (hQ : IsPVM Q)
    (hc : ∀ y i, Commute (Q y) (P i)) :
    (∑ i, bornProb ψ (M i) (P i)) ≤
      ∑ p : Y × Z, bornProb ψ (fibSum M (f p.1) p.2) (conditionalIdeal P Q f p) := by
  have hjoint := joint_measurement_isPVM Q P hQ hP hc
  have hfib (y : Y) (z : Z) :
      bornProb ψ (fibSum M (f y) z) (conditionalIdeal P Q f (y, z)) =
        ∑ i ∈ univ.filter (fun i => f y i = z),
          ∑ j ∈ univ.filter (fun j => f y j = z), bornProb ψ (M i) (Q y * P j) := by
    simp only [conditionalIdeal, fibSum, Finset.mul_sum]
    rw [bornProb_sum_left]
    exact Finset.sum_congr rfl fun i _ => bornProb_sum_right ψ _ _ _
  have hdiag (y : Y) (z : Z) :
      (∑ i ∈ univ.filter (fun i => f y i = z), bornProb ψ (M i) (Q y * P i)) ≤
        bornProb ψ (fibSum M (f y) z) (conditionalIdeal P Q f (y, z)) := by
    rw [hfib]
    apply Finset.sum_le_sum
    intro i hi
    exact Finset.single_le_sum
      (fun j _ => bornProb_nonneg ψ (hM.posSemidef i) (hjoint.posSemidef (y, j))) hi
  have hsum (y : Y) :
      (∑ i, bornProb ψ (M i) (Q y * P i)) ≤
        ∑ z, bornProb ψ (fibSum M (f y) z) (conditionalIdeal P Q f (y, z)) := by
    calc
      _ = ∑ z, ∑ i ∈ univ.filter (fun i => f y i = z),
          bornProb ψ (M i) (Q y * P i) := (Finset.sum_fiberwise _ _ _).symm
      _ ≤ _ := Finset.sum_le_sum fun z _ => hdiag y z
  have hrecover : (∑ y, ∑ i, bornProb ψ (M i) (Q y * P i)) =
      ∑ i, bornProb ψ (M i) (P i) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← bornProb_sum_right, ← Finset.sum_mul, hQ.sum_eq_one, one_mul]
  rw [← hrecover, Fintype.sum_prod_type]
  exact Finset.sum_le_sum fun y _ => hsum y

/-- With the ideal prefix attached, keyed coarse-graining costs no more than
the fine cross-party squared error. -/
theorem conditional_coarse_ideal_distance (ψ : H × K → ℂ) (hψ : ‖evec ψ‖ = 1)
    (M : I → Matrix H H ℂ) (P : I → Matrix K K ℂ) (Q : Y → Matrix K K ℂ)
    (f : Y → I → Z) (hM : IsPVM M) (hP : IsPVM P) (hQ : IsPVM Q)
    (hc : ∀ y i, Commute (Q y) (P i)) :
    (∑ p : Y × Z, snorm ψ
      (fibSum M (f p.1) p.2 ⊗ₖ Q p.1 - bOp (conditionalIdeal P Q f p)) ^ 2) ≤
      ∑ i, xSqNorm ψ (M i) (P i) := by
  let C (p : Y × Z) := fibSum M (f p.1) p.2 ⊗ₖ Q p.1
  have hC0 p : (0 : Matrix (H × K) _ ℂ) ≤ C p :=
    Matrix.nonneg_iff_posSemidef.mpr
      (((isPVM_fibSum hM (f p.1)).posSemidef p.2).kronecker (hQ.posSemidef p.1))
  have hCsum : ∑ p, C p ≤ (1 : Matrix (H × K) _ ℂ) := by
    apply le_of_eq
    simp only [C, Fintype.sum_prod_type]
    simp_rw [← sum_kronecker_left, (isPVM_fibSum hM _).sum_eq_one]
    rw [← kronecker_sum_right, hQ.sum_eq_one, one_kronecker_one]
  have hprod p : bOp (conditionalIdeal P Q f p) * C p =
      fibSum M (f p.1) p.2 ⊗ₖ conditionalIdeal P Q f p := by
    simp only [bOp, C, ← mul_kronecker_mul, one_mul]
    rw [conditionalIdeal_mul_normalizer P Q f hQ hc]
  have hdist := submeasurement_agreement_dist ψ hψ
    (fun p => bOp (conditionalIdeal P Q f p)) C
    (conditionalIdeal_isPVM P Q f hP hQ hc).bOp hC0 hCsum
  have heq p : qform ψ (bOp (conditionalIdeal P Q f p) * C p) =
      bornProb ψ (fibSum M (f p.1) p.2) (conditionalIdeal P Q f p) := by
    rw [hprod, bornProb_eq_qform, aOp_mul_bOp_eq]
  simp_rw [heq] at hdist
  have hcoarse := conditional_coarse_overlap ψ M P Q f hM hP hQ hc
  have hfine := one_sub_sum_bornProb_eq hψ hM hP
  have horient : (∑ p : Y × Z, snorm ψ
      (fibSum M (f p.1) p.2 ⊗ₖ Q p.1 - bOp (conditionalIdeal P Q f p)) ^ 2) =
      ∑ p : Y × Z, snorm ψ (bOp (conditionalIdeal P Q f p) - C p) ^ 2 := by
    apply Finset.sum_congr rfl
    intro p _
    rw [snorm_sub_comm]
  rw [horient]
  linarith

/-- Summing the complete keyed Alice PVM removes it from the normalizer error. -/
theorem conditional_normalizer_change (ψ : H × K → ℂ)
    (M : I → Matrix H H ℂ) (R Q : Y → Matrix K K ℂ)
    (f : Y → I → Z) (hM : IsPVM M) :
    (∑ p : Y × Z, snorm ψ
      (fibSum M (f p.1) p.2 ⊗ₖ R p.1 - fibSum M (f p.1) p.2 ⊗ₖ Q p.1) ^ 2) ≤
      ∑ y, snorm ψ (bOp (R y - Q y)) ^ 2 := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_le_sum
  intro y _
  have hfamily := sum_aOp_conjTranspose_mul_self_of_isPVM (dB := K) (isPVM_fibSum hM (f y))
  have h := sum_snorm_sq_mul_le ψ (fun z => aOp (fibSum M (f y) z))
    (le_of_eq hfamily) (bOp (R y - Q y))
  have heq z : fibSum M (f y) z ⊗ₖ (R y - Q y) =
      fibSum M (f y) z ⊗ₖ R y - fibSum M (f y) z ⊗ₖ Q y := by
    ext i j
    simp [kroneckerMap_apply, mul_sub]
  simpa only [aOp_mul_bOp_eq, heq] using h

/-- Replace the actual conditioning marginal by the commuting ideal prefix.
There is no factor depending on the fine, coarse, or conditioning alphabet. -/
theorem conditional_coarse_ideal_replacement (ψ : H × K → ℂ) (hψ : ‖evec ψ‖ = 1)
    (M : I → Matrix H H ℂ) (P : I → Matrix K K ℂ) (Q : Y → Matrix K K ℂ)
    (B : Y × Z → Matrix K K ℂ) (f : Y → I → Z)
    (hM : IsPVM M) (hP : IsPVM P) (hQ : IsPVM Q)
    (hc : ∀ y i, Commute (Q y) (P i)) {α η ε : ℝ}
    (hfine : ∑ i, xSqNorm ψ (M i) (P i) ≤ ε)
    (hnorm : ∑ y, snorm ψ (bOp ((∑ z, B (y, z)) - Q y)) ^ 2 ≤ η)
    (hconditional : ∑ p : Y × Z, snorm ψ
      (bOp (B p) - fibSum M (f p.1) p.2 ⊗ₖ (∑ z, B (p.1, z))) ^ 2 ≤ α) :
    (∑ p : Y × Z, snorm ψ (bOp (B p) - bOp (conditionalIdeal P Q f p)) ^ 2) ≤
      3 * α + 3 * η + 3 * ε := by
  have hcoarse := conditional_coarse_ideal_distance ψ hψ M P Q f hM hP hQ hc
  have hnorm' := conditional_normalizer_change ψ M (fun y => ∑ z, B (y, z)) Q f hM
  have htri := sum_snorm_sq_triangle3 ψ (fun p => bOp (B p))
    (fun p : Y × Z => fibSum M (f p.1) p.2 ⊗ₖ (∑ z, B (p.1, z)))
    (fun p : Y × Z => fibSum M (f p.1) p.2 ⊗ₖ Q p.1)
    (fun p => bOp (conditionalIdeal P Q f p))
  linarith

end MIPRE.Introspection

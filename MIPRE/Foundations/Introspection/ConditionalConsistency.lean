/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.RetainedFibre

/-! # Conditional consistency

The paper's `lem:conditional-consistency`, with constant two in the summed
squared state norm. The conditioning index may determine Alice's entire POVM.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker

variable {N I : Type*} [Fintype N] [DecidableEq N] [Fintype I]

/-- Agreement with a positive submeasurement controls distance to a PVM. -/
theorem submeasurement_agreement_dist (ψ : N → ℂ) (hψ : ‖evec ψ‖ = 1)
    (P C : I → Matrix N N ℂ) (hP : IsPVM P)
    (hC0 : ∀ i, 0 ≤ C i) (hCsum : ∑ i, C i ≤ 1) :
    (∑ i, snorm ψ (P i - C i) ^ 2) ≤
      2 * (1 - ∑ i, qform ψ (P i * C i)) := by
  have hCsa i := (Matrix.nonneg_iff_posSemidef.mp (hC0 i)).isHermitian
  have hC1 i : C i ≤ (1 : Matrix N N ℂ) :=
    (Finset.single_le_sum (fun j _ => hC0 j) (mem_univ i)).trans hCsum
  have hexp i : snorm ψ (P i - C i) ^ 2 = qform ψ (P i) +
      qform ψ (C i * C i) - 2 * qform ψ (P i * C i) := by
    have hsym : qform ψ (C i * P i) = qform ψ (P i * C i) := by
      rw [← qform_conjTranspose ψ (P i * C i), Matrix.conjTranspose_mul,
        hP.isSelfAdjoint, hCsa]
    rw [snorm_sq_eq_qform, Matrix.conjTranspose_sub, hP.isSelfAdjoint, hCsa,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hP.idem,
      qform_sub, qform_sub, qform_sub, hsym]
    ring
  have hmass : (∑ i, qform ψ (C i * C i)) ≤ 1 := by
    calc (∑ i, qform ψ (C i * C i)) ≤ ∑ i, qform ψ (C i) :=
          Finset.sum_le_sum fun i _ => qform_le_of_le ψ
            (mul_self_le_of_le_one (hC0 i) (hC1 i))
      _ = qform ψ (∑ i, C i) := (qform_sum ψ _ _).symm
      _ ≤ qform ψ 1 := qform_le_of_le ψ hCsum
      _ = 1 := qform_one ψ hψ
  simp_rw [hexp]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← qform_sum, hP.sum_eq_one, qform_one ψ hψ]
  linarith

variable {H K X Y Z : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]

/-- A positive tensor factor preserves the Loewner order in the other factor. -/
theorem kron_le_kron_right {A B : Matrix H H ℂ} (hAB : A ≤ B)
    {R : Matrix K K ℂ} (hR : R.PosSemidef) : A ⊗ₖ R ≤ B ⊗ₖ R := by
  apply sub_nonneg.mp
  rw [← sub_kronecker_right]
  exact Matrix.nonneg_iff_posSemidef.mpr
    ((Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hAB)).kronecker hR)

/-- Conditioning Alice's measurement on Bob's first two reported indices preserves consistency. -/
theorem conditional_consistency (ψ : H × K → ℂ) (hψ : ‖evec ψ‖ = 1)
    (A : Y → POVM (X × Z) H) (B : (X × Y) × Z → Matrix K K ℂ)
    (hB : IsPVM B) {δ : ℝ}
    (hagree : 1 - δ ≤ ∑ p : (X × Y) × Z,
      bornProb ψ (((A p.1.2).mats (p.1.1, p.2)).val) (B p)) :
    (∑ p : (X × Y) × Z, snorm ψ
      (bOp (B p) - (((A p.1.2).mats (p.1.1, p.2)).val ⊗ₖ (∑ z, B (p.1, z)))) ^ 2) ≤
      2 * δ := by
  let R (i : X × Y) := ∑ z, B (i, z)
  let C (p : (X × Y) × Z) := (((A p.1.2).mats (p.1.1, p.2)).val) ⊗ₖ R p.1
  have hR : IsPVM R := hB.marg_left
  have hC0 p : (0 : Matrix (H × K) _ ℂ) ≤ C p :=
    Matrix.nonneg_iff_posSemidef.mpr
      (((A p.1.2).posSemidef (p.1.1, p.2)).kronecker (hR.posSemidef p.1))
  have hAsum (i : X × Y) : (∑ z, ((A i.2).mats (i.1, z)).val) ≤ (1 : Matrix H H ℂ) := by
    calc (∑ z, ((A i.2).mats (i.1, z)).val) ≤
        ∑ x, ∑ z, ((A i.2).mats (x, z)).val :=
          Finset.single_le_sum
            (fun x _ => Finset.sum_nonneg fun z _ =>
              Matrix.nonneg_iff_posSemidef.mpr ((A i.2).posSemidef (x, z))) (mem_univ i.1)
      _ = 1 := by rw [sum_prod_eq, POVM.sum_val]
  have hCsum : ∑ p, C p ≤ (1 : Matrix (H × K) _ ℂ) := by
    calc (∑ p, C p) = ∑ i, (∑ z, ((A i.2).mats (i.1, z)).val) ⊗ₖ R i := by
          simp only [C, Fintype.sum_prod_type, sum_kronecker_left]
      _ ≤ ∑ i, (1 : Matrix H H ℂ) ⊗ₖ R i :=
        Finset.sum_le_sum fun i _ => kron_le_kron_right (hAsum i) (hR.posSemidef i)
      _ = 1 := by rw [← kronecker_sum_right, hR.sum_eq_one, Matrix.one_kronecker_one]
  have hprod p : bOp (B p) * C p = ((A p.1.2).mats (p.1.1, p.2)).val ⊗ₖ B p := by
    dsimp only [bOp, C, R]
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, joint_mul_marginal hB]
  have h := submeasurement_agreement_dist ψ hψ (fun p => bOp (B p)) C hB.bOp hC0 hCsum
  have heq p : qform ψ (bOp (B p) * C p) =
      bornProb ψ (((A p.1.2).mats (p.1.1, p.2)).val) (B p) := by
    rw [hprod, bornProb_eq_qform]
    simp only [aOp, bOp, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  simp_rw [heq] at h
  exact h.trans (by linarith)

end MIPRE.Introspection

end

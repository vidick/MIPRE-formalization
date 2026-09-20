/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Pasting

/-! # Completing a nearby submeasurement

The paper's `lem:replace-with-measurement`, with the explicit estimate
`2 δ + 4 sqrt δ` for the squared state norm. The outcome alphabet contributes no factor.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix
open scoped ComplexOrder MatrixOrder

variable {N A : Type*} [Fintype N] [DecidableEq N] [Fintype A] [DecidableEq A]

/-- Completing a positive submeasurement dominated by a POVM costs at most its missing mass. -/
theorem submeasurement_completion_mass (ψ : N → ℂ) (hψ : ‖evec ψ‖ = 1)
    (B C : A → Matrix N N ℂ) (hB : ∀ a, 0 ≤ B a) (hC : ∀ a, 0 ≤ C a)
    (hCsum : ∑ a, C a = 1) (hBC : ∀ a, B a ≤ C a) :
    (∑ a, snorm ψ (B a - C a) ^ 2) ≤ 1 - ∑ a, qform ψ (B a) := by
  have hdiff a : 0 ≤ C a - B a := sub_nonneg.mpr (hBC a)
  have hdiff1 a : C a - B a ≤ (1 : Matrix N N ℂ) :=
    (sub_le_self _ (hB a)).trans
      ((Finset.single_le_sum (fun b _ => hC b) (mem_univ a)).trans_eq hCsum)
  have hterm a : snorm ψ (B a - C a) ^ 2 ≤ qform ψ (C a - B a) := by
    rw [snorm_sub_comm, snorm_sq_eq_qform,
      (Matrix.nonneg_iff_posSemidef.mp (hdiff a)).isHermitian]
    exact qform_le_of_le ψ (mul_self_le_of_le_one (hdiff a) (hdiff1 a))
  refine (Finset.sum_le_sum fun a _ => hterm a).trans_eq ?_
  simp_rw [qform_sub]
  rw [Finset.sum_sub_distrib, ← qform_sum, hCsum, qform_one ψ hψ]

/-- A POVM completing a nearby submeasurement stays close to the original PVM. -/
theorem submeasurement_completion_dist (ψ : N → ℂ) (hψ : ‖evec ψ‖ = 1)
    (P B C : A → Matrix N N ℂ) (hP : IsPVM P)
    (hB : ∀ a, 0 ≤ B a) (hC : ∀ a, 0 ≤ C a)
    (hCsum : ∑ a, C a = 1) (hBC : ∀ a, B a ≤ C a)
    {δ : ℝ} (hclose : ∑ a, snorm ψ (P a - B a) ^ 2 ≤ δ) :
    (∑ a, snorm ψ (P a - C a) ^ 2) ≤ 2 * δ + 4 * Real.sqrt δ := by
  have hBsum : ∑ a, B a ≤ (1 : Matrix N N ℂ) :=
    (Finset.sum_le_sum fun a _ => hBC a).trans_eq hCsum
  have hmass := qform_sum_ge_of_close hψ hP hB hBsum hclose
  have hfill := submeasurement_completion_mass ψ hψ B C hB hC hCsum hBC
  have htri := sum_snorm_sq_triangle' ψ P B C
  linarith

/-- Averaging preserves the completion estimate, by concavity of the square root. -/
theorem submeasurement_completion_dist_avg {X : Type*} [Fintype X]
    (D : X → ℝ) (hD0 : ∀ x, 0 ≤ D x) (hD1 : ∑ x, D x = 1)
    (ψ : N → ℂ) (hψ : ‖evec ψ‖ = 1)
    (P B C : X → A → Matrix N N ℂ) (hP : ∀ x, IsPVM (P x))
    (hB : ∀ x a, 0 ≤ B x a) (hC : ∀ x a, 0 ≤ C x a)
    (hCsum : ∀ x, ∑ a, C x a = 1) (hBC : ∀ x a, B x a ≤ C x a)
    {δ : ℝ} (hclose : ∑ x, D x * ∑ a, snorm ψ (P x a - B x a) ^ 2 ≤ δ) :
    (∑ x, D x * ∑ a, snorm ψ (P x a - C x a) ^ 2) ≤
      2 * δ + 4 * Real.sqrt δ := by
  let E x := ∑ a, snorm ψ (P x a - B x a) ^ 2
  have hE0 x : 0 ≤ E x := Finset.sum_nonneg fun a _ => sq_nonneg _
  have hpoint x := submeasurement_completion_dist ψ hψ (P x) (B x) (C x)
    (hP x) (hB x) (hC x) (hCsum x) (hBC x) (le_refl (E x))
  have hsum := Finset.sum_le_sum (fun x (_ : x ∈ univ) =>
    mul_le_mul_of_nonneg_left (hpoint x) (hD0 x))
  have hroot := (sum_weighted_sqrt_le D E hD0 hD1 hE0).trans (Real.sqrt_le_sqrt hclose)
  have heq : (∑ x, D x * (2 * E x + 4 * Real.sqrt (E x))) =
      2 * (∑ x, D x * E x) + 4 * ∑ x, D x * Real.sqrt (E x) := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring
  change _ ≤ ∑ x, D x * (2 * E x + 4 * Real.sqrt (E x)) at hsum
  rw [heq] at hsum
  linarith

end MIPRE.Introspection

end

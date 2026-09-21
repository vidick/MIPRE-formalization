/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.SubmeasurementCompletion
import MIPRE.Foundations.Introspection.IsometricCompletionError

/-! # Recovering all outcomes from valid-outcome extraction estimates

Pauli extraction sums only the valid full-register answers. The actual
introspection induction also retains every malformed answer. Positivity
and the submeasurement mass estimate extend the former guarantee to the
whole mapped alphabet, without an answer-cardinality factor or a premise
that malformed effects vanish.
-/

noncomputable section
namespace MIPRE.Introspection
open Finset Matrix Classical
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false

variable {N A B : Type*} [Fintype N] [DecidableEq N]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- Extending a positive submeasurement inside another submeasurement
costs at most the missing mass. Normalization of the extension is not needed. -/
theorem submeasurement_extension_mass (ψ : N → ℂ) (hψ : ‖evec ψ‖ = 1)
    (M C : A → Matrix N N ℂ) (hM : ∀ a, 0 ≤ M a) (hC : ∀ a, 0 ≤ C a)
    (hCsum : ∑ a, C a ≤ 1) (hMC : ∀ a, M a ≤ C a) :
    (∑ a, snorm ψ (M a - C a) ^ 2) ≤ 1 - ∑ a, qform ψ (M a) := by
  have hdiff a : 0 ≤ C a - M a := sub_nonneg.mpr (hMC a)
  have hdiff1 a : C a - M a ≤ (1 : Matrix N N ℂ) :=
    (sub_le_self _ (hM a)).trans
      ((single_le_sum (fun b _ => hC b) (mem_univ a)).trans hCsum)
  have hterm a : snorm ψ (M a - C a) ^ 2 ≤ qform ψ (C a - M a) := by
    rw [snorm_sub_comm, snorm_sq_eq_qform,
      (Matrix.nonneg_iff_posSemidef.mp (hdiff a)).isHermitian]
    exact qform_le_of_le ψ (mul_self_le_of_le_one (hdiff a) (hdiff1 a))
  have hs := sum_le_sum fun a (_ : a ∈ univ) => hterm a
  simp_rw [qform_sub] at hs
  rw [sum_sub_distrib] at hs
  have hc : ∑ a, qform ψ (C a) ≤ 1 := by
    rw [← qform_sum, ← qform_one ψ hψ]
    exact qform_le_of_le ψ hCsum
  linarith

/-- A nearby positive submeasurement may be extended arbitrarily inside
the identity with the same dimension-independent completion bound. -/
theorem submeasurement_extension_dist (ψ : N → ℂ) (hψ : ‖evec ψ‖ = 1)
    (P M C : A → Matrix N N ℂ) (hP : IsPVM P)
    (hM : ∀ a, 0 ≤ M a) (hC : ∀ a, 0 ≤ C a)
    (hCsum : ∑ a, C a ≤ 1) (hMC : ∀ a, M a ≤ C a)
    {δ : ℝ} (hclose : ∑ a, snorm ψ (P a - M a) ^ 2 ≤ δ) :
    (∑ a, snorm ψ (P a - C a) ^ 2) ≤ 2 * δ + 4 * Real.sqrt δ := by
  have hMsum : ∑ a, M a ≤ (1 : Matrix N N ℂ) :=
    (sum_le_sum fun a _ => hMC a).trans hCsum
  have hmass := qform_sum_ge_of_close hψ hP hM hMsum hclose
  have hfill := submeasurement_extension_mass ψ hψ M C hM hC hCsum hMC
  have htri := sum_snorm_sq_triangle' ψ P M C
  linarith

/-- Closeness on one correctly labelled raw answer for each valid outcome
controls the complete coarse measurement, including all malformed answers.
The ideal measurement has zero effect at the explicit malformed outcome. -/
theorem valid_outcome_error_le (ψ : N → ℂ) (hψ : ‖evec ψ‖ = 1)
    (M : B → Matrix N N ℂ) (hM : ∀ b, 0 ≤ M b) (hMsum : ∑ b, M b ≤ 1)
    (f : B → Option A) (v : A → B) (hv : ∀ a, f (v a) = some a)
    (P : Option A → Matrix N N ℂ) (hP : IsPVM P) (hPnone : P none = 0)
    {δ : ℝ} (hclose : ∑ a, snorm ψ (M (v a) - P (some a)) ^ 2 ≤ δ) :
    (∑ a, snorm ψ (fibSum M f a - P a) ^ 2) ≤ 2 * δ + 4 * Real.sqrt δ := by
  let Q : Option A → Matrix N N ℂ := fun a => a.elim 0 (fun a => M (v a))
  have hQ a : 0 ≤ Q a := by cases a <;> simp only [Q, Option.elim_none, Option.elim_some]; exacts [le_refl _, hM _]
  have hC a : 0 ≤ fibSum M f a := sum_nonneg fun b _ => hM b
  have hCsum : ∑ a, fibSum M f a ≤ (1 : Matrix N N ℂ) := by
    have he : (∑ a, fibSum M f a) = ∑ b, M b := by
      simp only [fibSum, sum_filter]
      rw [sum_comm]
      simp
    rw [he]
    exact hMsum
  have hQC a : Q a ≤ fibSum M f a := by
    cases a with
    | none => exact hC none
    | some a =>
      exact single_le_sum (fun b _ => hM b) (by simp [hv a])
  have hc : ∑ a, snorm ψ (P a - Q a) ^ 2 ≤ δ := by
    simpa only [Fintype.sum_option, Q, Option.elim_none, Option.elim_some,
      hPnone, sub_self, show snorm ψ 0 = 0 by simp [snorm],
      zero_pow (by decide : 2 ≠ 0), zero_add,
      snorm_sub_comm] using hclose
  have h := submeasurement_extension_dist ψ hψ P Q (fibSum M f) hP hQ hC hCsum hQC hc
  simpa only [snorm_sub_comm] using h

section Isometric
variable {H R S : Type*} [Fintype H] [DecidableEq H]
  [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]

theorem isometricImage_nonneg (V : Matrix R H ℂ) {M : Matrix H H ℂ} (hM : 0 ≤ M) :
    0 ≤ isometricImage V M :=
  ((Matrix.nonneg_iff_posSemidef.mp hM).mul_mul_conjTranspose_same V).nonneg

theorem isometricImage_one_le (V : Matrix R H ℂ) (hV : Vᴴ * V = 1) :
    isometricImage V 1 ≤ 1 := by
  apply proj_le_one
  · rw [isometricImage_conjTranspose, Matrix.conjTranspose_one]
  · rw [isometricImage_mul V hV, Matrix.one_mul]

/-- Valid raw-answer estimates for an isometric image imply the complete
mapped estimate on Alice, including the explicit malformed outcome. -/
theorem isometric_valid_outcome_alice_error_le (V : Matrix R H ℂ) (hV : Vᴴ * V = 1)
    (ψ : R × S → ℂ) (hψ : ‖evec ψ‖ = 1) (M : POVM B H)
    (f : B → Option A) (v : A → B) (hv : ∀ a, f (v a) = some a)
    (P : Option A → Matrix R R ℂ) (hP : IsPVM P) (hPnone : P none = 0)
    {δ : ℝ} (hclose : ∑ a, snorm ψ
      (aOp (isometricImage V (M.mats (v a)).val - P (some a))) ^ 2 ≤ δ) :
    (∑ a, snorm ψ (aOp (isometricImage V ((M.map f).mats a).val - P a)) ^ 2) ≤
      2 * δ + 4 * Real.sqrt δ := by
  have hm b : 0 ≤ (aOp (isometricImage V (M.mats b).val) : Matrix (R × S) _ ℂ) :=
    aOp_nonneg (isometricImage_nonneg V (Subtype.coe_le_coe.mpr (M.nonneg b)))
  have hs : ∑ b, (aOp (isometricImage V (M.mats b).val) : Matrix (R × S) _ ℂ) ≤ 1 := by
    simp only [← aOp_sum, isometricImage, ← Matrix.mul_sum, ← Matrix.sum_mul, M.sum_val]
    exact (aOp_mono (isometricImage_one_le V hV)).trans_eq aOp_one
  have h := valid_outcome_error_le ψ hψ _ hm hs f v hv (fun a => aOp (P a)) hP.aOp
    (by rw [hPnone, aOp_zero]) (by simpa only [aOp_sub] using hclose)
  have he a : fibSum (fun b => (aOp (isometricImage V (M.mats b).val) :
      Matrix (R × S) _ ℂ)) f a = aOp (isometricImage V ((M.map f).mats a).val) := by
    rw [POVM.map_mats]
    simp only [fibSum, isometricImage, Matrix.mul_sum, Matrix.sum_mul, aOp_sum]
  simpa only [he, ← aOp_sub] using h

/-- The corresponding full-outcome estimate on Bob. -/
theorem isometric_valid_outcome_bob_error_le (V : Matrix S H ℂ) (hV : Vᴴ * V = 1)
    (ψ : R × S → ℂ) (hψ : ‖evec ψ‖ = 1) (M : POVM B H)
    (f : B → Option A) (v : A → B) (hv : ∀ a, f (v a) = some a)
    (P : Option A → Matrix S S ℂ) (hP : IsPVM P) (hPnone : P none = 0)
    {δ : ℝ} (hclose : ∑ a, snorm ψ
      (bOp (isometricImage V (M.mats (v a)).val - P (some a))) ^ 2 ≤ δ) :
    (∑ a, snorm ψ (bOp (isometricImage V ((M.map f).mats a).val - P a)) ^ 2) ≤
      2 * δ + 4 * Real.sqrt δ := by
  have hm b : 0 ≤ (bOp (isometricImage V (M.mats b).val) : Matrix (R × S) _ ℂ) :=
    bOp_nonneg (isometricImage_nonneg V (Subtype.coe_le_coe.mpr (M.nonneg b)))
  have hs : ∑ b, (bOp (isometricImage V (M.mats b).val) : Matrix (R × S) _ ℂ) ≤ 1 := by
    simp only [← bOp_sum, isometricImage, ← Matrix.mul_sum, ← Matrix.sum_mul, M.sum_val]
    exact (bOp_mono (isometricImage_one_le V hV)).trans_eq bOp_one
  have h := valid_outcome_error_le ψ hψ _ hm hs f v hv (fun a => bOp (P a)) hP.bOp
    (by rw [hPnone, bOp_zero]) (by simpa only [bOp_sub] using hclose)
  have he a : fibSum (fun b => (bOp (isometricImage V (M.mats b).val) :
      Matrix (R × S) _ ℂ)) f a = bOp (isometricImage V ((M.map f).mats a).val) := by
    rw [POVM.map_mats]
    simp only [fibSum, isometricImage, Matrix.mul_sum, Matrix.sum_mul, bOp_sum]
  simpa only [he, ← bOp_sub] using h

end Isometric
end MIPRE.Introspection
end

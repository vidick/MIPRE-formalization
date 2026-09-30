/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Pasting

@[expose] public section

/-! # Completing a nearby submeasurement

The paper's `lem:replace-with-measurement`, with the explicit estimate
`2 δ + 4 sqrt δ` for the squared state norm. The outcome alphabet contributes no factor.

Stated for a state model (Phase 4 of `planning/mipco-track.md`), with the positivity of the
families on the represented operators, as in `StateModel.qform_sum_ge_of_close`: the joint
algebra of a model need not be ordered.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset

variable {𝒞 : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] (Ψ : StateModel 𝒞)
  {A : Type*} [Fintype A]

/-- Completing a positive submeasurement dominated by a POVM costs at most its missing mass. -/
theorem submeasurement_completion_mass (hΨ : ‖Ψ.ψ‖ = 1)
    (B C : A → 𝒞) (hB : ∀ a, 0 ≤ Ψ.π (B a)) (hC : ∀ a, 0 ≤ Ψ.π (C a))
    (hCsum : ∑ a, C a = 1) (hBC : ∀ a, Ψ.π (B a) ≤ Ψ.π (C a)) :
    (∑ a, Ψ.snorm (B a - C a) ^ 2) ≤ 1 - ∑ a, Ψ.qform (B a) := by
  classical
  have hdiff a : 0 ≤ Ψ.π (C a - B a) := by
    rw [map_sub]
    exact sub_nonneg.mpr (hBC a)
  have hdiff1 a : Ψ.π (C a - B a) ≤ 1 := by
    rw [map_sub]
    refine (sub_le_self _ (hB a)).trans ?_
    have h := Finset.single_le_sum (fun b (_ : b ∈ univ) => hC b) (mem_univ a)
    rwa [← map_sum, hCsum, map_one] at h
  have hterm a : Ψ.snorm (B a - C a) ^ 2 ≤ Ψ.qform (C a - B a) := by
    rw [Ψ.snorm_sub_comm]
    exact Ψ.snorm_sq_le_qform (hdiff a) (hdiff1 a)
  refine (Finset.sum_le_sum fun a _ => hterm a).trans_eq ?_
  simp_rw [Ψ.qform_sub]
  rw [Finset.sum_sub_distrib, ← Ψ.qform_sum, hCsum, Ψ.qform_one hΨ]

/-- A POVM completing a nearby submeasurement stays close to the original PVM. -/
theorem submeasurement_completion_dist (hΨ : ‖Ψ.ψ‖ = 1)
    (P B C : A → 𝒞) (hP : IsPVMIn P)
    (hB : ∀ a, 0 ≤ Ψ.π (B a)) (hC : ∀ a, 0 ≤ Ψ.π (C a))
    (hCsum : ∑ a, C a = 1) (hBC : ∀ a, Ψ.π (B a) ≤ Ψ.π (C a))
    {δ : ℝ} (hclose : ∑ a, Ψ.snorm (P a - B a) ^ 2 ≤ δ) :
    (∑ a, Ψ.snorm (P a - C a) ^ 2) ≤ 2 * δ + 4 * Real.sqrt δ := by
  have hBsum : ∑ a, Ψ.π (B a) ≤ 1 := by
    refine (Finset.sum_le_sum fun a _ => hBC a).trans_eq ?_
    rw [← map_sum, hCsum, map_one]
  have hmass := Ψ.qform_sum_ge_of_close hΨ hP hB hBsum hclose
  have hfill := submeasurement_completion_mass Ψ hΨ B C hB hC hCsum hBC
  have htri := Ψ.sum_snorm_sq_triangle univ P B C
  linarith

/-- Averaging preserves the completion estimate, by concavity of the square root. -/
theorem submeasurement_completion_dist_avg {X : Type*} [Fintype X]
    (D : X → ℝ) (hD0 : ∀ x, 0 ≤ D x) (hD1 : ∑ x, D x = 1) (hΨ : ‖Ψ.ψ‖ = 1)
    (P B C : X → A → 𝒞) (hP : ∀ x, IsPVMIn (P x))
    (hB : ∀ x a, 0 ≤ Ψ.π (B x a)) (hC : ∀ x a, 0 ≤ Ψ.π (C x a))
    (hCsum : ∀ x, ∑ a, C x a = 1) (hBC : ∀ x a, Ψ.π (B x a) ≤ Ψ.π (C x a))
    {δ : ℝ} (hclose : ∑ x, D x * ∑ a, Ψ.snorm (P x a - B x a) ^ 2 ≤ δ) :
    (∑ x, D x * ∑ a, Ψ.snorm (P x a - C x a) ^ 2) ≤
      2 * δ + 4 * Real.sqrt δ := by
  let E x := ∑ a, Ψ.snorm (P x a - B x a) ^ 2
  have hE0 x : 0 ≤ E x := Finset.sum_nonneg fun a _ => sq_nonneg _
  have hpoint x := submeasurement_completion_dist Ψ hΨ (P x) (B x) (C x)
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

end

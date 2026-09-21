/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Pasting
import MIPRE.Foundations.Swap

/-! # Value stability for the introspection induction

The induction replaces projective measurements using summed squared state
distance. The resulting change in test acceptance is dimension independent:
`2 sqrt(delta)` per party. Summing outcomes before Cauchy--Schwarz avoids any
loss depending on the size of the introspection answer alphabet.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder

variable {N C : Type*} [Fintype N] [DecidableEq N] [Fintype C] [DecidableEq C]

set_option linter.unusedSectionVars false

/-- A subset of the outcomes of a projective measurement has squared mass at most one. -/
theorem pvm_subset_mass (v : N → ℂ) (hv : ‖evec v‖ = 1)
    {M : C → Matrix N N ℂ} (hM : IsPVM M) (s : Finset C) :
    ∑ c ∈ s, snorm v (M c) ^ 2 ≤ 1 := by
  have hall : ∑ c, snorm v (M c) ^ 2 = 1 := by
    simp_rw [snorm_sq_eq_qform, hM.isSelfAdjoint, hM.idem]
    rw [← qform_sum, hM.sum_eq_one, qform_one v hv]
  rw [← hall]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => sq_nonneg _)

/-- Cauchy--Schwarz for a selected set of outcome-indexed operator products. -/
theorem abs_sum_qform_mul_le (v : N → ℂ) (s : Finset C)
    (M R : C → Matrix N N ℂ) (hM : ∀ c, (M c)ᴴ = M c) :
    |∑ c ∈ s, qform v (M c * R c)| ≤
      Real.sqrt (∑ c ∈ s, snorm v (M c) ^ 2) *
        Real.sqrt (∑ c ∈ s, snorm v (R c) ^ 2) := by
  have hsq := sum_mul_sq_le_sq_mul_sq s (fun c => snorm v (M c)) (fun c => snorm v (R c))
  have hn : 0 ≤ ∑ c ∈ s, snorm v (M c) ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hcs : (∑ c ∈ s, snorm v (M c) * snorm v (R c)) ≤
      Real.sqrt (∑ c ∈ s, snorm v (M c) ^ 2) *
        Real.sqrt (∑ c ∈ s, snorm v (R c) ^ 2) := by
    calc
      _ ≤ |∑ c ∈ s, snorm v (M c) * snorm v (R c)| := le_abs_self _
      _ = Real.sqrt ((∑ c ∈ s, snorm v (M c) * snorm v (R c)) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((∑ c ∈ s, snorm v (M c) ^ 2) * ∑ c ∈ s, snorm v (R c) ^ 2) :=
        Real.sqrt_le_sqrt hsq
      _ = _ := Real.sqrt_mul hn _
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun c _ => ?_).trans hcs)
  simpa only [hM c] using abs_qform_conjTranspose_mul_le v (M c) (R c)

/-- Changing a projective measurement by squared distance `delta` changes the
probability of any event by at most `2 sqrt(delta)`, with no outcome-count factor. -/
theorem pvm_event_stability (v : N → ℂ) (hv : ‖evec v‖ = 1)
    {M R : C → Matrix N N ℂ} (hM : IsPVM M) (hR : IsPVM R)
    (s : Finset C) {δ : ℝ} (hd : ∑ c, snorm v (M c - R c) ^ 2 ≤ δ) :
    |(∑ c ∈ s, qform v (M c)) - ∑ c ∈ s, qform v (R c)| ≤ 2 * Real.sqrt δ := by
  have hδ : 0 ≤ δ := (sum_nonneg fun _ _ => sq_nonneg _).trans hd
  have hds : ∑ c ∈ s, snorm v (M c - R c) ^ 2 ≤ δ :=
    (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => sq_nonneg _)).trans hd
  have h1 : |∑ c ∈ s, qform v (M c * (M c - R c))| ≤ Real.sqrt δ := by
    refine (abs_sum_qform_mul_le v s M (fun c => M c - R c) hM.isSelfAdjoint).trans ?_
    calc
      _ ≤ Real.sqrt 1 * Real.sqrt δ := mul_le_mul
        (Real.sqrt_le_sqrt (pvm_subset_mass v hv hM s)) (Real.sqrt_le_sqrt hds)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := by rw [Real.sqrt_one, one_mul]
  have h2 : |∑ c ∈ s, qform v ((M c - R c) * R c)| ≤ Real.sqrt δ := by
    refine (abs_sum_qform_mul_le v s (fun c => M c - R c) R
      (fun c => by rw [conjTranspose_sub, hM.isSelfAdjoint, hR.isSelfAdjoint])).trans ?_
    calc
      _ ≤ Real.sqrt δ * Real.sqrt 1 := mul_le_mul (Real.sqrt_le_sqrt hds)
        (Real.sqrt_le_sqrt (pvm_subset_mass v hv hR s))
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := by rw [Real.sqrt_one, mul_one]
  have heq : (∑ c ∈ s, qform v (M c)) - ∑ c ∈ s, qform v (R c) =
      (∑ c ∈ s, qform v (M c * (M c - R c))) +
        ∑ c ∈ s, qform v ((M c - R c) * R c) := by
    rw [← sum_sub_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro c _
    rw [← qform_sub, ← qform_add]
    congr 1
    rw [mul_sub, sub_mul, hM.idem, hR.idem]
    abel
  rw [heq]
  exact (abs_add_le _ _).trans (by linarith)

section Bipartite

variable {A B H K : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

/-- Independent local projective measurements give a projective measurement of both answers. -/
theorem joint_isPVM (M : A → Matrix H H ℂ) (Q : B → Matrix K K ℂ)
    (hM : IsPVM M) (hQ : IsPVM Q) : IsPVM (fun ab : A × B => M ab.1 ⊗ₖ Q ab.2) where
  isSelfAdjoint ab := by rw [conjTranspose_kronecker, hM.isSelfAdjoint, hQ.isSelfAdjoint]
  idem ab := by rw [← mul_kronecker_mul, hM.idem, hQ.idem]
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [← kronecker_sum_right, hQ.sum_eq_one]
    rw [← sum_kronecker_left, hM.sum_eq_one, one_kronecker_one]

/-- Summing the unchanged party's projective outcomes removes that party from the error. -/
theorem joint_distance_left (ψ : H × K → ℂ)
    (M R : A → Matrix H H ℂ) (Q : B → Matrix K K ℂ) (hQ : IsPVM Q) :
    (∑ ab : A × B, snorm ψ (M ab.1 ⊗ₖ Q ab.2 - R ab.1 ⊗ₖ Q ab.2) ^ 2) =
      ∑ a, stateSqNorm ψ (M a - R a) := by
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro a _
  have heq (b : B) : M a ⊗ₖ Q b - R a ⊗ₖ Q b = (M a - R a) ⊗ₖ Q b := by
    ext i j
    simp [kroneckerMap_apply, sub_mul]
  simp_rw [heq, snorm_sq_eq_qform, conjTranspose_kronecker,
    ← mul_kronecker_mul, hQ.isSelfAdjoint, hQ.idem]
  rw [← qform_sum, ← kronecker_sum_right, hQ.sum_eq_one, stateSqNorm_eq]
  rfl

/-- The acceptance functional of one test on bare local measurement families. -/
def testAcceptance (ψ : H × K → ℂ) (D : A → B → Bool)
    (M : A → Matrix H H ℂ) (Q : B → Matrix K K ℂ) : ℝ :=
  ∑ a, ∑ b, (if D a b then 1 else 0) * bornProb ψ (M a) (Q b)

/-- One player's projective replacement changes any test by at most `2 sqrt(delta)`. -/
theorem testAcceptance_stability_left (ψ : H × K → ℂ) (hψ : ‖evec ψ‖ = 1)
    (D : A → B → Bool) (M R : A → Matrix H H ℂ) (Q : B → Matrix K K ℂ)
    (hM : IsPVM M) (hR : IsPVM R) (hQ : IsPVM Q)
    {δ : ℝ} (hd : ∑ a, stateSqNorm ψ (M a - R a) ≤ δ) :
    |testAcceptance ψ D M Q - testAcceptance ψ D R Q| ≤ 2 * Real.sqrt δ := by
  have h := pvm_event_stability ψ hψ (joint_isPVM M Q hM hQ)
    (joint_isPVM R Q hR hQ) (univ.filter fun ab : A × B => D ab.1 ab.2)
    (δ := δ) (by rw [joint_distance_left ψ M R Q hQ]; exact hd)
  simpa only [sum_filter, Fintype.sum_prod_type, testAcceptance, qform, bornProb,
    ite_mul, one_mul, zero_mul] using h

/-- Swapping the two parties preserves test acceptance with the predicate arguments swapped. -/
theorem testAcceptance_swap (ψ : H × K → ℂ) (D : A → B → Bool)
    (M : A → Matrix H H ℂ) (Q : B → Matrix K K ℂ) :
    testAcceptance (swapVec ψ) (fun b a => D a b) Q M = testAcceptance ψ D M Q := by
  simp only [testAcceptance, bornProb_swapVec]
  exact sum_comm

/-- The corresponding replacement estimate on Bob's side, with its actual state norm. -/
theorem testAcceptance_stability_right (ψ : H × K → ℂ) (hψ : ‖evec ψ‖ = 1)
    (D : A → B → Bool) (M : A → Matrix H H ℂ) (Q R : B → Matrix K K ℂ)
    (hM : IsPVM M) (hQ : IsPVM Q) (hR : IsPVM R)
    {δ : ℝ} (hd : ∑ b, ‖stateVecB ψ (Q b - R b)‖ ^ 2 ≤ δ) :
    |testAcceptance ψ D M Q - testAcceptance ψ D M R| ≤ 2 * Real.sqrt δ := by
  have hd' : ∑ b, stateSqNorm (swapVec ψ) (Q b - R b) ≤ δ := by
    simpa only [norm_stateVecB, stateSqNorm] using hd
  have h := testAcceptance_stability_left (swapVec ψ) (by rwa [norm_swapVec])
    (fun b a => D a b) Q R M hQ hR hM hd'
  simpa only [testAcceptance_swap] using h

/-- Replacing both local PVMs costs the sum of their square-root errors. -/
theorem testAcceptance_stability (ψ : H × K → ℂ) (hψ : ‖evec ψ‖ = 1)
    (D : A → B → Bool) (M R : A → Matrix H H ℂ) (Q T : B → Matrix K K ℂ)
    (hM : IsPVM M) (hR : IsPVM R) (hQ : IsPVM Q) (hT : IsPVM T)
    {δA δB : ℝ} (hA : ∑ a, stateSqNorm ψ (M a - R a) ≤ δA)
    (hB : ∑ b, ‖stateVecB ψ (Q b - T b)‖ ^ 2 ≤ δB) :
    |testAcceptance ψ D M Q - testAcceptance ψ D R T| ≤
      2 * Real.sqrt δA + 2 * Real.sqrt δB := by
  have hleft := testAcceptance_stability_left ψ hψ D M R Q hM hR hQ hA
  have hright := testAcceptance_stability_right ψ hψ D R Q T hR hQ hT hB
  calc
    _ ≤ |testAcceptance ψ D M Q - testAcceptance ψ D R Q| +
        |testAcceptance ψ D R Q - testAcceptance ψ D R T| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add hleft hright

end Bipartite

end MIPRE.Introspection

end

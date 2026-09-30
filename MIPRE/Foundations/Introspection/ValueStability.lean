/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Pasting
public import MIPRE.Foundations.Swap

@[expose] public section

/-! # Value stability for the introspection induction

The induction replaces projective measurements using summed squared state
distance. The resulting change in test acceptance is dimension independent:
`2 sqrt(delta)` per party. Summing outcomes before Cauchy--Schwarz avoids any
loss depending on the size of the introspection answer alphabet.

Everything is stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the
single-state facts for a state model `Ψ`, the facts about tests for a bipartite model `Ψ`, the
model playing the part of the state vector of the matrix analysis.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset

set_option linter.unusedSectionVars false

section State

variable {𝒞 : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] (Ψ : StateModel 𝒞)
  {C : Type*} [Fintype C]

/-- A subset of the outcomes of a projective measurement has squared mass at most one. -/
theorem pvm_subset_mass (hv : ‖Ψ.ψ‖ = 1) {M : C → 𝒞} (hM : IsPVMIn M) (s : Finset C) :
    ∑ c ∈ s, Ψ.snorm (M c) ^ 2 ≤ 1 := by
  have hall : ∑ c, Ψ.snorm (M c) ^ 2 = 1 := by
    simp_rw [Ψ.snorm_sq_eq_qform, hM.star_eq, hM.idem]
    rw [← Ψ.qform_sum, hM.sum_eq_one, Ψ.qform_one hv]
  rw [← hall]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => sq_nonneg _)

/-- Cauchy--Schwarz for a selected set of outcome-indexed operator products. -/
theorem abs_sum_qform_mul_le (s : Finset C) (M R : C → 𝒞) (hM : ∀ c, star (M c) = M c) :
    |∑ c ∈ s, Ψ.qform (M c * R c)| ≤
      Real.sqrt (∑ c ∈ s, Ψ.snorm (M c) ^ 2) *
        Real.sqrt (∑ c ∈ s, Ψ.snorm (R c) ^ 2) := by
  have hsq := sum_mul_sq_le_sq_mul_sq s (fun c => Ψ.snorm (M c)) (fun c => Ψ.snorm (R c))
  have hn : 0 ≤ ∑ c ∈ s, Ψ.snorm (M c) ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hcs : (∑ c ∈ s, Ψ.snorm (M c) * Ψ.snorm (R c)) ≤
      Real.sqrt (∑ c ∈ s, Ψ.snorm (M c) ^ 2) *
        Real.sqrt (∑ c ∈ s, Ψ.snorm (R c) ^ 2) := by
    calc
      _ ≤ |∑ c ∈ s, Ψ.snorm (M c) * Ψ.snorm (R c)| := le_abs_self _
      _ = Real.sqrt ((∑ c ∈ s, Ψ.snorm (M c) * Ψ.snorm (R c)) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((∑ c ∈ s, Ψ.snorm (M c) ^ 2) * ∑ c ∈ s, Ψ.snorm (R c) ^ 2) :=
        Real.sqrt_le_sqrt hsq
      _ = _ := Real.sqrt_mul hn _
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun c _ => ?_).trans hcs)
  simpa only [hM c] using Ψ.abs_qform_star_mul_le (M c) (R c)

/-- Changing a projective measurement by squared distance `delta` changes the
probability of any event by at most `2 sqrt(delta)`, with no outcome-count factor. -/
theorem pvm_event_stability (hv : ‖Ψ.ψ‖ = 1) {M R : C → 𝒞} (hM : IsPVMIn M) (hR : IsPVMIn R)
    (s : Finset C) {δ : ℝ} (hd : ∑ c, Ψ.snorm (M c - R c) ^ 2 ≤ δ) :
    |(∑ c ∈ s, Ψ.qform (M c)) - ∑ c ∈ s, Ψ.qform (R c)| ≤ 2 * Real.sqrt δ := by
  have hδ : 0 ≤ δ := (sum_nonneg fun _ _ => sq_nonneg _).trans hd
  have hds : ∑ c ∈ s, Ψ.snorm (M c - R c) ^ 2 ≤ δ :=
    (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => sq_nonneg _)).trans hd
  have h1 : |∑ c ∈ s, Ψ.qform (M c * (M c - R c))| ≤ Real.sqrt δ := by
    refine (abs_sum_qform_mul_le Ψ s M (fun c => M c - R c) hM.star_eq).trans ?_
    calc
      _ ≤ Real.sqrt 1 * Real.sqrt δ := mul_le_mul
        (Real.sqrt_le_sqrt (pvm_subset_mass Ψ hv hM s)) (Real.sqrt_le_sqrt hds)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := by rw [Real.sqrt_one, one_mul]
  have h2 : |∑ c ∈ s, Ψ.qform ((M c - R c) * R c)| ≤ Real.sqrt δ := by
    refine (abs_sum_qform_mul_le Ψ s (fun c => M c - R c) R
      (fun c => by rw [star_sub, hM.star_eq, hR.star_eq])).trans ?_
    calc
      _ ≤ Real.sqrt δ * Real.sqrt 1 := mul_le_mul (Real.sqrt_le_sqrt hds)
        (Real.sqrt_le_sqrt (pvm_subset_mass Ψ hv hR s))
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := by rw [Real.sqrt_one, mul_one]
  have heq : (∑ c ∈ s, Ψ.qform (M c)) - ∑ c ∈ s, Ψ.qform (R c) =
      (∑ c ∈ s, Ψ.qform (M c * (M c - R c))) +
        ∑ c ∈ s, Ψ.qform ((M c - R c) * R c) := by
    rw [← sum_sub_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro c _
    rw [← Ψ.qform_sub, ← Ψ.qform_add]
    congr 1
    rw [mul_sub, sub_mul, hM.idem, hR.idem]
    abel
  rw [heq]
  exact (abs_add_le _ _).trans (by linarith)

end State

section Bipartite

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] (Ψ : BipartiteModel 𝒞 𝒜 ℬ)
  {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- Independent local projective measurements give a projective measurement of both answers. -/
theorem joint_isPVM (M : A → 𝒜) (Q : B → ℬ) (hM : IsPVMIn M) (hQ : IsPVMIn Q) :
    IsPVMIn (fun ab : A × B => Ψ.πA (M ab.1) * Ψ.πB (Q ab.2)) where
  star_eq ab := by rw [Ψ.star_πA_mul_πB, hM.star_eq, hQ.star_eq]
  idem ab := by rw [Ψ.πA_mul_πB_mul, hM.idem, hQ.idem]
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, ← map_sum, hQ.sum_eq_one, map_one, mul_one, ← map_sum,
      hM.sum_eq_one, map_one]
  orthogonal {ab ab'} h := by
    rw [Ψ.πA_mul_πB_mul]
    by_cases ha : ab.1 = ab'.1
    · have hb : ab.2 ≠ ab'.2 := fun hb => h (Prod.ext ha hb)
      rw [hQ.orthogonal hb, map_zero, mul_zero]
    · rw [hM.orthogonal ha, map_zero, zero_mul]

/-- Summing the unchanged party's projective outcomes removes that party from the error. -/
theorem joint_distance_left (M R : A → 𝒜) (Q : B → ℬ) (hQ : IsPVMIn Q) :
    (∑ ab : A × B, Ψ.snorm (Ψ.πA (M ab.1) * Ψ.πB (Q ab.2) - Ψ.πA (R ab.1) * Ψ.πB (Q ab.2)) ^ 2) =
      ∑ a, Ψ.stateSqNorm (M a - R a) := by
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro a _
  have heq (b : B) : Ψ.πA (M a) * Ψ.πB (Q b) - Ψ.πA (R a) * Ψ.πB (Q b) =
      Ψ.πA (M a - R a) * Ψ.πB (Q b) := by
    rw [map_sub, sub_mul]
  simp_rw [heq, Ψ.snorm_sq_eq_qform, Ψ.star_πA_mul_πB, Ψ.πA_mul_πB_mul, hQ.star_eq, hQ.idem]
  rw [← Ψ.qform_sum, ← Finset.mul_sum, ← map_sum, hQ.sum_eq_one, map_one, mul_one,
    Ψ.stateSqNorm_eq]

/-- The acceptance functional of one test on bare local measurement families. -/
def testAcceptance (D : A → B → Bool) (M : A → 𝒜) (Q : B → ℬ) : ℝ :=
  ∑ a, ∑ b, (if D a b then 1 else 0) * Ψ.bornProb (M a) (Q b)

/-- One player's projective replacement changes any test by at most `2 sqrt(delta)`. -/
theorem testAcceptance_stability_left (hΨ : ‖Ψ.ψ‖ = 1) (D : A → B → Bool) (M R : A → 𝒜)
    (Q : B → ℬ) (hM : IsPVMIn M) (hR : IsPVMIn R) (hQ : IsPVMIn Q)
    {δ : ℝ} (hd : ∑ a, Ψ.stateSqNorm (M a - R a) ≤ δ) :
    |testAcceptance Ψ D M Q - testAcceptance Ψ D R Q| ≤ 2 * Real.sqrt δ := by
  have h := pvm_event_stability Ψ.toStateModel hΨ (joint_isPVM Ψ M Q hM hQ)
    (joint_isPVM Ψ R Q hR hQ) (univ.filter fun ab : A × B => D ab.1 ab.2)
    (δ := δ) (by rw [joint_distance_left Ψ M R Q hQ]; exact hd)
  simpa only [sum_filter, Fintype.sum_prod_type, testAcceptance, BipartiteModel.bornProb,
    ite_mul, one_mul, zero_mul] using h

/-- Swapping the two parties preserves test acceptance with the predicate arguments swapped. -/
theorem testAcceptance_swap (D : A → B → Bool) (M : A → 𝒜) (Q : B → ℬ) :
    testAcceptance Ψ.swap (fun b a => D a b) Q M = testAcceptance Ψ D M Q := by
  simp only [testAcceptance, BipartiteModel.bornProb_swap]
  exact sum_comm

/-- The corresponding replacement estimate on Bob's side, with its actual state norm. -/
theorem testAcceptance_stability_right (hΨ : ‖Ψ.ψ‖ = 1) (D : A → B → Bool) (M : A → 𝒜)
    (Q R : B → ℬ) (hM : IsPVMIn M) (hQ : IsPVMIn Q) (hR : IsPVMIn R)
    {δ : ℝ} (hd : ∑ b, Ψ.swap.stateSqNorm (Q b - R b) ≤ δ) :
    |testAcceptance Ψ D M Q - testAcceptance Ψ D M R| ≤ 2 * Real.sqrt δ := by
  have h := testAcceptance_stability_left Ψ.swap hΨ (fun b a => D a b) Q R M hQ hR hM hd
  simpa only [testAcceptance_swap] using h

/-- Replacing both local PVMs costs the sum of their square-root errors. -/
theorem testAcceptance_stability (hΨ : ‖Ψ.ψ‖ = 1) (D : A → B → Bool) (M R : A → 𝒜)
    (Q T : B → ℬ) (hM : IsPVMIn M) (hR : IsPVMIn R) (hQ : IsPVMIn Q) (hT : IsPVMIn T)
    {δA δB : ℝ} (hA : ∑ a, Ψ.stateSqNorm (M a - R a) ≤ δA)
    (hB : ∑ b, Ψ.swap.stateSqNorm (Q b - T b) ≤ δB) :
    |testAcceptance Ψ D M Q - testAcceptance Ψ D R T| ≤
      2 * Real.sqrt δA + 2 * Real.sqrt δB := by
  have hleft := testAcceptance_stability_left Ψ hΨ D M R Q hM hR hQ hA
  have hright := testAcceptance_stability_right Ψ hΨ D R Q T hR hQ hT hB
  calc
    _ ≤ |testAcceptance Ψ D M Q - testAcceptance Ψ D R Q| +
        |testAcceptance Ψ D R Q - testAcceptance Ψ D R T| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add hleft hright

end Bipartite

end MIPRE.Introspection

end

end

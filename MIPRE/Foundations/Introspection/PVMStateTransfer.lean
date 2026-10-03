/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.StateStability

@[expose] public section

/-! # Transferring projective measurement errors between nearby states

The summed squared distance of two PVMs on a new state is at most twice its
old value plus eight times the squared vector distance. PVM normalization
removes any dependence on the number of outcomes. The state vectors need not
be normalized. Alice and Bob forms expose the estimate in the conventions
used by the extracted Pauli guarantees.

Stated in a model (Phase 4 of `planning/mipco-track.md`): the old state is the model's own, the new
state `φ` is any vector of its Hilbert space, and the model at the new state is `Ψ.withState φ`.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset

section State

variable {𝒞 : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] (Ψ : StateModel 𝒞)
  {C : Type*} [Fintype C]

/-- The identity's state norm is the norm of the state. -/
theorem snorm_one_eq_norm : Ψ.snorm 1 = ‖Ψ.ψ‖ := by
  unfold StateModel.snorm
  rw [map_one]
  rfl

/-- The total squared PVM mass on any vector is its squared norm. -/
theorem sum_pvm_snorm_sq {M : C → 𝒞} (hM : IsPVMIn M) :
    ∑ c, Ψ.snorm (M c) ^ 2 = ‖Ψ.ψ‖ ^ 2 := by
  have h1 : Ψ.qform 1 = ‖Ψ.ψ‖ ^ 2 := by
    rw [← snorm_one_eq_norm, Ψ.snorm_sq_eq_qform, star_one, one_mul]
  simp_rw [Ψ.snorm_sq_eq_qform, hM.star_eq, hM.idem]
  rw [← Ψ.qform_sum, hM.sum_eq_one, h1]

/-- Two PVMs have summed squared difference at most four times the state's
squared norm, without an outcome-count factor. -/
theorem sum_pvm_difference_snorm_sq_le {M R : C → 𝒞} (hM : IsPVMIn M) (hR : IsPVMIn R) :
    ∑ c, Ψ.snorm (M c - R c) ^ 2 ≤ 4 * ‖Ψ.ψ‖ ^ 2 := by
  calc
    _ ≤ ∑ c, (2 * Ψ.snorm (M c) ^ 2 + 2 * Ψ.snorm (R c) ^ 2) := by
      refine sum_le_sum fun c _ => ?_
      have ht := Ψ.snorm_sub_le (M c) (R c)
      have hn := Ψ.snorm_nonneg (M c - R c)
      nlinarith [sq_nonneg (Ψ.snorm (M c) - Ψ.snorm (R c))]
    _ = _ := by
      rw [sum_add_distrib, ← mul_sum, ← mul_sum,
        sum_pvm_snorm_sq Ψ hM, sum_pvm_snorm_sq Ψ hR]
      ring

/-- A single operator's squared state norm splits with coefficient two when
the state vector changes. -/
theorem snorm_state_sq_le (φ : Ψ.H) (R : 𝒞) :
    (Ψ.withState φ).snorm R ^ 2 ≤
      2 * Ψ.snorm R ^ 2 + 2 * (Ψ.withState (Ψ.ψ - φ)).snorm R ^ 2 := by
  have hs : Ψ.π R φ = Ψ.π R Ψ.ψ - Ψ.π R (Ψ.ψ - φ) := by
    rw [map_sub]
    abel
  have ht : (Ψ.withState φ).snorm R ≤ Ψ.snorm R + (Ψ.withState (Ψ.ψ - φ)).snorm R := by
    rw [StateModel.withState_snorm, StateModel.withState_snorm, hs]
    exact norm_sub_le _ _
  have hn := (Ψ.withState φ).snorm_nonneg R
  nlinarith [sq_nonneg (Ψ.snorm R - (Ψ.withState (Ψ.ψ - φ)).snorm R)]

/-- Transfer the summed squared difference of two projective measurements
to a nearby state. No unit-state assumptions are needed. -/
theorem sum_snorm_state_transfer (φ : Ψ.H) {M R : C → 𝒞} (hM : IsPVMIn M) (hR : IsPVMIn R) :
    ∑ c, (Ψ.withState φ).snorm (M c - R c) ^ 2 ≤
      2 * ∑ c, Ψ.snorm (M c - R c) ^ 2 + 8 * ‖Ψ.ψ - φ‖ ^ 2 := by
  have ht := sum_le_sum (s := (univ : Finset C))
    (fun c _ => snorm_state_sq_le Ψ φ (M c - R c))
  rw [sum_add_distrib, ← mul_sum, ← mul_sum] at ht
  have hd : ∑ c, (Ψ.withState (Ψ.ψ - φ)).snorm (M c - R c) ^ 2 ≤ 4 * ‖Ψ.ψ - φ‖ ^ 2 :=
    sum_pvm_difference_snorm_sq_le (Ψ.withState (Ψ.ψ - φ)) hM hR
  calc _ ≤ _ := ht
    _ ≤ 2 * ∑ c, Ψ.snorm (M c - R c) ^ 2 + 2 * (4 * ‖Ψ.ψ - φ‖ ^ 2) := by gcongr
    _ = _ := by ring

end State

section Bipartite

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] (Ψ : BipartiteModel 𝒞 𝒜 ℬ)
  {C : Type*} [Fintype C]

/-- Alice's local PVM error transfers between arbitrary vectors. -/
theorem sum_stateSqNorm_state_transfer (φ : Ψ.H) {M R : C → 𝒜} (hM : IsPVMIn M)
    (hR : IsPVMIn R) :
    ∑ c, (Ψ.withState φ).stateSqNorm (M c - R c) ≤
      2 * ∑ c, Ψ.stateSqNorm (M c - R c) + 8 * ‖Ψ.ψ - φ‖ ^ 2 := by
  have h := sum_snorm_state_transfer Ψ.toStateModel φ (hM.map Ψ.πA) (hR.map Ψ.πA)
  simp only [← map_sub] at h
  exact h

/-- Transfer a bounded Alice PVM approximation to the extracted state. -/
theorem sum_stateSqNorm_state_transfer_le (φ : Ψ.H) {M R : C → 𝒜} (hM : IsPVMIn M)
    (hR : IsPVMIn R) {δ η : ℝ} (hδ : ∑ c, Ψ.stateSqNorm (M c - R c) ≤ δ)
    (hdist : ‖Ψ.ψ - φ‖ ^ 2 ≤ η) :
    ∑ c, (Ψ.withState φ).stateSqNorm (M c - R c) ≤ 2 * δ + 8 * η := by
  have ht := sum_stateSqNorm_state_transfer Ψ φ hM hR
  linarith

/-- Bob's local PVM error transfers with the same constants. -/
theorem sum_bob_snorm_state_transfer (φ : Ψ.H) {M R : C → ℬ} (hM : IsPVMIn M)
    (hR : IsPVMIn R) :
    ∑ c, (Ψ.withState φ).snorm (Ψ.πB (M c - R c)) ^ 2 ≤
      2 * ∑ c, Ψ.snorm (Ψ.πB (M c - R c)) ^ 2 + 8 * ‖Ψ.ψ - φ‖ ^ 2 := by
  have h := sum_snorm_state_transfer Ψ.toStateModel φ (hM.map Ψ.πB) (hR.map Ψ.πB)
  simp only [← map_sub] at h
  exact h

/-- Transfer a bounded Bob PVM approximation to the extracted state. -/
theorem sum_bob_snorm_state_transfer_le (φ : Ψ.H) {M R : C → ℬ} (hM : IsPVMIn M)
    (hR : IsPVMIn R) {δ η : ℝ} (hδ : ∑ c, Ψ.snorm (Ψ.πB (M c - R c)) ^ 2 ≤ δ)
    (hdist : ‖Ψ.ψ - φ‖ ^ 2 ≤ η) :
    ∑ c, (Ψ.withState φ).snorm (Ψ.πB (M c - R c)) ^ 2 ≤ 2 * δ + 8 * η := by
  have ht := sum_bob_snorm_state_transfer Ψ φ hM hR
  linarith

end Bipartite
end MIPRE.Introspection

end

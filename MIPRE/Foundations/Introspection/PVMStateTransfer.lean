/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.StateStability

/-! # Transferring projective measurement errors between nearby states

The summed squared distance of two PVMs on a new state is at most twice its
old value plus eight times the squared vector distance. PVM normalization
removes any dependence on the number of outcomes. The state vectors need not
be normalized. Alice and Bob forms expose the estimate in the conventions
used by the extracted Pauli guarantees.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder

variable {N C : Type*} [Fintype N] [DecidableEq N] [Fintype C]

/-- The total squared PVM mass on any vector is its squared norm. -/
theorem sum_pvm_snorm_sq (v : N → ℂ) {M : C → Matrix N N ℂ} (hM : IsPVM M) :
    ∑ c, snorm v (M c) ^ 2 = ‖evec v‖ ^ 2 := by
  simp_rw [snorm_sq_eq_qform, hM.isSelfAdjoint, hM.idem]
  rw [← qform_sum, hM.sum_eq_one, qform, Matrix.one_mulVec, norm_evec_sq]

/-- Two PVMs have summed squared difference at most four times the state's
squared norm, without an outcome-count factor. -/
theorem sum_pvm_difference_snorm_sq_le (v : N → ℂ)
    {M R : C → Matrix N N ℂ} (hM : IsPVM M) (hR : IsPVM R) :
    ∑ c, snorm v (M c - R c) ^ 2 ≤ 4 * ‖evec v‖ ^ 2 := by
  calc
    _ ≤ ∑ c, (2 * snorm v (M c) ^ 2 + 2 * snorm v (R c) ^ 2) := by
      refine sum_le_sum fun c _ => ?_
      have ht := snorm_sub_le v (M c) (R c)
      have hn := snorm_nonneg v (M c - R c)
      nlinarith [sq_nonneg (snorm v (M c) - snorm v (R c))]
    _ = _ := by
      rw [sum_add_distrib, ← mul_sum, ← mul_sum,
        sum_pvm_snorm_sq v hM, sum_pvm_snorm_sq v hR]
      ring

omit [DecidableEq N] in
/-- A single operator's squared state norm splits with coefficient two when
the state vector changes. -/
theorem snorm_state_sq_le (ψ φ : N → ℂ) (R : Matrix N N ℂ) :
    snorm φ R ^ 2 ≤ 2 * snorm ψ R ^ 2 + 2 * snorm (ψ - φ) R ^ 2 := by
  have hs : R *ᵥ φ = R *ᵥ ψ - R *ᵥ (ψ - φ) := by
    rw [Matrix.mulVec_sub]
    abel
  have ht : snorm φ R ≤ snorm ψ R + snorm (ψ - φ) R := by
    rw [snorm, hs, evec_sub]
    exact norm_sub_le _ _
  have hn := snorm_nonneg φ R
  nlinarith [sq_nonneg (snorm ψ R - snorm (ψ - φ) R)]

/-- Transfer the summed squared difference of two projective measurements
to a nearby state. No unit-state assumptions are needed. -/
theorem sum_snorm_state_transfer (ψ φ : N → ℂ)
    {M R : C → Matrix N N ℂ} (hM : IsPVM M) (hR : IsPVM R) :
    ∑ c, snorm φ (M c - R c) ^ 2 ≤
      2 * ∑ c, snorm ψ (M c - R c) ^ 2 + 8 * ‖evec (ψ - φ)‖ ^ 2 := by
  have ht := sum_le_sum (s := (univ : Finset C))
    (fun c _ => snorm_state_sq_le ψ φ (M c - R c))
  rw [sum_add_distrib, ← mul_sum, ← mul_sum] at ht
  have hd := sum_pvm_difference_snorm_sq_le (ψ - φ) hM hR
  linarith

/-- A hypothesis form of state transfer for joint-space PVM errors. -/
theorem sum_snorm_state_transfer_le (ψ φ : N → ℂ)
    {M R : C → Matrix N N ℂ} (hM : IsPVM M) (hR : IsPVM R)
    {δ η : ℝ} (hδ : ∑ c, snorm ψ (M c - R c) ^ 2 ≤ δ)
    (hdist : ‖evec (ψ - φ)‖ ^ 2 ≤ η) :
    ∑ c, snorm φ (M c - R c) ^ 2 ≤ 2 * δ + 8 * η := by
  have ht := sum_snorm_state_transfer ψ φ hM hR
  linarith

section Bipartite

variable {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

/-- Alice's local PVM error transfers between arbitrary bipartite vectors. -/
theorem sum_stateSqNorm_state_transfer (ψ φ : H × K → ℂ)
    {M R : C → Matrix H H ℂ} (hM : IsPVM M) (hR : IsPVM R) :
    ∑ c, stateSqNorm φ (M c - R c) ≤
      2 * ∑ c, stateSqNorm ψ (M c - R c) + 8 * ‖evec (ψ - φ)‖ ^ 2 := by
  simpa only [stateSqNorm, stateNorm, norm_stateVec_eq_snorm, aOp_sub] using
    sum_snorm_state_transfer ψ φ hM.aOp hR.aOp

/-- Transfer a bounded Alice PVM approximation to the extracted state. -/
theorem sum_stateSqNorm_state_transfer_le (ψ φ : H × K → ℂ)
    {M R : C → Matrix H H ℂ} (hM : IsPVM M) (hR : IsPVM R)
    {δ η : ℝ} (hδ : ∑ c, stateSqNorm ψ (M c - R c) ≤ δ)
    (hdist : ‖evec (ψ - φ)‖ ^ 2 ≤ η) :
    ∑ c, stateSqNorm φ (M c - R c) ≤ 2 * δ + 8 * η := by
  have ht := sum_stateSqNorm_state_transfer ψ φ hM hR
  linarith

/-- Bob's local PVM error transfers with the same constants. -/
theorem sum_bob_snorm_state_transfer (ψ φ : H × K → ℂ)
    {M R : C → Matrix K K ℂ} (hM : IsPVM M) (hR : IsPVM R) :
    ∑ c, snorm φ (bOp (M c - R c)) ^ 2 ≤
      2 * ∑ c, snorm ψ (bOp (M c - R c)) ^ 2 + 8 * ‖evec (ψ - φ)‖ ^ 2 := by
  simpa only [bOp_sub] using sum_snorm_state_transfer ψ φ hM.bOp hR.bOp

/-- Transfer a bounded Bob PVM approximation to the extracted state. -/
theorem sum_bob_snorm_state_transfer_le (ψ φ : H × K → ℂ)
    {M R : C → Matrix K K ℂ} (hM : IsPVM M) (hR : IsPVM R)
    {δ η : ℝ} (hδ : ∑ c, snorm ψ (bOp (M c - R c)) ^ 2 ≤ δ)
    (hdist : ‖evec (ψ - φ)‖ ^ 2 ≤ η) :
    ∑ c, snorm φ (bOp (M c - R c)) ^ 2 ≤ 2 * δ + 8 * η := by
  have ht := sum_bob_snorm_state_transfer ψ φ hM hR
  linarith

end Bipartite
end MIPRE.Introspection

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.PauliTwirlDistance
import MIPRE.Foundations.Introspection.BlockRetention

/-! # Pauli mixing with a retained classical fibre

The sampled register has a fixed coordinate presentation, with arbitrary auxiliary systems.
The output consists of actual ancillary POVMs. Consistency and the two readout commutator
errors control the squared state distance by an explicit square-root estimate.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Weyl Classical
open scoped Kronecker

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {n : ℕ} {H K A : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype A] [DecidableEq A]

/-- Sum of the commutator errors against a linear-map readout, over all outcomes and fibres. -/
def readoutCommutatorError {B : Type*} [Fintype B]
    (ψ : ((Fin n → F) × H) × K → ℂ)
    (M : B → Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ)
    (w : (Fin n → F) → Matrix (Fin n → F) (Fin n → F) ℂ)
    (L : (Fin n → F) →ₗ[F] (Fin n → F)) : ℝ :=
  ∑ a, ∑ y : Fin n → F, stateSqNorm ψ
    (M a * aOp (synOf w L y) - aOp (synOf w L y) * M a)

/-- The first marginal's consistency error with the retained `Z` readout. -/
def readoutMarginalError (L : (Fin n → F) →ₗ[F] (Fin n → F))
    (ψ : ((Fin n → F) × H) × K → ℂ)
    (M : (Fin n → F) × A → Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) : ℝ :=
  ∑ y, stateSqNorm ψ ((∑ a, M (y, a)) - aOp (synOf wZ L y))

/-- The error before completing the retained submeasurement: coefficients `2, 8, 8`. -/
def mixingError (L : (Fin n → F) →ₗ[F] (Fin n → F)) (ξ : H × K → ℂ)
    (M : POVM ((Fin n → F) × A) ((Fin n → F) × H)) : ℝ :=
  2 * readoutMarginalError L (eprWithAux ξ) (fun p => (M.mats p).val) +
  8 * readoutCommutatorError (eprWithAux ξ) (fun p => (M.mats p).val) wZ LinearMap.id +
  8 * readoutCommutatorError (eprWithAux ξ) (fun p => (M.mats p).val) wX (CL.lperp L)

/-- Every term entering the mixing error is a squared norm. -/
theorem mixingError_nonneg (L : (Fin n → F) →ₗ[F] (Fin n → F)) (ξ : H × K → ℂ)
    (M : POVM ((Fin n → F) × A) ((Fin n → F) × H)) : 0 ≤ mixingError L ξ M := by
  unfold mixingError readoutMarginalError readoutCommutatorError stateSqNorm stateNorm
  positivity

/-- Pauli mixing produces normalized POVMs on the ancilla at every retained fibre. -/
theorem exists_pauli_mixing (L : (Fin n → F) →ₗ[F] (Fin n → F))
    (ξ : H × K → ℂ) (hξ : ‖evec ξ‖ = 1)
    (M : POVM ((Fin n → F) × A) ((Fin n → F) × H))
    (hM : IsPVM (fun p => (M.mats p).val)) :
    ∃ Q : (Fin n → F) → POVM A H,
      (∑ p : (Fin n → F) × A, stateSqNorm (eprWithAux ξ)
        ((M.mats p).val - synOf wZ L p.1 ⊗ₖ ((Q p.1).mats p.2).val)) ≤
      2 * mixingError L ξ M + 4 * Real.sqrt (mixingError L ξ M) := by
  obtain ⟨Q, hQ⟩ := linear_twirl_povm L M
  have hdist := pauli_twirl_readout_dist_le L ξ M
  have hswap : (∑ p : (Fin n → F) × A, stateSqNorm (eprWithAux ξ)
      ((M.mats p).val - ∑ z, synOf wZ L z ⊗ₖ ((Q z).mats p).val)) =
      ∑ p : (Fin n → F) × A, stateSqNorm (eprWithAux ξ)
        (averageX L.ker (dephaseZ (M.mats p).val) - (M.mats p).val) := by
    apply Finset.sum_congr rfl
    intro p _
    rw [← hQ p, stateSqNorm_sub_comm]
  have hclose : 2 * (∑ y : Fin n → F, stateSqNorm (eprWithAux ξ)
      ((∑ a, (M.mats (y, a)).val) - aOp (synOf wZ L y))) +
      2 * (∑ p : (Fin n → F) × A, stateSqNorm (eprWithAux ξ)
        ((M.mats p).val - ∑ z, synOf wZ L z ⊗ₖ ((Q z).mats p).val)) ≤ mixingError L ξ M := by
    rw [hswap]
    unfold mixingError readoutMarginalError readoutCommutatorError
    linarith
  have h := block_retention_dist_avg (fun _ : Unit => (1 : ℝ)) (by simp) (by simp)
    (eprWithAux ξ) (eprWithAux_norm ξ hξ) (fun _ p => (M.mats p).val) (fun _ => hM)
    (fun _ => synOf wZ L) (fun _ => linear_measurement_isPVM wZ isWeylFamily_wZ L)
    (fun _ => Q) (fun _ y => (aOp (synOf wZ L y) : Matrix ((Fin n → F) × K) _ ℂ))
    (fun _ => (linear_measurement_isPVM wZ isWeylFamily_wZ L).aOp)
    (fun _ y => eprWithAux_readout_mirror ξ L y)
    (by simpa only [Finset.univ_unique, Finset.sum_singleton, one_mul] using hclose)
  refine ⟨fun y => (Q y).map Prod.snd, ?_⟩
  simpa only [Finset.univ_unique, Finset.sum_singleton, one_mul] using h

/-- Question averaging costs no dimension factor and moves the error inside one square root. -/
theorem exists_pauli_mixing_avg {X : Type*} [Fintype X]
    (D : X → ℝ) (hD0 : ∀ x, 0 ≤ D x) (hD1 : ∑ x, D x = 1)
    (L : X → (Fin n → F) →ₗ[F] (Fin n → F)) (ξ : H × K → ℂ) (hξ : ‖evec ξ‖ = 1)
    (M : X → POVM ((Fin n → F) × A) ((Fin n → F) × H))
    (hM : ∀ x, IsPVM (fun p => ((M x).mats p).val))
    {δ : ℝ} (hδ : ∑ x, D x * mixingError (L x) ξ (M x) ≤ δ) :
    ∃ Q : X → (Fin n → F) → POVM A H,
      (∑ x, D x * ∑ p : (Fin n → F) × A, stateSqNorm (eprWithAux ξ)
        (((M x).mats p).val - synOf wZ (L x) p.1 ⊗ₖ ((Q x p.1).mats p.2).val)) ≤
      2 * δ + 4 * Real.sqrt δ := by
  choose Q hQ using fun x => exists_pauli_mixing (L x) ξ hξ (M x) (hM x)
  refine ⟨Q, ?_⟩
  have hsum := Finset.sum_le_sum fun x (_ : x ∈ univ) =>
    mul_le_mul_of_nonneg_left (hQ x) (hD0 x)
  have hroot := (sum_weighted_sqrt_le D (fun x => mixingError (L x) ξ (M x)) hD0 hD1
    (fun x => mixingError_nonneg (L x) ξ (M x))).trans (Real.sqrt_le_sqrt hδ)
  have heq : (∑ x, D x * (2 * mixingError (L x) ξ (M x) +
      4 * Real.sqrt (mixingError (L x) ξ (M x)))) =
      2 * (∑ x, D x * mixingError (L x) ξ (M x)) +
      4 * ∑ x, D x * Real.sqrt (mixingError (L x) ξ (M x)) := by
    simp only [mul_add, Finset.sum_add_distrib, mul_left_comm (b := (2 : ℝ)),
      mul_left_comm (b := (4 : ℝ)), ← Finset.mul_sum]
  rw [heq] at hsum
  linarith

end MIPRE.Introspection

end

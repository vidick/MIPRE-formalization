/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.PauliTwirlDistance
public import MIPRE.Foundations.Introspection.BlockRetention

@[expose] public section

/-! # Pauli mixing with a retained classical fibre

The sampled register has a fixed coordinate presentation, with arbitrary auxiliary systems.
The output consists of actual ancillary POVMs. Consistency and the two readout commutator
errors control the squared state distance by an explicit square-root estimate.

In the register model (Phase 4 of `planning/mipco-track.md`): the EPR state on the sampled
register adjoined to an ancillary model `Ξ`, `Ξ.reg (Fin n → F)`; the output POVMs are in the
ancilla's algebra.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Weyl Classical

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {n : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [StarModule ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [StarModule ℂ ℬ]

/-- Sum of the commutator errors against a linear-map readout, over all outcomes and fibres. -/
def readoutCommutatorError {B : Type*} [Fintype B]
    (Ψ : BipartiteModel 𝒞 (Matrix (Fin n → F) (Fin n → F) 𝒜) ℬ)
    (M : B → Matrix (Fin n → F) (Fin n → F) 𝒜)
    (w : (Fin n → F) → Matrix (Fin n → F) (Fin n → F) ℂ)
    (L : (Fin n → F) →ₗ[F] (Fin n → F)) : ℝ :=
  ∑ a, ∑ y : Fin n → F, Ψ.stateSqNorm
    (M a * smulKron 1 (synOf w L y) - smulKron 1 (synOf w L y) * M a)

/-- The first marginal's consistency error with the retained `Z` readout. -/
def readoutMarginalError (L : (Fin n → F) →ₗ[F] (Fin n → F))
    (Ψ : BipartiteModel 𝒞 (Matrix (Fin n → F) (Fin n → F) 𝒜) ℬ)
    (M : (Fin n → F) × A → Matrix (Fin n → F) (Fin n → F) 𝒜) : ℝ :=
  ∑ y, Ψ.stateSqNorm ((∑ a, M (y, a)) - smulKron 1 (synOf wZ L y))

variable [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarProper 𝒜]

/-- The error before completing the retained submeasurement: coefficients `2, 8, 8`. -/
def mixingError (L : (Fin n → F) →ₗ[F] (Fin n → F)) (Ξ : BipartiteModel 𝒞 𝒜 ℬ)
    (M : POVMIn ((Fin n → F) × A) (Matrix (Fin n → F) (Fin n → F) 𝒜)) : ℝ :=
  2 * readoutMarginalError L (Ξ.reg (Fin n → F)) M.op +
  8 * readoutCommutatorError (Ξ.reg (Fin n → F)) M.op wZ LinearMap.id +
  8 * readoutCommutatorError (Ξ.reg (Fin n → F)) M.op wX (CL.lperp L)

/-- Every term entering the mixing error is a squared norm. -/
theorem mixingError_nonneg (L : (Fin n → F) →ₗ[F] (Fin n → F)) (Ξ : BipartiteModel 𝒞 𝒜 ℬ)
    (M : POVMIn ((Fin n → F) × A) (Matrix (Fin n → F) (Fin n → F) 𝒜)) :
    0 ≤ mixingError L Ξ M := by
  unfold mixingError readoutMarginalError readoutCommutatorError BipartiteModel.stateSqNorm
  positivity

/-- Pauli mixing produces normalized POVMs on the ancilla at every retained fibre. -/
theorem exists_pauli_mixing (L : (Fin n → F) →ₗ[F] (Fin n → F))
    (Ξ : BipartiteModel 𝒞 𝒜 ℬ) (hΞ : ‖Ξ.ψ‖ = 1)
    (M : POVMIn ((Fin n → F) × A) (Matrix (Fin n → F) (Fin n → F) 𝒜)) (hM : IsPVMIn M.op) :
    ∃ Q : (Fin n → F) → POVMIn A 𝒜,
      (∑ p : (Fin n → F) × A, (Ξ.reg (Fin n → F)).stateSqNorm
        (M.op p - smulKron ((Q p.1).op p.2) (synOf wZ L p.1))) ≤
      2 * mixingError L Ξ M + 4 * Real.sqrt (mixingError L Ξ M) := by
  obtain ⟨Q, hQ⟩ := linear_twirl_povm L M
  have hdist := pauli_twirl_readout_dist_le L Ξ M
  have hswap : (∑ p : (Fin n → F) × A, (Ξ.reg (Fin n → F)).stateSqNorm
      (M.op p - ∑ z, smulKron ((Q z).op p) (synOf wZ L z))) =
      ∑ p : (Fin n → F) × A, (Ξ.reg (Fin n → F)).stateSqNorm
        (averageX L.ker (dephaseZ (M.op p)) - M.op p) := by
    apply Finset.sum_congr rfl
    intro p _
    rw [← hQ p, BipartiteModel.stateSqNorm_sub_comm]
  have hclose : 2 * (∑ y : Fin n → F, (Ξ.reg (Fin n → F)).stateSqNorm
      ((∑ a, M.op (y, a)) - smulKron 1 (synOf wZ L y))) +
      2 * (∑ p : (Fin n → F) × A, (Ξ.reg (Fin n → F)).stateSqNorm
        (M.op p - ∑ z, smulKron ((Q z).op p) (synOf wZ L z))) ≤ mixingError L Ξ M := by
    rw [hswap]
    unfold mixingError readoutMarginalError readoutCommutatorError
    linarith
  have hP := linear_measurement_isPVM wZ isWeylFamily_wZ L
  have h := block_retention_dist_avg (fun _ : Unit => (1 : ℝ)) (by simp) (by simp)
    (Ξ.reg (Fin n → F)) (by rw [Ξ.norm_reg_ψ, hΞ]) (fun _ p => M.op p) (fun _ => hM)
    (fun _ => synOf wZ L) (fun _ => hP)
    (fun _ => Q) (fun _ y => smulKron (1 : ℬ) (synOf wZ L y))
    (fun _ => hP.toIn.smulKron_one)
    (fun _ y => reg_readout_mirror Ξ L y)
    (by simpa only [Finset.univ_unique, Finset.sum_singleton, one_mul] using hclose)
  refine ⟨fun y => (Q y).map Prod.snd, ?_⟩
  simpa only [Finset.univ_unique, Finset.sum_singleton, one_mul] using h

/-- Question averaging costs no dimension factor and moves the error inside one square root. -/
theorem exists_pauli_mixing_avg {X : Type*} [Fintype X]
    (D : X → ℝ) (hD0 : ∀ x, 0 ≤ D x) (hD1 : ∑ x, D x = 1)
    (L : X → (Fin n → F) →ₗ[F] (Fin n → F)) (Ξ : BipartiteModel 𝒞 𝒜 ℬ) (hΞ : ‖Ξ.ψ‖ = 1)
    (M : X → POVMIn ((Fin n → F) × A) (Matrix (Fin n → F) (Fin n → F) 𝒜))
    (hM : ∀ x, IsPVMIn (M x).op)
    {δ : ℝ} (hδ : ∑ x, D x * mixingError (L x) Ξ (M x) ≤ δ) :
    ∃ Q : X → (Fin n → F) → POVMIn A 𝒜,
      (∑ x, D x * ∑ p : (Fin n → F) × A, (Ξ.reg (Fin n → F)).stateSqNorm
        ((M x).op p - smulKron ((Q x p.1).op p.2) (synOf wZ (L x) p.1))) ≤
      2 * δ + 4 * Real.sqrt δ := by
  choose Q hQ using fun x => exists_pauli_mixing (L x) Ξ hΞ (M x) (hM x)
  refine ⟨Q, ?_⟩
  have hsum := Finset.sum_le_sum fun x (_ : x ∈ univ) =>
    mul_le_mul_of_nonneg_left (hQ x) (hD0 x)
  have hroot := (sum_weighted_sqrt_le D (fun x => mixingError (L x) Ξ (M x)) hD0 hD1
    (fun x => mixingError_nonneg (L x) Ξ (M x))).trans (Real.sqrt_le_sqrt hδ)
  have heq : (∑ x, D x * (2 * mixingError (L x) Ξ (M x) +
      4 * Real.sqrt (mixingError (L x) Ξ (M x)))) =
      2 * (∑ x, D x * mixingError (L x) Ξ (M x)) +
      4 * ∑ x, D x * Real.sqrt (mixingError (L x) Ξ (M x)) := by
    simp only [mul_add, Finset.sum_add_distrib, mul_left_comm (b := (2 : ℝ)),
      mul_left_comm (b := (4 : ℝ)), ← Finset.mul_sum]
  rw [heq] at hsum
  linarith

end MIPRE.Introspection

end

end

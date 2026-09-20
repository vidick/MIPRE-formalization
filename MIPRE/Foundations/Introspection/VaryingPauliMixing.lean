/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.PauliMixing

/-! # Pauli mixing in question-dependent coordinate presentations

The number of sampled coordinates and both ancillary spaces can depend on the
question. This is the form used after splitting a retained register from its
complement. The register's ambient embeddings are not part of this statement.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Weyl Classical
open scoped Kronecker

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
  {n : X → ℕ} {H K : X → Type*}
  [∀ x, Fintype (H x)] [∀ x, DecidableEq (H x)]
  [∀ x, Fintype (K x)] [∀ x, DecidableEq (K x)]

/-- Averaged mixing when the retained register and its complement vary with the question. -/
theorem exists_pauli_mixing_varying
    (D : X → ℝ) (hD0 : ∀ x, 0 ≤ D x) (hD1 : ∑ x, D x = 1)
    (L : (x : X) → (Fin (n x) → F) →ₗ[F] (Fin (n x) → F))
    (ξ : (x : X) → H x × K x → ℂ) (hξ : ∀ x, ‖evec (ξ x)‖ = 1)
    (M : (x : X) → POVM ((Fin (n x) → F) × A) ((Fin (n x) → F) × H x))
    (hM : ∀ x, IsPVM (fun p => ((M x).mats p).val))
    {δ : ℝ} (hδ : ∑ x, D x * mixingError (L x) (ξ x) (M x) ≤ δ) :
    ∃ Q : (x : X) → (Fin (n x) → F) → POVM A (H x),
      (∑ x, D x * ∑ p : (Fin (n x) → F) × A, stateSqNorm (eprWithAux (ξ x))
        (((M x).mats p).val - synOf wZ (L x) p.1 ⊗ₖ ((Q x p.1).mats p.2).val)) ≤
      2 * δ + 4 * Real.sqrt δ := by
  choose Q hQ using fun x => exists_pauli_mixing (L x) (ξ x) (hξ x) (M x) (hM x)
  refine ⟨Q, ?_⟩
  have hsum := Finset.sum_le_sum fun x (_ : x ∈ univ) =>
    mul_le_mul_of_nonneg_left (hQ x) (hD0 x)
  have hroot := (sum_weighted_sqrt_le D (fun x => mixingError (L x) (ξ x) (M x)) hD0 hD1
    (fun x => mixingError_nonneg (L x) (ξ x) (M x))).trans (Real.sqrt_le_sqrt hδ)
  have heq : (∑ x, D x * (2 * mixingError (L x) (ξ x) (M x) +
      4 * Real.sqrt (mixingError (L x) (ξ x) (M x)))) =
      2 * (∑ x, D x * mixingError (L x) (ξ x) (M x)) +
      4 * ∑ x, D x * Real.sqrt (mixingError (L x) (ξ x) (M x)) := by
    simp only [mul_add, Finset.sum_add_distrib, mul_left_comm (b := (2 : ℝ)),
      mul_left_comm (b := (4 : ℝ)), ← Finset.mul_sum]
  rw [heq] at hsum
  linarith

/-- A convenient universal constant for three error hypotheses bounded by `ε ≤ 1`. -/
theorem mixing_error_sqrt_bound {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    2 * (18 * ε) + 4 * Real.sqrt (18 * ε) ≤ 56 * Real.sqrt ε := by
  have hroot0 := Real.sqrt_nonneg ε
  have hroot1 := Real.sq_sqrt hε0
  have hroot18 := Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 18) hε0)
  have hle : ε ≤ Real.sqrt ε := by nlinarith [sq_nonneg (Real.sqrt ε - 1)]
  have h18 : Real.sqrt (18 * ε) ≤ 5 * Real.sqrt ε := by
    nlinarith [Real.sqrt_nonneg (18 * ε)]
  linarith

/-- The three readout hypotheses yield a dimension-independent `56 sqrt ε` bound. -/
theorem exists_pauli_mixing_sqrt
    (D : X → ℝ) (hD0 : ∀ x, 0 ≤ D x) (hD1 : ∑ x, D x = 1)
    (L : (x : X) → (Fin (n x) → F) →ₗ[F] (Fin (n x) → F))
    (ξ : (x : X) → H x × K x → ℂ) (hξ : ∀ x, ‖evec (ξ x)‖ = 1)
    (M : (x : X) → POVM ((Fin (n x) → F) × A) ((Fin (n x) → F) × H x))
    (hM : ∀ x, IsPVM (fun p => ((M x).mats p).val))
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hmarg : ∑ x, D x * readoutMarginalError (L x) (eprWithAux (ξ x))
      (fun p => ((M x).mats p).val) ≤ ε)
    (hZ : ∑ x, D x * readoutCommutatorError (eprWithAux (ξ x))
      (fun p => ((M x).mats p).val) wZ LinearMap.id ≤ ε)
    (hX : ∑ x, D x * readoutCommutatorError (eprWithAux (ξ x))
      (fun p => ((M x).mats p).val) wX (CL.lperp (L x)) ≤ ε) :
    ∃ Q : (x : X) → (Fin (n x) → F) → POVM A (H x),
      (∑ x, D x * ∑ p : (Fin (n x) → F) × A, stateSqNorm (eprWithAux (ξ x))
        (((M x).mats p).val - synOf wZ (L x) p.1 ⊗ₖ ((Q x p.1).mats p.2).val)) ≤
      56 * Real.sqrt ε := by
  have hδ : ∑ x, D x * mixingError (L x) (ξ x) (M x) ≤ 18 * ε := by
    simp only [mixingError, mul_add, Finset.sum_add_distrib,
      mul_left_comm (b := (2 : ℝ)), mul_left_comm (b := (8 : ℝ)), ← Finset.mul_sum]
    linarith
  obtain ⟨Q, hQ⟩ := exists_pauli_mixing_varying D hD0 hD1 L ξ hξ M hM hδ
  exact ⟨Q, hQ.trans (mixing_error_sqrt_bound hε0 hε1)⟩

end MIPRE.Introspection

end

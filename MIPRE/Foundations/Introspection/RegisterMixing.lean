/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.RegisterEPR

/-! # Pauli mixing in the original local register

The basis equivalence explicitly splits the retained coordinates from the local
complement. Hypotheses and the conclusion are stated on the original EPR state,
and the output POVMs act only on that local complement and the original ancilla.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Weyl Classical
open scoped Kronecker

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {I R H K A : Type*} [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype A] [DecidableEq A] {n : ℕ}

/-- Read a Pauli linear map on the selected coordinates of the original register. -/
def registerReadout (e : I ≃ (Fin n → F) × R)
    (w : (Fin n → F) → Matrix (Fin n → F) (Fin n → F) ℂ)
    (L : (Fin n → F) →ₗ[F] (Fin n → F)) (y : Fin n → F) :
    Matrix (I × H) (I × H) ℂ :=
  registerOp (registerParty e H) (aOp (synOf w L y))

/-- The split EPR state is the existing coordinate mixing state, exactly. -/
theorem registerState_coordinate (ξ : H × K → ℂ) :
    registerState (Fin n → F) ξ = eprWithAux ξ := by
  unfold registerState eprWithAux
  rw [registerEPR_eq_weyl]

/-- Express any local operator in split coordinates without changing its state error. -/
theorem stateSqNorm_split_original (e : I ≃ (Fin n → F) × R) (ξ : H × K → ℂ)
    (M : Matrix (I × H) (I × H) ℂ) :
    stateSqNorm (registerState I ξ) M =
      stateSqNorm (eprWithAux (registerState R ξ))
        (registerOp (registerParty e H).symm M) := by
  conv_lhs => rw [← registerOp_symm (registerParty e H) M]
  rw [stateSqNorm_registerState_split, registerState_coordinate]

/-- The first marginal consistency error in the original coordinates. -/
def registerMarginalError (e : I ≃ (Fin n → F) × R)
    (L : (Fin n → F) →ₗ[F] (Fin n → F)) (ξ : H × K → ℂ)
    (M : (Fin n → F) × A → Matrix (I × H) (I × H) ℂ) : ℝ :=
  ∑ y, stateSqNorm (registerState I ξ)
    ((∑ a, M (y, a)) - registerReadout e wZ L y)

/-- The readout commutation error in the original coordinates. -/
def registerCommutatorError (e : I ≃ (Fin n → F) × R) (ξ : H × K → ℂ)
    (M : (Fin n → F) × A → Matrix (I × H) (I × H) ℂ)
    (w : (Fin n → F) → Matrix (Fin n → F) (Fin n → F) ℂ)
    (L : (Fin n → F) →ₗ[F] (Fin n → F)) : ℝ :=
  ∑ p, ∑ y, stateSqNorm (registerState I ξ)
    (M p * registerReadout e w L y - registerReadout e w L y * M p)

theorem registerMarginalError_eq (e : I ≃ (Fin n → F) × R)
    (L : (Fin n → F) →ₗ[F] (Fin n → F)) (ξ : H × K → ℂ)
    (M : (Fin n → F) × A → Matrix (I × H) (I × H) ℂ) :
    registerMarginalError e L ξ M = readoutMarginalError L
      (eprWithAux (registerState R ξ)) (fun p => registerOp (registerParty e H).symm (M p)) := by
  unfold registerMarginalError readoutMarginalError registerReadout
  simp_rw [stateSqNorm_split_original e, registerOp_sub, registerOp_sum]
  simp only [registerOp_inv]

theorem registerCommutatorError_eq (e : I ≃ (Fin n → F) × R) (ξ : H × K → ℂ)
    (M : (Fin n → F) × A → Matrix (I × H) (I × H) ℂ)
    (w : (Fin n → F) → Matrix (Fin n → F) (Fin n → F) ℂ)
    (L : (Fin n → F) →ₗ[F] (Fin n → F)) :
    registerCommutatorError e ξ M w L = readoutCommutatorError
      (eprWithAux (registerState R ξ)) (fun p => registerOp (registerParty e H).symm (M p)) w L := by
  unfold registerCommutatorError readoutCommutatorError registerReadout
  simp_rw [stateSqNorm_split_original e, registerOp_sub, registerOp_mul]
  simp only [registerOp_inv]

section Varying

variable {X : Type*} [Fintype X] {n : X → ℕ} {I R : X → Type*}
  [∀ x, Fintype (I x)] [∀ x, DecidableEq (I x)]
  [∀ x, Fintype (R x)] [∀ x, DecidableEq (R x)] [∀ x, Nonempty (R x)]

/-- Pauli mixing on the original registers, with question-dependent coordinate splits.
The conclusion supplies genuine POVMs on the local complement, with no ambient complement
adjoined to their support and no dimension factor in the error. -/
theorem exists_register_mixing_sqrt
    (D : X → ℝ) (hD0 : ∀ x, 0 ≤ D x) (hD1 : ∑ x, D x = 1)
    (e : (x : X) → I x ≃ (Fin (n x) → F) × R x)
    (L : (x : X) → (Fin (n x) → F) →ₗ[F] (Fin (n x) → F))
    (ξ : H × K → ℂ) (hξ : ‖evec ξ‖ = 1)
    (M : (x : X) → POVM ((Fin (n x) → F) × A) (I x × H))
    (hM : ∀ x, IsPVM (fun p => ((M x).mats p).val))
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hmarg : ∑ x, D x * registerMarginalError (e x) (L x) ξ
      (fun p => ((M x).mats p).val) ≤ ε)
    (hZ : ∑ x, D x * registerCommutatorError (e x) ξ
      (fun p => ((M x).mats p).val) wZ LinearMap.id ≤ ε)
    (hX : ∑ x, D x * registerCommutatorError (e x) ξ
      (fun p => ((M x).mats p).val) wX (CL.lperp (L x)) ≤ ε) :
    ∃ Q : (x : X) → (Fin (n x) → F) → POVM A (R x × H),
      (∑ x, D x * ∑ p : (Fin (n x) → F) × A, stateSqNorm (registerState (I x) ξ)
        (((M x).mats p).val - registerOp (registerParty (e x) H)
          (synOf wZ (L x) p.1 ⊗ₖ ((Q x p.1).mats p.2).val))) ≤ 56 * Real.sqrt ε := by
  let Mc x := registerPOVM (registerParty (e x) H).symm (M x)
  have hMc x : IsPVM (fun p => ((Mc x).mats p).val) :=
    registerOp_isPVM _ (hM x)
  simp_rw [registerMarginalError_eq] at hmarg
  simp_rw [registerCommutatorError_eq] at hZ hX
  obtain ⟨Q, hQ⟩ := exists_pauli_mixing_sqrt D hD0 hD1 L
    (fun x => registerState (R x) ξ) (fun _ => registerState_norm ξ hξ)
    Mc hMc hε0 hε1 hmarg hZ hX
  refine ⟨Q, ?_⟩
  convert hQ using 1
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rw [stateSqNorm_split_original (e x), registerOp_sub]
  simp only [registerOp_inv]
  rfl

end Varying

end MIPRE.Introspection

end

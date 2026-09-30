/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.RegisterEPR
public import MIPRE.Foundations.Introspection.VaryingPauliMixing

@[expose] public section

/-! # Pauli mixing in the original local register

The basis equivalence explicitly splits the retained coordinates from the local
complement. Hypotheses and the conclusion are stated on the original EPR state,
and the output POVMs act only on that local complement and the original ancilla.

In the register model `Ξ.reg I` (Phase 4 of `planning/mipco-track.md`), the split of the register
along `e : I ≃ (Fin n → F) × R` is the local isometry `BipartiteModel.regSplit`, whose
homomorphism `regSplitHom e` reads a block matrix over the coordinates of block matrices over
the complement as a block matrix over `I`, with inverse `regSplitInvHom e`.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Weyl Classical

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {I R A : Type*} [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]
  [Fintype A] [DecidableEq A] {n : ℕ}
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [StarModule ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [StarModule ℂ ℬ]

/-- Read a Pauli linear map on the selected coordinates of the original register. -/
def registerReadout (e : I ≃ (Fin n → F) × R)
    (w : (Fin n → F) → Matrix (Fin n → F) (Fin n → F) ℂ)
    (L : (Fin n → F) →ₗ[F] (Fin n → F)) (y : Fin n → F) : Matrix I I 𝒜 :=
  regSplitHom e (smulKron 1 (synOf w L y))

/-- Express any local operator in split coordinates without changing its state error. -/
theorem stateSqNorm_split_original (e : I ≃ (Fin n → F) × R) (Ξ : BipartiteModel 𝒞 𝒜 ℬ)
    (M : Matrix I I 𝒜) :
    (Ξ.reg I).stateSqNorm M =
      ((Ξ.reg R).reg (Fin n → F)).stateSqNorm (regSplitInvHom e M) := by
  have h := BipartiteModel.LocalIsometry.stateSqNorm_of_W_ψ (Ξ.regSplit_W_ψ e)
    (regSplitInvHom e M)
  rwa [BipartiteModel.regSplit_ΦA_eq, regSplitHom_inv] at h

/-- The first marginal consistency error in the original coordinates. -/
def registerMarginalError (e : I ≃ (Fin n → F) × R)
    (L : (Fin n → F) →ₗ[F] (Fin n → F)) (Ξ : BipartiteModel 𝒞 𝒜 ℬ)
    (M : (Fin n → F) × A → Matrix I I 𝒜) : ℝ :=
  ∑ y, (Ξ.reg I).stateSqNorm ((∑ a, M (y, a)) - registerReadout e wZ L y)

/-- The readout commutation error in the original coordinates. -/
def registerCommutatorError (e : I ≃ (Fin n → F) × R) (Ξ : BipartiteModel 𝒞 𝒜 ℬ)
    (M : (Fin n → F) × A → Matrix I I 𝒜)
    (w : (Fin n → F) → Matrix (Fin n → F) (Fin n → F) ℂ)
    (L : (Fin n → F) →ₗ[F] (Fin n → F)) : ℝ :=
  ∑ p, ∑ y, (Ξ.reg I).stateSqNorm
    (M p * registerReadout e w L y - registerReadout e w L y * M p)

theorem registerMarginalError_eq (e : I ≃ (Fin n → F) × R)
    (L : (Fin n → F) →ₗ[F] (Fin n → F)) (Ξ : BipartiteModel 𝒞 𝒜 ℬ)
    (M : (Fin n → F) × A → Matrix I I 𝒜) :
    registerMarginalError e L Ξ M = readoutMarginalError L
      ((Ξ.reg R).reg (Fin n → F)) (fun p => regSplitInvHom e (M p)) := by
  unfold registerMarginalError readoutMarginalError registerReadout
  simp_rw [stateSqNorm_split_original e Ξ, map_sub, map_sum, regSplitInvHom_hom]

theorem registerCommutatorError_eq (e : I ≃ (Fin n → F) × R) (Ξ : BipartiteModel 𝒞 𝒜 ℬ)
    (M : (Fin n → F) × A → Matrix I I 𝒜)
    (w : (Fin n → F) → Matrix (Fin n → F) (Fin n → F) ℂ)
    (L : (Fin n → F) →ₗ[F] (Fin n → F)) :
    registerCommutatorError e Ξ M w L = readoutCommutatorError
      ((Ξ.reg R).reg (Fin n → F)) (fun p => regSplitInvHom e (M p)) w L := by
  unfold registerCommutatorError readoutCommutatorError registerReadout
  simp_rw [stateSqNorm_split_original e Ξ, map_sub, map_mul, regSplitInvHom_hom]

section Varying

variable [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarProper 𝒜]
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
    (Ξ : BipartiteModel 𝒞 𝒜 ℬ) (hΞ : ‖Ξ.ψ‖ = 1)
    (M : (x : X) → POVMIn ((Fin (n x) → F) × A) (Matrix (I x) (I x) 𝒜))
    (hM : ∀ x, IsPVMIn (M x).op)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hmarg : ∑ x, D x * registerMarginalError (e x) (L x) Ξ (M x).op ≤ ε)
    (hZ : ∑ x, D x * registerCommutatorError (e x) Ξ (M x).op wZ LinearMap.id ≤ ε)
    (hX : ∑ x, D x * registerCommutatorError (e x) Ξ (M x).op wX (CL.lperp (L x)) ≤ ε) :
    ∃ Q : (x : X) → (Fin (n x) → F) → POVMIn A (Matrix (R x) (R x) 𝒜),
      (∑ x, D x * ∑ p : (Fin (n x) → F) × A, (Ξ.reg (I x)).stateSqNorm
        ((M x).op p - regSplitHom (e x)
          (smulKron ((Q x p.1).op p.2) (synOf wZ (L x) p.1)))) ≤ 56 * Real.sqrt ε := by
  let Mc x := (M x).pushforward (regSplitInvHom (e x)) (regSplitInvHom_one (e x))
  have hMc x : IsPVMIn (Mc x).op := POVMIn.isPVMIn_pushforward _ _ (hM x)
  simp_rw [registerMarginalError_eq] at hmarg
  simp_rw [registerCommutatorError_eq] at hZ hX
  obtain ⟨Q, hQ⟩ := exists_pauli_mixing_sqrt D hD0 hD1 L
    (fun x => Ξ.reg (R x)) (fun _ => by rw [Ξ.norm_reg_ψ, hΞ])
    Mc hMc hε0 hε1 hmarg hZ hX
  refine ⟨Q, ?_⟩
  convert hQ using 1
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rw [stateSqNorm_split_original (e x), map_sub, regSplitInvHom_hom]
  rfl

end Varying

end MIPRE.Introspection

end

end

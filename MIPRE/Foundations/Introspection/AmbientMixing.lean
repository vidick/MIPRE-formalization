/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.RegisterCoordinates
public import MIPRE.Foundations.Introspection.RegisterMixing

@[expose] public section

/-! # Pauli mixing for nested registers in one ambient EPR state

This is the ambient-register form of the paper's `lem:mixing`. A measurement
acts on `V` and the original ancilla, and the selected Pauli readout acts on
`U ⊆ V`. Its extracted POVMs act on `V \ U` and that same ancilla. All three
hypotheses and the conclusion use the one ambient EPR state. Restricting to
the local register and returning to the ambient register are exact operations.

In the register model `Ξ.reg (ι → F)` (Phase 4 of `planning/mipco-track.md`): the extension of a
local operator by the identity on the ambient complement is `regExtendHom`, the homomorphism of the
register extension `BipartiteModel.regExtend`, which carries the state exactly.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Weyl Classical

set_option linter.unusedSectionVars false

variable {ι F A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A]
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [StarModule ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [StarModule ℂ ℬ]

/-- Extend an operator on `V` and the ancilla by identity on `V`'s ambient complement. -/
def ambientOperator (V : Finset ι) (M : Matrix (V → F) (V → F) 𝒜) :
    Matrix (ι → F) (ι → F) 𝒜 := regExtendHom (ambientSplit V) M

/-- The selected readout, embedded into the original ambient space. -/
def ambientReadout (U V : Finset ι) (hUV : U ⊆ V)
    (w : (Fin (Fintype.card U) → F) →
      Matrix (Fin (Fintype.card U) → F) (Fin (Fintype.card U) → F) ℂ)
    (L : (Fin (Fintype.card U) → F) →ₗ[F] (Fin (Fintype.card U) → F))
    (y : Fin (Fintype.card U) → F) : Matrix (ι → F) (ι → F) 𝒜 :=
  ambientOperator V (registerReadout (coordinateSplit U V hUV) w L y)

/-- A local operator extended to the ambient register has its state error on the local EPR
factor. -/
theorem stateSqNorm_ambientOperator (Ξ : BipartiteModel 𝒞 𝒜 ℬ) (V : Finset ι)
    (M : Matrix (V → F) (V → F) 𝒜) :
    (Ξ.reg (ι → F)).stateSqNorm (regExtendHom (ambientSplit V) M) =
      (Ξ.reg (V → F)).stateSqNorm M := by
  have h := BipartiteModel.LocalIsometry.stateSqNorm_of_W_ψ (Ξ.regExtend_W_ψ (ambientSplit V)) M
  rwa [BipartiteModel.regExtend_ΦA_eq] at h

/-- Ambient consistency of the first outcome with the selected `Z` readout. -/
def ambientMarginalError (U V : Finset ι) (hUV : U ⊆ V)
    (L : CL.RegLinear F U) (Ξ : BipartiteModel 𝒞 𝒜 ℬ)
    (M : (Fin (Fintype.card U) → F) × A → Matrix (V → F) (V → F) 𝒜) : ℝ :=
  ∑ y, (Ξ.reg (ι → F)).stateSqNorm
    ((∑ a, ambientOperator V (M (y, a))) - ambientReadout U V hUV wZ (coordinateLinear L) y)

/-- Ambient commutation with a selected Pauli readout. -/
def ambientCommutatorError (U V : Finset ι) (hUV : U ⊆ V) (Ξ : BipartiteModel 𝒞 𝒜 ℬ)
    (M : (Fin (Fintype.card U) → F) × A → Matrix (V → F) (V → F) 𝒜)
    (w : (Fin (Fintype.card U) → F) →
      Matrix (Fin (Fintype.card U) → F) (Fin (Fintype.card U) → F) ℂ)
    (L : (Fin (Fintype.card U) → F) →ₗ[F] (Fin (Fintype.card U) → F)) : ℝ :=
  ∑ p, ∑ y, (Ξ.reg (ι → F)).stateSqNorm
    (ambientOperator V (M p) * ambientReadout U V hUV w L y -
      ambientReadout U V hUV w L y * ambientOperator V (M p))

/-- Consistency on the ambient state is exactly consistency on the local EPR factor. -/
theorem ambientMarginalError_eq (U V : Finset ι) (hUV : U ⊆ V)
    (L : CL.RegLinear F U) (Ξ : BipartiteModel 𝒞 𝒜 ℬ)
    (M : (Fin (Fintype.card U) → F) × A → Matrix (V → F) (V → F) 𝒜) :
    ambientMarginalError U V hUV L Ξ M =
      registerMarginalError (coordinateSplit U V hUV) (coordinateLinear L) Ξ M := by
  unfold ambientMarginalError registerMarginalError ambientReadout ambientOperator
  simp_rw [← map_sum, ← map_sub, stateSqNorm_ambientOperator]

/-- Commutation on the ambient state is exactly commutation on the local EPR factor. -/
theorem ambientCommutatorError_eq (U V : Finset ι) (hUV : U ⊆ V) (Ξ : BipartiteModel 𝒞 𝒜 ℬ)
    (M : (Fin (Fintype.card U) → F) × A → Matrix (V → F) (V → F) 𝒜)
    (w : (Fin (Fintype.card U) → F) →
      Matrix (Fin (Fintype.card U) → F) (Fin (Fintype.card U) → F) ℂ)
    (L : (Fin (Fintype.card U) → F) →ₗ[F] (Fin (Fintype.card U) → F)) :
    ambientCommutatorError U V hUV Ξ M w L =
      registerCommutatorError (coordinateSplit U V hUV) Ξ M w L := by
  unfold ambientCommutatorError registerCommutatorError ambientReadout ambientOperator
  simp_rw [← map_mul, ← map_sub, stateSqNorm_ambientOperator]

/-- **Ambient Pauli mixing.** The finite-set register inclusions, the CL linear maps,
and the one global EPR state are supplied directly. The output measurements have precisely
the local residual register as support. All answer values, including those outside the
linear map's range, occur in the sums; the error is at most `56 sqrt ε`. -/
theorem exists_ambient_pauli_mixing [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarProper 𝒜]
    {X : Type*} [Fintype X]
    (D : X → ℝ) (hD0 : ∀ x, 0 ≤ D x) (hD1 : ∑ x, D x = 1)
    (U V : X → Finset ι) (hUV : ∀ x, U x ⊆ V x)
    (L : (x : X) → CL.RegLinear F (U x))
    (Ξ : BipartiteModel 𝒞 𝒜 ℬ) (hΞ : ‖Ξ.ψ‖ = 1)
    (M : (x : X) → POVMIn ((Fin (Fintype.card (U x)) → F) × A) (Matrix (V x → F) (V x → F) 𝒜))
    (hM : ∀ x, IsPVMIn (M x).op)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hmarg : ∑ x, D x * ambientMarginalError (U x) (V x) (hUV x) (L x) Ξ (M x).op ≤ ε)
    (hZ : ∑ x, D x * ambientCommutatorError (U x) (V x) (hUV x) Ξ (M x).op wZ
      LinearMap.id ≤ ε)
    (hX : ∑ x, D x * ambientCommutatorError (U x) (V x) (hUV x) Ξ (M x).op wX
      (CL.lperp (coordinateLinear (L x))) ≤ ε) :
    ∃ Q : (x : X) → (Fin (Fintype.card (U x)) → F) →
        POVMIn A (Matrix (↥(V x \ U x) → F) (↥(V x \ U x) → F) 𝒜),
      (∑ x, D x * ∑ p : (Fin (Fintype.card (U x)) → F) × A,
        (Ξ.reg (ι → F)).stateSqNorm
          (ambientOperator (V x) ((M x).op p) -
            ambientOperator (V x) (regSplitHom (coordinateSplit (U x) (V x) (hUV x))
              (smulKron ((Q x p.1).op p.2) (synOf wZ (coordinateLinear (L x)) p.1))))) ≤
        56 * Real.sqrt ε := by
  simp_rw [ambientMarginalError_eq] at hmarg
  simp_rw [ambientCommutatorError_eq] at hZ hX
  obtain ⟨Q, hQ⟩ := exists_register_mixing_sqrt D hD0 hD1
    (fun x => coordinateSplit (U x) (V x) (hUV x))
    (fun x => coordinateLinear (L x)) Ξ hΞ M hM hε0 hε1 hmarg hZ hX
  refine ⟨Q, ?_⟩
  unfold ambientOperator
  simp_rw [← map_sub, stateSqNorm_ambientOperator]
  exact hQ

end MIPRE.Introspection

end

end

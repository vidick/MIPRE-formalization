/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.RegisterCoordinates

/-! # Pauli mixing for nested registers in one ambient EPR state

This is the ambient-register form of the paper's `lem:mixing`. A measurement
acts on `V` and the original ancilla, and the selected Pauli readout acts on
`U ⊆ V`. Its extracted POVMs act on `V \ U` and that same ancilla. All three
hypotheses and the conclusion use the one ambient EPR state. Restricting to
the local register and returning to the ambient register are exact operations.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Weyl Classical
open scoped Kronecker

set_option linter.unusedSectionVars false

variable {ι F H K A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype A] [DecidableEq A]

/-- Extend an operator on `V` and the ancilla by identity on `V`'s ambient complement. -/
def ambientOperator (V : Finset ι) (M : Matrix ((V → F) × H) ((V → F) × H) ℂ) :
    Matrix ((ι → F) × H) ((ι → F) × H) ℂ := registerExtend (ambientSplit V) M

/-- The selected readout, embedded into the original ambient space. -/
def ambientReadout (U V : Finset ι) (hUV : U ⊆ V)
    (w : (Fin (Fintype.card U) → F) →
      Matrix (Fin (Fintype.card U) → F) (Fin (Fintype.card U) → F) ℂ)
    (L : (Fin (Fintype.card U) → F) →ₗ[F] (Fin (Fintype.card U) → F))
    (y : Fin (Fintype.card U) → F) : Matrix ((ι → F) × H) ((ι → F) × H) ℂ :=
  ambientOperator V (registerReadout (coordinateSplit U V hUV) w L y)

/-- Ambient consistency of the first outcome with the selected `Z` readout. -/
def ambientMarginalError (U V : Finset ι) (hUV : U ⊆ V)
    (L : CL.RegLinear F U) (ξ : H × K → ℂ)
    (M : (Fin (Fintype.card U) → F) × A → Matrix ((V → F) × H) ((V → F) × H) ℂ) : ℝ :=
  ∑ y, stateSqNorm (registerState (ι → F) ξ)
    ((∑ a, ambientOperator V (M (y, a))) - ambientReadout U V hUV wZ (coordinateLinear L) y)

/-- Ambient commutation with a selected Pauli readout. -/
def ambientCommutatorError (U V : Finset ι) (hUV : U ⊆ V) (ξ : H × K → ℂ)
    (M : (Fin (Fintype.card U) → F) × A → Matrix ((V → F) × H) ((V → F) × H) ℂ)
    (w : (Fin (Fintype.card U) → F) →
      Matrix (Fin (Fintype.card U) → F) (Fin (Fintype.card U) → F) ℂ)
    (L : (Fin (Fintype.card U) → F) →ₗ[F] (Fin (Fintype.card U) → F)) : ℝ :=
  ∑ p, ∑ y, stateSqNorm (registerState (ι → F) ξ)
    (ambientOperator V (M p) * ambientReadout U V hUV w L y -
      ambientReadout U V hUV w L y * ambientOperator V (M p))

/-- Consistency on the ambient state is exactly consistency on the local EPR factor. -/
theorem ambientMarginalError_eq (U V : Finset ι) (hUV : U ⊆ V)
    (L : CL.RegLinear F U) (ξ : H × K → ℂ)
    (M : (Fin (Fintype.card U) → F) × A → Matrix ((V → F) × H) ((V → F) × H) ℂ) :
    ambientMarginalError U V hUV L ξ M =
      registerMarginalError (coordinateSplit U V hUV) (coordinateLinear L) ξ M := by
  unfold ambientMarginalError registerMarginalError ambientReadout ambientOperator
  simp_rw [← registerExtend_sum, ← registerExtend_sub, stateSqNorm_registerExtend]

/-- Commutation on the ambient state is exactly commutation on the local EPR factor. -/
theorem ambientCommutatorError_eq (U V : Finset ι) (hUV : U ⊆ V) (ξ : H × K → ℂ)
    (M : (Fin (Fintype.card U) → F) × A → Matrix ((V → F) × H) ((V → F) × H) ℂ)
    (w : (Fin (Fintype.card U) → F) →
      Matrix (Fin (Fintype.card U) → F) (Fin (Fintype.card U) → F) ℂ)
    (L : (Fin (Fintype.card U) → F) →ₗ[F] (Fin (Fintype.card U) → F)) :
    ambientCommutatorError U V hUV ξ M w L =
      registerCommutatorError (coordinateSplit U V hUV) ξ M w L := by
  unfold ambientCommutatorError registerCommutatorError ambientReadout ambientOperator
  simp_rw [← registerExtend_mul, ← registerExtend_sub, stateSqNorm_registerExtend]

/-- **Ambient Pauli mixing.** The finite-set register inclusions, the CL linear maps,
and the one global EPR state are supplied directly. The output measurements have precisely
the local residual register as support. All answer values, including those outside the
linear map's range, occur in the sums; the error is at most `56 sqrt ε`. -/
theorem exists_ambient_pauli_mixing {X : Type*} [Fintype X]
    (D : X → ℝ) (hD0 : ∀ x, 0 ≤ D x) (hD1 : ∑ x, D x = 1)
    (U V : X → Finset ι) (hUV : ∀ x, U x ⊆ V x)
    (L : (x : X) → CL.RegLinear F (U x))
    (ξ : H × K → ℂ) (hξ : ‖evec ξ‖ = 1)
    (M : (x : X) → POVM ((Fin (Fintype.card (U x)) → F) × A) ((V x → F) × H))
    (hM : ∀ x, IsPVM (fun p => ((M x).mats p).val))
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hmarg : ∑ x, D x * ambientMarginalError (U x) (V x) (hUV x) (L x) ξ
      (fun p => ((M x).mats p).val) ≤ ε)
    (hZ : ∑ x, D x * ambientCommutatorError (U x) (V x) (hUV x) ξ
      (fun p => ((M x).mats p).val) wZ LinearMap.id ≤ ε)
    (hX : ∑ x, D x * ambientCommutatorError (U x) (V x) (hUV x) ξ
      (fun p => ((M x).mats p).val) wX (CL.lperp (coordinateLinear (L x))) ≤ ε) :
    ∃ Q : (x : X) → (Fin (Fintype.card (U x)) → F) → POVM A ((↥(V x \ U x) → F) × H),
      (∑ x, D x * ∑ p : (Fin (Fintype.card (U x)) → F) × A,
        stateSqNorm (registerState (ι → F) ξ)
          (ambientOperator (V x) ((M x).mats p).val -
            ambientOperator (V x) (registerOp
              (registerParty (coordinateSplit (U x) (V x) (hUV x)) H)
              (synOf wZ (coordinateLinear (L x)) p.1 ⊗ₖ ((Q x p.1).mats p.2).val)))) ≤
        56 * Real.sqrt ε := by
  simp_rw [ambientMarginalError_eq] at hmarg
  simp_rw [ambientCommutatorError_eq] at hZ hX
  obtain ⟨Q, hQ⟩ := exists_register_mixing_sqrt D hD0 hD1
    (fun x => coordinateSplit (U x) (V x) (hUV x))
    (fun x => coordinateLinear (L x)) ξ hξ M hM hε0 hε1 hmarg hZ hX
  refine ⟨Q, ?_⟩
  unfold ambientOperator
  simpa only [← registerExtend_sub, stateSqNorm_registerExtend] using hQ

end MIPRE.Introspection

end

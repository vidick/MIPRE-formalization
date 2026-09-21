/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AmbientMixing
import MIPRE.Foundations.Introspection.HidingTests

/-! # One product-form induction step from the coarse joint measurements

The two commutators needed by Pauli mixing are derived from the tested
marginals of actual projective measurements on the other party. Coarse-graining
is performed before applying the commutation analysis. The error does not
depend on the size of a coarse-graining fibre.

The final theorem constructs the residual POVMs on `V \ U`, from averaged
cross-party errors on one ambient EPR state. Identifying these measurements
with the prefix-conditioned introspection strategy is a separate obligation.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Weyl Classical
open scoped Kronecker

set_option linter.unusedSectionVars false

section Coarse

variable {H K A B C O : Type*}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C] [Fintype O] [DecidableEq O]

/-- Consistency with the first marginal of an actual coarse joint measurement. -/
def coarseJointLeftError (ψ : H × K → ℂ) (M : POVM A H) (B : POVM O K)
    (f : O → A × C) : ℝ :=
  ∑ a, xSqNorm ψ (M.mats a).val (∑ c, ((B.map f).mats (a, c)).val)

/-- Consistency with the second marginal of the same coarse joint measurement. -/
def coarseJointRightError (ψ : H × K → ℂ) (N : POVM C H) (B : POVM O K)
    (f : O → A × C) : ℝ :=
  ∑ c, xSqNorm ψ (N.mats c).val (∑ a, ((B.map f).mats (a, c)).val)

theorem coarseJointLeftError_nonneg (ψ : H × K → ℂ) (M : POVM A H)
    (B : POVM O K) (f : O → A × C) : 0 ≤ coarseJointLeftError ψ M B f :=
  Finset.sum_nonneg fun _ _ => xSqNorm_nonneg _ _ _

theorem coarseJointRightError_nonneg (ψ : H × K → ℂ) (N : POVM C H)
    (B : POVM O K) (f : O → A × C) : 0 ≤ coarseJointRightError ψ N B f :=
  Finset.sum_nonneg fun _ _ => xSqNorm_nonneg _ _ _

/-- The coarse joint measurement is used directly. In particular this theorem
does not coarse-grain an already established commutator estimate. -/
theorem coarse_joint_commutator_bound (ψ : H × K → ℂ)
    (M : POVM A H) (N : POVM C H) (B : POVM O K)
    (hB : IsPVM (fun b => (B.mats b).val)) (f : O → A × C) :
    (∑ a, ∑ c, stateSqNorm ψ
      ((M.mats a).val * (N.mats c).val - (N.mats c).val * (M.mats a).val)) ≤
      16 * (coarseJointLeftError ψ M B f + coarseJointRightError ψ N B f) := by
  have hleft : 0 ≤ coarseJointLeftError ψ M B f :=
    Finset.sum_nonneg fun _ _ => xSqNorm_nonneg _ _ _
  have hright : 0 ≤ coarseJointRightError ψ N B f :=
    Finset.sum_nonneg fun _ _ => xSqNorm_nonneg _ _ _
  have h := commutation_analysis_aOp (ψ := ψ) (A := M) (Cm := N)
    (isPVM_povm_map B hB f)
    (δ := coarseJointLeftError ψ M B f + coarseJointRightError ψ N B f)
    (by simpa only [coarseJointLeftError, ← xSqNorm_eq_snorm_sq]
          using le_add_of_nonneg_right hright)
    (by simpa only [coarseJointRightError, ← xSqNorm_eq_snorm_sq]
          using le_add_of_nonneg_left hleft)
  simpa only [Fintype.sum_prod_type, stateSqNorm, stateNorm,
    norm_stateVec_eq_snorm] using h

end Coarse

section Ambient

variable {ι F H K A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype A] [DecidableEq A]

/-- Embedding in the ambient register preserves the projective measurement. -/
theorem ambientOperator_isPVM (V : Finset ι)
    {M : A → Matrix ((V → F) × H) ((V → F) × H) ℂ} (hM : IsPVM M) :
    IsPVM (fun a => ambientOperator V (M a)) := by
  apply registerOp_isPVM
  exact hM.aOp

/-- The actual ambient POVM of a projective local measurement. -/
def ambientProjectivePOVM (V : Finset ι) (M : POVM A ((V → F) × H))
    (hM : IsPVM (fun a => (M.mats a).val)) : POVM A ((ι → F) × H) :=
  (ambientOperator_isPVM V hM).toPOVM

@[simp] theorem ambientProjectivePOVM_mats (V : Finset ι)
    (M : POVM A ((V → F) × H)) (hM : IsPVM (fun a => (M.mats a).val)) (a : A) :
    ((ambientProjectivePOVM V M hM).mats a).val = ambientOperator V (M.mats a).val := rfl

/-- Projectivity of a selected linear Pauli readout in the original register. -/
theorem ambientReadout_isPVM (U V : Finset ι) (hUV : U ⊆ V)
    (w : (Fin (Fintype.card U) → F) →
      Matrix (Fin (Fintype.card U) → F) (Fin (Fintype.card U) → F) ℂ)
    (hw : IsWeylFamily w)
    (L : (Fin (Fintype.card U) → F) →ₗ[F] (Fin (Fintype.card U) → F)) :
    IsPVM (ambientReadout (H := H) U V hUV w L) :=
  ambientOperator_isPVM V
    (registerOp_isPVM (registerParty (coordinateSplit U V hUV) H)
      (linear_measurement_isPVM w hw L).aOp)

/-- The selected Pauli readout as a normalized positive measurement. -/
def ambientReadoutPOVM (U V : Finset ι) (hUV : U ⊆ V)
    (w : (Fin (Fintype.card U) → F) →
      Matrix (Fin (Fintype.card U) → F) (Fin (Fintype.card U) → F) ℂ)
    (hw : IsWeylFamily w)
    (L : (Fin (Fintype.card U) → F) →ₗ[F] (Fin (Fintype.card U) → F)) :
    POVM (Fin (Fintype.card U) → F) ((ι → F) × H) :=
  (ambientReadout_isPVM U V hUV w hw L).toPOVM

@[simp] theorem ambientReadoutPOVM_mats (U V : Finset ι) (hUV : U ⊆ V)
    (w : (Fin (Fintype.card U) → F) →
      Matrix (Fin (Fintype.card U) → F) (Fin (Fintype.card U) → F) ℂ)
    (hw : IsWeylFamily w)
    (L : (Fin (Fintype.card U) → F) →ₗ[F] (Fin (Fintype.card U) → F))
    (y : Fin (Fintype.card U) → F) :
    ((ambientReadoutPOVM (H := H) U V hUV w hw L).mats y).val =
      ambientReadout U V hUV w L y := rfl

variable {B C : Type*} [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

/-- The six cross-party errors used in one product-form stage: two sampling
marginal comparisons, and the two marginal comparisons for each coarse joint
measurement. Every summand is evaluated on the same original ambient state. -/
def productStageTestError (U V : Finset ι) (hUV : U ⊆ V)
    (L : CL.RegLinear F U) (ξ : H × K → ℂ)
    (M : POVM ((Fin (Fintype.card U) → F) × A) ((V → F) × H))
    (hM : IsPVM (fun p => (M.mats p).val))
    (BZ : POVM B ((ι → F) × K)) (BX : POVM C ((ι → F) × K))
    (fZ : B → ((Fin (Fintype.card U) → F) × A) × (Fin (Fintype.card U) → F))
    (fX : C → ((Fin (Fintype.card U) → F) × A) × (Fin (Fintype.card U) → F))
    (R : POVM (Fin (Fintype.card U) → F) ((ι → F) × K)) : ℝ :=
  (∑ y, xSqNorm (registerState (ι → F) ξ)
    (∑ a, ambientOperator V (M.mats (y, a)).val) (R.mats y).val) +
  (∑ y, xSqNorm (registerState (ι → F) ξ)
    (ambientReadout U V hUV wZ (coordinateLinear L) y) (R.mats y).val) +
  coarseJointLeftError (registerState (ι → F) ξ) (ambientProjectivePOVM V M hM) BZ fZ +
  coarseJointRightError (registerState (ι → F) ξ)
    (ambientReadoutPOVM U V hUV wZ isWeylFamily_wZ LinearMap.id) BZ fZ +
  coarseJointLeftError (registerState (ι → F) ξ) (ambientProjectivePOVM V M hM) BX fX +
  coarseJointRightError (registerState (ι → F) ξ)
    (ambientReadoutPOVM U V hUV wX isWeylFamily_wX (CL.lperp (coordinateLinear L))) BX fX

/-- All three analytic premises of mixing follow from the actual coarse joint
measurements and a common opposite-party sampling marginal. -/
theorem productStage_mixing_premises (U V : Finset ι) (hUV : U ⊆ V)
    (L : CL.RegLinear F U) (ξ : H × K → ℂ)
    (M : POVM ((Fin (Fintype.card U) → F) × A) ((V → F) × H))
    (hM : IsPVM (fun p => (M.mats p).val))
    (BZ : POVM B ((ι → F) × K)) (BX : POVM C ((ι → F) × K))
    (hBZ : IsPVM (fun b => (BZ.mats b).val))
    (hBX : IsPVM (fun b => (BX.mats b).val))
    (fZ : B → ((Fin (Fintype.card U) → F) × A) × (Fin (Fintype.card U) → F))
    (fX : C → ((Fin (Fintype.card U) → F) × A) × (Fin (Fintype.card U) → F))
    (R : POVM (Fin (Fintype.card U) → F) ((ι → F) × K)) :
    ambientMarginalError U V hUV L ξ (fun p => (M.mats p).val) ≤
        16 * productStageTestError U V hUV L ξ M hM BZ BX fZ fX R ∧
    ambientCommutatorError U V hUV ξ (fun p => (M.mats p).val) wZ LinearMap.id ≤
        16 * productStageTestError U V hUV L ξ M hM BZ BX fZ fX R ∧
    ambientCommutatorError U V hUV ξ (fun p => (M.mats p).val)
      wX (CL.lperp (coordinateLinear L)) ≤
        16 * productStageTestError U V hUV L ξ M hM BZ BX fZ fX R := by
  let ψ := registerState (ι → F) ξ
  let MA := ambientProjectivePOVM V M hM
  let Z := ambientReadoutPOVM (F := F) (H := H) U V hUV wZ isWeylFamily_wZ LinearMap.id
  let X := ambientReadoutPOVM (H := H) U V hUV wX isWeylFamily_wX
    (CL.lperp (coordinateLinear L))
  have hZ := coarse_joint_commutator_bound ψ MA Z BZ hBZ fZ
  have hX := coarse_joint_commutator_bound ψ MA X BX hBX fX
  have hMarg := same_side_via_common_other ψ
    (fun y => ∑ a, ambientOperator V (M.mats (y, a)).val)
    (ambientReadout U V hUV wZ (coordinateLinear L)) (fun y => (R.mats y).val)
  have hm₁ : 0 ≤ ∑ y, xSqNorm ψ
      (∑ a, ambientOperator V (M.mats (y, a)).val) (R.mats y).val :=
    Finset.sum_nonneg fun _ _ => xSqNorm_nonneg _ _ _
  have hm₂ : 0 ≤ ∑ y, xSqNorm ψ
      (ambientReadout U V hUV wZ (coordinateLinear L) y) (R.mats y).val :=
    Finset.sum_nonneg fun _ _ => xSqNorm_nonneg _ _ _
  have hz₁ := coarseJointLeftError_nonneg ψ MA BZ fZ
  have hz₂ := coarseJointRightError_nonneg ψ Z BZ fZ
  have hx₁ := coarseJointLeftError_nonneg ψ MA BX fX
  have hx₂ := coarseJointRightError_nonneg ψ X BX fX
  change ambientMarginalError U V hUV L ξ (fun p => (M.mats p).val) ≤ _ at hMarg
  change ambientCommutatorError U V hUV ξ (fun p => (M.mats p).val) wZ LinearMap.id ≤ _ at hZ
  change ambientCommutatorError U V hUV ξ (fun p => (M.mats p).val)
    wX (CL.lperp (coordinateLinear L)) ≤ _ at hX
  unfold productStageTestError
  change _ ≤ 16 * ((_ + _) + coarseJointLeftError ψ MA BZ fZ +
    coarseJointRightError ψ Z BZ fZ + coarseJointLeftError ψ MA BX fX +
    coarseJointRightError ψ X BX fX) ∧ _ ≤ _ ∧ _ ≤ _
  exact ⟨by linarith, by linarith, by linarith⟩

/-- **One product-form extraction stage.** The input consists of the actual
projective local measurement, two opposite-party projective measurements with
explicit coarse outcome maps, and the sampling marginal. Small average test
errors construct the next POVMs on exactly `V \ U` and the original ancilla.
Neither commutation nor the product-form conclusion is assumed. -/
theorem exists_product_stage_of_coarse_tests {J : Type*} [Fintype J]
    (D : J → ℝ) (hD0 : ∀ j, 0 ≤ D j) (hD1 : ∑ j, D j = 1)
    (U V : J → Finset ι) (hUV : ∀ j, U j ⊆ V j)
    (L : (j : J) → CL.RegLinear F (U j))
    (ξ : H × K → ℂ) (hξ : ‖evec ξ‖ = 1)
    (M : (j : J) → POVM ((Fin (Fintype.card (U j)) → F) × A) ((V j → F) × H))
    (hM : ∀ j, IsPVM (fun p => ((M j).mats p).val))
    (BZ : J → POVM B ((ι → F) × K)) (BX : J → POVM C ((ι → F) × K))
    (hBZ : ∀ j, IsPVM (fun b => ((BZ j).mats b).val))
    (hBX : ∀ j, IsPVM (fun b => ((BX j).mats b).val))
    (fZ : (j : J) → B →
      ((Fin (Fintype.card (U j)) → F) × A) × (Fin (Fintype.card (U j)) → F))
    (fX : (j : J) → C →
      ((Fin (Fintype.card (U j)) → F) × A) × (Fin (Fintype.card (U j)) → F))
    (R : (j : J) → POVM (Fin (Fintype.card (U j)) → F) ((ι → F) × K))
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : 16 * ε ≤ 1)
    (htests : ∑ j, D j * productStageTestError (U j) (V j) (hUV j)
      (L j) ξ (M j) (hM j) (BZ j) (BX j) (fZ j) (fX j) (R j) ≤ ε) :
    ∃ Q : (j : J) → (Fin (Fintype.card (U j)) → F) →
      POVM A ((↥(V j \ U j) → F) × H),
      (∑ j, D j * ∑ p : (Fin (Fintype.card (U j)) → F) × A,
        stateSqNorm (registerState (ι → F) ξ)
          (ambientOperator (V j) ((M j).mats p).val -
            ambientOperator (V j) (registerOp
              (registerParty (coordinateSplit (U j) (V j) (hUV j)) H)
              (synOf wZ (coordinateLinear (L j)) p.1 ⊗ₖ ((Q j p.1).mats p.2).val)))) ≤
        224 * Real.sqrt ε := by
  have hp j := productStage_mixing_premises (U j) (V j) (hUV j) (L j) ξ
    (M j) (hM j) (BZ j) (BX j) (hBZ j) (hBX j) (fZ j) (fX j) (R j)
  have hbudget : (∑ j, D j * (16 * productStageTestError (U j) (V j) (hUV j)
      (L j) ξ (M j) (hM j) (BZ j) (BX j) (fZ j) (fX j) (R j))) ≤ 16 * ε := by
    simpa only [mul_left_comm (b := (16 : ℝ)), ← Finset.mul_sum] using
      mul_le_mul_of_nonneg_left htests (by norm_num : (0 : ℝ) ≤ 16)
  obtain ⟨Q, hQ⟩ := exists_ambient_pauli_mixing D hD0 hD1 U V hUV L ξ hξ M hM
    (show 0 ≤ 16 * ε by positivity) hε1
    ((Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hp j).1 (hD0 j)).trans hbudget)
    ((Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hp j).2.1 (hD0 j)).trans hbudget)
    ((Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hp j).2.2 (hD0 j)).trans hbudget)
  refine ⟨Q, hQ.trans_eq ?_⟩
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)]
  rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
  ring

end Ambient

end MIPRE.Introspection

end

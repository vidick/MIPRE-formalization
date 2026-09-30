/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.AmbientMixing
public import MIPRE.Foundations.Introspection.HidingTests

@[expose] public section

/-! # One product-form induction step from the coarse joint measurements

The two commutators needed by Pauli mixing are derived from the tested
marginals of actual projective measurements on the other party. Coarse-graining
is performed before applying the commutation analysis. The error does not
depend on the size of a coarse-graining fibre.

The final theorem constructs the residual POVMs on `V \ U`, from averaged
cross-party errors on one ambient EPR state. Identifying these measurements
with the prefix-conditioned introspection strategy is a separate obligation.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`). The coarse joint measurement
is a projective measurement in the other player's algebra, and the ambient EPR state is the
register model `Ξ.reg (ι → F)`: a local measurement on `V` is a POVM of `V → F` block matrices over
the first player's algebra of `Ξ`, carried to the ambient register by `ambientOperator`, and the
residual POVMs are `V \ U → F` block matrices over that algebra, placed beside the selected Pauli
readout by `regSplitHom`.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Weyl Classical

set_option linter.unusedSectionVars false

section Coarse

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] (Ψ : BipartiteModel 𝒞 𝒜 ℬ)
variable {A C O : Type*} [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C] [Fintype O]

/-- Consistency with the first marginal of an actual coarse joint measurement. -/
def coarseJointLeftError (M : POVMIn A 𝒜) (B : POVMIn O ℬ) (f : O → A × C) : ℝ :=
  ∑ a, Ψ.xSqNorm (M.op a) (∑ c, (B.map f).op (a, c))

/-- Consistency with the second marginal of the same coarse joint measurement. -/
def coarseJointRightError (N : POVMIn C 𝒜) (B : POVMIn O ℬ) (f : O → A × C) : ℝ :=
  ∑ c, Ψ.xSqNorm (N.op c) (∑ a, (B.map f).op (a, c))

theorem coarseJointLeftError_nonneg (M : POVMIn A 𝒜) (B : POVMIn O ℬ) (f : O → A × C) :
    0 ≤ coarseJointLeftError Ψ M B f :=
  Finset.sum_nonneg fun _ _ => Ψ.xSqNorm_nonneg _ _

theorem coarseJointRightError_nonneg (N : POVMIn C 𝒜) (B : POVMIn O ℬ) (f : O → A × C) :
    0 ≤ coarseJointRightError Ψ N B f :=
  Finset.sum_nonneg fun _ _ => Ψ.xSqNorm_nonneg _ _

/-- The coarse joint measurement is used directly. In particular this theorem
does not coarse-grain an already established commutator estimate. -/
theorem coarse_joint_commutator_bound (M : POVMIn A 𝒜) (N : POVMIn C 𝒜) (B : POVMIn O ℬ)
    (hB : IsPVMIn B.op) (f : O → A × C) :
    (∑ a, ∑ c, Ψ.stateSqNorm (M.op a * N.op c - N.op c * M.op a)) ≤
      16 * (coarseJointLeftError Ψ M B f + coarseJointRightError Ψ N B f) := by
  have hBf : IsPVMIn (B.map f).op := by
    rw [show (B.map f).op = _ from funext (POVMIn.map_op f B)]
    exact hB.coarse f
  have h := Ψ.commutation_analysis (A := M) (Cm := N) hBf
    (δ := coarseJointLeftError Ψ M B f + coarseJointRightError Ψ N B f)
    (le_add_of_nonneg_right (coarseJointRightError_nonneg Ψ N B f))
    (le_add_of_nonneg_left (coarseJointLeftError_nonneg Ψ M B f))
  simpa only [Fintype.sum_prod_type] using h

end Coarse

section Ambient

variable {ι F A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A]
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [StarModule ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [StarModule ℂ ℬ]

/-- Embedding in the ambient register preserves the projective measurement. -/
theorem ambientOperator_isPVM (V : Finset ι)
    {M : A → Matrix (V → F) (V → F) 𝒜} (hM : IsPVMIn M) :
    IsPVMIn (fun a => ambientOperator V (M a)) :=
  hM.pushforward (regExtendHom_one (ambientSplit V))

/-- Projectivity of a selected linear Pauli readout in the original register. -/
theorem ambientReadout_isPVM (U V : Finset ι) (hUV : U ⊆ V)
    (w : (Fin (Fintype.card U) → F) →
      Matrix (Fin (Fintype.card U) → F) (Fin (Fintype.card U) → F) ℂ)
    (hw : IsWeylFamily w)
    (L : (Fin (Fintype.card U) → F) →ₗ[F] (Fin (Fintype.card U) → F)) :
    IsPVMIn (ambientReadout (𝒜 := 𝒜) U V hUV w L) := by
  have h : IsPVMIn fun y =>
      smulKron (1 : Matrix (↥(V \ U) → F) (↥(V \ U) → F) 𝒜) (synOf w L y) :=
    (linear_measurement_isPVM w hw L).toIn.smulKron_one
  exact ambientOperator_isPVM V (h.pushforward (regSplitHom_one (coordinateSplit U V hUV)))

variable [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarProper 𝒜]

/-- The actual ambient POVM of a projective local measurement. -/
def ambientProjectivePOVM (V : Finset ι) (M : POVMIn A (Matrix (V → F) (V → F) 𝒜))
    (hM : IsPVMIn M.op) : POVMIn A (Matrix (ι → F) (ι → F) 𝒜) :=
  (ambientOperator_isPVM V hM).toPOVMIn

@[simp] theorem ambientProjectivePOVM_mats (V : Finset ι)
    (M : POVMIn A (Matrix (V → F) (V → F) 𝒜)) (hM : IsPVMIn M.op) (a : A) :
    (ambientProjectivePOVM V M hM).op a = ambientOperator V (M.op a) := rfl

/-- The selected Pauli readout as a normalized positive measurement. -/
def ambientReadoutPOVM (U V : Finset ι) (hUV : U ⊆ V)
    (w : (Fin (Fintype.card U) → F) →
      Matrix (Fin (Fintype.card U) → F) (Fin (Fintype.card U) → F) ℂ)
    (hw : IsWeylFamily w)
    (L : (Fin (Fintype.card U) → F) →ₗ[F] (Fin (Fintype.card U) → F)) :
    POVMIn (Fin (Fintype.card U) → F) (Matrix (ι → F) (ι → F) 𝒜) :=
  (ambientReadout_isPVM U V hUV w hw L).toPOVMIn

@[simp] theorem ambientReadoutPOVM_mats (U V : Finset ι) (hUV : U ⊆ V)
    (w : (Fin (Fintype.card U) → F) →
      Matrix (Fin (Fintype.card U) → F) (Fin (Fintype.card U) → F) ℂ)
    (hw : IsWeylFamily w)
    (L : (Fin (Fintype.card U) → F) →ₗ[F] (Fin (Fintype.card U) → F))
    (y : Fin (Fintype.card U) → F) :
    (ambientReadoutPOVM (𝒜 := 𝒜) U V hUV w hw L).op y = ambientReadout U V hUV w L y := rfl

variable [PartialOrder ℬ] [StarOrderedRing ℬ] [StarProper ℬ]
variable {B C : Type*} [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

/-- The six cross-party errors used in one product-form stage: two sampling
marginal comparisons, and the two marginal comparisons for each coarse joint
measurement. Every summand is evaluated on the same original ambient state. -/
def productStageTestError (U V : Finset ι) (hUV : U ⊆ V)
    (L : CL.RegLinear F U) (Ξ : BipartiteModel 𝒞 𝒜 ℬ)
    (M : POVMIn ((Fin (Fintype.card U) → F) × A) (Matrix (V → F) (V → F) 𝒜))
    (hM : IsPVMIn M.op)
    (BZ : POVMIn B (Matrix (ι → F) (ι → F) ℬ)) (BX : POVMIn C (Matrix (ι → F) (ι → F) ℬ))
    (fZ : B → ((Fin (Fintype.card U) → F) × A) × (Fin (Fintype.card U) → F))
    (fX : C → ((Fin (Fintype.card U) → F) × A) × (Fin (Fintype.card U) → F))
    (R : POVMIn (Fin (Fintype.card U) → F) (Matrix (ι → F) (ι → F) ℬ)) : ℝ :=
  (∑ y, (Ξ.reg (ι → F)).xSqNorm (∑ a, ambientOperator V (M.op (y, a))) (R.op y)) +
  (∑ y, (Ξ.reg (ι → F)).xSqNorm
    (ambientReadout U V hUV wZ (coordinateLinear L) y) (R.op y)) +
  coarseJointLeftError (Ξ.reg (ι → F)) (ambientProjectivePOVM V M hM) BZ fZ +
  coarseJointRightError (Ξ.reg (ι → F))
    (ambientReadoutPOVM U V hUV wZ isWeylFamily_wZ LinearMap.id) BZ fZ +
  coarseJointLeftError (Ξ.reg (ι → F)) (ambientProjectivePOVM V M hM) BX fX +
  coarseJointRightError (Ξ.reg (ι → F))
    (ambientReadoutPOVM U V hUV wX isWeylFamily_wX (CL.lperp (coordinateLinear L))) BX fX

/-- All three analytic premises of mixing follow from the actual coarse joint
measurements and a common opposite-party sampling marginal. -/
theorem productStage_mixing_premises (U V : Finset ι) (hUV : U ⊆ V)
    (L : CL.RegLinear F U) (Ξ : BipartiteModel 𝒞 𝒜 ℬ)
    (M : POVMIn ((Fin (Fintype.card U) → F) × A) (Matrix (V → F) (V → F) 𝒜))
    (hM : IsPVMIn M.op)
    (BZ : POVMIn B (Matrix (ι → F) (ι → F) ℬ)) (BX : POVMIn C (Matrix (ι → F) (ι → F) ℬ))
    (hBZ : IsPVMIn BZ.op) (hBX : IsPVMIn BX.op)
    (fZ : B → ((Fin (Fintype.card U) → F) × A) × (Fin (Fintype.card U) → F))
    (fX : C → ((Fin (Fintype.card U) → F) × A) × (Fin (Fintype.card U) → F))
    (R : POVMIn (Fin (Fintype.card U) → F) (Matrix (ι → F) (ι → F) ℬ)) :
    ambientMarginalError U V hUV L Ξ M.op ≤
        16 * productStageTestError U V hUV L Ξ M hM BZ BX fZ fX R ∧
    ambientCommutatorError U V hUV Ξ M.op wZ LinearMap.id ≤
        16 * productStageTestError U V hUV L Ξ M hM BZ BX fZ fX R ∧
    ambientCommutatorError U V hUV Ξ M.op wX (CL.lperp (coordinateLinear L)) ≤
        16 * productStageTestError U V hUV L Ξ M hM BZ BX fZ fX R := by
  let Ψ := Ξ.reg (ι → F)
  let MA := ambientProjectivePOVM V M hM
  let Z := ambientReadoutPOVM (F := F) (𝒜 := 𝒜) U V hUV wZ isWeylFamily_wZ LinearMap.id
  let X := ambientReadoutPOVM (𝒜 := 𝒜) U V hUV wX isWeylFamily_wX
    (CL.lperp (coordinateLinear L))
  have hZ := coarse_joint_commutator_bound Ψ MA Z BZ hBZ fZ
  have hX := coarse_joint_commutator_bound Ψ MA X BX hBX fX
  have hMarg := same_side_via_common_other Ψ
    (fun y => ∑ a, ambientOperator V (M.op (y, a)))
    (ambientReadout U V hUV wZ (coordinateLinear L)) (fun y => R.op y)
  have hm₁ : 0 ≤ ∑ y, Ψ.xSqNorm (∑ a, ambientOperator V (M.op (y, a))) (R.op y) :=
    Finset.sum_nonneg fun _ _ => Ψ.xSqNorm_nonneg _ _
  have hm₂ : 0 ≤ ∑ y, Ψ.xSqNorm (ambientReadout U V hUV wZ (coordinateLinear L) y) (R.op y) :=
    Finset.sum_nonneg fun _ _ => Ψ.xSqNorm_nonneg _ _
  have hz₁ := coarseJointLeftError_nonneg Ψ MA BZ fZ
  have hz₂ := coarseJointRightError_nonneg Ψ Z BZ fZ
  have hx₁ := coarseJointLeftError_nonneg Ψ MA BX fX
  have hx₂ := coarseJointRightError_nonneg Ψ X BX fX
  change ambientMarginalError U V hUV L Ξ M.op ≤ _ at hMarg
  change ambientCommutatorError U V hUV Ξ M.op wZ LinearMap.id ≤ _ at hZ
  change ambientCommutatorError U V hUV Ξ M.op wX (CL.lperp (coordinateLinear L)) ≤ _ at hX
  unfold productStageTestError
  change _ ≤ 16 * ((_ + _) + coarseJointLeftError Ψ MA BZ fZ +
    coarseJointRightError Ψ Z BZ fZ + coarseJointLeftError Ψ MA BX fX +
    coarseJointRightError Ψ X BX fX) ∧ _ ≤ _ ∧ _ ≤ _
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
    (Ξ : BipartiteModel 𝒞 𝒜 ℬ) (hΞ : ‖Ξ.ψ‖ = 1)
    (M : (j : J) → POVMIn ((Fin (Fintype.card (U j)) → F) × A)
      (Matrix (V j → F) (V j → F) 𝒜))
    (hM : ∀ j, IsPVMIn (M j).op)
    (BZ : J → POVMIn B (Matrix (ι → F) (ι → F) ℬ))
    (BX : J → POVMIn C (Matrix (ι → F) (ι → F) ℬ))
    (hBZ : ∀ j, IsPVMIn (BZ j).op)
    (hBX : ∀ j, IsPVMIn (BX j).op)
    (fZ : (j : J) → B →
      ((Fin (Fintype.card (U j)) → F) × A) × (Fin (Fintype.card (U j)) → F))
    (fX : (j : J) → C →
      ((Fin (Fintype.card (U j)) → F) × A) × (Fin (Fintype.card (U j)) → F))
    (R : (j : J) → POVMIn (Fin (Fintype.card (U j)) → F) (Matrix (ι → F) (ι → F) ℬ))
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : 16 * ε ≤ 1)
    (htests : ∑ j, D j * productStageTestError (U j) (V j) (hUV j)
      (L j) Ξ (M j) (hM j) (BZ j) (BX j) (fZ j) (fX j) (R j) ≤ ε) :
    ∃ Q : (j : J) → (Fin (Fintype.card (U j)) → F) →
        POVMIn A (Matrix (↥(V j \ U j) → F) (↥(V j \ U j) → F) 𝒜),
      (∑ j, D j * ∑ p : (Fin (Fintype.card (U j)) → F) × A,
        (Ξ.reg (ι → F)).stateSqNorm
          (ambientOperator (V j) ((M j).op p) -
            ambientOperator (V j) (regSplitHom (coordinateSplit (U j) (V j) (hUV j))
              (smulKron ((Q j p.1).op p.2) (synOf wZ (coordinateLinear (L j)) p.1))))) ≤
        224 * Real.sqrt ε := by
  have hp j := productStage_mixing_premises (U j) (V j) (hUV j) (L j) Ξ
    (M j) (hM j) (BZ j) (BX j) (hBZ j) (hBX j) (fZ j) (fX j) (R j)
  have hbudget : (∑ j, D j * (16 * productStageTestError (U j) (V j) (hUV j)
      (L j) Ξ (M j) (hM j) (BZ j) (BX j) (fZ j) (fX j) (R j))) ≤ 16 * ε := by
    simpa only [mul_left_comm (b := (16 : ℝ)), ← Finset.mul_sum] using
      mul_le_mul_of_nonneg_left htests (by norm_num : (0 : ℝ) ≤ 16)
  obtain ⟨Q, hQ⟩ := exists_ambient_pauli_mixing D hD0 hD1 U V hUV L Ξ hΞ M hM
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

end

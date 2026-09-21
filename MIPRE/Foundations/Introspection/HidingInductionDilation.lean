/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.RegisterEPR
import MIPRE.Foundations.Introspection.ValueStability

/-! # Projectivizing a conditional residual measurement

One fixed ancilla is added on the residual side of every prefix. The prefix
projectors are unchanged. Squared distance to the old projective measurement
costs `2 sqrt(delta)`; a dilation does not in general preserve that distance.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder

set_option linter.unusedSectionVars false

section Distance

variable {H K A T : Type*}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype A] [DecidableEq A] [Fintype T] [DecidableEq T]

/-- The one-party fixed-ancilla embedding changes no Born probability after
compressing the measured operator. -/
theorem bornProb_extVecA (ψ : H × K → ℂ) (a₀ : T)
    (P : Matrix (H × T) (H × T) ℂ) (B : Matrix K K ℂ) :
    bornProb (extVecA ψ a₀) P B =
      bornProb ψ ((ancillaEmbed H a₀)ᴴ * (P * ancillaEmbed H a₀)) B := by
  rw [bornProb, bornProb, extVecA, dotProduct_mulVec_conj]
  congr 2
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.mul_one, Matrix.one_mul]

/-- Coordinate formula for adding the same fixed ancilla to every question. -/
theorem extVecA_apply (ψ : H × K → ℂ) (a₀ : T) (h : H) (a : T) (k : K) :
    extVecA ψ a₀ ((h, a), k) = if a = a₀ then ψ (h, k) else 0 := by
  classical
  simp [extVecA, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, ancillaEmbed, Matrix.one_apply, Prod.mk.injEq]
  by_cases ha : a = a₀ <;> simp [ha]

/-- Extending an old operator by identity preserves its state norm exactly. -/
theorem stateSqNorm_extVecA_aOp (ψ : H × K → ℂ) (a₀ : T) (M : Matrix H H ℂ) :
    stateSqNorm (extVecA ψ a₀) (aOp M) = stateSqNorm ψ M := by
  rw [stateSqNorm_eq_qform, aOp_conjTranspose, ← aOp_mul,
    qform_extVecA, compress_aOp, ← stateSqNorm_eq_qform]

/-- A fixed-state projective dilation remains close to an old PVM. The bound
is uniform over every dilation with the displayed compression identity. -/
theorem dilated_pvm_distance (ψ : H × K → ℂ) (hψ : ‖evec ψ‖ = 1) (a₀ : T)
    (M R : A → Matrix H H ℂ) (P : A → Matrix (H × T) (H × T) ℂ)
    (hM : IsPVM M) (hP : IsPVM P)
    (hk : ∀ a, (ancillaEmbed H a₀)ᴴ * (P a * ancillaEmbed H a₀) = R a)
    {δ : ℝ} (hd : ∑ a, stateSqNorm ψ (M a - R a) ≤ δ) :
    (∑ a, stateSqNorm (extVecA ψ a₀) (aOp (M a) - P a)) ≤ 2 * Real.sqrt δ := by
  have hsumR : ∑ a, R a = 1 := by
    simp_rw [← hk]
    rw [← Matrix.mul_sum, ← Matrix.sum_mul, hP.sum_eq_one, Matrix.one_mul,
      ancillaEmbed_isometry]
  have hexp a : stateSqNorm (extVecA ψ a₀) (aOp (M a) - P a) =
      qform ψ (aOp (M a)) + qform ψ (aOp (R a)) -
        2 * qform ψ (aOp (M a * R a)) := by
    have hsym : qform (extVecA ψ a₀) (aOp (P a * aOp (M a))) =
        qform (extVecA ψ a₀) (aOp (aOp (M a) * P a)) := by
      rw [← qform_conjTranspose _ (aOp (aOp (M a) * P a)),
        aOp_conjTranspose, Matrix.conjTranspose_mul, hP.isSelfAdjoint,
        aOp_conjTranspose, hM.isSelfAdjoint]
    rw [stateSqNorm_eq_qform, Matrix.conjTranspose_sub, aOp_conjTranspose,
      hM.isSelfAdjoint, hP.isSelfAdjoint, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_sub, ← aOp_mul, hM.idem, hP.idem,
      aOp_sub, aOp_sub, aOp_sub, qform_sub, qform_sub, qform_sub, hsym]
    have hc : (ancillaEmbed H a₀)ᴴ * (aOp (M a) * P a * ancillaEmbed H a₀) = M a * R a := by
      rw [aOp, compress_kron_one_mul, hk]
    simp only [qform_extVecA, compress_aOp, hk, hc]
    ring
  have hsum : (∑ a, stateSqNorm (extVecA ψ a₀) (aOp (M a) - P a)) =
      2 * ∑ a, qform ψ (aOp (M a * (M a - R a))) := by
    simp_rw [hexp, Matrix.mul_sub, hM.idem, aOp_sub, qform_sub]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_sub_distrib, ← qform_sum, ← qform_sum, ← aOp_sum,
      ← aOp_sum, hM.sum_eq_one, hsumR]
    ring
  have hmass : (∑ a, snorm ψ (aOp (M a) : Matrix (H × K) _ ℂ) ^ 2) = 1 := by
    simp_rw [snorm_sq_eq_qform, aOp_conjTranspose, ← aOp_mul, hM.isSelfAdjoint, hM.idem]
    rw [← qform_sum, ← aOp_sum, hM.sum_eq_one, aOp_one, qform_one ψ hψ]
  have hcs := abs_sum_qform_mul_le ψ univ
    (fun a => (aOp (M a) : Matrix (H × K) _ ℂ))
    (fun a => (aOp (M a - R a) : Matrix (H × K) _ ℂ))
    (fun a => by rw [aOp_conjTranspose, hM.isSelfAdjoint])
  rw [hmass, Real.sqrt_one, one_mul] at hcs
  simp only [← aOp_mul] at hcs
  have hδ : (∑ a, snorm ψ (aOp (M a - R a) : Matrix (H × K) _ ℂ) ^ 2) ≤ δ := hd
  rw [hsum]
  exact mul_le_mul_of_nonneg_left
    ((le_abs_self _).trans (hcs.trans (Real.sqrt_le_sqrt hδ))) (by norm_num)

end Distance

section Conditional

variable {I H K Y A J : Type*}
  [Fintype I] [DecidableEq I] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K] [Fintype Y] [DecidableEq Y]
  [Fintype A] [DecidableEq A] [Fintype J]

/-- Compression to a fixed ancilla slice is literally the corresponding
matrix subblock. -/
theorem ancilla_compress_apply (a₀ : A) (M : Matrix (H × A) (H × A) ℂ) (i j : H) :
    ((ancillaEmbed H a₀)ᴴ * (M * ancillaEmbed H a₀)) i j = M (i, a₀) (j, a₀) := by
  simp [Matrix.mul_apply, ancillaEmbed, Matrix.conjTranspose_apply]

/-- Keep the prefix register outside the new ancilla, in the original party
ordering `(prefix × residual) × ancilla`. -/
def conditionalDilationOp (Z : Y → Matrix I I ℂ)
    (P : Y → A → Matrix (H × A) (H × A) ℂ) (p : Y × A) :
    Matrix ((I × H) × A) ((I × H) × A) ℂ :=
  registerOp (Equiv.prodAssoc I H A) (Z p.1 ⊗ₖ P p.1 p.2)

/-- Conditional projective residual measurements keep the joint measurement
projective while leaving every prefix projector untouched. -/
theorem conditionalDilationOp_isPVM (Z : Y → Matrix I I ℂ) (hZ : IsPVM Z)
    (P : Y → A → Matrix (H × A) (H × A) ℂ) (hP : ∀ y, IsPVM (P y)) :
    IsPVM (conditionalDilationOp Z P) := by
  apply registerOp_isPVM
  refine ⟨fun p => ?_, fun p => ?_, ?_⟩
  · rw [Matrix.conjTranspose_kronecker, hZ.isSelfAdjoint, (hP _).isSelfAdjoint]
  · rw [← Matrix.mul_kronecker_mul, hZ.idem, (hP _).idem]
  · rw [Fintype.sum_prod_type]
    simp_rw [← kronecker_sum_right, (hP _).sum_eq_one]
    rw [← sum_kronecker_left, hZ.sum_eq_one, Matrix.one_kronecker_one]

/-- The full conditional dilation compresses to the desired prefix times
residual POVM, using the same embedding for every prefix and outcome. -/
theorem conditionalDilationOp_compress (a₀ : A) (Z : Y → Matrix I I ℂ)
    (P : Y → A → Matrix (H × A) (H × A) ℂ)
    (R : Y → A → Matrix H H ℂ)
    (hk : ∀ y a, (ancillaEmbed H a₀)ᴴ * (P y a * ancillaEmbed H a₀) = R y a)
    (p : Y × A) :
    (ancillaEmbed (I × H) a₀)ᴴ *
      (conditionalDilationOp Z P p * ancillaEmbed (I × H) a₀) = Z p.1 ⊗ₖ R p.1 p.2 := by
  ext i j
  rw [ancilla_compress_apply]
  change Z p.1 i.1 j.1 * P p.1 p.2 (i.2, a₀) (j.2, a₀) =
    Z p.1 i.1 j.1 * R p.1 p.2 i.2 j.2
  rw [← ancilla_compress_apply a₀ (P p.1 p.2) i.2 j.2, hk]

/-- The conditional product form has exactly the original outcome
probabilities against every measurement on the other party. -/
theorem conditionalDilationOp_born (ψ : (I × H) × K → ℂ) (a₀ : A)
    (Z : Y → Matrix I I ℂ) (P : Y → A → Matrix (H × A) (H × A) ℂ)
    (R : Y → A → Matrix H H ℂ)
    (hk : ∀ y a, (ancillaEmbed H a₀)ᴴ * (P y a * ancillaEmbed H a₀) = R y a)
    (p : Y × A) (B : Matrix K K ℂ) :
    bornProb (extVecA ψ a₀) (conditionalDilationOp Z P p) B =
      bornProb ψ (Z p.1 ⊗ₖ R p.1 p.2) B := by
  rw [bornProb_extVecA, conditionalDilationOp_compress a₀ Z P R hk]

/-- Dilation changes only the auxiliary state, after the explicit party
reassociation. The original EPR factor is kept exactly. -/
theorem extVecA_registerState (ξ : H × K → ℂ) (a₀ : A) :
    extVecA (registerState I ξ) a₀ =
      registerState I (extVecA ξ a₀) ∘
        (Equiv.prodAssoc I H A).prodCongr (Equiv.refl (I × K)) := by
  funext p
  rcases p with ⟨⟨⟨i, h⟩, a⟩, j, k⟩
  simp only [extVecA_apply, registerState, expVec, Function.comp_apply,
    Equiv.prodCongr_apply, Equiv.prodAssoc_apply, Equiv.refl_apply, Prod.map_fst, Prod.map_snd]
  split_ifs <;> simp

/-- **Common-ancilla conditional projectivization.** All residual POVMs in a
question/prefix family are dilated with one fixed ancilla state. The resulting
joint PVMs retain the displayed prefix projectors and are quantitatively close
to the old projective family on the one extended state. -/
theorem exists_conditional_projective_dilation
    (ψ : (I × H) × K → ℂ) (hψ : ‖evec ψ‖ = 1) (a₀ : A)
    (D : J → ℝ) (hD0 : ∀ j, 0 ≤ D j) (hD1 : ∑ j, D j = 1)
    (Z : J → Y → Matrix I I ℂ) (hZ : ∀ j, IsPVM (Z j))
    (Q : J → Y → POVM A H)
    (M : J → Y × A → Matrix (I × H) (I × H) ℂ) (hM : ∀ j, IsPVM (M j))
    {δ : ℝ} (hd : ∑ j, D j * ∑ p : Y × A,
      stateSqNorm ψ (M j p - Z j p.1 ⊗ₖ ((Q j p.1).mats p.2).val) ≤ δ) :
    ∃ P : J → Y → A → Matrix (H × A) (H × A) ℂ,
      (∀ j y, IsPVM (P j y)) ∧
      (∀ j y a, (ancillaEmbed H a₀)ᴴ * (P j y a * ancillaEmbed H a₀) =
        ((Q j y).mats a).val) ∧
      (∀ j, IsPVM (conditionalDilationOp (Z j) (P j))) ∧
      (∀ j p, (ancillaEmbed (I × H) a₀)ᴴ *
        (conditionalDilationOp (Z j) (P j) p * ancillaEmbed (I × H) a₀) =
          Z j p.1 ⊗ₖ ((Q j p.1).mats p.2).val) ∧
      (∑ j, D j * ∑ p : Y × A,
        stateSqNorm (extVecA ψ a₀) (aOp (M j p) - conditionalDilationOp (Z j) (P j) p)) ≤
          2 * Real.sqrt δ := by
  obtain ⟨P, hsa, hid, hsum, hk⟩ := exists_projective_dilation
    (d := H) (A := A) (X := J × Y) a₀
    (E := fun jy a => ((Q jy.1 jy.2).mats a).val)
    (fun jy a => (Q jy.1 jy.2).posSemidef a) (fun jy => POVM.sum_val (Q jy.1 jy.2))
  let P' j y a := P (j, y) a
  have hP' j y : IsPVM (P' j y) :=
    ⟨fun a => by rw [← Matrix.star_eq_conjTranspose]; exact hsa (j, y) a,
      hid (j, y), hsum (j, y)⟩
  have hjoint j := conditionalDilationOp_isPVM (Z j) (hZ j) (P' j) (hP' j)
  have hcompress j p := conditionalDilationOp_compress a₀ (Z j) (P' j)
    (fun y a => ((Q j y).mats a).val) (fun y a => hk (j, y) a) p
  refine ⟨P', hP', fun j y a => hk (j, y) a, hjoint, hcompress, ?_⟩
  let err j := ∑ p : Y × A,
    stateSqNorm ψ (M j p - Z j p.1 ⊗ₖ ((Q j p.1).mats p.2).val)
  have herr j : 0 ≤ err j := Finset.sum_nonneg fun _ _ => stateSqNorm_nonneg _ _
  have hpoint j := dilated_pvm_distance ψ hψ a₀ (M j)
    (fun p => Z j p.1 ⊗ₖ ((Q j p.1).mats p.2).val)
    (conditionalDilationOp (Z j) (P' j)) (hM j) (hjoint j) (hcompress j) (δ := err j) le_rfl
  calc
    _ ≤ ∑ j, D j * (2 * Real.sqrt (err j)) :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hpoint j) (hD0 j)
    _ = 2 * ∑ j, D j * Real.sqrt (err j) := by
      simp only [mul_left_comm (b := (2 : ℝ)), ← Finset.mul_sum]
    _ ≤ 2 * Real.sqrt δ := mul_le_mul_of_nonneg_left
      ((sum_weighted_sqrt_le D err hD0 hD1 herr).trans (Real.sqrt_le_sqrt hd)) (by norm_num)

end Conditional

section Varying

variable {J A : Type*} [Fintype J] [Fintype A] [DecidableEq A]
  {I H K Y : J → Type*}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (H j)] [∀ j, DecidableEq (H j)]
  [∀ j, Fintype (K j)] [∀ j, DecidableEq (K j)]
  [∀ j, Fintype (Y j)] [∀ j, DecidableEq (Y j)]

/-- **Conditional projectivization with varying local registers.** The prefix,
residual and other-party carriers may all depend on the conditioned question.
The added ancilla still has the single outcome type `A` and fixed state `a₀`.
The caller supplies the local states arising from its register transports;
there is no assumption that different prefixes have the same residual dimension. -/
theorem exists_varying_conditional_projective_dilation
    (ψ : (j : J) → (I j × H j) × K j → ℂ) (hψ : ∀ j, ‖evec (ψ j)‖ = 1) (a₀ : A)
    (D : J → ℝ) (hD0 : ∀ j, 0 ≤ D j) (hD1 : ∑ j, D j = 1)
    (Z : (j : J) → Y j → Matrix (I j) (I j) ℂ) (hZ : ∀ j, IsPVM (Z j))
    (Q : (j : J) → Y j → POVM A (H j))
    (M : (j : J) → Y j × A → Matrix (I j × H j) (I j × H j) ℂ)
    (hM : ∀ j, IsPVM (M j))
    {δ : ℝ} (hd : ∑ j, D j * ∑ p : Y j × A,
      stateSqNorm (ψ j) (M j p - Z j p.1 ⊗ₖ ((Q j p.1).mats p.2).val) ≤ δ) :
    ∃ P : (j : J) → Y j → A → Matrix (H j × A) (H j × A) ℂ,
      (∀ j y, IsPVM (P j y)) ∧
      (∀ j y a, (ancillaEmbed (H j) a₀)ᴴ * (P j y a * ancillaEmbed (H j) a₀) =
        ((Q j y).mats a).val) ∧
      (∀ j, IsPVM (conditionalDilationOp (Z j) (P j))) ∧
      (∀ j p, (ancillaEmbed (I j × H j) a₀)ᴴ *
        (conditionalDilationOp (Z j) (P j) p * ancillaEmbed (I j × H j) a₀) =
          Z j p.1 ⊗ₖ ((Q j p.1).mats p.2).val) ∧
      (∑ j, D j * ∑ p : Y j × A,
        stateSqNorm (extVecA (ψ j) a₀)
          (aOp (M j p) - conditionalDilationOp (Z j) (P j) p)) ≤ 2 * Real.sqrt δ := by
  let err j := ∑ p : Y j × A,
    stateSqNorm (ψ j) (M j p - Z j p.1 ⊗ₖ ((Q j p.1).mats p.2).val)
  have herr j : 0 ≤ err j := Finset.sum_nonneg fun _ _ => stateSqNorm_nonneg _ _
  have hlocal j : ∃ P : Y j → A → Matrix (H j × A) (H j × A) ℂ,
      (∀ y, IsPVM (P y)) ∧
      (∀ y a, (ancillaEmbed (H j) a₀)ᴴ * (P y a * ancillaEmbed (H j) a₀) =
        ((Q j y).mats a).val) ∧
      IsPVM (conditionalDilationOp (Z j) P) ∧
      (∀ p, (ancillaEmbed (I j × H j) a₀)ᴴ *
        (conditionalDilationOp (Z j) P p * ancillaEmbed (I j × H j) a₀) =
          Z j p.1 ⊗ₖ ((Q j p.1).mats p.2).val) ∧
      (∑ p : Y j × A, stateSqNorm (extVecA (ψ j) a₀)
        (aOp (M j p) - conditionalDilationOp (Z j) P p)) ≤ 2 * Real.sqrt (err j) := by
    obtain ⟨P, hp, hk, hjoint, hfull, hdist⟩ :=
      exists_conditional_projective_dilation (J := Unit) (ψ j) (hψ j) a₀
        (fun _ => 1) (fun _ => zero_le_one) (by simp)
        (fun _ => Z j) (fun _ => hZ j) (fun _ => Q j)
        (fun _ => M j) (fun _ => hM j) (δ := err j) (by simp [err])
    refine ⟨P (), hp (), hk (), hjoint (), hfull (), ?_⟩
    simpa only [Fintype.sum_unique, one_mul] using hdist
  choose P hp hk hjoint hfull hdist using hlocal
  refine ⟨P, hp, hk, hjoint, hfull, ?_⟩
  calc
    _ ≤ ∑ j, D j * (2 * Real.sqrt (err j)) :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hdist j) (hD0 j)
    _ = 2 * ∑ j, D j * Real.sqrt (err j) := by
      simp only [mul_left_comm (b := (2 : ℝ)), ← Finset.mul_sum]
    _ ≤ 2 * Real.sqrt δ := mul_le_mul_of_nonneg_left
      ((sum_weighted_sqrt_le D err hD0 hD1 herr).trans (Real.sqrt_le_sqrt hd)) (by norm_num)

end Varying

end MIPRE.Introspection

end

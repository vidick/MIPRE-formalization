/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AdaptivePrefixAdvance
import MIPRE.Foundations.Introspection.AdaptivePrefixReplacement

/-! # Exact next-prefix factorization of the adaptive replacement

The old prefix and current Z projector combine into the actual next prefix
projector. The remaining coordinates are transported by their proved set
equality, with the same auxiliary space for every branch.
-/

noncomputable section
namespace MIPRE.Introspection
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false

variable {ι F H A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype H] [DecidableEq H] [Fintype A] [DecidableEq A] {ℓ : ℕ}

/-- Transport an assignment between literally equal coordinate subsets. -/
def registerSetEquiv {S T : Finset ι} (h : S = T) : (S → F) ≃ (T → F) where
  toFun x i := x ⟨i, h.symm ▸ i.property⟩
  invFun x i := x ⟨i, h ▸ i.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem nextRemaining_eq (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (y : ι → F) (z : Fin (Fintype.card (P.factorOfPrefix k y)) → F) :
    stageRemaining P (k + 1) (advancePrefix P k y z) =
      stageRemaining P k y \ P.factorOfPrefix k y :=
  (advancePrefix_remaining hP k y z).trans (stageRemaining_step P k y).symm

/-- Pull the dilated remaining operator into the actual next-prefix carrier. -/
def nextResidualOp (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (y : ι → F) (z : Fin (Fintype.card (P.factorOfPrefix k y)) → F)
    (N : Matrix (((↥(stageRemaining P k y \ P.factorOfPrefix k y) → F) × H) × A)
      (((↥(stageRemaining P k y \ P.factorOfPrefix k y) → F) × H) × A) ℂ) :
    Matrix ((stageRemaining P (k + 1) (advancePrefix P k y z) → F) × (H × A))
      ((stageRemaining P (k + 1) (advancePrefix P k y z) → F) × (H × A)) ℂ :=
  registerOp ((registerSetEquiv (F := F) (nextRemaining_eq P hP k y z)).prodCongr
    (Equiv.refl (H × A))) (registerOp (Equiv.prodAssoc _ H A).symm N)

theorem nextResidualOp_isPVM (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (y : ι → F) (z : Fin (Fintype.card (P.factorOfPrefix k y)) → F)
    (N : A → Matrix (((↥(stageRemaining P k y \ P.factorOfPrefix k y) → F) × H) × A) _ ℂ)
    (hN : IsPVM N) : IsPVM (nextResidualOp P hP k y z ∘ N) :=
  registerOp_isPVM _ (registerOp_isPVM _ hN)

theorem advancePrefix_fibre (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (y : ι → F) (hy : y ∈ prefixOutcomes P k)
    (z : Fin (Fintype.card (P.factorOfPrefix k y)) → F) (x : ι → F) :
    (P.truncate (k + 1)).eval x = advancePrefix P k y z ↔
      adaptiveLinearOutcome P k x = ⟨y, z⟩ := by
  constructor
  · intro hx
    have hi := advancePrefix_injective hP k
      (a₁ := ⟨⟨(P.truncate k).eval x, mem_image.mpr ⟨x, mem_univ _, rfl⟩⟩,
        (adaptiveLinearOutcome P k x).2⟩)
      (a₂ := ⟨⟨y, hy⟩, z⟩) ((advancePrefix_eval hP k x).trans hx)
    exact congrArg
      (fun p : (v : ↥(prefixOutcomes P k)) ×
          (Fin (Fintype.card (P.factorOfPrefix k v)) → F) =>
        (⟨p.1.val, p.2⟩ : (v : ι → F) ×
          (Fin (Fintype.card (P.factorOfPrefix k v)) → F))) hi
  · intro hx
    rw [← advancePrefix_adaptiveLinearOutcome hP k x, hx]

set_option backward.isDefEq.respectTransparency false in
theorem prefixResidualOp_apply (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (y : ι → F)
    (M : Matrix ((stageRemaining P k y → F) × H) _ ℂ)
    (x x' : ι → F) (a a' : H) :
    prefixResidualOp P k y M (x, a) (x', a') =
      if (∀ i ∈ CLChecks.prefixRegister P k y, x i = x' i) ∧ (P.truncate k).eval x = y then
        M (fun i => x i, a) (fun i => x' i, a') else 0 := by
  have he : (fun i : CLChecks.prefixRegister P k y => x i) =
      (fun i : CLChecks.prefixRegister P k y => x' i) ↔
      ∀ i ∈ CLChecks.prefixRegister P k y, x i = x' i := by
    constructor
    · intro h i hi; exact congrFun h ⟨i, hi⟩
    · intro h; funext i; exact h i i.property
  have hf := CLChecks.truncate_fibre_proj hP k y x
  rw [← Honest.insertRegister_ambientSplit] at hf
  unfold prefixResidualOp Honest.prefixProjector
  simp only [registerOp_apply, registerParty, Equiv.trans_apply,
    Equiv.prodCongr_apply, Equiv.prodAssoc_apply, ambientSplit,
    Matrix.kroneckerMap_apply, readout, Matrix.diagonal_apply]
  change (if (fun i : CLChecks.prefixRegister P k y => x i) =
    (fun i : CLChecks.prefixRegister P k y => x' i) then
    (if (P.truncate k).eval (Honest.insertRegister _ (fun i => x i)) = y then 1 else 0)
    else 0) * _ = _
  simp only [he, ← hf]
  split_ifs <;> simp_all

theorem adaptiveLinearOutcome_eq_iff (P : CL.CLFun F ι ℓ) (k : ℕ)
    (y : ι → F) (z : Fin (Fintype.card (P.factorOfPrefix k y)) → F) (x : ι → F) :
    adaptiveLinearOutcome P k x = ⟨y, z⟩ ↔
      (P.truncate k).eval x = y ∧
        coordinateLinear (CLChecks.stageLinear P k y)
          (coordinateRestrict (P.factorOfPrefix k y) x) = z := by
  by_cases hy : (P.truncate k).eval x = y
  · subst y
    simp only [adaptiveLinearOutcome, Sigma.mk.inj_iff, heq_eq_eq, true_and]
  · have hn : adaptiveLinearOutcome P k x ≠ ⟨y, z⟩ := by
      intro h; exact hy (congrArg Sigma.fst h)
    simp [hn, hy]

theorem coordinateRestrict_eq_iff (S : Finset ι) (x x' : ι → F) :
    coordinateRestrict S x = coordinateRestrict S x' ↔ ∀ i ∈ S, x i = x' i := by
  constructor
  · intro h i hi
    have hh := congrFun h (Fintype.equivFin S ⟨i, hi⟩)
    simpa only [coordinateRestrict, LinearMap.coe_mk, AddHom.coe_mk,
      Equiv.symm_apply_apply] using hh
  · intro h; funext j
    exact h _ ((Fintype.equivFin S).symm j).property

set_option backward.isDefEq.respectTransparency false in
theorem adaptiveReplacementJointOp_apply (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (D : AdaptiveDilationFamily P k H A)
    (y : ι → F) (z : Fin (Fintype.card (P.factorOfPrefix k y)) → F) (a : A)
    (x x' : ι → F) (b b' : H × A) :
    adaptiveReplacementJointOp P hP k D ⟨y, (z, a)⟩ (x, b) (x', b') =
      if ((∀ i ∈ CLChecks.prefixRegister P k y, x i = x' i) ∧
          (∀ i ∈ P.factorOfPrefix k y, x i = x' i)) ∧
          ((P.truncate k).eval x = y ∧
            coordinateLinear (CLChecks.stageLinear P k y)
              (coordinateRestrict (P.factorOfPrefix k y) x) = z) then
        D y z a ((fun i => x i, b.1), b.2) ((fun i => x' i, b'.1), b'.2) else 0 := by
  rw [adaptiveReplacementJointOp, prefixResidualOp_apply P hP,
    reassociatedConditionalDilation_factor, ← readout_eq_synOf]
  simp only [registerOp_apply, Matrix.kroneckerMap_apply, readout, Matrix.diagonal_apply]
  change (if (∀ i ∈ CLChecks.prefixRegister P k y, x i = x' i) ∧ (P.truncate k).eval x = y then
    (if coordinateRestrict (P.factorOfPrefix k y) x = coordinateRestrict (P.factorOfPrefix k y) x'
      then (if coordinateLinear (CLChecks.stageLinear P k y)
        (coordinateRestrict (P.factorOfPrefix k y) x) = z then 1 else 0) else 0) *
      D y z a ((fun i => x i, b.1), b.2) ((fun i => x' i, b'.1), b'.2) else 0) = _
  simp only [coordinateRestrict_eq_iff]
  split_ifs <;> simp_all

set_option backward.isDefEq.respectTransparency false in
/-- Every attainable old-prefix block is exactly a next-prefix residual
block. The current coordinate outcome may be outside the linear image;
both sides then vanish, without imposing a support hypothesis on `D`. -/
theorem adaptiveReplacementJointOp_next_factor (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ) (D : AdaptiveDilationFamily P k H A)
    (y : ι → F) (hy : y ∈ prefixOutcomes P k)
    (z : Fin (Fintype.card (P.factorOfPrefix k y)) → F) (a : A) :
    adaptiveReplacementJointOp P hP k D ⟨y, (z, a)⟩ =
      prefixResidualOp P (k + 1) (advancePrefix P k y z)
        (nextResidualOp P hP k y z (D y z a)) := by
  ext ⟨x, b⟩ ⟨x', b'⟩
  rw [adaptiveReplacementJointOp_apply, prefixResidualOp_apply P hP]
  have hc : ((∀ i ∈ CLChecks.prefixRegister P (k + 1) (advancePrefix P k y z),
      x i = x' i) ∧ (P.truncate (k + 1)).eval x = advancePrefix P k y z) ↔
      ((∀ i ∈ CLChecks.prefixRegister P k y, x i = x' i) ∧
        (∀ i ∈ P.factorOfPrefix k y, x i = x' i)) ∧
        ((P.truncate k).eval x = y ∧
          coordinateLinear (CLChecks.stageLinear P k y)
            (coordinateRestrict (P.factorOfPrefix k y) x) = z) := by
    rw [advancePrefix_register hP, CLChecks.prefixRegister_step,
      advancePrefix_fibre P hP k y hy, adaptiveLinearOutcome_eq_iff]
    simp only [mem_union, or_imp, forall_and]
  exact if_congr hc.symm rfl rfl

end MIPRE.Introspection
end

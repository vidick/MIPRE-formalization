/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.AdaptivePrefixAdvance
public import MIPRE.Foundations.Introspection.AdaptivePrefixReplacement

@[expose] public section

/-! # Exact next-prefix factorization of the adaptive replacement

The old prefix and current Z projector combine into the actual next prefix
projector. The remaining coordinates are transported by their proved set
equality, with the same auxiliary space for every branch.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): a dilated residual operator is
a block matrix over the ancilla of block matrices over the remaining coordinates, with entries in
any algebra `𝒜`, so the auxiliary system lives inside the algebra. The reassociation
`((R → F) × H) × A ≃ (R → F) × (H × A)`, which moved the ancilla next to the auxiliary space,
becomes the exchange of the two layers (`BipartiteModel.layerSwap`), which moves the ancilla
inside, next to the algebra; the next residual operator (`nextResidualOp`) is this exchange
relabelled along the set equality of the remaining coordinates, a unital `⋆`-homomorphism along
which projectivity is pushed forward. The entry formulas (`prefixResidualOp_apply`,
`adaptiveReplacementJointOp_apply`) have their entries in the algebra, and the next-prefix
factorization is proved entrywise, as before.
-/

noncomputable section
namespace MIPRE.Introspection
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false

variable {ι F A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype A] [DecidableEq A] {ℓ : ℕ}
variable {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜]

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

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- Pull the dilated remaining operator into the actual next-prefix carrier: the ancilla layer is
moved inside (`layerSwap`), and the remaining coordinates are relabelled along their proved set
equality. -/
def nextResidualOp (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (y : ι → F) (z : Fin (Fintype.card (P.factorOfPrefix k y)) → F)
    (N : Matrix T T (Matrix (↥(stageRemaining P k y \ P.factorOfPrefix k y) → F)
      (↥(stageRemaining P k y \ P.factorOfPrefix k y) → F) 𝒜)) :
    Matrix (stageRemaining P (k + 1) (advancePrefix P k y z) → F)
      (stageRemaining P (k + 1) (advancePrefix P k y z) → F) (Matrix T T 𝒜) :=
  submatrixHom (registerSetEquiv (F := F) (nextRemaining_eq P hP k y z))
    (BipartiteModel.layerSwap N)

theorem nextResidualOp_isPVM (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (y : ι → F) (z : Fin (Fintype.card (P.factorOfPrefix k y)) → F)
    (N : A → Matrix T T (Matrix (↥(stageRemaining P k y \ P.factorOfPrefix k y) → F)
      (↥(stageRemaining P k y \ P.factorOfPrefix k y) → F) 𝒜))
    (hN : IsPVMIn N) : IsPVMIn (nextResidualOp P hP k y z ∘ N) :=
  (hN.pushforward BipartiteModel.layerSwap_one).pushforward (submatrixHom_one _)

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

/-- An entry of a reinserted residual operator: the entry of the residual operator on the
remaining coordinates if the prefix coordinates agree and lie in the fibre of the prefix, and zero
otherwise. -/
theorem prefixResidualOp_apply (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (y : ι → F)
    (M : Matrix (stageRemaining P k y → F) (stageRemaining P k y → F) 𝒜)
    (x x' : ι → F) :
    prefixResidualOp P k y M x x' =
      if (∀ i ∈ CLChecks.prefixRegister P k y, x i = x' i) ∧ (P.truncate k).eval x = y then
        M (fun i => x i) (fun i => x' i) else 0 := by
  have he : (fun i : CLChecks.prefixRegister P k y => x i) =
      (fun i : CLChecks.prefixRegister P k y => x' i) ↔
      ∀ i ∈ CLChecks.prefixRegister P k y, x i = x' i := by
    constructor
    · intro h i hi; exact congrFun h ⟨i, hi⟩
    · intro h; funext i; exact h i i.property
  have hf : (P.truncate k).eval
      (Honest.insertRegister (CLChecks.prefixRegister P k y)
        (fun i : CLChecks.prefixRegister P k y => x i)) = y ↔
      (P.truncate k).eval x = y := by
    change (P.truncate k).eval (Honest.insertRegister (CLChecks.prefixRegister P k y)
      (ambientSplit (CLChecks.prefixRegister P k y) x).1) = y ↔ _
    rw [Honest.insertRegister_ambientSplit]
    exact (CLChecks.truncate_fibre_proj hP k y x).symm
  rw [prefixResidualOp, regSplitHom_apply, smulKron_apply, Matrix.smul_apply]
  change Honest.prefixProjector P k y (fun i => x i) (fun i => x' i) •
    M (fun i => x i) (fun i => x' i) = _
  simp only [Honest.prefixProjector, readout, Matrix.diagonal_apply, he, hf]
  by_cases ha : ∀ i ∈ CLChecks.prefixRegister P k y, x i = x' i <;>
    by_cases hb : (P.truncate k).eval x = y <;> simp [ha, hb]

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

/-- An entry of the reassociated dilation is the readout entry times the entry, with the ancilla
layer inside, of the dilated residual operator on the remaining coordinates. -/
private theorem reassociatedConditionalDilation_apply {V I R Y : Type*}
    [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]
    (e : V ≃ I × R) (Z : Y → Matrix I I ℂ) (Q : Y → A → Matrix T T (Matrix R R 𝒜))
    (p : Y × A) (v v' : V) :
    reassociatedConditionalDilation e Z Q p v v' =
      Z p.1 (e v).1 (e v').1 • BipartiteModel.layerSwap (Q p.1 p.2) (e v).2 (e v').2 := by
  ext t t'
  rfl

theorem adaptiveReplacementJointOp_apply (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (D : AdaptiveDilationFamily P k 𝒜 T A)
    (y : ι → F) (z : Fin (Fintype.card (P.factorOfPrefix k y)) → F) (a : A)
    (x x' : ι → F) :
    adaptiveReplacementJointOp P hP k D ⟨y, (z, a)⟩ x x' =
      if ((∀ i ∈ CLChecks.prefixRegister P k y, x i = x' i) ∧
          (∀ i ∈ P.factorOfPrefix k y, x i = x' i)) ∧
          ((P.truncate k).eval x = y ∧
            coordinateLinear (CLChecks.stageLinear P k y)
              (coordinateRestrict (P.factorOfPrefix k y) x) = z) then
        BipartiteModel.layerSwap (D y z a) (fun i => x i) (fun i => x' i) else 0 := by
  rw [adaptiveReplacementJointOp, prefixResidualOp_apply P hP,
    reassociatedConditionalDilation_apply, ← readout_eq_synOf]
  change (if (∀ i ∈ CLChecks.prefixRegister P k y, x i = x' i) ∧ (P.truncate k).eval x = y then
    readout (coordinateLinear (CLChecks.stageLinear P k y)) z
        (coordinateRestrict (P.factorOfPrefix k y) x)
        (coordinateRestrict (P.factorOfPrefix k y) x') •
      BipartiteModel.layerSwap (D y z a) (fun i => x i) (fun i => x' i) else 0) = _
  simp only [readout, Matrix.diagonal_apply, coordinateRestrict_eq_iff]
  split_ifs <;> simp_all

/-- Every attainable old-prefix block is exactly a next-prefix residual
block. The current coordinate outcome may be outside the linear image;
both sides then vanish, without imposing a support hypothesis on `D`. -/
theorem adaptiveReplacementJointOp_next_factor (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ) (D : AdaptiveDilationFamily P k 𝒜 T A)
    (y : ι → F) (hy : y ∈ prefixOutcomes P k)
    (z : Fin (Fintype.card (P.factorOfPrefix k y)) → F) (a : A) :
    adaptiveReplacementJointOp P hP k D ⟨y, (z, a)⟩ =
      prefixResidualOp P (k + 1) (advancePrefix P k y z)
        (nextResidualOp P hP k y z (D y z a)) := by
  refine Matrix.ext fun x x' => ?_
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

end

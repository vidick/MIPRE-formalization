/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AdaptivePrefixFactor
import MIPRE.Foundations.Introspection.ReadRigidity

/-! # The actual adaptive hiding marginal retaining one dual register -/

noncomputable section
namespace MIPRE.Introspection.Honest

open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false

variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

private theorem matrix_ite_entry {I J : Type*} (p : Prop) [Decidable p]
    (M N : Matrix I J ℂ) (i : I) (j : J) :
    (if p then M else N) i j = if p then M i j else N i j := by
  by_cases h : p <;> simp [h]

def dualLabel (P : CL.CLFun F ι ℓ) (k : ℕ) (a : HideLabel F ι) : ReadLabel F ι :=
  (a.1, CL.proj (P.factorOfPrefix k a.1) a.2.1)

def dualRegister (P : CL.CLFun F ι ℓ) (k : ℕ) (V : Finset ι)
    (h : P.SupportedOn V) : ReadLabel F ι → Matrix (V → F) (V → F) ℂ :=
  fibSum (hideRegister P k V h) (dualLabel P k)

theorem readDualOp_eq_registerDual (P : CL.CLFun F ι ℓ) (k : ℕ)
    (h : P.SupportedOn univ) (p : ReadLabel F ι) :
    readDualOp P k h (some p) = registerOp univRestriction (dualRegister P k univ h p) := by
  unfold readDualOp hideCoarseOp
  rw [show fibSum (fibSum (hideOp P k h) (hideLabelCoarse P k))
      TypedEstimates.hidingForgetTail (some p) =
      fibSum (hideOp P k h) (TypedEstimates.hidingForgetTail ∘ hideLabelCoarse P k) (some p) from
    coarseOp_comp _ _ _ _]
  unfold dualRegister fibSum
  ext x x'
  simp only [registerOp_apply, Matrix.sum_apply, Finset.sum_filter, matrix_ite_entry, Matrix.zero_apply]
  apply Finset.sum_congr rfl
  intro a _
  change (if (TypedEstimates.hidingForgetTail ∘ hideLabelCoarse P k) a = some p then
      hideOp P k h a x x' else 0) =
    (if dualLabel P k a = p then hideOp P k h a x x' else 0)
  by_cases hz : hideOp P k h a = 0
  · simp [hz]
  · have hf := hideOp_prefix_fixed P k h a hz
    have hg : (TypedEstimates.hidingForgetTail ∘ hideLabelCoarse P k) a =
        some (dualLabel P k a) := by
      simp only [TypedEstimates.hidingForgetTail, hideLabelCoarse, hideLabelAnswer,
        TypedEstimates.hidingCoarse, Function.comp_apply, Option.map_some, hf, dualLabel]
    have hc : ((TypedEstimates.hidingForgetTail ∘ hideLabelCoarse P k) a = some p) ↔
        dualLabel P k a = p := by rw [hg, Option.some.injEq]
    exact if_congr hc rfl rfl

theorem dualLabel_join {S V : Finset ι} (L : CL.RegLinear F S)
    (next : (ι → F) → CL.CLFun F ι ℓ)
    (h : (CL.CLFun.cons S L next).SupportedOn V) (k : ℕ)
    (z : (Fin (Fintype.card S) → F) × (Fin (Fintype.card S) → F))
    (a : HideLabel F ι) (ha : CL.proj (V \ S) a.1 = a.1) :
    dualLabel (.cons S L next) (k + 1) (joinHide S (z, a)) =
      (coordinateInsert S z.1 + a.1,
        CL.proj ((next (coordinateInsert S z.1)).factorOfPrefix k a.1) a.2.1) := by
  have hp := proj_local_add z.1 a.1 ha
  have hs : (next (coordinateInsert S z.1)).factorOfPrefix k a.1 ⊆ V \ S :=
    (CLChecks.factorOfPrefix_subset_prefixRegister _ _ _).trans
      (CLChecks.prefixRegister_subset (h.2 _) _ _)
  simp only [dualLabel, joinHide, CL.CLFun.factorOfPrefix_cons_succ, hp.1, hp.2]
  congr 1
  ext i
  by_cases hi : i ∈ (next (coordinateInsert S z.1)).factorOfPrefix k a.1
  · have hiS := (mem_sdiff.mp (hs hi)).2
    simp [CL.proj_apply, coordinateInsert, hiS]
  · simp [CL.proj_apply, hi]

theorem dualLabel_join_eq_iff {S V : Finset ι} (L : CL.RegLinear F S)
    (next : (ι → F) → CL.CLFun F ι ℓ)
    (h : (CL.CLFun.cons S L next).SupportedOn V) (k : ℕ)
    (z : (Fin (Fintype.card S) → F) × (Fin (Fintype.card S) → F))
    (a : HideLabel F ι) (ha : CL.proj (V \ S) a.1 = a.1) (y yp : ι → F) :
    dualLabel (.cons S L next) (k + 1) (joinHide S (z, a)) = (y, yp) ↔
      z.1 = coordinateRestrict S y ∧
        dualLabel (next (coordinateInsert S z.1)) k a = (CL.proj Sᶜ y, yp) := by
  rw [dualLabel_join L next h k z a ha]
  simp only [Prod.mk.injEq, dualLabel]
  constructor
  · rintro ⟨hy, hd⟩
    have hp := proj_local_add z.1 a.1 ha
    rw [hy] at hp
    refine ⟨?_, hp.2.symm, hd⟩
    have he := congrArg (coordinateRestrict S) hp.1
    simpa only [← coordinateInsert_restrict, coordinateRestrict_insert] using he.symm
  · rintro ⟨hz, hy, hd⟩
    refine ⟨?_, hd⟩
    rw [hz, hy, coordinateInsert_restrict, CL.proj_add_proj_compl]

theorem localRead_sum_dual {S : Finset ι} (L : CL.RegLinear F S)
    (a : Fin (Fintype.card S) → F) :
    (∑ b, localRead L (a,b)) = synOf wZ (coordinateLinear L) a := by
  simp only [localRead, ← Finset.mul_sum]
  rw [(linear_measurement_isPVM wX isWeylFamily_wX (CL.lperp (coordinateLinear L))).sum_eq_one,
    mul_one]

theorem dualRegister_zero (P : CL.CLFun F ι ℓ) (V : Finset ι) (h : P.SupportedOn V)
    (y yp : ι → F) :
    dualRegister P 0 V h (y,yp) = if y = 0 then
      synOf wX (fun x : V → F => CLChecks.dualReadout P 0 0 (insertRegister V x)) yp else 0 := by
  unfold dualRegister
  rw [hideRegister_zero_fun]
  change coarseOp (dualLabel P 0) (coarseOp (stopHideAnswer P V) (proj wX)) (y,yp) = _
  rw [coarseOp_comp]
  have hf (x : V → F) : dualLabel P 0 (stopHideAnswer P V x) =
      (0, CLChecks.dualReadout P 0 0 (insertRegister V x)) := by
    simp only [dualLabel, stopHideAnswer, firstHideAnswer, dualReadout_first_supported]
  simp only [coarseOp, Function.comp_apply, hf, Finset.sum_filter, Prod.mk.injEq]
  by_cases hy : y = 0
  · subst y
    simp [synOf, Finset.sum_filter]
  · simp [hy, Ne.symm hy]

theorem coarseOp_registerOp {I J A B : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (e : I ≃ J) (f : A → B)
    (M : A → Matrix J J ℂ) (b : B) :
    coarseOp f (fun a => registerOp e (M a)) b = registerOp e (coarseOp f M b) := by
  ext i j
  simp only [coarseOp, Matrix.sum_apply, registerOp_apply]

set_option backward.isDefEq.respectTransparency false in
/-- Summing out the earlier dual coordinate leaves precisely its Z readout;
the retained prefix still selects the actual continuation. -/
theorem dualRegister_cons_succ {S V : Finset ι} (L : CL.RegLinear F S)
    (next : (ι → F) → CL.CLFun F ι ℓ)
    (h : (CL.CLFun.cons S L next).SupportedOn V) (k : ℕ) (y yp : ι → F) :
    dualRegister (.cons S L next) (k + 1) V h (y,yp) =
      registerOp (coordinateSplit S V h.1)
        (synOf wZ (coordinateLinear L) (coordinateRestrict S y) ⊗ₖ
          dualRegister (next (CL.proj S y)) k (V \ S) (h.2 _) (CL.proj Sᶜ y,yp)) := by
  change coarseOp (dualLabel (.cons S L next) (k+1))
    (fun a => registerOp (coordinateSplit S V h.1)
      (coarseOp (joinHide S) (adaptiveTensor (localRead L)
        (fun z => hideRegister (next (coordinateInsert S z.1)) k (V \ S) (h.2 _))) a)) (y,yp) = _
  rw [coarseOp_registerOp, coarseOp_comp]
  apply congrArg (registerOp (coordinateSplit S V h.1))
  have hm : coarseOp (dualLabel (.cons S L next) (k+1) ∘ joinHide S)
      (adaptiveTensor (localRead L)
        (fun z => hideRegister (next (coordinateInsert S z.1)) k (V \ S) (h.2 _))) (y,yp) =
      ∑ b, localRead L (coordinateRestrict S y,b) ⊗ₖ
        dualRegister (next (CL.proj S y)) k (V \ S) (h.2 _) (CL.proj Sᶜ y,yp) := by
    ext x x'
    simp only [coarseOp, dualRegister, fibSum, Matrix.sum_apply, Finset.sum_filter,
      Fintype.sum_prod_type, adaptiveTensor, Matrix.kroneckerMap_apply, Function.comp_apply,
      matrix_ite_entry, Matrix.zero_apply]
    have ht (a b : Fin (Fintype.card S) → F) (u : HideLabel F ι) :
        (if dualLabel (.cons S L next) (k+1) (joinHide S ((a,b),u)) = (y,yp) then
          localRead L (a,b) x.1 x'.1 *
            hideRegister (next (coordinateInsert S a)) k (V \ S) (h.2 _) u x.2 x'.2 else 0) =
        (if a = coordinateRestrict S y then localRead L (a,b) x.1 x'.1 *
          (if dualLabel (next (coordinateInsert S a)) k u = (CL.proj Sᶜ y,yp) then
            hideRegister (next (coordinateInsert S a)) k (V \ S) (h.2 _) u x.2 x'.2 else 0) else 0) := by
      by_cases hz : hideRegister (next (coordinateInsert S a)) k (V \ S) (h.2 _) u x.2 x'.2 = 0
      · simp [hz]
      · have hu := (hideRegister_entry_supported (next (coordinateInsert S a)) k
          (V \ S) (h.2 _) u x.2 x'.2 hz).1
        simp only [dualLabel_join_eq_iff L next h k (a,b) u hu]
        by_cases ha : a = coordinateRestrict S y <;>
          by_cases hb : dualLabel (next (coordinateInsert S a)) k u = (CL.proj Sᶜ y,yp) <;>
          simp [ha, hb]
    simp_rw [ht]
    simp [Finset.mul_sum, mul_ite, coordinateInsert_restrict]
  rw [hm, ← sum_kronecker_left, localRead_sum_dual]

end MIPRE.Introspection.Honest

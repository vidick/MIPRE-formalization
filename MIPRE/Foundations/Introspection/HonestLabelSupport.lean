/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.HonestHiding

/-! # Support of the actual honest Read and Hide answers

A nonzero entry of either adaptive measurement forces every reported vector
to lie in the active coordinate register. The statements cover the full answer
alphabet: no support or honest-format assumption is imposed on the answer.
-/

noncomputable section

namespace MIPRE.Introspection.Honest

open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false

variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι]

private theorem support_mono {S V : Finset ι} (h : S ⊆ V) {x : ι → F}
    (hx : CL.proj S x = x) : CL.proj V x = x := by
  calc
    CL.proj V x = CL.proj V (CL.proj S x) := congrArg (CL.proj V) hx.symm
    _ = CL.proj S x := CL.proj_proj_of_subset' h x
    _ = x := hx

theorem proj_coordinateInsert_of_subset {S V : Finset ι} (h : S ⊆ V)
    (x : Fin (Fintype.card S) → F) : CL.proj V (coordinateInsert S x) = coordinateInsert S x := by
  funext i
  by_cases hi : i ∈ S
  · simp [CL.proj_apply, coordinateInsert, hi, h hi]
  · simp [CL.proj_apply, coordinateInsert, hi]

theorem proj_insertRegister (V : Finset ι) (x : V → F) :
    CL.proj V (insertRegister V x) = insertRegister V x := by
  funext i
  by_cases hi : i ∈ V <;> simp [CL.proj_apply, insertRegister, hi]

/-- All three stopping-Hide vectors are supported on the active register. -/
theorem stopHideAnswer_supported {ℓ : ℕ} (P : CL.CLFun F ι ℓ)
    (V : Finset ι) (h : P.SupportedOn V) (x : V → F) :
    CL.proj V (stopHideAnswer P V x).1 = (stopHideAnswer P V x).1 ∧
    CL.proj V (stopHideAnswer P V x).2.1 = (stopHideAnswer P V x).2.1 ∧
    CL.proj V (stopHideAnswer P V x).2.2 = (stopHideAnswer P V x).2.2 := by
  have hS : P.factorOfPrefix 0 0 ⊆ V := by
    cases P with
    | zero => simp [CL.CLFun.factorOfPrefix]
    | cons S L next => exact h.1
  refine ⟨by simp [stopHideAnswer, firstHideAnswer], ?_, ?_⟩
  · exact support_mono hS (dualReadout_first_supported P (insertRegister V x))
  · change CL.proj V (CL.proj (P.factorOfPrefix 0 0)ᶜ (insertRegister V x)) =
      CL.proj (P.factorOfPrefix 0 0)ᶜ (insertRegister V x)
    funext i
    by_cases hi : i ∈ V <;> simp [CL.proj_apply, insertRegister, hi]

/-- A nonzero stopping-Hide entry has no reported coordinates outside its register. -/
theorem stopHide_entry_supported {ℓ : ℕ} (P : CL.CLFun F ι ℓ)
    (V : Finset ι) (h : P.SupportedOn V) (a : HideLabel F ι) (x x' : V → F)
    (ha : stopHide P V a x x' ≠ 0) :
    CL.proj V a.1 = a.1 ∧ CL.proj V a.2.1 = a.2.1 ∧ CL.proj V a.2.2 = a.2.2 := by
  simp only [stopHide, synOf, Matrix.sum_apply] at ha
  obtain ⟨z, hz, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
  rw [← (Finset.mem_filter.mp hz).2]
  exact stopHideAnswer_supported P V h z

/-- Both labels of every nonzero Read entry are supported in the active register. -/
theorem readRegister_entry_supported {ℓ : ℕ} (P : CL.CLFun F ι ℓ)
    (V : Finset ι) (h : P.SupportedOn V) (a : ReadLabel F ι) (x x' : V → F)
    (ha : readRegister P V h a x x' ≠ 0) :
    CL.proj V a.1 = a.1 ∧ CL.proj V a.2 = a.2 := by
  induction P generalizing V a with
  | zero =>
      have hz : a = (0, 0) := by
        by_contra hn
        exact ha (by simp [readRegister, hn])
      simp [hz]
  | cons S L next ih =>
      simp only [readRegister, registerOp_apply, Matrix.sum_apply] at ha
      obtain ⟨q, hq, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
      have hj := (Finset.mem_filter.mp hq).2
      change localRead L q.1 (coordinateSplit S V h.1 x).1
          (coordinateSplit S V h.1 x').1 *
        readRegister (next (coordinateInsert S q.1.1)) (V \ S) (h.2 _)
          q.2 (coordinateSplit S V h.1 x).2 (coordinateSplit S V h.1 x').2 ≠ 0 at hterm
      have hr := ih (coordinateInsert S q.1.1) (V \ S) (h.2 _) q.2
        (coordinateSplit S V h.1 x).2 (coordinateSplit S V h.1 x').2
        (mul_ne_zero_iff.mp hterm).2
      rw [← hj]
      constructor
      · change CL.proj V (coordinateInsert S q.1.1 + q.2.1) = _
        rw [map_add, proj_coordinateInsert_of_subset h.1, support_mono sdiff_subset hr.1]
        rfl
      · change CL.proj V (coordinateInsert S q.1.2 + q.2.2) = _
        rw [map_add, proj_coordinateInsert_of_subset h.1, support_mono sdiff_subset hr.2]
        rfl

/-- Every component of a nonzero Hide entry is supported in the active register. -/
theorem hideRegister_entry_supported {ℓ : ℕ} (P : CL.CLFun F ι ℓ) (k : ℕ)
    (V : Finset ι) (h : P.SupportedOn V) (a : HideLabel F ι) (x x' : V → F)
    (ha : hideRegister P k V h a x x' ≠ 0) :
    CL.proj V a.1 = a.1 ∧ CL.proj V a.2.1 = a.2.1 ∧ CL.proj V a.2.2 = a.2.2 := by
  induction P generalizing V a k with
  | zero =>
      cases k <;> exact stopHide_entry_supported .zero V h a x x' ha
  | cons S L next ih =>
      cases k with
      | zero => exact stopHide_entry_supported _ V h a x x' ha
      | succ k =>
          simp only [hideRegister, registerOp_apply, Matrix.sum_apply] at ha
          obtain ⟨q, hq, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
          have hj := (Finset.mem_filter.mp hq).2
          change localRead L q.1 (coordinateSplit S V h.1 x).1
              (coordinateSplit S V h.1 x').1 *
            hideRegister (next (coordinateInsert S q.1.1)) k (V \ S) (h.2 _)
              q.2 (coordinateSplit S V h.1 x).2 (coordinateSplit S V h.1 x').2 ≠ 0 at hterm
          have hr := ih (coordinateInsert S q.1.1) k (V \ S) (h.2 _) q.2
            (coordinateSplit S V h.1 x).2 (coordinateSplit S V h.1 x').2
            (mul_ne_zero_iff.mp hterm).2
          rw [← hj]
          refine ⟨?_, ?_, support_mono sdiff_subset hr.2.2⟩
          · change CL.proj V (coordinateInsert S q.1.1 + q.2.1) = _
            rw [map_add, proj_coordinateInsert_of_subset h.1, support_mono sdiff_subset hr.1]
            rfl
          · change CL.proj V (coordinateInsert S q.1.2 + q.2.2.1) = _
            rw [map_add, proj_coordinateInsert_of_subset h.1, support_mono sdiff_subset hr.2.1]
            rfl

end MIPRE.Introspection.Honest

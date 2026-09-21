/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.HonestXCoordinates
import MIPRE.Foundations.Introspection.HonestHiding

/-! # The first honest Hide measurement in the full Pauli register

The recursive construction uses the subtype of the active register as its
basis. At the full register this is precisely the ordinary Pauli-X coarse
measurement, after the explicit computational-basis relabelling.
-/

noncomputable section

namespace MIPRE.Introspection.Honest

open Finset Matrix Classical Weyl
set_option linter.unusedSectionVars false

variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

def univIndex : ↥(Finset.univ : Finset ι) ≃ ι where
  toFun := Subtype.val
  invFun i := ⟨i, Finset.mem_univ i⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem trDot_univRestriction (x y : ι → F) :
    trDot (univRestriction x) (univRestriction y) = trDot x y := by
  unfold trDot
  congr 1
  exact Equiv.sum_comp univIndex (fun i => x i * y i)

theorem pauliX_univRestriction (z : ι → F) :
    registerOp univRestriction (proj wX (univRestriction z)) = proj wX z := by
  have hc := Fintype.card_congr (univRestriction (F := F) (ι := ι))
  ext x y
  simp only [registerOp_apply, pauliX_entry, ← hc]
  change _ * sgn (trDot (univRestriction (x + y)) (univRestriction z)) = _
  rw [trDot_univRestriction]

/-- The zero-stage recursive Hide PVM is exactly the ordinary full-register X coarsening. -/
theorem hideOp_zero_eq_firstHideOp (P : CL.CLFun F ι ℓ)
    (h : P.SupportedOn Finset.univ) (a : HideLabel F ι) :
    hideOp P 0 h a = firstHideOp P a := by
  simp only [hideOp, hideRegister_zero, stopHide, firstHideOp, synOf]
  ext x y
  simp only [registerOp_apply, Matrix.sum_apply, Finset.sum_filter]
  symm
  apply Fintype.sum_equiv (univRestriction (F := F) (ι := ι))
  intro z
  simp only [stopHideAnswer, insertRegister_univ]
  by_cases hz : firstHideAnswer P z = a
  · simp only [hz, if_true]
    exact (congrArg (fun M => M x y) (pauliX_univRestriction z)).symm
  · simp [hz]

theorem pauliX_hideOp_zero_commute (P : CL.CLFun F ι ℓ)
    (h : P.SupportedOn Finset.univ) (x : ι → F) (a : HideLabel F ι) :
    Commute (proj wX x) (hideOp P 0 h a) := by
  rw [hideOp_zero_eq_firstHideOp]
  exact pauli_firstHide_commute P x a

theorem pauliX_hideOp_zero_reject (P : CL.CLFun F ι ℓ)
    (h : P.SupportedOn Finset.univ) (x : ι → F) (a : HideLabel F ι)
    (hr : ¬ CLChecks.hidingPauli P x a) : proj wX x * hideOp P 0 h a = 0 := by
  rw [hideOp_zero_eq_firstHideOp]
  exact firstHide_reject_zero P x a hr

end MIPRE.Introspection.Honest

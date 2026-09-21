/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.HonestRead

/-! # The honest adaptive hiding prefixes

The first component of the honest hiding measurement is exactly the preceding
CL prefix, for every level of the adaptive construction. The statement concerns
the actual recursively constructed operators and the source CL truncation.
-/

noncomputable section

namespace MIPRE.Introspection.Honest

open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false

variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι]

theorem stopHide_entry_nonzero {ℓ : ℕ} (P : CL.CLFun F ι ℓ) (V : Finset ι)
    (a : HideLabel F ι) (x x' : V → F) (ha : stopHide P V a x x' ≠ 0) : a.1 = 0 := by
  simp only [stopHide, synOf, Matrix.sum_apply] at ha
  obtain ⟨z, hz, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
  exact (congrArg Prod.fst (Finset.mem_filter.mp hz).2).symm

/-- The question reported by Hide at level `k` is the actual first `k` CL stages. -/
theorem hideRegister_entry_nonzero {ℓ : ℕ} (P : CL.CLFun F ι ℓ) (k : ℕ)
    (V : Finset ι) (h : P.SupportedOn V) (a : HideLabel F ι) (x x' : V → F)
    (ha : hideRegister P k V h a x x' ≠ 0) :
    (P.truncate k).eval (insertRegister V x) = a.1 := by
  induction P generalizing V a k with
  | zero =>
      cases k with
      | zero => exact (stopHide_entry_nonzero .zero V a x x' ha).symm
      | succ k =>
          rw [CL.CLFun.eval_truncate_zero]
          exact (stopHide_entry_nonzero .zero V a x x' ha).symm
  | cons S L next ih =>
      cases k with
      | zero => exact (stopHide_entry_nonzero _ V a x x' ha).symm
      | succ k =>
          simp only [hideRegister, registerOp_apply, Matrix.sum_apply] at ha
          obtain ⟨q, hq, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
          have hj := (Finset.mem_filter.mp hq).2
          change localRead L q.1 (coordinateSplit S V h.1 x).1
              (coordinateSplit S V h.1 x').1 *
            hideRegister (next (coordinateInsert S q.1.1)) k (V \ S) (h.2 _)
              q.2 (coordinateSplit S V h.1 x).2 (coordinateSplit S V h.1 x').2 ≠ 0 at hterm
          have hl := localRead_entry_nonzero L q.1 _ _ (mul_ne_zero_iff.mp hterm).1
          have hr := ih (coordinateInsert S q.1.1) k (V \ S) (h.2 _) q.2
            (coordinateSplit S V h.1 x).2 (coordinateSplit S V h.1 x').2
            (mul_ne_zero_iff.mp hterm).2
          rw [CL.CLFun.truncate_succ_cons, CL.CLFun.eval_cons,
            linear_insertRegister h.1 L x, hl, tail_insertRegister S V h.1 x, hr]
          exact congrArg Prod.fst hj

theorem readout_mul_hideRegister {ℓ : ℕ} (P : CL.CLFun F ι ℓ) (k : ℕ)
    (V : Finset ι) (h : P.SupportedOn V) (y : ι → F) (a : HideLabel F ι) :
    readout (fun x => (P.truncate k).eval (insertRegister V x)) y * hideRegister P k V h a =
      if y = a.1 then hideRegister P k V h a else 0 := by
  ext x x'
  rw [readout, Matrix.diagonal_mul]
  by_cases he : hideRegister P k V h a x x' = 0
  · by_cases hy : y = a.1 <;> simp [he, hy]
  · rw [hideRegister_entry_nonzero P k V h a x x' he]
    by_cases hy : y = a.1 <;> simp [hy, eq_comm]

/-- Forgetting the dual answer and untouched X tail gives exactly the preceding CL prefix. -/
theorem hideRegister_marginal {ℓ : ℕ} (P : CL.CLFun F ι ℓ) (k : ℕ)
    (V : Finset ι) (h : P.SupportedOn V) (y : ι → F) :
    (∑ yp : (ι → F) × (ι → F), hideRegister P k V h (y, yp)) =
      readout (fun x => (P.truncate k).eval (insertRegister V x)) y := by
  calc
    _ = ∑ a : HideLabel F ι, if y = a.1 then hideRegister P k V h a else 0 := by
      conv_rhs => rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp
    _ = readout (fun x => (P.truncate k).eval (insertRegister V x)) y *
        (∑ a, hideRegister P k V h a) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      exact (readout_mul_hideRegister P k V h y a).symm
    _ = _ := by rw [(hideRegister_isPVM P k V h).sum_eq_one, mul_one]

def hideOp {ℓ : ℕ} (P : CL.CLFun F ι ℓ) (k : ℕ) (h : P.SupportedOn Finset.univ)
    (a : HideLabel F ι) : Matrix (ι → F) (ι → F) ℂ :=
  registerOp univRestriction (hideRegister P k Finset.univ h a)

theorem hideOp_isPVM {ℓ : ℕ} (P : CL.CLFun F ι ℓ) (k : ℕ)
    (h : P.SupportedOn Finset.univ) : IsPVM (hideOp P k h) :=
  registerOp_isPVM _ (hideRegister_isPVM P k _ h)

theorem hideOp_marginal {ℓ : ℕ} (P : CL.CLFun F ι ℓ) (k : ℕ)
    (h : P.SupportedOn Finset.univ) (y : ι → F) :
    (∑ yp : (ι → F) × (ι → F), hideOp P k h (y, yp)) = readout (P.truncate k).eval y := by
  unfold hideOp
  rw [← registerOp_sum, hideRegister_marginal]
  ext x x'
  simp [readout, registerOp_apply, Matrix.diagonal_apply]

end MIPRE.Introspection.Honest

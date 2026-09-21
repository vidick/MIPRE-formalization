/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.HonestAdaptive
import MIPRE.Foundations.Introspection.HonestCore

/-! # Correctness of the adaptive honest Read measurement

The adaptive register measurement refines the actual CL question readout.
Consequently attaching the original question-dependent answer measurement gives
the honest Read PVM and perfect commutation and acceptance on Introspect/Read.
-/

noncomputable section

namespace MIPRE.Introspection.Honest

open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false

variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι]

theorem restrict_insertRegister (S V : Finset ι) (h : S ⊆ V) (x : V → F) :
    coordinateRestrict S (insertRegister V x) = (coordinateSplit S V h x).1 := by
  funext i
  simp [coordinateRestrict, insertRegister, coordinateSplit,
    h ((Fintype.equivFin S).symm i).property]

theorem linear_insertRegister {S V : Finset ι} (h : S ⊆ V)
    (L : CL.RegLinear F S) (x : V → F) :
    L (insertRegister V x) =
      coordinateInsert S (coordinateLinear L (coordinateSplit S V h x).1) := by
  rw [← restrict_insertRegister S V h, coordinateLinear_restrict,
    coordinateInsert_restrict, CL.RegLinear.proj_apply]

theorem tail_insertRegister (S V : Finset ι) (h : S ⊆ V) (x : V → F) :
    CL.proj Sᶜ (insertRegister V x) =
      insertRegister (V \ S) (coordinateSplit S V h x).2 := by
  funext i
  by_cases hiS : i ∈ S <;> by_cases hiV : i ∈ V <;>
    simp [CL.proj_apply, insertRegister, coordinateSplit, hiS, hiV]

theorem localRead_entry_nonzero {S : Finset ι} (L : CL.RegLinear F S)
    (a : (Fin (Fintype.card S) → F) × (Fin (Fintype.card S) → F))
    (x x' : Fin (Fintype.card S) → F) (h : localRead L a x x' ≠ 0) :
    coordinateLinear L x = a.1 := by
  by_contra hn
  apply h
  rw [localRead, ← readout_eq_synOf, readout, Matrix.diagonal_mul]
  simp [hn]

/-- A nonzero Read entry has the claimed CL question on its computational row. -/
theorem readRegister_entry_nonzero {ℓ : ℕ} (P : CL.CLFun F ι ℓ)
    (V : Finset ι) (h : P.SupportedOn V) (a : ReadLabel F ι) (x x' : V → F)
    (ha : readRegister P V h a x x' ≠ 0) : P.eval (insertRegister V x) = a.1 := by
  induction P generalizing V a with
  | zero =>
      have hz : a = (0, 0) := by
        by_contra hn
        exact ha (by simp [readRegister, hn])
      subst a
      rfl
  | cons S L next ih =>
      simp only [readRegister, registerOp_apply, Matrix.sum_apply] at ha
      obtain ⟨q, hq, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
      have hj := (Finset.mem_filter.mp hq).2
      change localRead L q.1 (coordinateSplit S V h.1 x).1
          (coordinateSplit S V h.1 x').1 *
        readRegister (next (coordinateInsert S q.1.1)) (V \ S) (h.2 _)
          q.2 (coordinateSplit S V h.1 x).2 (coordinateSplit S V h.1 x').2 ≠ 0 at hterm
      have hl := localRead_entry_nonzero L q.1 _ _ (mul_ne_zero_iff.mp hterm).1
      have hr := ih (coordinateInsert S q.1.1) (V \ S) (h.2 _) q.2
        (coordinateSplit S V h.1 x).2 (coordinateSplit S V h.1 x').2
        (mul_ne_zero_iff.mp hterm).2
      rw [CL.CLFun.eval_cons, linear_insertRegister h.1 L x, hl,
        tail_insertRegister S V h.1 x, hr]
      exact congrArg Prod.fst hj

/-- Multiplying by the CL question readout selects precisely the reported question. -/
theorem readout_mul_readRegister {ℓ : ℕ} (P : CL.CLFun F ι ℓ)
    (V : Finset ι) (h : P.SupportedOn V) (y : ι → F) (a : ReadLabel F ι) :
    readout (fun x => P.eval (insertRegister V x)) y * readRegister P V h a =
      if y = a.1 then readRegister P V h a else 0 := by
  ext x x'
  rw [readout, Matrix.diagonal_mul]
  by_cases he : readRegister P V h a x x' = 0
  · by_cases hy : y = a.1 <;> simp [he, hy]
  · rw [readRegister_entry_nonzero P V h a x x' he]
    by_cases hy : y = a.1 <;> simp [hy, eq_comm]

/-- The first marginal of the honest Read PVM is exactly the source CL readout. -/
theorem readRegister_marginal {ℓ : ℕ} (P : CL.CLFun F ι ℓ)
    (V : Finset ι) (h : P.SupportedOn V) (y : ι → F) :
    (∑ yp, readRegister P V h (y, yp)) =
      readout (fun x => P.eval (insertRegister V x)) y := by
  calc
    _ = ∑ a : ReadLabel F ι, if y = a.1 then readRegister P V h a else 0 := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp
    _ = readout (fun x => P.eval (insertRegister V x)) y *
        (∑ a, readRegister P V h a) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      exact (readout_mul_readRegister P V h y a).symm
    _ = _ := by rw [(readRegister_isPVM P V h).sum_eq_one, mul_one]

def univRestriction : (ι → F) ≃ (↥(Finset.univ : Finset ι) → F) where
  toFun x i := x i
  invFun x i := x ⟨i, Finset.mem_univ i⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem insertRegister_univ (x : ι → F) :
    insertRegister Finset.univ (univRestriction x) = x := by
  funext i
  simp [insertRegister, univRestriction]

/-- The full adaptive Read measurement on the ambient Pauli register. -/
def readOp {ℓ : ℕ} (P : CL.CLFun F ι ℓ) (h : P.SupportedOn Finset.univ)
    (a : ReadLabel F ι) : Matrix (ι → F) (ι → F) ℂ :=
  registerOp univRestriction (readRegister P Finset.univ h a)

theorem readOp_isPVM {ℓ : ℕ} (P : CL.CLFun F ι ℓ) (h : P.SupportedOn Finset.univ) :
    IsPVM (readOp P h) := registerOp_isPVM _ (readRegister_isPVM P _ h)

theorem readout_mul_readOp {ℓ : ℕ} (P : CL.CLFun F ι ℓ)
    (h : P.SupportedOn Finset.univ) (y : ι → F) (a : ReadLabel F ι) :
    readout P.eval y * readOp P h a = if y = a.1 then readOp P h a else 0 := by
  ext x x'
  rw [readout, Matrix.diagonal_mul]
  by_cases he : readOp P h a x x' = 0
  · by_cases hy : y = a.1 <;> simp [he, hy]
  · have hs := readRegister_entry_nonzero P Finset.univ h a
      (univRestriction x) (univRestriction x') he
    rw [insertRegister_univ] at hs
    rw [hs]
    by_cases hy : y = a.1 <;> simp [hy, eq_comm]

theorem readOp_mul_readout {ℓ : ℕ} (P : CL.CLFun F ι ℓ)
    (h : P.SupportedOn Finset.univ) (y : ι → F) (a : ReadLabel F ι) :
    readOp P h a * readout P.eval y = if y = a.1 then readOp P h a else 0 := by
  have he := congrArg Matrix.conjTranspose (readout_mul_readOp P h y a)
  rw [Matrix.conjTranspose_mul, (readout_isPVM P.eval).isSelfAdjoint,
    (readOp_isPVM P h).isSelfAdjoint] at he
  by_cases hy : y = a.1 <;> simpa [hy, (readOp_isPVM P h).isSelfAdjoint] using he

theorem readOp_marginal {ℓ : ℕ} (P : CL.CLFun F ι ℓ)
    (h : P.SupportedOn Finset.univ) (y : ι → F) :
    (∑ yp, readOp P h (y, yp)) = readout P.eval y := by
  unfold readOp
  rw [← registerOp_sum, readRegister_marginal]
  ext x x'
  simp [readout, registerOp_apply, Matrix.diagonal_apply]

end MIPRE.Introspection.Honest

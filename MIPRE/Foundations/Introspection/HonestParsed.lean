/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.HonestReading
import MIPRE.Foundations.Introspection.HonestHiding

/-! # Honest measurements on the complete parsed-answer alphabet

The actual core, Read and Hide operators act on one common register/source
space. Wrong constructors have zero effect. This retains every answer label,
gives genuine PVMs, and makes the Introspect/Read operator tests apply without
a promise that the reported constructors are well formed.
-/

noncomputable section

namespace MIPRE.Introspection.Honest

open Finset Matrix Classical
open scoped Kronecker

set_option linter.unusedSectionVars false

variable {F ι A PA : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype ι] [DecidableEq ι]
  [Fintype A] [DecidableEq A] [Fintype PA] {ℓ : ℕ}
  (L : Bool → CL.CLFun F ι ℓ) (D : (ι → F) → (ι → F) → A → A → Bool)
  (R : SyncStrategy (sourceGame L D).doubled)

private theorem sum_supported {B C M : Type*} [Fintype B] [Fintype C] [AddCommMonoid M]
    (f : B → C) (hf : Function.Injective f) (g : C → M)
    (hz : ∀ c, c ∉ Set.range f → g c = 0) : (∑ c, g c) = ∑ b, g (f b) := by
  symm
  exact Fintype.sum_of_injective f hf _ g hz (fun _ => rfl)

/-- Introspect and Sample use their actual core operators on pair answers. -/
def parsedCoreOp (t : CoreType) : ParsedAnswer (ι → F) A PA →
    Matrix ((ι → F) × Fin R.d) ((ι → F) × Fin R.d) ℂ
  | .pair y a => coreOp L D R t (y, a)
  | _ => 0

/-- Read uses the full adaptive register and source-answer measurement. -/
def parsedReadOp (w : Bool) (h : (L w).SupportedOn Finset.univ) :
    ParsedAnswer (ι → F) A PA → Matrix ((ι → F) × Fin R.d) ((ι → F) × Fin R.d) ℂ
  | .read y yp a => fullReadOp L D R w h ((y, yp), a)
  | _ => 0

/-- Hide acts on the genuine adaptive hiding register, leaving the source register alone. -/
def parsedHideOp (w : Bool) (k : ℕ) (h : (L w).SupportedOn Finset.univ) :
    ParsedAnswer (ι → F) A PA → Matrix ((ι → F) × Fin R.d) ((ι → F) × Fin R.d) ℂ
  | .hide y yp x => hideOp (L w) k h (y, yp, x) ⊗ₖ (1 : Matrix (Fin R.d) (Fin R.d) ℂ)
  | _ => 0

@[simp] theorem parsedCoreOp_pair (t : CoreType) (y : ι → F) (a : A) :
    parsedCoreOp (PA := PA) L D R t (.pair y a) = coreOp L D R t (y, a) := rfl

@[simp] theorem parsedReadOp_read (w : Bool) (h : (L w).SupportedOn Finset.univ)
    (y yp : ι → F) (a : A) : parsedReadOp (PA := PA) L D R w h (.read y yp a) =
      fullReadOp L D R w h ((y, yp), a) := rfl

@[simp] theorem parsedHideOp_hide (w : Bool) (k : ℕ) (h : (L w).SupportedOn Finset.univ)
    (y yp x : ι → F) : parsedHideOp (PA := PA) L D R w k h (.hide y yp x) =
      hideOp (L w) k h (y, yp, x) ⊗ₖ (1 : Matrix (Fin R.d) (Fin R.d) ℂ) := rfl

theorem parsedCoreOp_isPVM (t : CoreType) : IsPVM (parsedCoreOp (PA := PA) L D R t) where
  isSelfAdjoint a := by
    cases a <;> simp only [parsedCoreOp, conjTranspose_zero]
    exact (coreOp_isPVM L D R t).isSelfAdjoint _
  idem a := by
    cases a <;> simp only [parsedCoreOp, zero_mul]
    exact (coreOp_isPVM L D R t).idem _
  sum_eq_one := by
    rw [sum_supported (fun ya : (ι → F) × A =>
      (ParsedAnswer.pair ya.1 ya.2 : ParsedAnswer (ι → F) A PA))
      (by intro a b h; cases a; cases b; simpa using h)]
    · exact (coreOp_isPVM L D R t).sum_eq_one
    · intro a ha
      cases a with
      | pair y a => exact (ha ⟨(y, a), rfl⟩).elim
      | pauli p => rfl
      | read y yp a => rfl
      | hide y yp x => rfl

theorem parsedReadOp_isPVM (w : Bool) (h : (L w).SupportedOn Finset.univ) :
    IsPVM (parsedReadOp (PA := PA) L D R w h) where
  isSelfAdjoint a := by
    cases a <;> simp only [parsedReadOp, conjTranspose_zero]
    exact (fullReadOp_isPVM L D R w h).isSelfAdjoint _
  idem a := by
    cases a <;> simp only [parsedReadOp, zero_mul]
    exact (fullReadOp_isPVM L D R w h).idem _
  sum_eq_one := by
    rw [sum_supported (fun ya : ReadLabel F ι × A =>
      (ParsedAnswer.read ya.1.1 ya.1.2 ya.2 : ParsedAnswer (ι → F) A PA))
      (by intro a b hab; rcases a with ⟨⟨y, yp⟩, a⟩; rcases b with ⟨⟨z, zp⟩, b⟩
          simpa only [ParsedAnswer.read.injEq, Prod.mk.injEq, and_assoc] using hab)]
    · exact (fullReadOp_isPVM L D R w h).sum_eq_one
    · intro a ha
      cases a with
      | read y yp a => exact (ha ⟨((y, yp), a), rfl⟩).elim
      | pauli p => rfl
      | pair y a => rfl
      | hide y yp x => rfl

theorem parsedHideOp_isPVM (w : Bool) (k : ℕ) (h : (L w).SupportedOn Finset.univ) :
    IsPVM (parsedHideOp (PA := PA) L D R w k h) where
  isSelfAdjoint a := by
    cases a <;> simp only [parsedHideOp, conjTranspose_zero]
    rw [conjTranspose_kronecker, (hideOp_isPVM (L w) k h).isSelfAdjoint, conjTranspose_one]
  idem a := by
    cases a <;> simp only [parsedHideOp, zero_mul]
    rw [← mul_kronecker_mul, (hideOp_isPVM (L w) k h).idem, one_mul]
  sum_eq_one := by
    rw [sum_supported (fun y : HideLabel F ι =>
      (ParsedAnswer.hide y.1 y.2.1 y.2.2 : ParsedAnswer (ι → F) A PA))
      (by intro a b hab; rcases a with ⟨y, yp, x⟩; rcases b with ⟨z, zp, t⟩
          simpa only [ParsedAnswer.hide.injEq, Prod.mk.injEq] using hab)]
    · change (∑ a : HideLabel F ι, hideOp (L w) k h a ⊗ₖ
        (1 : Matrix (Fin R.d) (Fin R.d) ℂ)) = 1
      rw [← sum_kronecker_left, (hideOp_isPVM (L w) k h).sum_eq_one, one_kronecker_one]
    · intro a ha
      cases a with
      | hide y yp x => exact (ha ⟨(y, yp, x), rfl⟩).elim
      | pauli p => rfl
      | pair y a => rfl
      | read y yp a => rfl

/-- Wrong constructor labels commute trivially; proper labels use the actual Read refinement. -/
theorem parsedCore_read_commute (w : Bool) (h : (L w).SupportedOn Finset.univ)
    (a b : ParsedAnswer (ι → F) A PA) :
    Commute (parsedCoreOp L D R (false, w) a) (parsedReadOp L D R w h b) := by
  cases a <;> cases b <;> simp only [parsedCoreOp, parsedReadOp, Commute.zero_left,
    Commute.zero_right]
  exact introspect_read_commute L D R w h _ _

theorem parsedRead_core_commute (w : Bool) (h : (L w).SupportedOn Finset.univ)
    (a b : ParsedAnswer (ι → F) A PA) :
    Commute (parsedReadOp L D R w h a) (parsedCoreOp L D R (false, w) b) :=
  (parsedCore_read_commute L D R w h b a).symm

/-- Every rejected pair of parsed labels on the reading edge has zero operator product. -/
theorem parsedCore_read_reject_zero {P : Type*} (X Z : P) (projectPauli : PA → ι → F)
    (DP : P → P → PA → PA → Bool) (w : Bool) (h : (L w).SupportedOn Finset.univ)
    (a b : ParsedAnswer (ι → F) A PA)
    (hr : TypedPredicate.check L X Z projectPauli D DP
      (.inr (.introspect, w)) (.inr (.read, w)) a b = false) :
    parsedCoreOp L D R (false, w) a * parsedReadOp L D R w h b = 0 := by
  cases a <;> cases b <;> simp only [parsedCoreOp, parsedReadOp, zero_mul, mul_zero]
  exact read_typed_reject_zero L D R X Z projectPauli DP w h _ _ hr

/-- The reversed ordered reading edge has the same all-label rejection guarantee. -/
theorem parsedRead_core_reject_zero {P : Type*} (X Z : P) (projectPauli : PA → ι → F)
    (DP : P → P → PA → PA → Bool) (w : Bool) (h : (L w).SupportedOn Finset.univ)
    (a b : ParsedAnswer (ι → F) A PA)
    (hr : TypedPredicate.check L X Z projectPauli D DP
      (.inr (.read, w)) (.inr (.introspect, w)) a b = false) :
    parsedReadOp L D R w h a * parsedCoreOp L D R (false, w) b = 0 := by
  rw [(parsedRead_core_commute L D R w h a b).eq]
  apply parsedCore_read_reject_zero L D R X Z projectPauli DP w h b a
  cases a <;> cases b <;>
    simp [TypedPredicate.check, TypedPredicate.fits, TypedPredicate.directed,
      Bool.and_comm] at hr ⊢
  exact hr

end MIPRE.Introspection.Honest

end

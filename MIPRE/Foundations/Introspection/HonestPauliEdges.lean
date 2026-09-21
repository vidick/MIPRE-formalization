/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.HonestPauliRegister
import MIPRE.Foundations.Introspection.HonestParsedHiding
import MIPRE.Foundations.Introspection.HonestSampling

/-! # Honest Pauli anchor edges on every parsed answer

The X and Z effects below are the genuine full-register basis measurements.
They leave the original strategy's auxiliary register unchanged. This file
connects them to the same parsed Sample and Hide effects used in the complete
auxiliary construction, including all malformed answer constructors.
-/

noncomputable section

namespace MIPRE.Introspection.Honest

open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false

section Parsed
variable {I V A PA : Type*} [Fintype I] [DecidableEq I]
  [Fintype V] [Fintype A] [Fintype PA]

def parsedPauliOp (M : PA → Matrix I I ℂ) : ParsedAnswer V A PA → Matrix I I ℂ
  | .pauli a => M a
  | _ => 0

theorem parsedPauliOp_isPVM (M : PA → Matrix I I ℂ) (hM : IsPVM M) :
    IsPVM (parsedPauliOp (V := V) (A := A) M) where
  isSelfAdjoint a := by
    cases a <;> simp only [parsedPauliOp, conjTranspose_zero]
    exact hM.isSelfAdjoint _
  idem a := by
    cases a <;> simp only [parsedPauliOp, zero_mul]
    exact hM.idem _
  sum_eq_one := by
    calc
      _ = ∑ a : PA, M a := by
        symm
        apply Fintype.sum_of_injective (fun a => (ParsedAnswer.pauli a : ParsedAnswer V A PA))
          (by intro a b h; simpa using h)
        · intro a ha
          cases a with
          | pauli a => exact (ha ⟨a, rfl⟩).elim
          | pair y a => rfl
          | read y yp a => rfl
          | hide y yp x => rfl
        · intro a; rfl
      _ = 1 := hM.sum_eq_one
end Parsed

variable {F ι A : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A] {ℓ : ℕ}
  (L : Bool → CL.CLFun F ι ℓ) (D : (ι → F) → (ι → F) → A → A → Bool)
  (R : SyncStrategy (sourceGame L D).doubled)

def pauliXOp (x : ι → F) : Matrix ((ι → F) × Fin R.d) ((ι → F) × Fin R.d) ℂ :=
  proj wX x ⊗ₖ (1 : Matrix (Fin R.d) (Fin R.d) ℂ)

theorem pauliXOp_isPVM : IsPVM (pauliXOp L D R) where
  isSelfAdjoint x := by simp [pauliXOp, conjTranspose_kronecker, proj_conjTranspose isWeylFamily_wX]
  idem x := by simp [pauliXOp, ← mul_kronecker_mul, proj_mul_proj isWeylFamily_wX]
  sum_eq_one := by
    simp only [pauliXOp]
    rw [← sum_kronecker_left, sum_proj isWeylFamily_wX, one_kronecker_one]

theorem pauliZOp_isPVM : IsPVM (pauliZOp L D R) where
  isSelfAdjoint x := by
    rw [pauliZOp, conjTranspose_kronecker, (readout_isPVM id).isSelfAdjoint, conjTranspose_one]
  idem x := by rw [pauliZOp, ← mul_kronecker_mul, (readout_isPVM id).idem, one_mul]
  sum_eq_one := by
    simp only [pauliZOp]
    rw [← sum_kronecker_left, (readout_isPVM id).sum_eq_one, one_kronecker_one]

def parsedPauliXOp : ParsedAnswer (ι → F) A (ι → F) →
    Matrix ((ι → F) × Fin R.d) ((ι → F) × Fin R.d) ℂ := parsedPauliOp (pauliXOp L D R)

def parsedPauliZOp : ParsedAnswer (ι → F) A (ι → F) →
    Matrix ((ι → F) × Fin R.d) ((ι → F) × Fin R.d) ℂ := parsedPauliOp (pauliZOp L D R)

theorem parsedPauliXOp_isPVM : IsPVM (parsedPauliXOp L D R) :=
  parsedPauliOp_isPVM _ (pauliXOp_isPVM L D R)

theorem parsedPauliZOp_isPVM : IsPVM (parsedPauliZOp L D R) :=
  parsedPauliOp_isPVM _ (pauliZOp_isPVM L D R)

theorem parsedPauliX_hide_commute (w : Bool) (h : (L w).SupportedOn Finset.univ)
    (a b : ParsedAnswer (ι → F) A (ι → F)) :
    Commute (parsedPauliXOp L D R a) (parsedHideOp L D R w 0 h b) := by
  cases a <;> cases b <;> simp only [parsedPauliXOp, parsedPauliOp, parsedHideOp,
    Commute.zero_left, Commute.zero_right]
  exact kronecker_commute (pauliX_hideOp_zero_commute _ h _ _) (Commute.refl _)

theorem parsedPauliZ_sample_commute (w : Bool) (a b : ParsedAnswer (ι → F) A (ι → F)) :
    Commute (parsedPauliZOp L D R a) (parsedCoreOp L D R (true, w) b) := by
  cases a <;> cases b <;> simp only [parsedPauliZOp, parsedPauliOp, parsedCoreOp,
    Commute.zero_left, Commute.zero_right]
  exact pauliZ_sample_commute L D R w _ _

private theorem check_pauli_aux_swap {P : Type*} (X Z : P)
    (DP : P → P → (ι → F) → (ι → F) → Bool) (p : P) (t : AuxType ℓ × Bool)
    (a b : ParsedAnswer (ι → F) A (ι → F)) :
    TypedPredicate.check L X Z id D DP (.inl p) (.inr t) a b =
      TypedPredicate.check L X Z id D DP (.inr t) (.inl p) b a := by
  simp [TypedPredicate.check, Bool.and_comm, Bool.and_left_comm]

theorem parsedPauliX_hide_reject_zero {P : Type*} (X Z : P)
    (DP : P → P → (ι → F) → (ι → F) → Bool) (w : Bool)
    (k : Fin ℓ) (hk : k.val = 0) (h : (L w).SupportedOn Finset.univ)
    (a b : ParsedAnswer (ι → F) A (ι → F))
    (hr : TypedPredicate.check L X Z id D DP (.inl X) (.inr (.hide k, w)) a b = false) :
    parsedPauliXOp L D R a * parsedHideOp L D R w 0 h b = 0 := by
  cases a <;> cases b <;> simp only [parsedPauliXOp, parsedPauliOp, parsedHideOp, zero_mul, mul_zero]
  rename_i x y yp t
  change (proj wX x ⊗ₖ (1 : Matrix (Fin R.d) _ ℂ)) * (hideOp (L w) 0 h (y, yp, t) ⊗ₖ 1) = 0
  rw [← mul_kronecker_mul, hideOp_zero_eq_firstHideOp,
    firstHide_typed_reject_zero L X Z D DP w k hk x (y, yp, t) hr, zero_kronecker]

theorem parsedPauliZ_sample_reject_zero {P : Type*} (X Z : P)
    (DP : P → P → (ι → F) → (ι → F) → Bool) (w : Bool)
    (a b : ParsedAnswer (ι → F) A (ι → F))
    (hr : TypedPredicate.check L X Z id D DP (.inl Z) (.inr (.sample, w)) a b = false) :
    parsedPauliZOp L D R a * parsedCoreOp L D R (true, w) b = 0 := by
  cases a <;> cases b <;> simp only [parsedPauliZOp, parsedPauliOp, parsedCoreOp, zero_mul, mul_zero]
  exact sample_typed_reject_zero L D R X Z DP w _ _ hr

theorem parsedHide_pauliX_reject_zero {P : Type*} (X Z : P)
    (DP : P → P → (ι → F) → (ι → F) → Bool) (w : Bool)
    (k : Fin ℓ) (hk : k.val = 0) (h : (L w).SupportedOn Finset.univ)
    (a b : ParsedAnswer (ι → F) A (ι → F))
    (hr : TypedPredicate.check L X Z id D DP (.inr (.hide k, w)) (.inl X) a b = false) :
    parsedHideOp L D R w 0 h a * parsedPauliXOp L D R b = 0 := by
  rw [← (parsedPauliX_hide_commute L D R w h b a).eq]
  exact parsedPauliX_hide_reject_zero L D R X Z DP w k hk h b a
    (by rwa [check_pauli_aux_swap L D X Z DP])

theorem parsedSample_pauliZ_reject_zero {P : Type*} (X Z : P)
    (DP : P → P → (ι → F) → (ι → F) → Bool) (w : Bool)
    (a b : ParsedAnswer (ι → F) A (ι → F))
    (hr : TypedPredicate.check L X Z id D DP (.inr (.sample, w)) (.inl Z) a b = false) :
    parsedCoreOp L D R (true, w) a * parsedPauliZOp L D R b = 0 := by
  rw [← (parsedPauliZ_sample_commute L D R w b a).eq]
  exact parsedPauliZ_sample_reject_zero L D R X Z DP w b a
    (by rwa [check_pauli_aux_swap L D X Z DP])

end MIPRE.Introspection.Honest

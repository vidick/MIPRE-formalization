/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.HonestCore

/-! # Perfect honest Pauli-Z/Sample edges

The Pauli-Z measurement reads the seed register and ignores the original
strategy's auxiliary register. Its product with the honest Sample operator
is zero unless their complete reported seeds agree.
-/

noncomputable section

namespace MIPRE.Introspection.Honest

open Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false

variable {F ι A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A] {ℓ : ℕ}
variable (L : Bool → CL.CLFun F ι ℓ) (D : (ι → F) → (ι → F) → A → A → Bool)
variable (R : SyncStrategy (sourceGame L D).doubled)

def pauliZOp (z : ι → F) : Matrix ((ι → F) × Fin R.d) ((ι → F) × Fin R.d) ℂ :=
  readout (id : (ι → F) → (ι → F)) z ⊗ₖ (1 : Matrix (Fin R.d) (Fin R.d) ℂ)

theorem sampleOp_eq (w : Bool) (ya : (ι → F) × A) :
    coreOp L D R (true, w) ya =
      readout (id : (ι → F) → (ι → F)) ya.1 ⊗ₖ R.P.M (w, (L w).eval ya.1) ya.2 := rfl

theorem pauliZ_sample_mul (w : Bool) (z : ι → F) (ya : (ι → F) × A) :
    pauliZOp L D R z * coreOp L D R (true, w) ya =
      if z = ya.1 then coreOp L D R (true, w) ya else 0 := by
  rw [pauliZOp, sampleOp_eq, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    (readout_isPVM (id : (ι → F) → (ι → F))).mul_eq_ite]
  by_cases h : z = ya.1
  · subst z; simp
  · simp [h]

theorem sample_pauliZ_mul (w : Bool) (z : ι → F) (ya : (ι → F) × A) :
    coreOp L D R (true, w) ya * pauliZOp L D R z =
      if z = ya.1 then coreOp L D R (true, w) ya else 0 := by
  rw [pauliZOp, sampleOp_eq, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
    (readout_isPVM (id : (ι → F) → (ι → F))).mul_eq_ite]
  by_cases h : z = ya.1
  · subst z; simp
  · simp [h, Ne.symm h]

theorem pauliZ_sample_commute (w : Bool) (z : ι → F) (ya : (ι → F) × A) :
    Commute (pauliZOp L D R z) (coreOp L D R (true, w) ya) := by
  show _ * _ = _ * _
  rw [pauliZ_sample_mul, sample_pauliZ_mul]

theorem sample_typed_check {P : Type*} (X Z : P)
    (DP : P → P → (ι → F) → (ι → F) → Bool) (w : Bool)
    (z : ι → F) (ya : (ι → F) × A) :
    TypedPredicate.check L X Z id D DP (.inl Z) (coreType (true, w))
      (.pauli z) (.pair ya.1 ya.2) = decide (z = ya.1) := by
  simp [coreType, TypedPredicate.check, TypedPredicate.fits, TypedPredicate.directed]

/-- Rejection by the actual Pauli-Z/Sample parsed test has zero honest operator product. -/
theorem sample_typed_reject_zero {P : Type*} (X Z : P)
    (DP : P → P → (ι → F) → (ι → F) → Bool) (w : Bool)
    (z : ι → F) (ya : (ι → F) × A)
    (h : TypedPredicate.check L X Z id D DP (.inl Z) (coreType (true, w))
      (.pauli z) (.pair ya.1 ya.2) = false) :
    pauliZOp L D R z * coreOp L D R (true, w) ya = 0 := by
  rw [sample_typed_check L D X Z DP w z ya] at h
  rw [pauliZ_sample_mul, if_neg (of_decide_eq_false h)]

end MIPRE.Introspection.Honest

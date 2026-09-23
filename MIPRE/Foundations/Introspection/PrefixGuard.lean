/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.TypedPredicate

/-! # Semantic prefix guards for executable introspection

A Hide answer at level `k` must have an attained `k`-stage prefix. A Read
answer must have an attained penultimate prefix. Constructor validity remains
the responsibility of the existing typed format check.
-/

noncomputable section
namespace MIPRE.Introspection.PrefixGuard
open Classical

variable {F ι A PA P : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

/-- The local image condition imposed by the executable prefix scan. -/
def holds (L : Bool → CL.CLFun F ι ℓ) :
    QuestionType P ℓ → ParsedAnswer (ι → F) A PA → Prop
  | .inr (.hide k, w), .hide y _ _ =>
      ∃ x, ((L w).truncate k.val).eval x = (L w).outputPrefix k.val y
  | .inr (.read, w), .read y _ _ =>
      ∃ x, ((L w).truncate (ℓ - 1)).eval x = (L w).outputPrefix (ℓ - 1) y
  | _, _ => True

/-- Boolean presentation of the local guard; executable scans implement this proposition. -/
def check (L : Bool → CL.CLFun F ι ℓ) (t : QuestionType P ℓ)
    (a : ParsedAnswer (ι → F) A PA) : Bool := decide (holds L t a)

@[simp] theorem check_eq_true (L : Bool → CL.CLFun F ι ℓ) (t : QuestionType P ℓ)
    (a : ParsedAnswer (ι → F) A PA) : check L t a = true ↔ holds L t a := by
  simp [check]

/-- Add both local guards to any typed comparison. -/
def guarded (L : Bool → CL.CLFun F ι ℓ)
    (D : QuestionType P ℓ → QuestionType P ℓ →
      ParsedAnswer (ι → F) A PA → ParsedAnswer (ι → F) A PA → Bool)
    (t u : QuestionType P ℓ) (a b : ParsedAnswer (ι → F) A PA) : Bool :=
  check L t a && check L u b && D t u a b

theorem guarded_eq_true (L : Bool → CL.CLFun F ι ℓ)
    (D : QuestionType P ℓ → QuestionType P ℓ →
      ParsedAnswer (ι → F) A PA → ParsedAnswer (ι → F) A PA → Bool)
    (t u : QuestionType P ℓ) (a b : ParsedAnswer (ι → F) A PA) :
    guarded L D t u a b = true ↔ holds L t a ∧ holds L u b ∧ D t u a b = true := by
  simp [guarded, and_assoc]

theorem guarded_eq_of_holds (L : Bool → CL.CLFun F ι ℓ)
    (D : QuestionType P ℓ → QuestionType P ℓ →
      ParsedAnswer (ι → F) A PA → ParsedAnswer (ι → F) A PA → Bool)
    (t u : QuestionType P ℓ) (a b : ParsedAnswer (ι → F) A PA)
    (ha : holds L t a) (hb : holds L u b) : guarded L D t u a b = D t u a b := by
  simp [guarded, check, ha, hb]

end MIPRE.Introspection.PrefixGuard

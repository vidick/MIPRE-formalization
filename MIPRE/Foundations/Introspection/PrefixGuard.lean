/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.TypedPredicate

@[expose] public section

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

end MIPRE.Introspection.PrefixGuard

end

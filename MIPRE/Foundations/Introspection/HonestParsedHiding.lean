/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.HonestParsed
import MIPRE.Foundations.Introspection.HonestHidingCommute
import MIPRE.Foundations.Introspection.HonestHidingAcceptance

/-! # Honest hiding checks on every parsed-answer label

The adjacent Hide and terminal Hide/Read edges use the actual adaptive
operators on the common register/source space. Both ordered orientations
commute, and every rejected answer pair has zero operator product. Wrong
constructors are retained as zero effects throughout.
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

/-- Consecutive hiding levels commute for all parsed labels, including wrong constructors. -/
theorem parsedHide_next_commute (w : Bool) (k : ℕ) (h : (L w).SupportedOn Finset.univ)
    (a b : ParsedAnswer (ι → F) A PA) :
    Commute (parsedHideOp L D R w k h a) (parsedHideOp L D R w (k + 1) h b) := by
  cases a <;> cases b <;> simp only [parsedHideOp, Commute.zero_left, Commute.zero_right]
  exact kronecker_commute (hideOp_commute_next (L w) k h _ _) (Commute.refl _)

theorem parsedHide_next_commute_reversed (w : Bool) (k : ℕ)
    (h : (L w).SupportedOn Finset.univ) (a b : ParsedAnswer (ι → F) A PA) :
    Commute (parsedHideOp L D R w (k + 1) h a) (parsedHideOp L D R w k h b) :=
  (parsedHide_next_commute L D R w k h b a).symm

/-- The terminal hiding level commutes with the full Read measurement and its source answer. -/
theorem parsedHide_read_commute (w : Bool) (k : ℕ) (hk : ℓ ≤ k + 1)
    (h : (L w).SupportedOn Finset.univ) (a b : ParsedAnswer (ι → F) A PA) :
    Commute (parsedHideOp L D R w k h a) (parsedReadOp L D R w h b) := by
  cases a <;> cases b <;> simp only [parsedHideOp, parsedReadOp,
    Commute.zero_left, Commute.zero_right]
  exact kronecker_commute (hideOp_commute_read (L w) k hk h _ _) (Commute.one_left _)

theorem parsedRead_hide_commute (w : Bool) (k : ℕ) (hk : ℓ ≤ k + 1)
    (h : (L w).SupportedOn Finset.univ) (a b : ParsedAnswer (ι → F) A PA) :
    Commute (parsedReadOp L D R w h a) (parsedHideOp L D R w k h b) :=
  (parsedHide_read_commute L D R w k hk h b a).symm

private theorem aux_check_swap {P : Type*} (X Z : P) (projectPauli : PA → ι → F)
    (DP : P → P → PA → PA → Bool) (t u : AuxType ℓ × Bool)
    (a b : ParsedAnswer (ι → F) A PA) :
    TypedPredicate.check L X Z projectPauli D DP (.inr t) (.inr u) a b =
      TypedPredicate.check L X Z projectPauli D DP (.inr u) (.inr t) b a := by
  by_cases ht : t = u <;> by_cases hab : a = b <;>
    simp [TypedPredicate.check, ht, hab, eq_comm, Bool.and_comm,
      Bool.and_left_comm]

private theorem hide_next_check {P : Type*} (X Z : P) (projectPauli : PA → ι → F)
    (DP : P → P → PA → PA → Bool) (w : Bool) (k j : Fin ℓ) (hk : k.val + 1 = j.val)
    (a b : HideLabel F ι) :
    TypedPredicate.check L X Z projectPauli D DP (.inr (.hide k, w)) (.inr (.hide j, w))
      (.hide a.1 a.2.1 a.2.2) (.hide b.1 b.2.1 b.2.2) =
        decide (CLChecks.hidingNext (L w) k.val a b) := by
  have hne : k ≠ j := by intro he; have := congrArg Fin.val he; omega
  have hrev : ¬ j.val + 1 = k.val := by omega
  simp [TypedPredicate.check, TypedPredicate.fits, TypedPredicate.directed, hk, hne, hrev]

private theorem hide_read_check {P : Type*} (X Z : P) (projectPauli : PA → ι → F)
    (DP : P → P → PA → PA → Bool) (w : Bool) (k : Fin ℓ) (hk : k.val + 1 = ℓ)
    (a : HideLabel F ι) (b : ReadLabel F ι × A) :
    TypedPredicate.check L X Z projectPauli D DP (.inr (.hide k, w)) (.inr (.read, w))
      (.hide a.1 a.2.1 a.2.2) (.read b.1.1 b.1.2 b.2) =
        decide (CLChecks.hidingRead (L w) a (b.1.1, b.1.2, b.2)) := by
  simp [TypedPredicate.check, TypedPredicate.fits, TypedPredicate.directed, hk]

/-- Rejection by the actual adjacent-Hide predicate annihilates the honest full-space product. -/
theorem parsedHide_next_reject_zero {P : Type*} (X Z : P) (projectPauli : PA → ι → F)
    (DP : P → P → PA → PA → Bool) (w : Bool) (k j : Fin ℓ) (hk : k.val + 1 = j.val)
    (h : (L w).SupportedOn Finset.univ) (a b : ParsedAnswer (ι → F) A PA)
    (hr : TypedPredicate.check L X Z projectPauli D DP
      (.inr (.hide k, w)) (.inr (.hide j, w)) a b = false) :
    parsedHideOp L D R w k.val h a * parsedHideOp L D R w j.val h b = 0 := by
  cases a <;> cases b <;> simp only [parsedHideOp, zero_mul, mul_zero]
  rename_i ya ypa xa yb ypb xb
  rw [hide_next_check L D X Z projectPauli DP w k j hk (ya, ypa, xa) (yb, ypb, xb)] at hr
  rw [← hk, ← mul_kronecker_mul,
    hideOp_reject_next_zero (L w) k.val (by omega) h _ _ (of_decide_eq_false hr),
    zero_kronecker]

theorem parsedHide_next_reject_zero_reversed {P : Type*} (X Z : P)
    (projectPauli : PA → ι → F) (DP : P → P → PA → PA → Bool)
    (w : Bool) (k j : Fin ℓ) (hk : k.val + 1 = j.val)
    (h : (L w).SupportedOn Finset.univ) (a b : ParsedAnswer (ι → F) A PA)
    (hr : TypedPredicate.check L X Z projectPauli D DP
      (.inr (.hide j, w)) (.inr (.hide k, w)) a b = false) :
    parsedHideOp L D R w j.val h a * parsedHideOp L D R w k.val h b = 0 := by
  have hc := parsedHide_next_commute L D R w k.val h b a
  rw [hk] at hc
  rw [← hc.eq]
  apply parsedHide_next_reject_zero L D R X Z projectPauli DP w k j hk h b a
  rw [aux_check_swap]
  exact hr

/-- Rejection by the terminal Hide/Read predicate annihilates the actual operator product. -/
theorem parsedHide_read_reject_zero {P : Type*} (X Z : P) (projectPauli : PA → ι → F)
    (DP : P → P → PA → PA → Bool) (w : Bool) (k : Fin ℓ) (hk : k.val + 1 = ℓ)
    (h : (L w).SupportedOn Finset.univ) (a b : ParsedAnswer (ι → F) A PA)
    (hr : TypedPredicate.check L X Z projectPauli D DP
      (.inr (.hide k, w)) (.inr (.read, w)) a b = false) :
    parsedHideOp L D R w k.val h a * parsedReadOp L D R w h b = 0 := by
  cases a <;> cases b <;> simp only [parsedHideOp, parsedReadOp, zero_mul, mul_zero]
  rename_i ya ypa xa yb ypb ab
  rw [hide_read_check L D X Z projectPauli DP w k hk (ya, ypa, xa) ((yb, ypb), ab)] at hr
  rw [fullReadOp, ← mul_kronecker_mul,
    hideOp_reject_read_zero (L w) k.val hk h _ _ _ (of_decide_eq_false hr), zero_kronecker]

theorem parsedRead_hide_reject_zero {P : Type*} (X Z : P) (projectPauli : PA → ι → F)
    (DP : P → P → PA → PA → Bool) (w : Bool) (k : Fin ℓ) (hk : k.val + 1 = ℓ)
    (h : (L w).SupportedOn Finset.univ) (a b : ParsedAnswer (ι → F) A PA)
    (hr : TypedPredicate.check L X Z projectPauli D DP
      (.inr (.read, w)) (.inr (.hide k, w)) a b = false) :
    parsedReadOp L D R w h a * parsedHideOp L D R w k.val h b = 0 := by
  rw [(parsedRead_hide_commute L D R w k.val (by omega) h a b).eq]
  apply parsedHide_read_reject_zero L D R X Z projectPauli DP w k hk h b a
  rw [aux_check_swap]
  exact hr

end MIPRE.Introspection.Honest

end

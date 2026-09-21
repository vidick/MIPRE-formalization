/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.ConditionalNormalizerExact
import MIPRE.Foundations.Introspection.HonestHidingCommute
import MIPRE.Foundations.Introspection.HonestHidingAcceptance
import MIPRE.Foundations.Introspection.HidingMaps

/-! # Concrete ideal prefixes for honest hiding

The next Z prefix is a marginal of the adjacent honest hiding PVM. Thus its
commutation with the preceding honest hiding family follows from the proved
adjacent commutation, without a new commutation assumption.
-/

noncomputable section

namespace MIPRE.Introspection.Honest

open Finset Matrix Classical
open scoped Kronecker

set_option linter.unusedSectionVars false

variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

/-- The ideal prefix retains an explicit zero operator for malformed labels. -/
def hidingPrefixOp (P : CL.CLFun F ι ℓ) (k : ℕ) :
    Option (ι → F) → Matrix (ι → F) (ι → F) ℂ :=
  readout (fun x => some ((P.truncate k).eval x))

@[simp] theorem hidingPrefixOp_none (P : CL.CLFun F ι ℓ) (k : ℕ) :
    hidingPrefixOp P k none = 0 := by
  ext x x'
  simp [hidingPrefixOp, readout, Matrix.diagonal_apply]

@[simp] theorem hidingPrefixOp_some (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F) :
    hidingPrefixOp P k (some y) = readout (P.truncate k).eval y := by
  ext x x'
  simp [hidingPrefixOp, readout, Matrix.diagonal_apply]

theorem hidingPrefixOp_isPVM (P : CL.CLFun F ι ℓ) (k : ℕ) :
    IsPVM (hidingPrefixOp P k) := readout_isPVM _

/-- The next ideal Z prefix commutes with every actual preceding honest Hide
operator, including prefixes whose readout projector is zero. -/
theorem hidingPrefixOp_commute_hideOp (P : CL.CLFun F ι ℓ) (k : ℕ)
    (h : P.SupportedOn univ) (y : Option (ι → F)) (a : HideLabel F ι) :
    Commute (hidingPrefixOp P (k + 1) y) (hideOp P k h a) := by
  cases y with
  | none => rw [hidingPrefixOp_none]; exact Commute.zero_left _
  | some y =>
    rw [hidingPrefixOp_some, ← hideOp_marginal P (k + 1) h y]
    apply Commute.sum_left
    intro b _
    exact (hideOp_commute_next P k h a (y, b)).symm

/-- The same explicit prefix commutes with any coarse family of the preceding
honest hiding measurement. This applies to the retained fine label in the
soundness induction. -/
theorem hidingPrefixOp_commute_coarse (P : CL.CLFun F ι ℓ) (k : ℕ)
    (h : P.SupportedOn univ) {J : Type*} [Fintype J] [DecidableEq J]
    (f : HideLabel F ι → J) (y : Option (ι → F)) (j : J) :
    Commute (hidingPrefixOp P (k + 1) y) (fibSum (hideOp P k h) f j) :=
  commute_fibSum_right (hideOp P k h) (hidingPrefixOp P (k + 1))
    (hidingPrefixOp_commute_hideOp P k h) f y j

theorem hideOp_entry_prefix (P : CL.CLFun F ι ℓ) (k : ℕ)
    (h : P.SupportedOn univ) (a : HideLabel F ι) (x x' : ι → F)
    (ha : hideOp P k h a x x' ≠ 0) : (P.truncate k).eval x = a.1 := by
  have he := hideRegister_entry_nonzero P k univ h a
    (univRestriction x) (univRestriction x') ha
  simpa using he

theorem hideOp_prefix_fixed (P : CL.CLFun F ι ℓ) (k : ℕ)
    (h : P.SupportedOn univ) (a : HideLabel F ι) (ha : hideOp P k h a ≠ 0) :
    P.outputPrefix k a.1 = a.1 := by
  have hex : ∃ x x', hideOp P k h a x x' ≠ 0 := by
    by_contra hn
    apply ha
    ext x x'
    exact not_not.mp (by simpa using not_exists.mp (not_exists.mp hn x) x')
  obtain ⟨x, x', hx⟩ := hex
  rw [← hideOp_entry_prefix P k h a x x' hx, ← h.outputPrefix_eval]
  exact CLChecks.outputPrefix_outputPrefix h _ le_rfl

theorem readout_mul_hideOp (P : CL.CLFun F ι ℓ) (k : ℕ)
    (h : P.SupportedOn univ) (y : ι → F) (a : HideLabel F ι) :
    readout (P.truncate k).eval y * hideOp P k h a =
      if a.1 = y then hideOp P k h a else 0 := by
  ext x x'
  rw [readout, Matrix.diagonal_mul]
  by_cases he : hideOp P k h a x x' = 0
  · by_cases hy : a.1 = y <;> simp [he, hy]
  · rw [hideOp_entry_prefix P k h a x x' he]
    by_cases hy : a.1 = y <;> simp [hy]

/-- Interpret a register hiding label as a correctly formatted parsed answer. -/
def hideLabelAnswer (a : HideLabel F ι) : ParsedAnswer (ι → F) Unit Unit :=
  .hide a.1 a.2.1 a.2.2

def hideLabelCoarse (P : CL.CLFun F ι ℓ) (k : ℕ) (a : HideLabel F ι) :
    Option (HideLabel F ι) := TypedEstimates.hidingCoarse P k (hideLabelAnswer a)

def hideLabelNext (P : CL.CLFun F ι ℓ) (k : ℕ) (a : HideLabel F ι) :
    Option (ι → F) × Option (HideLabel F ι) :=
  TypedEstimates.hidingNextLater P k (hideLabelAnswer a)

/-- The next prefix selects exactly the conditioning key of an honest next
Hide outcome. The fixed-prefix property is proved from matrix support. -/
theorem hidingPrefixOp_mul_next (P : CL.CLFun F ι ℓ) (k : ℕ)
    (h : P.SupportedOn univ) (y : Option (ι → F)) (a : HideLabel F ι) :
    hidingPrefixOp P (k + 1) y * hideOp P (k + 1) h a =
      if (hideLabelNext P k a).1 = y then hideOp P (k + 1) h a else 0 := by
  by_cases ha : hideOp P (k + 1) h a = 0
  · simp [ha]
  have hfix := hideOp_prefix_fixed P (k + 1) h a ha
  cases y with
  | none => simp [hideLabelNext, hideLabelAnswer, TypedEstimates.hidingNextLater,
      TypedEstimates.hidingNextCondition]
  | some y =>
    rw [hidingPrefixOp_some, readout_mul_hideOp]
    simp only [hideLabelNext, hideLabelAnswer, TypedEstimates.hidingNextLater,
      TypedEstimates.hidingNextCondition, hfix, Option.some.injEq]

theorem hideLabel_guarded_of_check (P : CL.CLFun F ι ℓ) (k : ℕ)
    (h : P.SupportedOn univ) (a b : HideLabel F ι)
    (hab : CLChecks.hidingNext P k a b) :
    TypedEstimates.hidingNextGuarded P k (hideLabelNext P k b).1 (hideLabelCoarse P k a) =
      (hideLabelNext P k b).2 := by
  have hmatch : P.outputPrefix k a.1 = P.outputPrefix k (P.outputPrefix (k + 1) b.1) := by
    rw [CLChecks.outputPrefix_outputPrefix h _ (by omega)]
    exact hab.1
  unfold hideLabelNext hideLabelCoarse hideLabelAnswer
  change TypedEstimates.hidingNextGuarded P k (some (P.outputPrefix (k + 1) b.1)) _ = _
  rw [TypedEstimates.hidingNextGuarded_factor h k a.1 a.2.1 a.2.2 _ hmatch]
  simp only [TypedEstimates.hidingNextEarlier, TypedEstimates.hidingNextLater,
    TypedEstimates.hidingNextCondition, Option.map_some,
    CLChecks.dualReadout_outputPrefix h,
    show k + 2 = (k + 1) + 1 by omega, CLChecks.prefixRegister_outputPrefix_succ h]
  exact congrArg some (Prod.ext hab.1 (Prod.ext hab.2.2.2.symm hab.2.2.1))

set_option backward.isDefEq.respectTransparency false in
/-- Exact identification of the conditional ideal product with the next
honest hiding PVM coarsened by the actual test's retained answer map. Every
premise is supplied by the recursively constructed honest operators. -/
theorem hideOp_conditionalIdeal_eq_next (P : CL.CLFun F ι ℓ) (k : ℕ)
    (hk : k + 1 < ℓ) (h : P.SupportedOn univ)
    (p : Option (ι → F) × Option (HideLabel F ι)) :
    conditionalIdeal (hideOp P k h) (hidingPrefixOp P (k + 1))
      (fun y a => TypedEstimates.hidingNextGuarded P k y (hideLabelCoarse P k a)) p =
        fibSum (hideOp P (k + 1) h) (hideLabelNext P k) p := by
  have he := conditionalIdeal_eq_coarse_of_reject (hideOp P k h) (hideOp P (k + 1) h)
    (hidingPrefixOp P (k + 1))
    (fun y a => TypedEstimates.hidingNextGuarded P k y (hideLabelCoarse P k a))
    (hideLabelNext P k) (hideOp_isPVM P k h) (hideOp_isPVM P (k + 1) h)
    (hidingPrefixOp_commute_hideOp P k h) (hidingPrefixOp_mul_next P k h)
    (by
      intro a b hab
      apply hideOp_reject_next_zero P k hk h a b
      intro hcheck
      exact hab (hideLabel_guarded_of_check P k h a b hcheck)) p
  refine he.trans ?_
  simp only [fibSum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : hideLabelNext P k a = p <;> simp [ha]

/-- The preceding ideal hiding family retains precisely the fine label used
by the parsed soundness induction. -/
def hideCoarseOp (P : CL.CLFun F ι ℓ) (k : ℕ) (h : P.SupportedOn univ) :
    Option (HideLabel F ι) → Matrix (ι → F) (ι → F) ℂ :=
  fibSum (hideOp P k h) (hideLabelCoarse P k)

theorem hideCoarseOp_isPVM (P : CL.CLFun F ι ℓ) (k : ℕ) (h : P.SupportedOn univ) :
    IsPVM (hideCoarseOp P k h) := isPVM_fibSum (hideOp_isPVM P k h) _

set_option backward.isDefEq.respectTransparency false in
/-- The guarded conditional ideal formed from the actual retained fine
family is exactly the next honest test-coarse measurement. -/
theorem hideCoarseOp_conditionalIdeal_eq_next (P : CL.CLFun F ι ℓ) (k : ℕ)
    (hk : k + 1 < ℓ) (h : P.SupportedOn univ)
    (p : Option (ι → F) × Option (HideLabel F ι)) :
    conditionalIdeal (hideCoarseOp P k h) (hidingPrefixOp P (k + 1))
      (TypedEstimates.hidingNextGuarded P k) p =
        fibSum (hideOp P (k + 1) h) (hideLabelNext P k) p := by
  have hc := coarseOp_comp (hideLabelCoarse P k)
    (TypedEstimates.hidingNextGuarded P k p.1) (hideOp P k h) p.2
  change fibSum (hideCoarseOp P k h) (TypedEstimates.hidingNextGuarded P k p.1) p.2 =
    fibSum (hideOp P k h)
      (fun a => TypedEstimates.hidingNextGuarded P k p.1 (hideLabelCoarse P k a)) p.2 at hc
  rw [conditionalIdeal, hc]
  exact hideOp_conditionalIdeal_eq_next P k hk h p

/-- Discard the now redundant old prefix and retain the new prefix, current
dual label, and tail. Dummy or inconsistent formats remain a dummy outcome. -/
def hideNextRetain : Option (ι → F) × Option (HideLabel F ι) → Option (HideLabel F ι)
  | (some y, some (_, yp, x)) => some (y, yp, x)
  | _ => none

theorem hideNextRetain_label (P : CL.CLFun F ι ℓ) (k : ℕ) (a : HideLabel F ι) :
    hideNextRetain (hideLabelNext P k a) = hideLabelCoarse P (k + 1) a := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Forgetting the redundant conditioning bookkeeping yields precisely the
next fine ideal hiding family, ready for the next induction stage. -/
theorem hideCoarseOp_conditionalIdeal_step (P : CL.CLFun F ι ℓ) (k : ℕ)
    (hk : k + 1 < ℓ) (h : P.SupportedOn univ) (z : Option (HideLabel F ι)) :
    fibSum (conditionalIdeal (hideCoarseOp P k h) (hidingPrefixOp P (k + 1))
      (TypedEstimates.hidingNextGuarded P k)) hideNextRetain z =
        hideCoarseOp P (k + 1) h z := by
  have he : conditionalIdeal (hideCoarseOp P k h) (hidingPrefixOp P (k + 1))
      (TypedEstimates.hidingNextGuarded P k) =
        fibSum (hideOp P (k + 1) h) (hideLabelNext P k) :=
    funext (hideCoarseOp_conditionalIdeal_eq_next P k hk h)
  rw [he]
  exact coarseOp_comp (hideLabelNext P k) hideNextRetain (hideOp P (k + 1) h) z

end MIPRE.Introspection.Honest

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.ConditionalNormalizerIdeal
public import MIPRE.Foundations.Introspection.HonestCompleteAux
public import MIPRE.Foundations.Introspection.PrefixGuard

@[expose] public section

/-! # Attained prefixes of honest hiding and reading outcomes

The honest register matrices already vanish outside the image of the relevant
CL computation. These lemmas expose that support on whole operators and on the
complete parsed-answer alphabet, so executable prefix scans may reject unattained
claims without changing honest measurements.
-/

noncomputable section
namespace MIPRE.Introspection.Honest

open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false

variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

/-- A nonzero honest Hide outcome reports an actual output after exactly `k` stages. -/
theorem hideOp_output_attained (P : CL.CLFun F ι ℓ) (k : ℕ)
    (h : P.SupportedOn univ) (a : HideLabel F ι) (ha : hideOp P k h a ≠ 0) :
    ∃ x, (P.truncate k).eval x = a.1 := by
  by_contra hn
  apply ha
  ext x x'
  by_contra he
  exact hn ⟨x, hideOp_entry_prefix P k h a x x' he⟩

/-- Every earlier prefix of a nonzero honest Hide claim is attained by the same seed. -/
theorem hideOp_prefix_attained (P : CL.CLFun F ι ℓ) (k : ℕ)
    (h : P.SupportedOn univ) (a : HideLabel F ι) (ha : hideOp P k h a ≠ 0)
    (j : ℕ) (hj : j ≤ k) : ∃ x, (P.truncate j).eval x = P.outputPrefix j a.1 := by
  obtain ⟨x, hx⟩ := hideOp_output_attained P k h a ha
  refine ⟨x, ?_⟩
  rw [← hx, ← h.outputPrefix_eval k, CLChecks.outputPrefix_outputPrefix h _ hj,
    h.outputPrefix_eval]

/-- A nonzero honest Read outcome reports an actual complete CL output. -/
theorem readOp_output_attained (P : CL.CLFun F ι ℓ)
    (h : P.SupportedOn univ) (a : ReadLabel F ι) (ha : readOp P h a ≠ 0) :
    ∃ x, P.eval x = a.1 := by
  by_contra hn
  apply ha
  ext x x'
  by_contra he
  have hx := readRegister_entry_nonzero P univ h a
    (univRestriction x) (univRestriction x') he
  exact hn ⟨x, by simpa using hx⟩

/-- Every prefix of a nonzero honest Read claim is attained, including `ℓ - 1`. -/
theorem readOp_prefix_attained (P : CL.CLFun F ι ℓ)
    (h : P.SupportedOn univ) (a : ReadLabel F ι) (ha : readOp P h a ≠ 0)
    (j : ℕ) : ∃ x, (P.truncate j).eval x = P.outputPrefix j a.1 := by
  obtain ⟨x, hx⟩ := readOp_output_attained P h a ha
  exact ⟨x, by rw [← hx, h.outputPrefix_eval]⟩

variable {A PA : Type*} [Fintype A] [DecidableEq A] [Fintype PA]
  (L : Bool → CL.CLFun F ι ℓ) (D : (ι → F) → (ι → F) → A → A → Bool)
  (R : SyncStrategy (sourceGame L D).doubled)

/-- Tensoring with the source identity does not create unattained Hide labels. -/
theorem parsedHideOp_prefix_attained (w : Bool) (k : ℕ) (h : (L w).SupportedOn univ)
    (y yp z : ι → F)
    (ha : parsedHideOp (PA := PA) L D R w k h (.hide y yp z) ≠ 0)
    (j : ℕ) (hj : j ≤ k) :
    ∃ x, ((L w).truncate j).eval x = (L w).outputPrefix j y := by
  apply hideOp_prefix_attained (L w) k h (y, yp, z) _ j hj
  intro hz
  apply ha
  simp [parsedHideOp, hz]

/-- Tensoring with the source answer effect does not create unattained Read labels. -/
theorem parsedReadOp_prefix_attained (w : Bool) (h : (L w).SupportedOn univ)
    (y yp : ι → F) (a : A)
    (ha : parsedReadOp (PA := PA) L D R w h (.read y yp a) ≠ 0) (j : ℕ) :
    ∃ x, ((L w).truncate j).eval x = (L w).outputPrefix j y := by
  apply readOp_prefix_attained (L w) h (y, yp) _ j
  intro hz
  apply ha
  simp [parsedReadOp, fullReadOp, hz]

/-- Every nonzero honest auxiliary effect passes the local prefix guard. The
claim includes every parsed label, so no format promise is needed. -/
theorem auxOp_nonzero_prefixGuard {P : Type*}
    (hL : ∀ w, (L w).SupportedOn univ) (t : AuxQuestion ℓ)
    (a : ParsedAnswer (ι → F) A PA) (ha : auxOp L D R hL t a ≠ 0) :
    PrefixGuard.holds L (.inr t : QuestionType P ℓ) a := by
  rcases t with ⟨t, w⟩
  cases t <;> cases a <;> try trivial
  · exact parsedReadOp_prefix_attained (PA := PA) L D R w (hL w) _ _ _ ha (ℓ - 1)
  · exact parsedHideOp_prefix_attained (PA := PA) L D R w _ (hL w) _ _ _ ha _ le_rfl

end MIPRE.Introspection.Honest

end

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.TypedPrefixChain
import MIPRE.Foundations.Introspection.HidingMaps

/-! # The dual readout retained along the actual hiding-to-Read chain

The stage and its preceding claimed prefix are fixed before coarse-graining.
Every later hiding edge preserves this same pair, including off-image answers.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Classical
set_option linter.unusedSectionVars false

namespace CLChecks

variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

theorem factorOfPrefix_outputPrefix {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y : ι → F) :
    P.factorOfPrefix k (P.outputPrefix k y) = P.factorOfPrefix k y := by
  induction P generalizing T k y with
  | zero => simp
  | cons S L next ih =>
    cases k with
    | zero => rfl
    | succ k =>
      obtain ⟨ha, hb⟩ := proj_outputPrefix_cons hP k y
      simp only [CL.CLFun.factorOfPrefix_cons_succ]
      rw [ha, hb, ih _ (hP.2 _) k _]

theorem factorOfPrefix_subset_prefixRegister (P : CL.CLFun F ι ℓ)
    (k : ℕ) (y : ι → F) :
    P.factorOfPrefix k y ⊆ prefixRegister P (k + 1) y := by
  induction P generalizing k y with
  | zero => simp
  | cons S L next ih =>
    cases k with
    | zero => simp [prefixRegister]
    | succ k =>
      exact (ih _ k _).trans (subset_union_right (s₁ := S))

end CLChecks

namespace TypedEstimates

variable {PauliType PauliAnswer F ι A : Type*}
  [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

/-- The prefix and the dual answer on one fixed stage's selected register. -/
def reportedDual (P : CL.CLFun F ι ℓ) (m : ℕ) :
    AuxType ℓ → ParsedAnswer (ι → F) A PauliAnswer → Option ((ι → F) × (ι → F))
  | .hide _, .hide y yp _ =>
      some (P.outputPrefix m y, CL.proj (P.factorOfPrefix m (P.outputPrefix m y)) yp)
  | .read, .read y yp _ =>
      some (P.outputPrefix m y, CL.proj (P.factorOfPrefix m (P.outputPrefix m y)) yp)
  | _, _ => none

/-- Forgetting only the unused tail of a fine hiding outcome. -/
def hidingForgetTail : Option ((ι → F) × (ι → F) × (ι → F)) →
    Option ((ι → F) × (ι → F)) := Option.map fun p => (p.1, p.2.1)

theorem hidingForgetTail_coarse (P : CL.CLFun F ι ℓ) (j : Fin ℓ)
    (a : ParsedAnswer (ι → F) A PauliAnswer) :
    hidingForgetTail (hidingCoarse P j.val a) = reportedDual P j.val (.hide j) a := by
  cases a <;> rfl

variable [DecidableEq PauliType]
  (L : Bool → CL.CLFun F ι ℓ) (X Z : PauliType)
  (projectPauli : PauliAnswer → ι → F)
  (D : (ι → F) → (ι → F) → A → A → Bool)
  (DP : PauliType → PauliType → PauliAnswer → PauliAnswer → Bool)

theorem check_hiding_next_dual (w : Bool) (hL : (L w).SupportedOn univ)
    (k j : Fin ℓ) (hk : k.val + 1 = j.val) (m : ℕ) (hm : m ≤ k.val)
    {a b : ParsedAnswer (ι → F) A PauliAnswer}
    (h : TypedPredicate.check L X Z projectPauli D DP
      (QuestionType.hide w k) (QuestionType.hide w j) a b = true) :
    reportedDual (L w) m (.hide k) a = reportedDual (L w) m (.hide j) b := by
  have hf := TypedPredicate.check_formats L X Z projectPauli D DP h
  cases a <;> cases b <;> simp [TypedPredicate.fits] at hf
  rename_i y yp x z zp t
  have hc := TypedPredicate.check_hiding_next L X Z projectPauli D DP w k j hk h
  have hp := congrArg ((L w).outputPrefix m) hc.1
  simp only [CLChecks.outputPrefix_outputPrefix hL _ hm] at hp
  have hs : (L w).factorOfPrefix m ((L w).outputPrefix m z) ⊆
      CLChecks.prefixRegister (L w) (k.val + 1) z := by
    rw [CLChecks.factorOfPrefix_outputPrefix hL]
    exact (CLChecks.factorOfPrefix_subset_prefixRegister (L w) m z).trans
      (CLChecks.prefixRegister_mono (L w) z (by omega))
  have hd := congrArg (CL.proj ((L w).factorOfPrefix m ((L w).outputPrefix m z))) hc.2.1
  simp only [CL.proj_proj_of_subset hs] at hd
  simp only [reportedDual, hp, hd]

theorem check_hiding_read_dual (w : Bool) (hL : (L w).SupportedOn univ)
    (k : Fin ℓ) (hk : k.val + 1 = ℓ) (m : ℕ) (hm : m ≤ k.val)
    {a b : ParsedAnswer (ι → F) A PauliAnswer}
    (h : TypedPredicate.check L X Z projectPauli D DP
      (QuestionType.hide w k) (QuestionType.read w) a b = true) :
    reportedDual (L w) m (.hide k) a = reportedDual (L w) m .read b := by
  have hf := TypedPredicate.check_formats L X Z projectPauli D DP h
  cases a <;> cases b <;> simp [TypedPredicate.fits] at hf
  rename_i y yp x z zp b
  have hc := TypedPredicate.check_hiding_read L X Z projectPauli D DP w k hk h
  have hp := congrArg ((L w).outputPrefix m) hc.1
  have hm' : m ≤ ℓ - 1 := by omega
  simp only [CLChecks.outputPrefix_outputPrefix hL _ hm'] at hp
  have hd : yp = zp := hc.2
  simp only [reportedDual, hp, hd]

@[simp] theorem prefixChainType_read (j : Fin ℓ) :
    prefixChainType j (ℓ - j.val) = .read := by
  have he : j.val + (ℓ - j.val) = ℓ := by omega
  simp [prefixChainType, he]

/-- Every edge up to Read preserves one fixed earlier dual readout. -/
theorem prefixChainType_check_dual (w : Bool) (hL : (L w).SupportedOn univ)
    (j : Fin ℓ) (m : ℕ) (hm : m ≤ j.val) (i : ℕ) (hi : i < ℓ - j.val)
    {a b : ParsedAnswer (ι → F) A PauliAnswer}
    (h : TypedPredicate.check L X Z projectPauli D DP
      (.inr (prefixChainType j i, w)) (.inr (prefixChainType j (i + 1), w)) a b = true) :
    reportedDual (L w) m (prefixChainType j i) a =
      reportedDual (L w) m (prefixChainType j (i + 1)) b := by
  have hp : j.val + i < ℓ := by omega
  by_cases hs : j.val + (i + 1) < ℓ
  · simp only [prefixChainType, dif_pos hp, dif_pos hs] at h ⊢
    exact check_hiding_next_dual L X Z projectPauli D DP w hL _ _
      (by simp; omega) m (by simp; omega) h
  · have he : j.val + (i + 1) = ℓ := by omega
    simp only [prefixChainType, dif_pos hp, dif_neg hs, if_pos he] at h ⊢
    exact check_hiding_read_dual L X Z projectPauli D DP w hL _
      (by simp; omega) m (by simp; omega) h

end TypedEstimates
end MIPRE.Introspection

end

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.HidingPrefix

/-! # Propagating reported question prefixes through the actual hiding chain

The adjacent hiding, terminal hiding/Read, and Read/Introspect tests preserve
every earlier question prefix. Coarse-graining these accepted-answer relations
before using consistency loops gives a polynomial chain loss, without an
answer-cardinality factor or an assumption that claimed answers are CL images.
-/

noncomputable section

namespace MIPRE.Introspection.TypedEstimates

open Finset Matrix Classical
set_option linter.unusedSectionVars false

variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

/-- The reported question prefix, with a shared dummy outcome for answer
constructors that do not fit the specified auxiliary question type. -/
def reportedPrefix (P : CL.CLFun F ι ℓ) (m : ℕ) :
    AuxType ℓ → ParsedAnswer (ι → F) A PauliAnswer → Option (ι → F)
  | .introspect, .pair y _ => some (P.outputPrefix m y)
  | .sample, .pair y _ => some (P.outputPrefix m y)
  | .read, .read y _ _ => some (P.outputPrefix m y)
  | .hide _, .hide y _ _ => some (P.outputPrefix m y)
  | _, _ => none

variable (L : Bool → CL.CLFun F ι ℓ) (X Z : PauliType)
  (projectPauli : PauliAnswer → ι → F)
  (D : (ι → F) → (ι → F) → A → A → Bool)
  (DP : PauliType → PauliType → PauliAnswer → PauliAnswer → Bool)

/-- Every prefix already present at the earlier hiding level agrees on an
accepted adjacent hiding edge, including arbitrary off-image claimed outputs. -/
theorem check_hiding_next_prefix (w : Bool) (hL : (L w).SupportedOn univ)
    (k j : Fin ℓ) (hk : k.val + 1 = j.val) (m : ℕ) (hm : m ≤ k.val)
    {a b : ParsedAnswer (ι → F) A PauliAnswer}
    (h : TypedPredicate.check L X Z projectPauli D DP
      (QuestionType.hide w k) (QuestionType.hide w j) a b = true) :
    reportedPrefix (L w) m (.hide k) a = reportedPrefix (L w) m (.hide j) b := by
  have hf := TypedPredicate.check_formats L X Z projectPauli D DP h
  cases a <;> cases b <;> simp [TypedPredicate.fits] at hf
  rename_i y yp x z zp t
  have hp := (TypedPredicate.check_hiding_next L X Z projectPauli D DP w k j hk h).1
  have he := congrArg ((L w).outputPrefix m) hp
  simp only [CLChecks.outputPrefix_outputPrefix hL _ hm] at he
  exact congrArg some he

/-- The last hiding/Read test preserves every question prefix available at
the last hiding level. -/
theorem check_hiding_read_prefix (w : Bool) (hL : (L w).SupportedOn univ)
    (k : Fin ℓ) (hk : k.val + 1 = ℓ) (m : ℕ) (hm : m ≤ k.val)
    {a b : ParsedAnswer (ι → F) A PauliAnswer}
    (h : TypedPredicate.check L X Z projectPauli D DP
      (QuestionType.hide w k) (QuestionType.read w) a b = true) :
    reportedPrefix (L w) m (.hide k) a = reportedPrefix (L w) m .read b := by
  have hf := TypedPredicate.check_formats L X Z projectPauli D DP h
  cases a <;> cases b <;> simp [TypedPredicate.fits] at hf
  rename_i y yp x z zp b
  have hp := (TypedPredicate.check_hiding_read L X Z projectPauli D DP w k hk h).1
  have he := congrArg ((L w).outputPrefix m) hp
  have hm' : m ≤ ℓ - 1 := by omega
  simp only [CLChecks.outputPrefix_outputPrefix hL _ hm'] at he
  exact congrArg some he

/-- Read and Introspect preserve every question prefix in this orientation. -/
theorem check_read_introspect_prefix (w : Bool) (m : ℕ)
    {a b : ParsedAnswer (ι → F) A PauliAnswer}
    (h : TypedPredicate.check L X Z projectPauli D DP
      (QuestionType.read w) (QuestionType.introspect w) a b = true) :
    reportedPrefix (L w) m .read a = reportedPrefix (L w) m .introspect b := by
  have hf := TypedPredicate.check_formats L X Z projectPauli D DP h
  cases a <;> cases b <;> simp [TypedPredicate.fits] at hf
  rename_i y yp a z b
  have hd := TypedPredicate.check_directed_reversed L X Z projectPauli D DP h
  simp only [TypedPredicate.directed, ↓reduceIte] at hd
  have he : z = y ∧ b = a := @of_decide_eq_true _ (Classical.propDecidable _) hd
  exact congrArg (fun y => some ((L w).outputPrefix m y)) he.1.symm

/-- The actual auxiliary path starting at hiding level `j`, followed by Read
and Introspect. Beyond the endpoint it remains at Introspect. -/
def prefixChainType (j : Fin ℓ) (i : ℕ) : AuxType ℓ :=
  if h : j.val + i < ℓ then .hide ⟨j.val + i, h⟩
  else if j.val + i = ℓ then .read else .introspect

@[simp] theorem prefixChainType_zero (j : Fin ℓ) : prefixChainType j 0 = .hide j := by
  simp [prefixChainType, j.isLt]

@[simp] theorem prefixChainType_end (j : Fin ℓ) :
    prefixChainType j (ℓ - j.val + 1) = .introspect := by
  have he : j.val + (ℓ - j.val + 1) = ℓ + 1 := by omega
  simp [prefixChainType, he]

variable [DecidableEq PauliType]

/-- Every step of this path is an actual edge of the introspection graph. -/
theorem prefixChainType_adj (E : PauliType → PauliType → Bool) (w : Bool)
    (j : Fin ℓ) (i : ℕ) (hi : i < ℓ - j.val + 1) :
    TypeGraph.Adj E X Z (.inr (prefixChainType j i, w))
      (.inr (prefixChainType j (i + 1), w)) := by
  by_cases hs : j.val + (i + 1) < ℓ
  · have hp : j.val + i < ℓ := by omega
    simp only [prefixChainType, dif_pos hs, dif_pos hp]
    exact TypeGraph.adj_hide_next E X Z w _ _ (by simp; omega)
  · by_cases hp : j.val + i < ℓ
    · have he : j.val + (i + 1) = ℓ := by omega
      simp only [prefixChainType, dif_neg hs, dif_pos hp, if_pos he]
      exact TypeGraph.adj_hide_read E X Z w _ (by simp; omega)
    · have he : j.val + i = ℓ := by omega
      have hn : j.val + (i + 1) ≠ ℓ := by omega
      simp only [prefixChainType, dif_neg hs, dif_neg hp, if_pos he, if_neg hn]
      exact TypeGraph.symmetric E X Z _ _ (TypeGraph.adj_introspect_read E X Z w)

/-- Accepted answers on every actual path edge preserve the requested earlier
prefix. There is no additional accepted-answer hypothesis in the final bound. -/
theorem prefixChainType_check (w : Bool) (hL : (L w).SupportedOn univ)
    (j : Fin ℓ) (m : ℕ) (hm : m ≤ j.val) (i : ℕ) (hi : i < ℓ - j.val + 1)
    {a b : ParsedAnswer (ι → F) A PauliAnswer}
    (h : TypedPredicate.check L X Z projectPauli D DP
      (.inr (prefixChainType j i, w)) (.inr (prefixChainType j (i + 1), w)) a b = true) :
    reportedPrefix (L w) m (prefixChainType j i) a =
      reportedPrefix (L w) m (prefixChainType j (i + 1)) b := by
  by_cases hs : j.val + (i + 1) < ℓ
  · have hp : j.val + i < ℓ := by omega
    simp only [prefixChainType, dif_pos hs, dif_pos hp] at h ⊢
    exact check_hiding_next_prefix L X Z projectPauli D DP w hL _ _
      (by simp; omega) m (by simp; omega) h
  · by_cases hp : j.val + i < ℓ
    · have he : j.val + (i + 1) = ℓ := by omega
      simp only [prefixChainType, dif_neg hs, dif_pos hp, if_pos he] at h ⊢
      exact check_hiding_read_prefix L X Z projectPauli D DP w hL _
        (by simp; omega) m (by simp; omega) h
    · have he : j.val + i = ℓ := by omega
      have hn : j.val + (i + 1) ≠ ℓ := by omega
      simp only [prefixChainType, dif_neg hs, dif_neg hp, if_pos he, if_neg hn] at h ⊢
      exact check_read_introspect_prefix L X Z projectPauli D DP w m h

end MIPRE.Introspection.TypedEstimates

end

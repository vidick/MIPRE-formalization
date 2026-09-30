/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.ProductStageZTests
public import MIPRE.Foundations.Introspection.StrategyReplacementValue

@[expose] public section

/-! # Exact normalization of the Introspect answer format

All malformed Introspect constructors are already rejected by the parsed
predicate. They may therefore be merged into one malformed representative,
without assuming that their effects vanish and without changing game value.
The normalized measurement factors exactly through its full option-valued
question/answer report, and preserves that report and projectivity.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the measurements are POVMs in any
ordered `⋆`-ring, and the value identity holds in any bipartite model.
-/

noncomputable section
namespace MIPRE.Introspection
open Finset Matrix Classical
set_option linter.unusedSectionVars false

variable {V A PauliAnswer : Type*}

/-- A fixed malformed representative avoids any inhabitedness requirement
on the source-answer and Pauli-answer alphabets. -/
def restoreIntroAnswer [Zero V] : Option (V × A) → ParsedAnswer V A PauliAnswer
  | none => .hide 0 0 0
  | some p => .pair p.1 p.2

section Answer
variable {F ι PauliType : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

@[simp] theorem introspectPair_restoreIntroAnswer (a : Option ((ι → F) × A)) :
    TypedEstimates.introspectPair (restoreIntroAnswer (PauliAnswer := PauliAnswer) a) = a := by
  cases a <;> rfl

def canonicalIntroAnswer (a : ParsedAnswer (ι → F) A PauliAnswer) :
    ParsedAnswer (ι → F) A PauliAnswer :=
  restoreIntroAnswer (TypedEstimates.introspectPair a)

@[simp] theorem introspectPair_canonicalIntroAnswer
    (a : ParsedAnswer (ι → F) A PauliAnswer) :
    TypedEstimates.introspectPair (canonicalIntroAnswer a) = TypedEstimates.introspectPair a :=
  introspectPair_restoreIntroAnswer _

theorem canonicalIntroAnswer_idempotent (a : ParsedAnswer (ι → F) A PauliAnswer) :
    canonicalIntroAnswer (canonicalIntroAnswer a) = canonicalIntroAnswer a := by
  simp only [canonicalIntroAnswer, introspectPair_restoreIntroAnswer]

theorem check_canonicalIntroAnswer_left
    (L : Bool → CL.CLFun F ι ℓ) (X Z : PauliType)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → PauliAnswer → PauliAnswer → Bool)
    (w : Bool) (t : QuestionType PauliType ℓ)
    (a b : ParsedAnswer (ι → F) A PauliAnswer) :
    TypedPredicate.check L X Z projectPauli D DP (QuestionType.introspect w) t
      (canonicalIntroAnswer a) b =
      TypedPredicate.check L X Z projectPauli D DP (QuestionType.introspect w) t a b := by
  cases a
  case pair => rfl
  all_goals simp [canonicalIntroAnswer, restoreIntroAnswer, TypedEstimates.introspectPair,
    TypedPredicate.check, TypedPredicate.fits]

theorem check_canonicalIntroAnswer_right
    (L : Bool → CL.CLFun F ι ℓ) (X Z : PauliType)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → PauliAnswer → PauliAnswer → Bool)
    (w : Bool) (t : QuestionType PauliType ℓ)
    (a b : ParsedAnswer (ι → F) A PauliAnswer) :
    TypedPredicate.check L X Z projectPauli D DP t (QuestionType.introspect w)
      a (canonicalIntroAnswer b) =
      TypedPredicate.check L X Z projectPauli D DP t (QuestionType.introspect w) a b := by
  cases b
  case pair => rfl
  all_goals simp [canonicalIntroAnswer, restoreIntroAnswer, TypedEstimates.introspectPair,
    TypedPredicate.check, TypedPredicate.fits]

end Answer

section Measurements
variable {F ι PauliType κ R : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] [Fintype PauliType] [DecidableEq PauliType]
  [Fintype κ] [DecidableEq κ] [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
  [Fintype A] [Fintype PauliAnswer] {ℓ : ℕ}

/-- The actual family changes only the selected zero-content Introspect
question, by deterministic postprocessing of its old answer. -/
def canonicalizeIntro
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) R) (w : Bool) :=
  fun q => if q = (QuestionType.introspect w, 0) then (MA q).map canonicalIntroAnswer else MA q

theorem canonicalizeIntro_at
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) R) (w : Bool) :
    canonicalizeIntro MA w (QuestionType.introspect w, 0) =
      (MA (QuestionType.introspect w, 0)).map canonicalIntroAnswer := by
  simp [canonicalizeIntro]

theorem canonicalizeIntro_other
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) R) (w : Bool)
    (q : CL.Detyping.Question (QuestionType PauliType ℓ) κ)
    (hq : q ≠ (QuestionType.introspect w, 0)) : canonicalizeIntro MA w q = MA q := by
  simp only [canonicalizeIntro, if_neg hq]

theorem canonicalizeIntro_factor
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) R) (w : Bool) :
    canonicalizeIntro MA w (QuestionType.introspect w, 0) =
      ((MA (QuestionType.introspect w, 0)).map TypedEstimates.introspectPair).map
        restoreIntroAnswer := by
  rw [canonicalizeIntro_at, POVMIn.map_map]
  rfl

theorem restoreIntroAnswer_map_recover (M : POVMIn (Option ((ι → F) × A)) R) :
    (M.map (restoreIntroAnswer (PauliAnswer := PauliAnswer))).map TypedEstimates.introspectPair = M := by
  rw [POVMIn.map_map]
  simp only [introspectPair_restoreIntroAnswer]
  exact POVMIn.map_id M

theorem canonicalizeIntro_recover
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) R) (w : Bool) :
    (canonicalizeIntro MA w (QuestionType.introspect w, 0)).map TypedEstimates.introspectPair =
      (MA (QuestionType.introspect w, 0)).map TypedEstimates.introspectPair := by
  rw [canonicalizeIntro_factor, restoreIntroAnswer_map_recover]

theorem canonicalizeIntro_isPVM
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) R) (w : Bool)
    (hMA : ∀ q, IsPVMIn (MA q).op)
    (q : CL.Detyping.Question (QuestionType PauliType ℓ) κ) :
    IsPVMIn (canonicalizeIntro MA w q).op := by
  by_cases hq : q = (QuestionType.introspect w, 0)
  · simp only [canonicalizeIntro, if_pos hq]
    exact POVMIn.isPVMIn_map (hMA q) canonicalIntroAnswer
  · simpa only [canonicalizeIntro, if_neg hq] using hMA q

end Measurements

namespace TypedEstimates
variable {F ι PauliType PauliAnswer κ A : Type*}
  [Field F] [Fintype F] [DecidableEq F] [Fintype ι] [DecidableEq ι]
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer] [Fintype A]
  [Fintype κ] [DecidableEq κ] {ℓ : ℕ}
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ]

theorem canonicalizeIntro_condWin
    (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
      PauliAnswer → PauliAnswer → Bool)
    (Ψ : BipartiteModel 𝒞 𝒜 ℬ)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) 𝒜)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) ℬ)
    (w : Bool) (q r : CL.Detyping.Question (QuestionType PauliType ℓ) κ) :
    Ψ.condWin (parsedGame E X Z P L projectPauli D DP) (canonicalizeIntro MA w) MB q r =
      Ψ.condWin (parsedGame E X Z P L projectPauli D DP) MA MB q r := by
  by_cases hq : q = (QuestionType.introspect w, 0)
  · subst q
    change testAcceptance Ψ
      (questionCheck L X Z projectPauli D DP (QuestionType.introspect w, 0) r)
      (canonicalizeIntro MA w (QuestionType.introspect w, 0)).op (MB r).op = _
    rw [canonicalizeIntro_at, testAcceptance_map_left]
    have hd : (fun a b => questionCheck L X Z projectPauli D DP
        (QuestionType.introspect w, 0) r (canonicalIntroAnswer a) b) =
        questionCheck L X Z projectPauli D DP (QuestionType.introspect w, 0) r := by
      funext a b
      exact check_canonicalIntroAnswer_left L X Z projectPauli D _ w r.1 a b
    rw [hd]
    rfl
  · simp only [BipartiteModel.condWin, canonicalizeIntro_other MA w q hq]

/-- Format normalization has exactly the original parsed-game value,
including the entire malformed-answer mass. -/
theorem canonicalizeIntro_value
    (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
      PauliAnswer → PauliAnswer → Bool)
    (Ψ : BipartiteModel 𝒞 𝒜 ℬ)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) 𝒜)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) ℬ) (w : Bool) :
    Ψ.povmValue (parsedGame E X Z P L projectPauli D DP) (canonicalizeIntro MA w) MB =
      Ψ.povmValue (parsedGame E X Z P L projectPauli D DP) MA MB := by
  simp only [BipartiteModel.povmValue, canonicalizeIntro_condWin]

end TypedEstimates
end MIPRE.Introspection
end

end

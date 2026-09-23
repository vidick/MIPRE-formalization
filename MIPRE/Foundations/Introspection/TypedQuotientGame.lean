/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.TypedQuotientPredicate
import MIPRE.Foundations.Introspection.TypedEstimates
import MIPRE.Foundations.GameTransportByQuestion
import MIPRE.Foundations.GameDouble

/-! # Finite-game transport for quotient hiding checks

The question law is unchanged. Decoding dual answer coordinates gives a
legacy strategy with at least the original value, on the same registers and
state and with every Pauli-question effect unchanged. In the other direction,
copying a legacy strategy preserves perfect PCC completeness and its dimension.
-/

noncomputable section
namespace MIPRE.Introspection.AuxiliaryQuotient
open Classical
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency true

variable {PauliType PauliAnswer F κ A : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Fintype κ] [DecidableEq κ] [Fintype A]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
  (E : PauliType → PauliType → Bool) (X Z : PauliType)
  (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F (ι) ℓ)
  (project : PauliAnswer → ι → F)
  (D : (ι → F) → (ι → F) → A → A → Bool)
  (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
    PauliAnswer → PauliAnswer → Bool)

/-- The complete quotient predicate at actual raw typed questions. -/
def questionCheck (q r : CL.Detyping.Question (QuestionType PauliType ℓ) κ) :
    ParsedAnswer (ι → F) A PauliAnswer → ParsedAnswer (ι → F) A PauliAnswer → Bool :=
  check L X Z project D (fun p s => DP p s q.2 r.2) q.1 r.1

/-- The quotient game retains the full legacy question-pair law. -/
def game : Game (CL.Detyping.Question (QuestionType PauliType ℓ) κ)
    (CL.Detyping.Question (QuestionType PauliType ℓ) κ)
    (ParsedAnswer (ι → F) A PauliAnswer) (ParsedAnswer (ι → F) A PauliAnswer) :=
  TypedPresentation.game E X Z ℓ P (questionCheck X Z L project D DP)

/-- The quotient and legacy games have exactly the same question law. -/
theorem game_mu (q r : CL.Detyping.Question (QuestionType PauliType ℓ) κ) :
    (game E X Z P L project D DP).μ q r =
      (TypedEstimates.parsedGame E X Z P L project D DP).μ q r := rfl

/-- Legacy acceptance implies quotient acceptance on every raw tuple. -/
theorem game_accepts_of_legacy (hL : ∀ w, (L w).SupportedOn Finset.univ)
    (q r : CL.Detyping.Question (QuestionType PauliType ℓ) κ)
    (a b : ParsedAnswer (ι → F) A PauliAnswer)
    (h : (TypedEstimates.parsedGame E X Z P L project D DP).D q r a b = true) :
    (game E X Z P L project D DP).D q r a b = true :=
  check_of_legacy L X Z project D hL _ q.1 r.1 a b h

/-- Decode auxiliary answers according to their question's side. -/
abbrev decodedStrategy (S : TensorProductStrategy (game E X Z P L project D DP)) :
    TensorProductStrategy (TypedEstimates.parsedGame E X Z P L project D DP) :=
  S.mergeAnswersByQuestion _ (fun q => decodeAnswer L q.1) (fun q => decodeAnswer L q.1)

/-- Deterministic answer decoding does not decrease the winning probability. -/
theorem value_le_decodedStrategy (hL : ∀ w, (L w).SupportedOn Finset.univ)
    (S : TensorProductStrategy (game E X Z P L project D DP)) :
    S.value ≤ (decodedStrategy E X Z P L project D DP S).value := by
  apply S.value_le_mergeAnswersByQuestion
    (TypedEstimates.parsedGame E X Z P L project D DP)
    (fun q => decodeAnswer L q.1) (fun q => decodeAnswer L q.1) (fun _ _ => rfl)
  intro q r a b h
  exact check_sound L X Z project D hL _ q.1 r.1 a b h

/-- Any failure bound for the quotient strategy also bounds its legacy decoding. -/
theorem decodedStrategy_failure_le (hL : ∀ w, (L w).SupportedOn Finset.univ)
    (S : TensorProductStrategy (game E X Z P L project D DP))
    {ε : ℝ} (hS : 1 - S.value ≤ ε) :
    1 - (decodedStrategy E X Z P L project D DP S).value ≤ ε :=
  (sub_le_sub_left (value_le_decodedStrategy E X Z P L project D DP hL S) 1).trans hS

/-- Decoding preserves the literal original shared state. -/
theorem decodedStrategy_state (S : TensorProductStrategy (game E X Z P L project D DP)) :
    S.MergeByQuestionStateEq (TypedEstimates.parsedGame E X Z P L project D DP)
      (fun q => decodeAnswer L q.1) (fun q => decodeAnswer L q.1) :=
  S.mergeByQuestionStateEq _ _ _

set_option linter.defProp false in
/-- Decoding preserves both register dimensions. The inferred exact equality
avoids reducing concrete game definitions inside strategy projections. -/
def decodedStrategy_dimensions
    (S : TensorProductStrategy (game E X Z P L project D DP)) :=
  S.mergeAnswersByQuestion_dimensions (TypedEstimates.parsedGame E X Z P L project D DP)
    (fun q => decodeAnswer L q.1) (fun q => decodeAnswer L q.1)

/-- Every Alice effect at every Pauli question is unchanged. -/
theorem decodedStrategy_pauli_A (S : TensorProductStrategy (game E X Z P L project D DP))
    (p : PauliType) (x : κ → ZMod 2) (a : ParsedAnswer (ι → F) A PauliAnswer) :
    S.MergeByQuestionPAEq (TypedEstimates.parsedGame E X Z P L project D DP)
      (fun q => decodeAnswer L q.1) (fun q => decodeAnswer L q.1) (.inl p,x) a :=
  S.mergeByQuestionPAEq _ _ _ _ _ (fun _ => rfl)

/-- Every Bob effect at every Pauli question is unchanged. -/
theorem decodedStrategy_pauli_B (S : TensorProductStrategy (game E X Z P L project D DP))
    (p : PauliType) (x : κ → ZMod 2) (a : ParsedAnswer (ι → F) A PauliAnswer) :
    S.MergeByQuestionPBEq (TypedEstimates.parsedGame E X Z P L project D DP)
      (fun q => decodeAnswer L q.1) (fun q => decodeAnswer L q.1) (.inl p,x) a :=
  S.mergeByQuestionPBEq _ _ _ _ _ (fun _ => rfl)

/-- The quotient relaxation has exactly the legacy quantum value. -/
theorem quantumValue_eq (hL : ∀ w, (L w).SupportedOn Finset.univ) :
    quantumValue (game E X Z P L project D DP) =
      quantumValue (TypedEstimates.parsedGame E X Z P L project D DP) := by
  apply le_antisymm
  · refine Real.iSup_le (fun S => ?_) (quantumValue_nonneg _)
    exact (value_le_decodedStrategy E X Z P L project D DP hL S).trans
      (le_ciSup (TensorProductStrategy.bddAbove_range_value _)
        (decodedStrategy E X Z P L project D DP S))
  · exact quantumValue_mono _ _ (game_mu E X Z P L project D DP)
      (game_accepts_of_legacy E X Z P L project D DP hL)

variable [DecidableEq A] [DecidableEq PauliAnswer]

/-- Copy the honest synchronous data to the doubled quotient game. -/
abbrev copiedPCC (S : SyncStrategy (TypedEstimates.parsedGame E X Z P L project D DP).doubled) :
    SyncStrategy (game E X Z P L project D DP).doubled := S.copy _

/-- Copying an honest strategy keeps its PCC property. -/
theorem copiedPCC_isPCC
    (S : SyncStrategy (TypedEstimates.parsedGame E X Z P L project D DP).doubled)
    (hS : S.IsPCC) : (copiedPCC E X Z P L project D DP S).IsPCC :=
  SyncStrategy.isPCC_copy hS _ (fun _ _ => rfl)

/-- Every perfect legacy PCC strategy remains perfect in the quotient game. -/
theorem copiedPCC_value_eq_one (hL : ∀ w, (L w).SupportedOn Finset.univ)
    (S : SyncStrategy (TypedEstimates.parsedGame E X Z P L project D DP).doubled)
    (hS : S.value = 1) : (copiedPCC E X Z P L project D DP S).value = 1 := by
  apply S.copy_value_eq_one (game E X Z P L project D DP).doubled (fun _ _ => rfl) _ hS
  intro q r a b h
  simp only [Game.doubled_D] at h ⊢
  split_ifs at h ⊢ with ht
  · exact game_accepts_of_legacy E X Z P L project D DP hL q.2 r.2 a b h

set_option linter.defProp false in
/-- Copying to the quotient game preserves the honest PCC dimension exactly. -/
def copiedPCC_dimension
    (S : SyncStrategy (TypedEstimates.parsedGame E X Z P L project D DP).doubled) :=
  S.copy_d (game E X Z P L project D DP).doubled

end MIPRE.Introspection.AuxiliaryQuotient
